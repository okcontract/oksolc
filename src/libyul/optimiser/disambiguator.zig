// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Scope-aware deep copy that assigns a unique name to every declaration.

const std = @import("std");
const AST = @import("../ast.zig");
const AsmAnalysisInfo = @import("../asm_analysis_info.zig").AsmAnalysisInfo;
const Scope = @import("../scope.zig");
const ASTCopierModule = @import("ast_copier.zig");
const NameCollectorModule = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const YulName = @import("../yul_name.zig").YulName;

pub const Disambiguator = struct {
    allocator: std.mem.Allocator,
    copier: ASTCopierModule.ASTCopier,
    info: *const AsmAnalysisInfo,
    externally_used_identifiers: *const NameCollectorModule.NameSet,
    scopes: std.ArrayList(*Scope.Scope) = .empty,
    translations: std.AutoHashMap(*const Scope.Identifier, YulName),
    name_dispenser: NameDispenser,

    pub fn init(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        info: *const AsmAnalysisInfo,
        externally_used_identifiers: *const NameCollectorModule.NameSet,
    ) !Disambiguator {
        var used_names = try externally_used_identifiers.clone(allocator);
        defer used_names.deinit(allocator);
        const name_dispenser = try NameDispenser.initWithUsedNames(
            allocator,
            dialect,
            used_names.take(),
        );
        return .{
            .allocator = allocator,
            .copier = ASTCopierModule.ASTCopier.initWithHooks(allocator, null, .{
                .translate_identifier = translateIdentifier,
                .enter_scope = enterScope,
                .leave_scope = leaveScope,
                .enter_function = enterFunction,
                .leave_function = leaveFunction,
            }),
            .info = info,
            .externally_used_identifiers = externally_used_identifiers,
            .translations = std.AutoHashMap(*const Scope.Identifier, YulName).init(allocator),
            .name_dispenser = name_dispenser,
        };
    }

    pub fn deinit(self: *Disambiguator) void {
        self.scopes.deinit(self.allocator);
        self.translations.deinit();
        self.name_dispenser.deinit();
        self.* = undefined;
    }

    pub fn translateBlock(self: *Disambiguator, block: *const AST.Block) anyerror!AST.Block {
        self.bind();
        const result = try self.copier.translateBlock(block);
        if (self.scopes.items.len != 0) {
            var owned = result;
            owned.deinit(self.allocator);
            return error.UnbalancedDisambiguatorScopes;
        }
        return result;
    }

    pub fn translateAst(self: *Disambiguator, ast: *const AST.AST) anyerror!AST.AST {
        return AST.AST.init(self.allocator, ast.dialect().*, try self.translateBlock(ast.root()));
    }

    fn bind(self: *Disambiguator) void {
        self.copier.context = self;
    }

    fn fromContext(context: ?*anyopaque) *Disambiguator {
        return @ptrCast(@alignCast(context.?));
    }

    fn translateIdentifier(context: ?*anyopaque, original_name: YulName) anyerror!YulName {
        const self = fromContext(context);
        if (self.externally_used_identifiers.contains(original_name)) return original_name;
        const scope = if (self.scopes.items.len == 0)
            return error.MissingDisambiguatorScope
        else
            self.scopes.items[self.scopes.items.len - 1];
        const identifier = scope.lookupConst(original_name) orelse return error.UnknownIdentifier;
        if (self.translations.get(identifier)) |translated| return translated;
        const translated = try self.name_dispenser.newName(original_name);
        try self.translations.put(identifier, translated);
        return translated;
    }

    fn enterScope(context: ?*anyopaque, block: *const AST.Block) anyerror!void {
        const self = fromContext(context);
        const scope = self.info.getScope(block) orelse return error.MissingAnalysisScope;
        try self.scopes.append(self.allocator, scope);
    }

    fn leaveScope(context: ?*anyopaque, block: *const AST.Block) anyerror!void {
        const self = fromContext(context);
        const expected = self.info.getScope(block) orelse return error.MissingAnalysisScope;
        if (self.scopes.items.len == 0 or self.scopes.items[self.scopes.items.len - 1] != expected)
            return error.UnbalancedDisambiguatorScopes;
        _ = self.scopes.pop();
    }

    fn enterFunction(context: ?*anyopaque, function: *const AST.FunctionDefinition) anyerror!void {
        const self = fromContext(context);
        const virtual_block = self.info.getVirtualBlock(function) orelse return error.MissingFunctionScope;
        try enterScope(context, virtual_block);
    }

    fn leaveFunction(context: ?*anyopaque, function: *const AST.FunctionDefinition) anyerror!void {
        const self = fromContext(context);
        const virtual_block = self.info.getVirtualBlock(function) orelse return error.MissingFunctionScope;
        try leaveScope(context, virtual_block);
    }
};

test "disambiguator gives sibling declarations distinct names" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Analysis = @import("../asm_analysis.zig");
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ { let x := 1 pop(x) } { let x := 2 pop(x) } }",
        "disambiguator.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    defer info.deinit();
    var analyzer = Analysis.AsmAnalyzer.init(
        allocator,
        &info,
        &reporter,
        dialect.dialect(),
        .{},
        .{},
        Analysis.instructionValidatorForEVMDialect(&dialect),
    );
    defer analyzer.deinit();
    try std.testing.expect(try analyzer.analyze(ast.root()));
    var external: NameCollectorModule.NameSet = .{};
    defer external.deinit(allocator);
    var disambiguator = try Disambiguator.init(allocator, dialect.dialect(), &info, &external);
    defer disambiguator.deinit();
    var copy = try disambiguator.translateBlock(ast.root());
    defer copy.deinit(allocator);
    const first = copy.statements.items[0].block.statements.items[0].variable_declaration.variables.items[0].name;
    const second = copy.statements.items[1].block.statements.items[0].variable_declaration.variables.items[0].name;
    try std.testing.expect(!first.eql(second));
}
