// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Scope-aware renaming that preserves AST storage and declaration order.

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

    /// Rename a private analyzed tree without moving any nodes. Scope records
    /// own their original names, so lookups remain valid as AST names change.
    /// On error names may be partially changed; discard the tree and analysis.
    pub fn run(self: *Disambiguator, block: *AST.Block) !void {
        if (self.scopes.items.len != 0) return error.UnbalancedDisambiguatorScopes;
        try self.visitBlock(block);
        std.debug.assert(self.scopes.items.len == 0);
    }

    fn visitBlock(self: *Disambiguator, block: *AST.Block) anyerror!void {
        try enterScope(self, block);
        defer _ = self.scopes.pop();
        for (block.statements.items) |*statement| switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| {
                for (value.variable_names.items) |*identifier|
                    identifier.name = try translateIdentifier(self, identifier.name);
                if (value.value) |expression| try self.visitExpression(expression);
            },
            .variable_declaration => |*value| {
                for (value.variables.items) |*variable|
                    variable.name = try translateIdentifier(self, variable.name);
                if (value.value) |expression| try self.visitExpression(expression);
            },
            .function_definition => |*value| {
                value.name = try translateIdentifier(self, value.name);
                try enterFunction(self, value);
                defer _ = self.scopes.pop();
                for (value.parameters.items) |*parameter|
                    parameter.name = try translateIdentifier(self, parameter.name);
                for (value.return_variables.items) |*variable|
                    variable.name = try translateIdentifier(self, variable.name);
                try self.visitBlock(&value.body);
            },
            .if_statement => |*value| {
                if (value.condition) |expression| try self.visitExpression(expression);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression| try self.visitExpression(expression);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                // The pre scope encloses condition, post and body. Preserve
                // the copier's declaration order, including its nested pre visit.
                try enterScope(self, &value.pre);
                defer _ = self.scopes.pop();
                try self.visitBlock(&value.pre);
                if (value.condition) |expression| try self.visitExpression(expression);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        };
    }

    fn visitExpression(self: *Disambiguator, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .literal => {},
            .identifier => |*value| value.name = try translateIdentifier(self, value.name),
            .function_call => |*value| {
                if (value.function_name == .identifier)
                    value.function_name.identifier.name = try translateIdentifier(self, value.function_name.identifier.name);
                // Unlike evaluation-order visitors, name allocation follows
                // the copier's left-to-right syntax order.
                for (value.arguments.items) |*argument| try self.visitExpression(argument);
            },
        }
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

test "disambiguator in-place names match the copier across scopes and allocation failures" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Analysis = @import("../asm_analysis.zig");
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Objects = @import("../object.zig");
    const Encoding = @import("../ast_encoding.zig");
    const H256 = @import("../../libsolutil/fixed_hash.zig").H256;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator,
        \\{ let sink := f(1, 2)
        \\  function f(a, b) -> r {
        \\    for { let i := 0x00 } lt(i, a) { i := add(i, 1) } {
        \\      switch i case 0 { r := b continue } default { if i { break } }
        \\    }
        \\    leave
        \\  }
        \\  { let x := 1 pop(x) } { let x := 2 pop(x) }
        \\}
    , "rename.yul", &reporter, dialect.dialect(), .{})).?;
    defer ast.deinit();
    var structure = try Objects.Structure.init(allocator, "");
    defer structure.deinit();
    var info = try Analysis.analyzeStrictBlock(allocator, dialect.dialect(), ast.root(), &structure, Analysis.instructionValidatorForEVMDialect(&dialect));
    defer info.deinit();
    var external: NameCollectorModule.NameSet = .{};
    defer external.deinit(allocator);
    _ = try external.insert(allocator, try YulName.init("f"));
    var oracle = try Disambiguator.init(allocator, dialect.dialect(), &info, &external);
    defer oracle.deinit();
    var expected = try oracle.translateBlock(ast.root());
    defer expected.deinit(allocator);
    const Check = struct {
        fn run(failing: std.mem.Allocator, source: *const AST.AST, evm: *const EVMDialect, shape: *const Objects.Structure, reserved: *const NameCollectorModule.NameSet, expected_hash: H256) !void {
            var copier = ASTCopierModule.ASTCopier.init(failing);
            var result = try copier.translateBlock(source.root());
            defer result.deinit(failing);
            var analysis = try Analysis.analyzeStrictBlock(failing, source.dialect().*, &result, shape, Analysis.instructionValidatorForEVMDialect(evm));
            defer analysis.deinit();
            var renamer = try Disambiguator.init(failing, source.dialect().*, &analysis, reserved);
            defer renamer.deinit();
            const storage = result.statements.items.ptr;
            const arguments = result.statements.items[0].variable_declaration.value.?.function_call.arguments.items.ptr;
            const original_scope = analysis.getScope(&result).?;
            try renamer.run(&result);
            try std.testing.expectEqual(@as(usize, 0), renamer.scopes.items.len);
            try std.testing.expectEqual(storage, result.statements.items.ptr);
            try std.testing.expectEqual(arguments, result.statements.items[0].variable_declaration.value.?.function_call.arguments.items.ptr);
            try std.testing.expectEqual(original_scope, analysis.getScope(&result).?);
            try std.testing.expectEqualDeep(source.root().debug_data, result.debug_data);
            try std.testing.expectEqualDeep(expected_hash, try Encoding.hashBlock(&result));
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ &ast, &dialect, &structure, &external, try Encoding.hashBlock(&expected) });
}
