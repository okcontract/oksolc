// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Scope construction and declaration-clash diagnostics for Yul ASTs.

const std = @import("std");
const AST = @import("ast.zig");
const AsmAnalysisInfo = @import("asm_analysis_info.zig").AsmAnalysisInfo;
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const Scope = @import("scope.zig").Scope;

pub const FillError = std.mem.Allocator.Error || error{
    FatalDiagnostic,
    InvalidAst,
    InvalidYulStringHandle,
};

pub const ScopeFiller = struct {
    info: *AsmAnalysisInfo,
    error_reporter: *Diagnostics.ErrorReporter,
    current_scope: *Scope,

    pub fn init(
        info: *AsmAnalysisInfo,
        error_reporter: *Diagnostics.ErrorReporter,
    ) std.mem.Allocator.Error!ScopeFiller {
        return .{
            .info = info,
            .error_reporter = error_reporter,
            .current_scope = try info.getOrCreateScope(null),
        };
    }

    pub fn fill(self: *ScopeFiller, block: *const AST.Block) FillError!bool {
        return self.visitBlock(block);
    }

    fn visitExpression(self: *ScopeFiller, expression: *const AST.Expression) FillError!bool {
        _ = self;
        return switch (expression.*) {
            .literal, .identifier, .function_call => true,
        };
    }

    fn visitStatement(self: *ScopeFiller, statement: *const AST.Statement) FillError!bool {
        return switch (statement.*) {
            .expression_statement => |*node| self.visitExpression(&node.expression),
            .assignment, .break_statement, .continue_statement, .leave_statement => true,
            .variable_declaration => |*node| self.visitVariableDeclaration(node),
            .function_definition => |*node| self.visitFunctionDefinition(node),
            .if_statement => |*node| self.visitBlock(&node.body),
            .switch_statement => |*node| self.visitSwitch(node),
            .for_loop => |*node| self.visitForLoop(node),
            .block => |*node| self.visitBlock(node),
        };
    }

    fn visitVariableDeclaration(
        self: *ScopeFiller,
        declaration: *const AST.VariableDeclaration,
    ) FillError!bool {
        for (declaration.variables.items) |*variable| {
            if (!try self.registerVariable(
                variable,
                nativeLocation(declaration.debug_data),
                self.current_scope,
            )) return false;
        }
        return true;
    }

    fn visitFunctionDefinition(
        self: *ScopeFiller,
        definition: *const AST.FunctionDefinition,
    ) FillError!bool {
        const virtual_block = try self.info.createVirtualBlock(definition);
        const variable_scope = try self.info.getOrCreateScope(virtual_block);
        variable_scope.super_scope = self.current_scope;
        variable_scope.function_scope = true;
        const previous_scope = self.current_scope;
        self.current_scope = variable_scope;
        defer self.current_scope = previous_scope;

        var success = true;
        for (definition.parameters.items) |*variable| {
            if (!try self.registerVariable(
                variable,
                nativeLocation(definition.debug_data),
                variable_scope,
            )) success = false;
        }
        for (definition.return_variables.items) |*variable| {
            if (!try self.registerVariable(
                variable,
                nativeLocation(definition.debug_data),
                variable_scope,
            )) success = false;
        }
        if (!try self.visitBlock(&definition.body)) success = false;
        return success;
    }

    fn visitSwitch(self: *ScopeFiller, switch_statement: *const AST.Switch) FillError!bool {
        var success = true;
        for (switch_statement.cases.items) |*case_value| {
            if (!try self.visitBlock(&case_value.body)) success = false;
        }
        return success;
    }

    fn visitForLoop(self: *ScopeFiller, loop: *const AST.ForLoop) FillError!bool {
        const original_scope = self.current_scope;
        var success = true;
        if (!try self.visitBlock(&loop.pre)) success = false;
        self.current_scope = self.info.getScope(&loop.pre) orelse return error.InvalidAst;
        defer self.current_scope = original_scope;
        if (loop.condition) |condition| {
            if (!try self.visitExpression(condition)) success = false;
        } else return error.InvalidAst;
        if (!try self.visitBlock(&loop.body)) success = false;
        if (!try self.visitBlock(&loop.post)) success = false;
        return success;
    }

    fn visitBlock(self: *ScopeFiller, block: *const AST.Block) FillError!bool {
        const block_scope = try self.info.getOrCreateScope(block);
        block_scope.super_scope = self.current_scope;
        const previous_scope = self.current_scope;
        self.current_scope = block_scope;
        defer self.current_scope = previous_scope;

        var success = true;
        for (block.statements.items) |*statement| {
            if (statement.* == .function_definition) {
                if (!try self.registerFunction(&statement.function_definition)) success = false;
            }
        }
        for (block.statements.items) |*statement| {
            if (!try self.visitStatement(statement)) success = false;
        }
        return success;
    }

    fn registerVariable(
        self: *ScopeFiller,
        value: *const AST.NameWithDebugData,
        location: Diagnostics.SourceLocation,
        scope: *Scope,
    ) FillError!bool {
        if (try scope.registerVariable(value.name)) return true;
        const name = try value.name.str();
        const description = try std.fmt.allocPrint(
            self.error_reporter.allocator,
            "Variable name {s} already taken in this scope.",
            .{name},
        );
        defer self.error_reporter.allocator.free(description);
        try self.error_reporter.declarationError(.{ .value = 1395 }, location, description);
        return false;
    }

    fn registerFunction(
        self: *ScopeFiller,
        definition: *const AST.FunctionDefinition,
    ) FillError!bool {
        if (try self.current_scope.registerFunction(
            definition.name,
            definition.parameters.items.len,
            definition.return_variables.items.len,
        )) return true;
        const name = try definition.name.str();
        const description = try std.fmt.allocPrint(
            self.error_reporter.allocator,
            "Function name {s} already taken in this scope.",
            .{name},
        );
        defer self.error_reporter.allocator.free(description);
        try self.error_reporter.declarationError(
            .{ .value = 6052 },
            nativeLocation(definition.debug_data),
            description,
        );
        return false;
    }
};

fn nativeLocation(debug_data: ?@import("../liblangutil/debug_data.zig").DebugData) Diagnostics.SourceLocation {
    return if (debug_data) |debug| debug.native_location else .{};
}

test "scope filler creates function and loop scope topology" {
    const Parser = @import("asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a) -> r { let local := a } let outer := 1 for { let i := 0 } i { i := 1 } { let body := i } }",
        "scope.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    defer info.deinit();
    var filler = try ScopeFiller.init(&info, &reporter);
    try std.testing.expect(try filler.fill(ast.root()));
    const root_scope = info.getScope(ast.root()).?;
    const function_name = try @import("yul_name.zig").YulName.init("f");
    const outer_name = try @import("yul_name.zig").YulName.init("outer");
    try std.testing.expect(root_scope.lookup(function_name).?.* == .function);
    try std.testing.expect(root_scope.lookup(outer_name).?.* == .variable);
    const definition = &ast.root_block.statements.items[0].function_definition;
    const virtual_block = info.getVirtualBlock(definition).?;
    const function_scope = info.getScope(virtual_block).?;
    try std.testing.expect(function_scope.function_scope);
    try std.testing.expect(function_scope.insideFunction());
    try std.testing.expect(function_scope.lookup(outer_name) == null);
    try std.testing.expect(function_scope.exists(outer_name));
}

test "scope filler reports declaration clashes in source order" {
    const Parser = @import("asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function x() {} function f(a, a) {} let x let x }",
        "clash.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    defer info.deinit();
    var filler = try ScopeFiller.init(&info, &reporter);
    try std.testing.expect(!(try filler.fill(ast.root())));
    const diagnostics = reporter.diagnostics();
    try std.testing.expectEqual(@as(usize, 3), diagnostics.len);
    try std.testing.expectEqual(@as(u64, 1395), diagnostics[0].error_id.value);
    try std.testing.expectEqual(@as(u64, 1395), diagnostics[1].error_id.value);
    try std.testing.expectEqual(@as(u64, 1395), diagnostics[2].error_id.value);
}
