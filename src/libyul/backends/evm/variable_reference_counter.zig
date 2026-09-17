// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Scope-aware reference counting used by the classic EVM code generator's
//! stack-slot reuse pass.

const std = @import("std");
const AST = @import("../../ast.zig");
const AsmAnalysisInfo = @import("../../asm_analysis_info.zig").AsmAnalysisInfo;
const ScopeModule = @import("../../scope.zig");
const Scope = ScopeModule.Scope;
const Variable = ScopeModule.Variable;
const YulName = @import("../../yul_name.zig").YulName;

pub const ReferenceMap = std.AutoHashMap(*const Variable, u32);

pub const CountError = std.mem.Allocator.Error || error{
    InvalidAnalysisInfo,
    ReferenceCountOverflow,
};

pub const VariableReferenceCounter = struct {
    allocator: std.mem.Allocator,
    info: *const AsmAnalysisInfo,
    current_scope: ?*Scope = null,
    references: ReferenceMap,

    pub fn run(
        allocator: std.mem.Allocator,
        info: *const AsmAnalysisInfo,
        block: *const AST.Block,
    ) CountError!ReferenceMap {
        var counter: VariableReferenceCounter = .{
            .allocator = allocator,
            .info = info,
            .references = ReferenceMap.init(allocator),
        };
        errdefer counter.references.deinit();
        try counter.visitBlock(block);
        return counter.references;
    }

    fn visitExpression(self: *VariableReferenceCounter, expression: *const AST.Expression) CountError!void {
        switch (expression.*) {
            .literal => {},
            .identifier => |*identifier| try self.increaseRefIfFound(identifier.name),
            .function_call => |*call| {
                // The function name is deliberately not a variable reference.
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
        }
    }

    fn visitStatement(self: *VariableReferenceCounter, statement: *const AST.Statement) CountError!void {
        switch (statement.*) {
            .expression_statement => |*node| try self.visitExpression(&node.expression),
            .assignment => |*node| {
                for (node.variable_names.items) |*identifier|
                    try self.increaseRefIfFound(identifier.name);
                try self.visitExpression(node.value orelse return error.InvalidAnalysisInfo);
            },
            .variable_declaration => |*node| {
                if (node.value) |value| try self.visitExpression(value);
            },
            .function_definition => |*node| try self.visitFunctionDefinition(node),
            .if_statement => |*node| {
                try self.visitExpression(node.condition orelse return error.InvalidAnalysisInfo);
                try self.visitBlock(&node.body);
            },
            .switch_statement => |*node| {
                try self.visitExpression(node.expression orelse return error.InvalidAnalysisInfo);
                for (node.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*node| try self.visitForLoop(node),
            .block => |*node| try self.visitBlock(node),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitFunctionDefinition(
        self: *VariableReferenceCounter,
        function: *const AST.FunctionDefinition,
    ) CountError!void {
        const original_scope = self.current_scope;
        defer self.current_scope = original_scope;
        const virtual_block = self.info.getVirtualBlock(function) orelse
            return error.InvalidAnalysisInfo;
        self.current_scope = self.info.getScope(virtual_block) orelse
            return error.InvalidAnalysisInfo;
        for (function.return_variables.items) |return_variable|
            try self.increaseRefIfFound(return_variable.name);
        try self.visitBlock(&function.body);
    }

    fn visitForLoop(self: *VariableReferenceCounter, loop: *const AST.ForLoop) CountError!void {
        const original_scope = self.current_scope;
        defer self.current_scope = original_scope;
        self.current_scope = self.info.getScope(&loop.pre) orelse
            return error.InvalidAnalysisInfo;
        for (loop.pre.statements.items) |*statement| try self.visitStatement(statement);
        try self.visitExpression(loop.condition orelse return error.InvalidAnalysisInfo);
        try self.visitBlock(&loop.body);
        try self.visitBlock(&loop.post);
    }

    fn visitBlock(self: *VariableReferenceCounter, block: *const AST.Block) CountError!void {
        const original_scope = self.current_scope;
        defer self.current_scope = original_scope;
        self.current_scope = self.info.getScope(block) orelse return error.InvalidAnalysisInfo;
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn increaseRefIfFound(self: *VariableReferenceCounter, name: YulName) CountError!void {
        const scope = self.current_scope orelse return error.InvalidAnalysisInfo;
        const identifier = scope.lookupConst(name) orelse return;
        switch (identifier.*) {
            .function => {},
            .variable => |*variable| {
                const result = try self.references.getOrPut(variable);
                if (!result.found_existing) result.value_ptr.* = 0;
                if (result.value_ptr.* == std.math.maxInt(u32))
                    return error.ReferenceCountOverflow;
                result.value_ptr.* += 1;
            },
        }
    }
};

test "reference counting distinguishes equal names in separate function scopes" {
    const Parser = @import("../../asm_parser.zig").Parser;
    const ScopeFiller = @import("../../scope_filler.zig").ScopeFiller;
    const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := 1 function f(a) -> r { r := add(a, a) } function g(a) -> r { r := a } x := x }",
        "references.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    defer info.deinit();
    var filler = try ScopeFiller.init(&info, &reporter);
    try std.testing.expect(try filler.fill(ast.root()));

    var references = try VariableReferenceCounter.run(allocator, &info, ast.root());
    defer references.deinit();
    const x = try YulName.init("x");
    const a = try YulName.init("a");
    const r = try YulName.init("r");
    const root_scope = info.getScope(ast.root()).?;
    const outer_x = &root_scope.lookupConst(x).?.variable;
    const first_function = &ast.root().statements.items[1].function_definition;
    const first_scope = info.getScope(info.getVirtualBlock(first_function).?).?;
    const first_argument = &first_scope.lookupConst(a).?.variable;
    const first_result = &first_scope.lookupConst(r).?.variable;
    const second_function = &ast.root().statements.items[2].function_definition;
    const second_scope = info.getScope(info.getVirtualBlock(second_function).?).?;
    const second_argument = &second_scope.lookupConst(a).?.variable;
    const second_result = &second_scope.lookupConst(r).?.variable;
    try std.testing.expect(first_argument != second_argument);
    try std.testing.expect(first_result != second_result);
    try std.testing.expectEqual(@as(u32, 2), references.get(outer_x).?);
    try std.testing.expectEqual(@as(u32, 2), references.get(first_argument).?);
    try std.testing.expectEqual(@as(u32, 2), references.get(first_result).?);
    try std.testing.expectEqual(@as(u32, 1), references.get(second_argument).?);
    try std.testing.expectEqual(@as(u32, 2), references.get(second_result).?);
}
