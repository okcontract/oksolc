// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Lexically resolves user-function calls to their declarations. The result
//! intentionally uses pointer identity and has no deterministic iteration
//! contract, matching the upstream unordered map.

const std = @import("std");
const AST = @import("ast.zig");
const YulName = @import("yul_name.zig").YulName;

pub const ReferenceMap = std.AutoHashMap(
    *const AST.FunctionCall,
    *const AST.FunctionDefinition,
);

pub const FunctionReferenceResolver = struct {
    allocator: std.mem.Allocator,
    function_references: ReferenceMap,
    scopes: std.ArrayList(std.AutoHashMap(YulName, *const AST.FunctionDefinition)) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        ast: *const AST.Block,
    ) !FunctionReferenceResolver {
        var result: FunctionReferenceResolver = .{
            .allocator = allocator,
            .function_references = ReferenceMap.init(allocator),
        };
        errdefer result.deinit();
        try result.visitBlock(ast);
        if (result.scopes.items.len != 0) return error.UnbalancedFunctionScopes;
        return result;
    }

    pub fn deinit(self: *FunctionReferenceResolver) void {
        for (self.scopes.items) |*scope| scope.deinit();
        self.scopes.deinit(self.allocator);
        self.function_references.deinit();
        self.* = undefined;
    }

    pub fn references(self: *const FunctionReferenceResolver) *const ReferenceMap {
        return &self.function_references;
    }

    pub fn takeReferences(self: *FunctionReferenceResolver) ReferenceMap {
        const result = self.function_references;
        self.function_references = ReferenceMap.init(self.allocator);
        return result;
    }

    pub fn resolve(allocator: std.mem.Allocator, ast: *const AST.Block) !ReferenceMap {
        var resolver = try FunctionReferenceResolver.init(allocator, ast);
        defer resolver.deinit();
        return resolver.takeReferences();
    }

    fn visitBlock(self: *FunctionReferenceResolver, block: *const AST.Block) anyerror!void {
        var scope = std.AutoHashMap(YulName, *const AST.FunctionDefinition).init(self.allocator);
        var owns_scope = true;
        defer if (owns_scope) scope.deinit();
        for (block.statements.items) |*statement| if (statement.* == .function_definition)
            try scope.put(statement.function_definition.name, &statement.function_definition);
        try self.scopes.append(self.allocator, scope);
        owns_scope = false;
        defer {
            var removed = self.scopes.pop().?;
            removed.deinit();
        }
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *FunctionReferenceResolver, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| try self.visitExpression(value.value orelse return error.InvalidAst),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| {
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                try self.visitExpression(value.expression orelse return error.InvalidAst);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
                try self.visitBlock(&value.post);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *FunctionReferenceResolver, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .literal, .identifier => {},
            .function_call => |*call| {
                if (call.function_name == .identifier) {
                    var scope_index = self.scopes.items.len;
                    while (scope_index != 0) {
                        scope_index -= 1;
                        if (self.scopes.items[scope_index].get(call.function_name.identifier.name)) |definition| {
                            try self.function_references.put(call, definition);
                            break;
                        }
                    }
                }
                var argument_index = call.arguments.items.len;
                while (argument_index != 0) {
                    argument_index -= 1;
                    try self.visitExpression(&call.arguments.items[argument_index]);
                }
            },
        }
    }
};

test "function references resolve through lexical scopes" {
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const Parser = @import("asm_parser.zig").Parser;
    const EVMDialect = @import("backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.init(.Cancun), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(x) -> r { r := x } function g() -> r { r := f(7) } pop(g()) }",
        "resolver.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var resolver = try FunctionReferenceResolver.init(allocator, ast.root());
    defer resolver.deinit();
    try std.testing.expectEqual(@as(usize, 2), resolver.references().count());
}
