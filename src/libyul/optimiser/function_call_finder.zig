// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Const and mutable post-order discovery of calls to one disambiguated Yul
//! function handle.

const std = @import("std");
const AST = @import("../ast.zig");
const Utilities = @import("../utilities.zig");

pub fn findFunctionCallsConst(
    allocator: std.mem.Allocator,
    block: *const AST.Block,
    function_handle: AST.FunctionHandle,
) !std.ArrayList(*const AST.FunctionCall) {
    var calls: std.ArrayList(*const AST.FunctionCall) = .empty;
    errdefer calls.deinit(allocator);
    try visitBlockConst(allocator, block, function_handle, &calls);
    return calls;
}

pub fn findFunctionCalls(
    allocator: std.mem.Allocator,
    block: *AST.Block,
    function_handle: AST.FunctionHandle,
) !std.ArrayList(*AST.FunctionCall) {
    var calls: std.ArrayList(*AST.FunctionCall) = .empty;
    errdefer calls.deinit(allocator);
    try visitBlockMutable(allocator, block, function_handle, &calls);
    return calls;
}

pub fn functionHandlesEqual(left: AST.FunctionHandle, right: AST.FunctionHandle) bool {
    if (@intFromEnum(left) != @intFromEnum(right)) return false;
    return switch (left) {
        .user => |name| name.eql(right.user),
        .builtin => |handle| handle.id == right.builtin.id,
    };
}

fn visitExpressionConst(
    allocator: std.mem.Allocator,
    expression: *const AST.Expression,
    function_handle: AST.FunctionHandle,
    calls: *std.ArrayList(*const AST.FunctionCall),
) anyerror!void {
    switch (expression.*) {
        .literal, .identifier => {},
        .function_call => |*call| {
            var index = call.arguments.items.len;
            while (index != 0) {
                index -= 1;
                try visitExpressionConst(allocator, &call.arguments.items[index], function_handle, calls);
            }
            if (functionHandlesEqual(Utilities.functionNameToHandle(&call.function_name), function_handle))
                try calls.append(allocator, call);
        },
    }
}

fn visitStatementConst(
    allocator: std.mem.Allocator,
    statement: *const AST.Statement,
    function_handle: AST.FunctionHandle,
    calls: *std.ArrayList(*const AST.FunctionCall),
) anyerror!void {
    switch (statement.*) {
        .expression_statement => |*value| try visitExpressionConst(allocator, &value.expression, function_handle, calls),
        .assignment => |*value| try visitExpressionConst(allocator, value.value orelse return error.InvalidAst, function_handle, calls),
        .variable_declaration => |*value| if (value.value) |expression|
            try visitExpressionConst(allocator, expression, function_handle, calls),
        .function_definition => |*value| try visitBlockConst(allocator, &value.body, function_handle, calls),
        .if_statement => |*value| {
            try visitExpressionConst(allocator, value.condition orelse return error.InvalidAst, function_handle, calls);
            try visitBlockConst(allocator, &value.body, function_handle, calls);
        },
        .switch_statement => |*value| {
            try visitExpressionConst(allocator, value.expression orelse return error.InvalidAst, function_handle, calls);
            for (value.cases.items) |*case_value|
                try visitBlockConst(allocator, &case_value.body, function_handle, calls);
        },
        .for_loop => |*value| {
            try visitBlockConst(allocator, &value.pre, function_handle, calls);
            try visitExpressionConst(allocator, value.condition orelse return error.InvalidAst, function_handle, calls);
            try visitBlockConst(allocator, &value.body, function_handle, calls);
            try visitBlockConst(allocator, &value.post, function_handle, calls);
        },
        .block => |*value| try visitBlockConst(allocator, value, function_handle, calls),
        .break_statement, .continue_statement, .leave_statement => {},
    }
}

fn visitBlockConst(
    allocator: std.mem.Allocator,
    block: *const AST.Block,
    function_handle: AST.FunctionHandle,
    calls: *std.ArrayList(*const AST.FunctionCall),
) anyerror!void {
    for (block.statements.items) |*statement|
        try visitStatementConst(allocator, statement, function_handle, calls);
}

fn visitExpressionMutable(
    allocator: std.mem.Allocator,
    expression: *AST.Expression,
    function_handle: AST.FunctionHandle,
    calls: *std.ArrayList(*AST.FunctionCall),
) anyerror!void {
    switch (expression.*) {
        .literal, .identifier => {},
        .function_call => |*call| {
            var index = call.arguments.items.len;
            while (index != 0) {
                index -= 1;
                try visitExpressionMutable(allocator, &call.arguments.items[index], function_handle, calls);
            }
            if (functionHandlesEqual(Utilities.functionNameToHandle(&call.function_name), function_handle))
                try calls.append(allocator, call);
        },
    }
}

fn visitStatementMutable(
    allocator: std.mem.Allocator,
    statement: *AST.Statement,
    function_handle: AST.FunctionHandle,
    calls: *std.ArrayList(*AST.FunctionCall),
) anyerror!void {
    switch (statement.*) {
        .expression_statement => |*value| try visitExpressionMutable(allocator, &value.expression, function_handle, calls),
        .assignment => |*value| try visitExpressionMutable(allocator, value.value orelse return error.InvalidAst, function_handle, calls),
        .variable_declaration => |*value| if (value.value) |expression|
            try visitExpressionMutable(allocator, expression, function_handle, calls),
        .function_definition => |*value| try visitBlockMutable(allocator, &value.body, function_handle, calls),
        .if_statement => |*value| {
            try visitExpressionMutable(allocator, value.condition orelse return error.InvalidAst, function_handle, calls);
            try visitBlockMutable(allocator, &value.body, function_handle, calls);
        },
        .switch_statement => |*value| {
            try visitExpressionMutable(allocator, value.expression orelse return error.InvalidAst, function_handle, calls);
            for (value.cases.items) |*case_value|
                try visitBlockMutable(allocator, &case_value.body, function_handle, calls);
        },
        .for_loop => |*value| {
            try visitBlockMutable(allocator, &value.pre, function_handle, calls);
            try visitExpressionMutable(allocator, value.condition orelse return error.InvalidAst, function_handle, calls);
            try visitBlockMutable(allocator, &value.post, function_handle, calls);
            try visitBlockMutable(allocator, &value.body, function_handle, calls);
        },
        .block => |*value| try visitBlockMutable(allocator, value, function_handle, calls),
        .break_statement, .continue_statement, .leave_statement => {},
    }
}

fn visitBlockMutable(
    allocator: std.mem.Allocator,
    block: *AST.Block,
    function_handle: AST.FunctionHandle,
    calls: *std.ArrayList(*AST.FunctionCall),
) anyerror!void {
    for (block.statements.items) |*statement|
        try visitStatementMutable(allocator, statement, function_handle, calls);
}

test "call finder returns nested calls in walker post-order" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const YulName = @import("../yul_name.zig").YulName;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.init(.Cancun), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(x) -> r { r := x } pop(f(f(1))) }",
        "calls.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var calls = try findFunctionCalls(allocator, &ast.root_block, .{ .user = try YulName.init("f") });
    defer calls.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 2), calls.items.len);
    try std.testing.expectEqual(@as(usize, 1), calls.items[0].arguments.items.len);
}
