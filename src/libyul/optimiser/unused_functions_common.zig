// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared construction helpers for unused function parameter/return pruning.

const std = @import("std");
const AST = @import("../ast.zig");
const Metrics = @import("metrics.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const YulName = @import("../yul_name.zig").YulName;

pub const UsageMasks = struct {
    parameters: []const bool,
    returns: []const bool,
};

pub fn tooSimpleToBePruned(function: *const AST.FunctionDefinition) bool {
    return function.body.statements.items.len <= 1 and
        Metrics.CodeSize.codeSize(&function.body, .{}) <= 1;
}

pub fn createLinkingFunction(
    allocator: std.mem.Allocator,
    original: *const AST.FunctionDefinition,
    masks: UsageMasks,
    original_function_name: YulName,
    linking_function_name: YulName,
    dispenser: *NameDispenser,
) anyerror!AST.FunctionDefinition {
    if (masks.parameters.len != original.parameters.items.len or
        masks.returns.len != original.return_variables.items.len)
    {
        return error.InvalidUsageMask;
    }

    var linking: AST.FunctionDefinition = .{
        .debug_data = original.debug_data,
        .name = linking_function_name,
        .body = .{ .debug_data = original.debug_data },
    };
    errdefer linking.deinit(allocator);
    try linking.parameters.ensureTotalCapacity(allocator, original.parameters.items.len);
    for (original.parameters.items) |parameter| linking.parameters.appendAssumeCapacity(.{
        .debug_data = parameter.debug_data,
        .name = try dispenser.newName(parameter.name),
    });
    try linking.return_variables.ensureTotalCapacity(allocator, original.return_variables.items.len);
    for (original.return_variables.items) |return_variable|
        linking.return_variables.appendAssumeCapacity(.{
            .debug_data = return_variable.debug_data,
            .name = try dispenser.newName(return_variable.name),
        });

    var call: AST.FunctionCall = .{
        .debug_data = original.debug_data,
        .function_name = .{ .identifier = .{
            .debug_data = original.debug_data,
            .name = original_function_name,
        } },
    };
    errdefer call.deinit(allocator);
    for (linking.parameters.items, masks.parameters) |parameter, used|
        if (used) try call.arguments.append(allocator, .{ .identifier = .{
            .debug_data = original.debug_data,
            .name = parameter.name,
        } });

    var assignment: AST.Assignment = .{ .debug_data = original.debug_data };
    errdefer assignment.deinit(allocator);
    for (linking.return_variables.items, masks.returns) |return_variable, used|
        if (used) try assignment.variable_names.append(allocator, .{
            .debug_data = original.debug_data,
            .name = return_variable.name,
        });

    try linking.body.statements.ensureTotalCapacity(allocator, 1);
    if (assignment.variable_names.items.len == 0) {
        assignment.deinit(allocator);
        assignment = .{};
        linking.body.statements.appendAssumeCapacity(.{ .expression_statement = .{
            .debug_data = original.debug_data,
            .expression = .{ .function_call = call },
        } });
        call = undefined;
    } else {
        const call_expression = try AST.createExpression(allocator, .{ .function_call = call });
        call = undefined;
        assignment.value = call_expression;
        linking.body.statements.appendAssumeCapacity(.{ .assignment = assignment });
        assignment = .{};
    }
    return linking;
}
