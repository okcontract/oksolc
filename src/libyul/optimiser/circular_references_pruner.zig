// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Removes function-only call cycles unreachable from roots or external names.

const std = @import("std");
const AST = @import("../ast.zig");
const CallGraphModule = @import("call_graph_generator.zig");
const FunctionGrouper = @import("function_grouper.zig").FunctionGrouper;
const NameCollectorModule = @import("name_collector.zig");
const OptimizerUtilities = @import("optimizer_utilities.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const CircularReferencesPruner = struct {
    pub const name = "CircularReferencesPruner";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var graph = try CallGraphModule.CallGraphGenerator.callGraph(
            context.dispenser.allocator,
            ast,
        );
        defer graph.deinit();
        var keep = try functionsCalledFromOutermostContext(
            context.dispenser.allocator,
            &graph,
            context.reserved_identifiers,
        );
        defer keep.deinit(context.dispenser.allocator);
        for (ast.statements.items) |*statement| {
            if (statement.* != .function_definition or keep.contains(statement.function_definition.name))
                continue;
            statement.deinit(context.dispenser.allocator);
            statement.* = .{ .block = .{} };
        }
        OptimizerUtilities.removeEmptyBlocks(context.dispenser.allocator, ast);
        try FunctionGrouper.run(context, ast);
    }

    pub fn functionsCalledFromOutermostContext(
        allocator: std.mem.Allocator,
        graph: *const CallGraphModule.CallGraph,
        reserved_identifiers: *const NameCollectorModule.NameSet,
    ) anyerror!NameCollectorModule.NameSet {
        var visited: NameCollectorModule.NameSet = .{};
        errdefer visited.deinit(allocator);
        var pending: std.ArrayList(@import("../yul_name.zig").YulName) = .empty;
        defer pending.deinit(allocator);
        for (0..reserved_identifiers.len()) |index| {
            const function_name = reserved_identifiers.at(index);
            if (try visited.insert(allocator, function_name)) try pending.append(allocator, function_name);
        }
        const top_level: @import("../yul_name.zig").YulName = .{};
        if (try visited.insert(allocator, top_level)) try pending.append(allocator, top_level);

        var next: usize = 0;
        while (next < pending.items.len) : (next += 1) {
            const caller: AST.FunctionHandle = .{ .user = pending.items[next] };
            const callees = graph.function_calls.get(caller) orelse continue;
            for (callees.items) |callee| switch (callee) {
                .builtin => {},
                .user => |callee_name| {
                    if (!graph.function_calls.contains(.{ .user = callee_name })) continue;
                    if (try visited.insert(allocator, callee_name))
                        try pending.append(allocator, callee_name);
                },
            };
        }
        return visited;
    }
};
