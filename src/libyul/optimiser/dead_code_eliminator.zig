// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Removes statements after unconditional control-flow changes.

const std = @import("std");
const AST = @import("../ast.zig");
const ControlFlowCollector = @import("../control_flow_side_effects_collector.zig").ControlFlowSideEffectsCollector;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");

pub const DeadCodeEliminator = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    function_side_effects: *const Semantics.NamedControlFlowSideEffects,

    pub const name = "DeadCodeEliminator";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var collector = try ControlFlowCollector.init(
            context.dispenser.allocator,
            context.dialect,
            ast,
        );
        defer collector.deinit();
        var named = try collector.functionSideEffectsNamed(context.dispenser.allocator);
        defer named.deinit();
        var pass: DeadCodeEliminator = .{
            .allocator = context.dispenser.allocator,
            .dialect = context.dialect,
            .function_side_effects = &named,
        };
        try pass.visitBlock(ast);
    }

    fn visitBlock(self: *DeadCodeEliminator, block: *AST.Block) anyerror!void {
        const finder = Semantics.TerminationFinder.init(self.dialect, self.function_side_effects);
        const first = try finder.firstUnconditionalControlFlowChange(block.statements.items);
        if (first.control_flow != .flow_out and first.index != std.math.maxInt(usize))
            removeUnreachableAfter(self.allocator, &block.statements, first.index + 1);
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *DeadCodeEliminator, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*value| {
                if (value.pre.statements.items.len != 0) return error.ForLoopInitNotRewritten;
                try self.visitBlock(&value.pre);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            else => {},
        }
    }
};

fn removeUnreachableAfter(
    allocator: std.mem.Allocator,
    statements: *std.ArrayList(AST.Statement),
    start: usize,
) void {
    var write = start;
    var read = start;
    while (read < statements.items.len) : (read += 1) {
        const statement = &statements.items[read];
        if (statement.* == .function_definition) {
            if (write != read) {
                statements.items[write] = statement.*;
                statement.* = .{ .block = .{} };
            }
            write += 1;
        } else {
            statement.deinit(allocator);
            statement.* = .{ .block = .{} };
        }
    }
    statements.shrinkRetainingCapacity(write);
}
