// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Fixed-point removal of unused functions, variables, and pure expressions.

const std = @import("std");
const AST = @import("../ast.zig");
const CallGraphModule = @import("call_graph_generator.zig");
const FunctionGrouper = @import("function_grouper.zig").FunctionGrouper;
const NameCollectorModule = @import("name_collector.zig");
const OptimizerUtilities = @import("optimizer_utilities.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const UnusedPruner = struct {
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    allow_msize_optimization: bool,
    function_side_effects: ?*const Semantics.FunctionSideEffects,
    references: NameCollectorModule.ReferenceMap,
    should_run_again: bool = false,

    pub const name = "UnusedPruner";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        try runUntilStabilisedOnFullASTWithScratch(
            context.dispenser.allocator,
            context.scratchAllocator(),
            context.dialect,
            ast,
            context.reserved_identifiers,
        );
        try FunctionGrouper.run(context, ast);
    }

    pub fn runUntilStabilised(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *AST.Block,
        allow_msize_optimization: bool,
        function_side_effects: ?*const Semantics.FunctionSideEffects,
        externally_used_functions: *const NameCollectorModule.NameSet,
    ) anyerror!void {
        return runUntilStabilisedWithScratch(
            allocator,
            allocator,
            dialect,
            ast,
            allow_msize_optimization,
            function_side_effects,
            externally_used_functions,
        );
    }

    fn runUntilStabilisedWithScratch(
        allocator: std.mem.Allocator,
        scratch_allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *AST.Block,
        allow_msize_optimization: bool,
        function_side_effects: ?*const Semantics.FunctionSideEffects,
        externally_used_functions: *const NameCollectorModule.NameSet,
    ) anyerror!void {
        var pruner = try init(
            allocator,
            scratch_allocator,
            dialect,
            ast,
            allow_msize_optimization,
            function_side_effects,
            externally_used_functions,
        );
        defer pruner.deinit();
        while (true) {
            pruner.should_run_again = false;
            try pruner.visitBlock(ast);
            if (!pruner.should_run_again) return;
        }
    }

    pub fn runUntilStabilisedOnFullAST(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *AST.Block,
        externally_used_functions: *const NameCollectorModule.NameSet,
    ) anyerror!void {
        return runUntilStabilisedOnFullASTWithScratch(
            allocator,
            allocator,
            dialect,
            ast,
            externally_used_functions,
        );
    }

    fn runUntilStabilisedOnFullASTWithScratch(
        allocator: std.mem.Allocator,
        scratch_allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *AST.Block,
        externally_used_functions: *const NameCollectorModule.NameSet,
    ) anyerror!void {
        var graph = try CallGraphModule.CallGraphGenerator.callGraph(scratch_allocator, ast);
        defer graph.deinit();
        var function_side_effects = try Semantics.SideEffectsPropagator.sideEffects(
            scratch_allocator,
            dialect,
            &graph,
        );
        defer function_side_effects.deinit(scratch_allocator);
        const allow_msize = !try Semantics.MSizeFinder.containsMSize(dialect, ast);
        try runUntilStabilisedWithScratch(
            allocator,
            scratch_allocator,
            dialect,
            ast,
            allow_msize,
            &function_side_effects,
            externally_used_functions,
        );
    }

    fn init(
        allocator: std.mem.Allocator,
        scratch_allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *const AST.Block,
        allow_msize_optimization: bool,
        function_side_effects: ?*const Semantics.FunctionSideEffects,
        externally_used_functions: *const NameCollectorModule.NameSet,
    ) anyerror!UnusedPruner {
        var references = try NameCollectorModule.ReferencesCounter.countReferencesBlock(
            scratch_allocator,
            ast,
        );
        errdefer references.deinit(scratch_allocator);
        for (0..externally_used_functions.len()) |index| {
            const handle: AST.FunctionHandle = .{ .user = externally_used_functions.at(index) };
            if (references.getPtr(handle)) |count|
                count.* += 1
            else
                _ = try references.insert(scratch_allocator, handle, 1);
        }
        return .{
            .allocator = allocator,
            .scratch_allocator = scratch_allocator,
            .dialect = dialect,
            .allow_msize_optimization = allow_msize_optimization,
            .function_side_effects = function_side_effects,
            .references = references,
        };
    }

    fn deinit(self: *UnusedPruner) void {
        self.references.deinit(self.scratch_allocator);
        self.* = undefined;
    }

    fn used(self: *const UnusedPruner, name_value: YulName) bool {
        const count = self.references.get(.{ .user = name_value }) orelse return false;
        return count.* > 0;
    }

    fn visitBlock(self: *UnusedPruner, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| {
            switch (statement.*) {
                .function_definition => |*function| if (!self.used(function.name)) {
                    var references = try NameCollectorModule.ReferencesCounter.countReferencesBlock(
                        self.scratch_allocator,
                        &function.body,
                    );
                    defer references.deinit(self.scratch_allocator);
                    try self.subtractReferences(&references);
                    const debug_data = function.debug_data;
                    statement.deinit(self.allocator);
                    statement.* = .{ .block = .{ .debug_data = debug_data } };
                },
                .variable_declaration => |*declaration| {
                    var any_used = false;
                    for (declaration.variables.items) |variable|
                        any_used = any_used or self.used(variable.name);
                    if (any_used) continue;
                    if (declaration.value == null) {
                        const debug_data = declaration.debug_data;
                        statement.deinit(self.allocator);
                        statement.* = .{ .block = .{ .debug_data = debug_data } };
                        continue;
                    }
                    const effects = try Semantics.SideEffectsCollector.collectExpression(
                        self.dialect,
                        declaration.value.?,
                        self.function_side_effects,
                    );
                    if (effects.canBeRemoved(self.allow_msize_optimization)) {
                        var references = try NameCollectorModule.ReferencesCounter.countReferencesExpression(
                            self.scratch_allocator,
                            declaration.value.?,
                        );
                        defer references.deinit(self.scratch_allocator);
                        try self.subtractReferences(&references);
                        const debug_data = declaration.debug_data;
                        statement.deinit(self.allocator);
                        statement.* = .{ .block = .{ .debug_data = debug_data } };
                    } else if (declaration.variables.items.len == 1 and
                        self.dialect.discardFunctionHandle() != null)
                    {
                        try self.replaceDeclarationWithDiscard(statement);
                    }
                },
                .expression_statement => |*expression_statement| {
                    const effects = try Semantics.SideEffectsCollector.collectExpression(
                        self.dialect,
                        &expression_statement.expression,
                        self.function_side_effects,
                    );
                    if (effects.canBeRemoved(self.allow_msize_optimization)) {
                        var references = try NameCollectorModule.ReferencesCounter.countReferencesExpression(
                            self.scratch_allocator,
                            &expression_statement.expression,
                        );
                        defer references.deinit(self.scratch_allocator);
                        try self.subtractReferences(&references);
                        const debug_data = expression_statement.debug_data;
                        statement.deinit(self.allocator);
                        statement.* = .{ .block = .{ .debug_data = debug_data } };
                    }
                },
                else => {},
            }
        }

        OptimizerUtilities.removeEmptyBlocks(self.allocator, block);
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *UnusedPruner, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            else => {},
        }
    }

    fn replaceDeclarationWithDiscard(
        self: *UnusedPruner,
        statement: *AST.Statement,
    ) anyerror!void {
        const declaration = &statement.variable_declaration;
        const discard = self.dialect.discardFunctionHandle().?;
        const debug_data = declaration.debug_data;
        var arguments: std.ArrayList(AST.Expression) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitExpressions(self.allocator, &arguments);
        try arguments.ensureTotalCapacity(self.allocator, 1);
        const value = declaration.value orelse return error.InvalidAst;
        const expression = value.*;
        self.allocator.destroy(value);
        declaration.value = null;
        arguments.appendAssumeCapacity(expression);
        declaration.deinit(self.allocator);
        statement.* = .{ .expression_statement = .{
            .debug_data = debug_data,
            .expression = .{ .function_call = .{
                .debug_data = debug_data,
                .function_name = .{ .builtin = .{
                    .debug_data = debug_data,
                    .handle = discard,
                } },
                .arguments = arguments,
            } },
        } };
        arguments = .empty;
    }

    fn subtractReferences(
        self: *UnusedPruner,
        subtrahend: *const NameCollectorModule.ReferenceMap,
    ) !void {
        for (subtrahend.items()) |entry| {
            const count = self.references.getPtr(entry.key) orelse return error.MissingReference;
            if (count.* < entry.value) return error.ReferenceUnderflow;
            count.* -= entry.value;
            self.should_run_again = true;
        }
    }
};

fn deinitExpressions(allocator: std.mem.Allocator, expressions: *std.ArrayList(AST.Expression)) void {
    for (expressions.items) |*expression| expression.deinit(allocator);
    expressions.deinit(allocator);
}
