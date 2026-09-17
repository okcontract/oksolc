// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Lowering from analyzed, disambiguated Yul into the symbolic control-flow
//! graph consumed by optimized EVM stack-layout generation.

const std = @import("std");
const AST = @import("../../ast.zig");
const AsmAnalysisInfo = @import("../../asm_analysis_info.zig").AsmAnalysisInfo;
const CFGModule = @import("control_flow_graph.zig");
const CollectorModule = @import("../../control_flow_side_effects_collector.zig");
const DebugData = @import("../../../liblangutil/debug_data.zig").DebugData;
const ScopeModule = @import("../../scope.zig");
const YulName = @import("../../yul_name.zig").YulName;

const ForLoopInfo = struct {
    after_loop: *CFGModule.BasicBlock,
    post: *CFGModule.BasicBlock,
};

pub const ControlFlowGraphBuilder = struct {
    allocator: std.mem.Allocator,
    graph: *CFGModule.CFG,
    info: *const AsmAnalysisInfo,
    function_side_effects: *const CollectorModule.FunctionEffectsMap,
    dialect: AST.Dialect,
    current_block: ?*CFGModule.BasicBlock = null,
    scope: ?*ScopeModule.Scope = null,
    for_loop_info: ?ForLoopInfo = null,
    current_function: ?*CFGModule.FunctionInfo = null,

    pub fn build(
        allocator: std.mem.Allocator,
        analysis_info: *const AsmAnalysisInfo,
        dialect: AST.Dialect,
        block: *const AST.Block,
    ) !CFGModule.CFG {
        var graph = CFGModule.CFG.init(allocator);
        errdefer graph.deinit();
        graph.entry = try graph.makeBlock(block.debug_data);
        var side_effects = try CollectorModule.ControlFlowSideEffectsCollector.init(
            allocator,
            dialect,
            block,
        );
        defer side_effects.deinit();
        var builder: ControlFlowGraphBuilder = .{
            .allocator = allocator,
            .graph = &graph,
            .info = analysis_info,
            .function_side_effects = side_effects.functionSideEffects(),
            .dialect = dialect,
            .current_block = graph.entry,
        };
        try builder.visitBlock(block);
        try cleanUnreachable(allocator, &graph);
        try markRecursiveCalls(allocator, &graph);
        try markStartsOfSubGraphs(allocator, &graph);
        try markNeedsCleanStack(allocator, &graph);
        return graph;
    }

    fn visitExpression(self: *ControlFlowGraphBuilder, expression: *const AST.Expression) anyerror!CFGModule.StackSlot {
        return switch (expression.*) {
            .literal => |*literal| .{ .literal = .{
                .value = try literal.value.value(),
                .debug_data = literal.debug_data,
            } },
            .identifier => |*identifier| .{ .variable = .{
                .variable = try self.lookupVariable(identifier.name),
                .debug_data = identifier.debug_data,
            } },
            .function_call => |*call| blk: {
                const output = try self.visitFunctionCall(call);
                if (output.len != 1) return error.InvalidAst;
                break :blk output[0];
            },
        };
    }

    fn visitStatement(self: *ControlFlowGraphBuilder, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*node| {
                if (node.expression != .function_call) return error.InvalidAst;
                const output = try self.visitFunctionCall(&node.expression.function_call);
                if (output.len != 0) return error.InvalidAst;
            },
            .assignment => |*node| try self.visitAssignment(node),
            .variable_declaration => |*node| try self.visitVariableDeclaration(node),
            .function_definition => |*node| try self.visitFunctionDefinition(node),
            .if_statement => |*node| try self.visitIf(node),
            .switch_statement => |*node| try self.visitSwitch(node),
            .for_loop => |*node| try self.visitForLoop(node),
            .break_statement => |*node| try self.visitBreak(node),
            .continue_statement => |*node| try self.visitContinue(node),
            .leave_statement => |*node| try self.visitLeave(node),
            .block => |*node| try self.visitBlock(node),
        }
    }

    fn visitBlock(self: *ControlFlowGraphBuilder, block: *const AST.Block) anyerror!void {
        const saved_scope = self.scope;
        defer self.scope = saved_scope;
        self.scope = self.info.getScope(block) orelse return error.InvalidAnalysisInfo;
        for (block.statements.items) |*statement|
            if (statement.* == .function_definition)
                try self.registerFunction(&statement.function_definition);
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitVariableDeclaration(self: *ControlFlowGraphBuilder, declaration: *const AST.VariableDeclaration) !void {
        var variables: std.ArrayList(CFGModule.VariableSlot) = .empty;
        errdefer variables.deinit(self.allocator);
        for (declaration.variables.items) |*variable| try variables.append(self.allocator, .{
            .variable = try self.lookupVariable(variable.name),
            .debug_data = variable.debug_data,
        });
        var input = if (declaration.value) |value|
            try self.visitAssignmentRightHandSide(value, variables.items.len)
        else
            CFGModule.Stack.empty;
        errdefer input.deinit(self.allocator);
        if (declaration.value == null) for (declaration.variables.items) |_| try input.append(
            self.allocator,
            .{ .literal = .{ .value = 0, .debug_data = declaration.debug_data } },
        );
        var output: CFGModule.Stack = .empty;
        errdefer output.deinit(self.allocator);
        for (variables.items) |variable| try output.append(self.allocator, .{ .variable = variable });
        try (self.current_block orelse return error.InvalidControlFlow).operations.append(self.allocator, .{
            .input = input,
            .output = output,
            .operation = .{ .assignment = .{
                .debug_data = declaration.debug_data,
                .variables = variables,
            } },
        });
    }

    fn visitAssignment(self: *ControlFlowGraphBuilder, assignment: *const AST.Assignment) !void {
        var variables: std.ArrayList(CFGModule.VariableSlot) = .empty;
        errdefer variables.deinit(self.allocator);
        for (assignment.variable_names.items) |*identifier| try variables.append(self.allocator, .{
            .variable = try self.lookupVariable(identifier.name),
            .debug_data = identifier.debug_data,
        });
        var input = try self.visitAssignmentRightHandSide(
            assignment.value orelse return error.InvalidAst,
            variables.items.len,
        );
        errdefer input.deinit(self.allocator);
        var output: CFGModule.Stack = .empty;
        errdefer output.deinit(self.allocator);
        for (variables.items) |variable| try output.append(self.allocator, .{ .variable = variable });
        try (self.current_block orelse return error.InvalidControlFlow).operations.append(self.allocator, .{
            .input = input,
            .output = output,
            .operation = .{ .assignment = .{
                .debug_data = assignment.debug_data,
                .variables = variables,
            } },
        });
    }

    fn visitIf(self: *ControlFlowGraphBuilder, if_statement: *const AST.If) !void {
        const if_branch = try self.graph.makeBlock(if_statement.body.debug_data);
        const after_if = try self.graph.makeBlock((self.current_block orelse return error.InvalidControlFlow).debug_data);
        const condition = try self.visitExpression(if_statement.condition orelse return error.InvalidAst);
        try self.makeConditionalJump(if_statement.debug_data, condition, if_branch, after_if);
        self.current_block = if_branch;
        try self.visitBlock(&if_statement.body);
        try self.jump(if_statement.body.debug_data, after_if, false);
    }

    fn visitSwitch(self: *ControlFlowGraphBuilder, switch_statement: *const AST.Switch) !void {
        if (switch_statement.cases.items.len == 0) return error.InvalidAst;
        const pre_switch_debug = switch_statement.debug_data;
        const ghost_name_text = try std.fmt.allocPrint(
            self.allocator,
            "GHOST[{d}]",
            .{self.graph.ghost_variables.items.len},
        );
        defer self.allocator.free(ghost_name_text);
        const ghost_variable = try self.graph.makeGhostVariable(try YulName.init(ghost_name_text));
        const ghost_slot = CFGModule.VariableSlot{
            .variable = ghost_variable,
            .debug_data = (switch_statement.expression orelse return error.InvalidAst).debugData().?.*,
        };
        const expression = try self.visitExpression(switch_statement.expression.?);
        var assignment_variables: std.ArrayList(CFGModule.VariableSlot) = .empty;
        errdefer assignment_variables.deinit(self.allocator);
        try assignment_variables.append(self.allocator, ghost_slot);
        var assignment_input: CFGModule.Stack = .empty;
        errdefer assignment_input.deinit(self.allocator);
        try assignment_input.append(self.allocator, expression);
        var assignment_output: CFGModule.Stack = .empty;
        errdefer assignment_output.deinit(self.allocator);
        try assignment_output.append(self.allocator, .{ .variable = ghost_slot });
        try (self.current_block orelse return error.InvalidControlFlow).operations.append(self.allocator, .{
            .input = assignment_input,
            .output = assignment_output,
            .operation = .{ .assignment = .{
                .debug_data = switch_statement.debug_data,
                .variables = assignment_variables,
            } },
        });
        const equality_handle = self.dialect.equalityFunctionHandle() orelse return error.MissingEqualityBuiltin;
        const equality_builtin = try self.dialect.builtin(equality_handle);
        const after_switch = try self.graph.makeBlock(pre_switch_debug);
        const last_index = switch_statement.cases.items.len - 1;
        for (switch_statement.cases.items[0..last_index]) |*case_value| {
            if (case_value.value == null) return error.InvalidAst;
            const case_branch = try self.graph.makeBlock(case_value.body.debug_data);
            const else_branch = try self.graph.makeBlock(switch_statement.debug_data);
            const comparison = try self.makeValueCompare(case_value, ghost_slot, equality_handle, equality_builtin);
            try self.makeConditionalJump(case_value.debug_data, comparison, case_branch, else_branch);
            self.current_block = case_branch;
            try self.visitBlock(&case_value.body);
            try self.jump(case_value.body.debug_data, after_switch, false);
            self.current_block = else_branch;
        }
        const last_case = &switch_statement.cases.items[last_index];
        if (last_case.value != null) {
            const case_branch = try self.graph.makeBlock(last_case.body.debug_data);
            const comparison = try self.makeValueCompare(last_case, ghost_slot, equality_handle, equality_builtin);
            try self.makeConditionalJump(last_case.debug_data, comparison, case_branch, after_switch);
            self.current_block = case_branch;
        }
        try self.visitBlock(&last_case.body);
        try self.jump(last_case.body.debug_data, after_switch, false);
    }

    fn makeValueCompare(
        self: *ControlFlowGraphBuilder,
        case_value: *const AST.Case,
        ghost_slot: CFGModule.VariableSlot,
        equality_handle: @import("../../builtins.zig").BuiltinHandle,
        equality_builtin: *const AST.BuiltinFunction,
    ) !CFGModule.StackSlot {
        const literal = case_value.value orelse return error.InvalidAst;
        var arguments: std.ArrayList(AST.Expression) = .empty;
        errdefer {
            for (arguments.items) |*argument| argument.deinit(self.allocator);
            arguments.deinit(self.allocator);
        }
        try arguments.append(self.allocator, .{ .literal = .{
            .debug_data = literal.debug_data,
            .kind = literal.kind,
            .value = try literal.value.clone(self.allocator),
        } });
        try arguments.append(self.allocator, .{ .identifier = .{
            .name = ghost_slot.variable.name,
        } });
        const ghost_call = try self.graph.ownGhostCall(.{
            .debug_data = case_value.debug_data,
            .function_name = .{ .builtin = .{
                .handle = equality_handle,
            } },
            .arguments = arguments,
        });
        var input: CFGModule.Stack = .empty;
        errdefer input.deinit(self.allocator);
        try input.append(self.allocator, .{ .variable = ghost_slot });
        try input.append(self.allocator, .{ .literal = .{
            .value = try literal.value.value(),
            .debug_data = literal.debug_data,
        } });
        var output: CFGModule.Stack = .empty;
        errdefer output.deinit(self.allocator);
        const temporary: CFGModule.StackSlot = .{ .temporary = .{ .call = ghost_call, .index = 0 } };
        try output.append(self.allocator, temporary);
        try (self.current_block orelse return error.InvalidControlFlow).operations.append(self.allocator, .{
            .input = input,
            .output = output,
            .operation = .{ .builtin_call = .{
                .debug_data = case_value.debug_data,
                .builtin = equality_builtin,
                .function_call = ghost_call,
                .arguments = 2,
            } },
        });
        return temporary;
    }

    fn visitForLoop(self: *ControlFlowGraphBuilder, loop: *const AST.ForLoop) !void {
        const saved_scope = self.scope;
        const saved_loop_info = self.for_loop_info;
        defer {
            self.scope = saved_scope;
            self.for_loop_info = saved_loop_info;
        }
        self.scope = self.info.getScope(&loop.pre) orelse return error.InvalidAnalysisInfo;
        try self.visitBlock(&loop.pre);
        const condition_expression = loop.condition orelse return error.InvalidAst;
        const constant_condition: ?bool = switch (condition_expression.*) {
            .literal => |*literal| (try literal.value.value()) != 0,
            else => null,
        };
        const loop_condition = try self.graph.makeBlock(condition_expression.debugData().?.*);
        const loop_body = try self.graph.makeBlock(loop.body.debug_data);
        const post = try self.graph.makeBlock(loop.post.debug_data);
        const after_loop = try self.graph.makeBlock(loop.debug_data);
        self.for_loop_info = .{ .after_loop = after_loop, .post = post };
        if (constant_condition) |condition| {
            if (condition) {
                try self.jump(loop.pre.debug_data, loop_body, false);
                try self.visitBlock(&loop.body);
                try self.jump(loop.body.debug_data, post, false);
                try self.visitBlock(&loop.post);
                try self.jump(loop.post.debug_data, loop_body, true);
            } else try self.jump(loop.pre.debug_data, after_loop, false);
        } else {
            try self.jump(loop.pre.debug_data, loop_condition, false);
            const condition = try self.visitExpression(condition_expression);
            try self.makeConditionalJump(condition_expression.debugData().?.*, condition, loop_body, after_loop);
            self.current_block = loop_body;
            try self.visitBlock(&loop.body);
            try self.jump(loop.body.debug_data, post, false);
            try self.visitBlock(&loop.post);
            try self.jump(loop.post.debug_data, loop_condition, true);
        }
        self.current_block = after_loop;
    }

    fn visitBreak(self: *ControlFlowGraphBuilder, node: *const AST.Break) !void {
        const loop_info = self.for_loop_info orelse return error.InvalidControlFlow;
        try self.jump(node.debug_data, loop_info.after_loop, false);
        self.current_block = try self.graph.makeBlock((self.current_block orelse return error.InvalidControlFlow).debug_data);
    }

    fn visitContinue(self: *ControlFlowGraphBuilder, node: *const AST.Continue) !void {
        const loop_info = self.for_loop_info orelse return error.InvalidControlFlow;
        try self.jump(node.debug_data, loop_info.post, false);
        self.current_block = try self.graph.makeBlock((self.current_block orelse return error.InvalidControlFlow).debug_data);
    }

    fn visitLeave(self: *ControlFlowGraphBuilder, node: *const AST.Leave) !void {
        const function = self.current_function orelse return error.InvalidControlFlow;
        const block = self.current_block orelse return error.InvalidControlFlow;
        block.exit = .{ .function_return = .{ .debug_data = node.debug_data, .info = function } };
        try function.exits.append(self.allocator, block);
        self.current_block = try self.graph.makeBlock(block.debug_data);
    }

    fn visitFunctionDefinition(
        self: *ControlFlowGraphBuilder,
        function_definition: *const AST.FunctionDefinition,
    ) !void {
        const function = try self.lookupFunction(function_definition.name);
        try self.graph.functions.append(self.allocator, function);
        const function_info = self.graph.function_info.get(function) orelse return error.InvalidAnalysisInfo;
        var builder: ControlFlowGraphBuilder = .{
            .allocator = self.allocator,
            .graph = self.graph,
            .info = self.info,
            .function_side_effects = self.function_side_effects,
            .dialect = self.dialect,
            .current_block = function_info.entry,
            .current_function = function_info,
        };
        try builder.visitBlock(&function_definition.body);
        const exit_block = builder.current_block orelse return error.InvalidControlFlow;
        try function_info.exits.append(self.allocator, exit_block);
        exit_block.exit = .{ .function_return = .{
            .debug_data = function_definition.debug_data,
            .info = function_info,
        } };
    }

    fn registerFunction(
        self: *ControlFlowGraphBuilder,
        definition: *const AST.FunctionDefinition,
    ) !void {
        const function = try self.lookupFunction(definition.name);
        const virtual_block = self.info.getVirtualBlock(definition) orelse return error.InvalidAnalysisInfo;
        const virtual_scope = self.info.getScope(virtual_block) orelse return error.InvalidAnalysisInfo;
        const entry = try self.graph.makeBlock(definition.body.debug_data);
        const effects = self.function_side_effects.get(definition) orelse return error.InvalidAnalysisInfo;
        const function_info = try self.graph.createFunctionInfo(
            function,
            definition,
            entry,
            definition.debug_data,
            effects.can_continue,
        );
        for (definition.parameters.items) |*parameter| try function_info.parameters.append(self.allocator, .{
            .variable = try variableFromScope(virtual_scope, parameter.name),
            .debug_data = parameter.debug_data,
        });
        for (definition.return_variables.items) |*return_variable| try function_info.return_variables.append(self.allocator, .{
            .variable = try variableFromScope(virtual_scope, return_variable.name),
            .debug_data = return_variable.debug_data,
        });
    }

    fn visitFunctionCall(self: *ControlFlowGraphBuilder, call: *const AST.FunctionCall) anyerror![]const CFGModule.StackSlot {
        var input: CFGModule.Stack = .empty;
        errdefer input.deinit(self.allocator);
        var output: CFGModule.Stack = .empty;
        errdefer output.deinit(self.allocator);
        var can_continue = true;
        var operation: CFGModule.OperationKind = undefined;
        switch (call.function_name) {
            .builtin => |builtin_name| {
                const builtin = try self.dialect.builtin(builtin_name.handle);
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    if (builtin.literalArgument(index) == null)
                        try input.append(self.allocator, try self.visitExpression(&call.arguments.items[index]));
                }
                for (0..builtin.num_returns) |return_index| try output.append(
                    self.allocator,
                    .{ .temporary = .{ .call = call, .index = return_index } },
                );
                can_continue = builtin.control_flow_side_effects.can_continue;
                operation = .{ .builtin_call = .{
                    .debug_data = call.debug_data,
                    .builtin = builtin,
                    .function_call = call,
                    .arguments = input.items.len,
                } };
            },
            .identifier => |identifier| {
                const function = try self.lookupFunction(identifier.name);
                const function_info = self.graph.function_info.get(function) orelse return error.InvalidAnalysisInfo;
                can_continue = function_info.can_continue;
                if (can_continue) try input.append(self.allocator, .{
                    .function_call_return_label = .{ .call = call },
                });
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try input.append(self.allocator, try self.visitExpression(&call.arguments.items[index]));
                }
                for (0..function.num_returns) |return_index| try output.append(
                    self.allocator,
                    .{ .temporary = .{ .call = call, .index = return_index } },
                );
                operation = .{ .function_call = .{
                    .debug_data = call.debug_data,
                    .function = function,
                    .function_call = call,
                    .can_continue = can_continue,
                } };
            },
        }
        // Argument evaluation may terminate the original block and advance
        // `current_block`. C++ appends the outer call to that new (unreachable)
        // block, so resolve the pointer only after visiting every argument.
        const block = self.current_block orelse return error.InvalidControlFlow;
        try block.operations.append(self.allocator, .{
            .input = input,
            .output = output,
            .operation = operation,
        });
        const result = block.operations.items[block.operations.items.len - 1].output.items;
        if (!can_continue) {
            block.exit = .{ .terminated = .{} };
            self.current_block = try self.graph.makeBlock(block.debug_data);
        }
        return result;
    }

    fn visitAssignmentRightHandSide(
        self: *ControlFlowGraphBuilder,
        expression: *const AST.Expression,
        expected_slots: usize,
    ) anyerror!CFGModule.Stack {
        var result: CFGModule.Stack = .empty;
        errdefer result.deinit(self.allocator);
        switch (expression.*) {
            .function_call => |*call| {
                const output = try self.visitFunctionCall(call);
                if (output.len != expected_slots) return error.InvalidAst;
                try result.appendSlice(self.allocator, output);
            },
            else => {
                if (expected_slots != 1) return error.InvalidAst;
                try result.append(self.allocator, try self.visitExpression(expression));
            },
        }
        return result;
    }

    fn lookupFunction(self: *const ControlFlowGraphBuilder, name: YulName) !*const ScopeModule.Function {
        const identifier = (self.scope orelse return error.InvalidAnalysisInfo).lookupConst(name) orelse
            return error.UnknownFunction;
        return switch (identifier.*) {
            .function => |*function| function,
            .variable => error.ExpectedFunction,
        };
    }

    fn lookupVariable(self: *const ControlFlowGraphBuilder, name: YulName) !*const ScopeModule.Variable {
        const identifier = (self.scope orelse return error.InvalidAnalysisInfo).lookupConst(name) orelse
            return error.ExternalIdentifierUnavailable;
        return switch (identifier.*) {
            .variable => |*variable| variable,
            .function => error.ExpectedVariable,
        };
    }

    fn makeConditionalJump(
        self: *ControlFlowGraphBuilder,
        debug_data: ?DebugData,
        condition: CFGModule.StackSlot,
        non_zero: *CFGModule.BasicBlock,
        zero: *CFGModule.BasicBlock,
    ) !void {
        const block = self.current_block orelse return error.InvalidControlFlow;
        block.exit = .{ .conditional_jump = .{
            .debug_data = debug_data,
            .condition = condition,
            .non_zero = non_zero,
            .zero = zero,
        } };
        try non_zero.entries.append(self.allocator, block);
        try zero.entries.append(self.allocator, block);
        self.current_block = null;
    }

    fn jump(
        self: *ControlFlowGraphBuilder,
        debug_data: ?DebugData,
        target: *CFGModule.BasicBlock,
        backwards: bool,
    ) !void {
        const block = self.current_block orelse return error.InvalidControlFlow;
        block.exit = .{ .jump = .{
            .debug_data = debug_data,
            .target = target,
            .backwards = backwards,
        } };
        try target.entries.append(self.allocator, block);
        self.current_block = target;
    }
};

fn variableFromScope(scope: *ScopeModule.Scope, name: YulName) !*const ScopeModule.Variable {
    const identifier = scope.identifiers.getPtr(name) orelse return error.UnknownVariable;
    return switch (identifier.*) {
        .variable => |*variable| variable,
        .function => error.ExpectedVariable,
    };
}

fn cleanUnreachable(allocator: std.mem.Allocator, graph: *CFGModule.CFG) !void {
    var visited = std.AutoHashMap(*CFGModule.BasicBlock, void).init(allocator);
    defer visited.deinit();
    var queue: std.ArrayList(*CFGModule.BasicBlock) = .empty;
    defer queue.deinit(allocator);
    try queue.append(allocator, graph.entry orelse return error.InvalidControlFlow);
    var cursor: usize = 0;
    while (cursor < queue.items.len) : (cursor += 1) {
        const block = queue.items[cursor];
        const inserted = try visited.getOrPut(block);
        if (inserted.found_existing) continue;
        for (block.operations.items) |*operation| if (operation.operation == .function_call) {
            const call = &operation.operation.function_call;
            if (graph.function_info.get(call.function)) |info| try queue.append(allocator, info.entry);
        };
        switch (block.exit) {
            .jump => |exit| try queue.append(allocator, exit.target),
            .conditional_jump => |exit| {
                try queue.append(allocator, exit.zero);
                try queue.append(allocator, exit.non_zero);
            },
            else => {},
        }
    }
    var blocks = visited.keyIterator();
    while (blocks.next()) |block_pointer| {
        const block = block_pointer.*;
        var write_index: usize = 0;
        for (block.entries.items) |entry| if (visited.contains(entry)) {
            block.entries.items[write_index] = entry;
            write_index += 1;
        };
        block.entries.shrinkRetainingCapacity(write_index);
    }
    var function_write: usize = 0;
    for (graph.functions.items) |function| {
        const info = graph.function_info.get(function) orelse continue;
        if (visited.contains(info.entry)) {
            graph.functions.items[function_write] = function;
            function_write += 1;
        }
    }
    graph.functions.shrinkRetainingCapacity(function_write);
    var dead_functions: std.ArrayList(*const ScopeModule.Function) = .empty;
    defer dead_functions.deinit(allocator);
    var infos = graph.function_info.iterator();
    while (infos.next()) |entry| if (!visited.contains(entry.value_ptr.*.entry))
        try dead_functions.append(allocator, entry.key_ptr.*);
    for (dead_functions.items) |function| {
        const removed = graph.function_info.fetchRemove(function).?;
        removed.value.deinit(allocator);
        allocator.destroy(removed.value);
    }
}

fn collectCallsInFunction(
    allocator: std.mem.Allocator,
    entry: *CFGModule.BasicBlock,
) !std.ArrayList(*CFGModule.FunctionCall) {
    var calls: std.ArrayList(*CFGModule.FunctionCall) = .empty;
    errdefer calls.deinit(allocator);
    var visited = std.AutoHashMap(*CFGModule.BasicBlock, void).init(allocator);
    defer visited.deinit();
    var queue: std.ArrayList(*CFGModule.BasicBlock) = .empty;
    defer queue.deinit(allocator);
    try queue.append(allocator, entry);
    var cursor: usize = 0;
    while (cursor < queue.items.len) : (cursor += 1) {
        const block = queue.items[cursor];
        const inserted = try visited.getOrPut(block);
        if (inserted.found_existing) continue;
        for (block.operations.items) |*operation| if (operation.operation == .function_call)
            try calls.append(allocator, &operation.operation.function_call);
        switch (block.exit) {
            .jump => |exit| try queue.append(allocator, exit.target),
            .conditional_jump => |exit| {
                try queue.append(allocator, exit.zero);
                try queue.append(allocator, exit.non_zero);
            },
            else => {},
        }
    }
    return calls;
}

fn markRecursiveCalls(allocator: std.mem.Allocator, graph: *CFGModule.CFG) !void {
    var calls_by_function = std.AutoHashMap(*const ScopeModule.Function, std.ArrayList(*CFGModule.FunctionCall)).init(allocator);
    defer {
        var values = calls_by_function.valueIterator();
        while (values.next()) |calls| calls.deinit(allocator);
        calls_by_function.deinit();
    }
    var infos = graph.function_info.iterator();
    while (infos.next()) |entry| try calls_by_function.put(
        entry.key_ptr.*,
        try collectCallsInFunction(allocator, entry.value_ptr.*.entry),
    );
    var outer = calls_by_function.iterator();
    while (outer.next()) |entry| {
        const containing_function = entry.key_ptr.*;
        for (entry.value_ptr.items) |call| {
            var visited = std.AutoHashMap(*const ScopeModule.Function, void).init(allocator);
            defer visited.deinit();
            var queue: std.ArrayList(*const ScopeModule.Function) = .empty;
            defer queue.deinit(allocator);
            try queue.append(allocator, call.function);
            var cursor: usize = 0;
            while (cursor < queue.items.len) : (cursor += 1) {
                const function = queue.items[cursor];
                if (function == containing_function) {
                    call.recursive = true;
                    break;
                }
                const inserted = try visited.getOrPut(function);
                if (inserted.found_existing) continue;
                if (calls_by_function.get(function)) |nested_calls|
                    for (nested_calls.items) |nested_call| try queue.append(allocator, nested_call.function);
            }
        }
    }
}

fn graphNeighbours(
    allocator: std.mem.Allocator,
    block: *CFGModule.BasicBlock,
) !std.ArrayList(*CFGModule.BasicBlock) {
    var result: std.ArrayList(*CFGModule.BasicBlock) = .empty;
    errdefer result.deinit(allocator);
    // Keep parallel/reverse edges in their upstream order. Tarjan's bridge
    // walk consumes the raw predecessor list followed by outgoing targets.
    try result.appendSlice(allocator, block.entries.items);
    switch (block.exit) {
        .jump => |exit| try result.append(allocator, exit.target),
        .conditional_jump => |exit| {
            try result.append(allocator, exit.zero);
            try result.append(allocator, exit.non_zero);
        },
        .terminated, .main_exit => block.is_start_of_sub_graph = true,
        else => {},
    }
    return result;
}

const BridgeContext = struct {
    allocator: std.mem.Allocator,
    visited: std.AutoHashMap(*CFGModule.BasicBlock, void),
    discovery: std.AutoHashMap(*CFGModule.BasicBlock, usize),
    low: std.AutoHashMap(*CFGModule.BasicBlock, usize),
    parent: std.AutoHashMap(*CFGModule.BasicBlock, *CFGModule.BasicBlock),
    time: usize = 0,

    fn init(allocator: std.mem.Allocator) BridgeContext {
        return .{
            .allocator = allocator,
            .visited = std.AutoHashMap(*CFGModule.BasicBlock, void).init(allocator),
            .discovery = std.AutoHashMap(*CFGModule.BasicBlock, usize).init(allocator),
            .low = std.AutoHashMap(*CFGModule.BasicBlock, usize).init(allocator),
            .parent = std.AutoHashMap(*CFGModule.BasicBlock, *CFGModule.BasicBlock).init(allocator),
        };
    }

    fn deinit(self: *BridgeContext) void {
        self.visited.deinit();
        self.discovery.deinit();
        self.low.deinit();
        self.parent.deinit();
    }

    fn dfs(self: *BridgeContext, block: *CFGModule.BasicBlock) anyerror!void {
        try self.visited.put(block, {});
        try self.discovery.put(block, self.time);
        try self.low.put(block, self.time);
        self.time += 1;
        var children = try graphNeighbours(self.allocator, block);
        defer children.deinit(self.allocator);
        for (children.items) |child| {
            if (!self.visited.contains(child)) {
                try self.parent.put(child, block);
                try self.dfs(child);
                self.low.getPtr(block).?.* = @min(self.low.get(block).?, self.low.get(child).?);
                if (self.low.get(child).? > self.discovery.get(block).?) {
                    const child_to_block = containsBlock(block.entries.items, child);
                    const block_to_child = containsBlock(child.entries.items, block);
                    if (child_to_block and !block_to_child)
                        block.is_start_of_sub_graph = true
                    else if (block_to_child and !child_to_block)
                        child.is_start_of_sub_graph = true;
                }
            } else if (self.parent.get(block) != child) {
                self.low.getPtr(block).?.* = @min(self.low.get(block).?, self.discovery.get(child).?);
            }
        }
    }
};

fn containsBlock(blocks: []const *CFGModule.BasicBlock, needle: *CFGModule.BasicBlock) bool {
    for (blocks) |block| if (block == needle) return true;
    return false;
}

fn markStartsOfSubGraphs(allocator: std.mem.Allocator, graph: *CFGModule.CFG) !void {
    var entries: std.ArrayList(*CFGModule.BasicBlock) = .empty;
    defer entries.deinit(allocator);
    try entries.append(allocator, graph.entry orelse return error.InvalidControlFlow);
    var infos = graph.function_info.valueIterator();
    while (infos.next()) |info| try entries.append(allocator, info.*.entry);
    for (entries.items) |entry| {
        var context = BridgeContext.init(allocator);
        defer context.deinit();
        try context.dfs(entry);
    }
}

fn markNeedsCleanStack(allocator: std.mem.Allocator, graph: *CFGModule.CFG) !void {
    var infos = graph.function_info.valueIterator();
    while (infos.next()) |info_pointer| for (info_pointer.*.exits.items) |exit_block| {
        var visited = std.AutoHashMap(*CFGModule.BasicBlock, void).init(allocator);
        defer visited.deinit();
        var queue: std.ArrayList(*CFGModule.BasicBlock) = .empty;
        defer queue.deinit(allocator);
        try queue.append(allocator, exit_block);
        var cursor: usize = 0;
        while (cursor < queue.items.len) : (cursor += 1) {
            const block = queue.items[cursor];
            const inserted = try visited.getOrPut(block);
            if (inserted.found_existing) continue;
            block.needs_clean_stack = true;
            try queue.appendSlice(allocator, block.entries.items);
        }
    };
}

test "CFG lowering records function calls, loop backedges, and clean returns" {
    const Parser = @import("../../asm_parser.zig").Parser;
    const AsmAnalysis = @import("../../asm_analysis.zig");
    const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("evm_dialect.zig");
    const allocator = std.testing.allocator;
    const dialect = try EVMDialect.strictAssemblyForEVM(EVMVersion.init(.Cancun));
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a) -> r { for { } a { a := sub(a, 1) } { if a { continue } r := a break } } pop(f(3)) }",
        "cfg.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    defer info.deinit();
    var analyzer = AsmAnalysis.AsmAnalyzer.init(
        allocator,
        &info,
        &reporter,
        dialect.dialect(),
        .{},
        .{},
        AsmAnalysis.instructionValidatorForEVMDialect(dialect),
    );
    defer analyzer.deinit();
    try std.testing.expect(try analyzer.analyze(ast.root()));
    var graph = try ControlFlowGraphBuilder.build(allocator, &info, dialect.dialect(), ast.root());
    defer graph.deinit();
    try std.testing.expect(graph.blocks.items.len >= 5);
    try std.testing.expectEqual(@as(usize, 1), graph.functions.items.len);
    const function_info = graph.function_info.get(graph.functions.items[0]).?;
    try std.testing.expect(function_info.exits.items.len != 0);
    try std.testing.expect(function_info.exits.items[0].needs_clean_stack);
}
