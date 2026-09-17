// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! CFG-based Yul-to-EVM code generation. This is the optimized stack-layout
//! backend used by the non-SSA Yul object compiler path.

const std = @import("std");
const AST = @import("../../ast.zig");
const AsmAnalysisInfo = @import("../../asm_analysis_info.zig").AsmAnalysisInfo;
const AbstractModule = @import("abstract_assembly.zig");
const AbstractAssembly = AbstractModule.AbstractAssembly;
const Builtins = @import("evm_builtins.zig");
const BuiltinContext = Builtins.BuiltinContext;
const CFG = @import("control_flow_graph.zig");
const ControlFlowGraphBuilder = @import("control_flow_graph_builder.zig").ControlFlowGraphBuilder;
const DebugData = @import("../../../liblangutil/debug_data.zig").DebugData;
const EVMDialect = @import("evm_dialect.zig").EVMDialect;
const InstructionModule = @import("../../../libevmasm/instruction.zig");
const ScopeModule = @import("../../scope.zig");
const SourceLocation = @import("../../../liblangutil/source_location.zig").SourceLocation;
const StackHelpers = @import("stack_helpers.zig");
const StackLayoutModule = @import("stack_layout_generator.zig");
const StackLayout = StackLayoutModule.StackLayout;
const StackLayoutGenerator = StackLayoutModule.StackLayoutGenerator;
const StackTooDeepError = @import("../../exceptions.zig").StackTooDeepError;
const YulName = @import("../../yul_name.zig").YulName;

pub const UseNamedLabels = enum(c_int) {
    yes_and_force_unique,
    never,
    for_first_function_of_each_name,
};

pub fn deinitStackErrors(allocator: std.mem.Allocator, errors: *std.ArrayList(StackTooDeepError)) void {
    for (errors.items) |*stack_error| stack_error.deinit();
    errors.deinit(allocator);
    errors.* = .empty;
}

pub const OptimizedEVMCodeTransform = struct {
    allocator: std.mem.Allocator,
    assembly: AbstractAssembly,
    builtin_context: *BuiltinContext,
    graph: *const CFG.CFG,
    stack_layout: *const StackLayout,
    dialect: *const EVMDialect,
    stack: CFG.Stack = .empty,
    return_labels: std.AutoHashMap(*const AST.FunctionCall, AbstractModule.LabelID),
    block_labels: std.AutoHashMap(*const CFG.BasicBlock, AbstractModule.LabelID),
    function_labels: std.AutoHashMap(*const CFG.FunctionInfo, AbstractModule.LabelID),
    generated: std.AutoHashMap(*const CFG.BasicBlock, void),
    current_function_info: ?*const CFG.FunctionInfo = null,
    stack_errors: std.ArrayList(StackTooDeepError) = .empty,
    reachable_stack_depth: usize,

    const Self = @This();

    pub fn run(
        allocator: std.mem.Allocator,
        assembly: AbstractAssembly,
        analysis_info: *AsmAnalysisInfo,
        block: *const AST.Block,
        dialect: *const EVMDialect,
        builtin_context: *BuiltinContext,
        use_named_labels: UseNamedLabels,
    ) anyerror!std.ArrayList(StackTooDeepError) {
        var graph = try ControlFlowGraphBuilder.build(
            allocator,
            analysis_info,
            dialect.dialect(),
            block,
        );
        defer graph.deinit();
        var stack_layout = try StackLayoutGenerator.run(allocator, &graph, dialect);
        defer stack_layout.deinit();
        var transform = try Self.init(
            allocator,
            assembly,
            builtin_context,
            use_named_labels,
            &graph,
            &stack_layout,
            dialect,
        );
        defer transform.deinit();

        const entry = graph.entry orelse return error.InvalidControlFlow;
        const entry_info = stack_layout.block_infos.get(entry) orelse return error.InvalidStackLayout;
        try transform.createStackLayout(entry.debug_data, entry_info.entry_layout.items);
        try transform.visitBasicBlock(entry);
        for (graph.functions.items) |function| {
            const function_info = graph.function_info.get(function) orelse return error.InvalidControlFlow;
            try transform.visitFunction(function_info);
        }

        const result = transform.stack_errors;
        transform.stack_errors = .empty;
        return result;
    }

    fn init(
        allocator: std.mem.Allocator,
        assembly: AbstractAssembly,
        builtin_context: *BuiltinContext,
        use_named_labels: UseNamedLabels,
        graph: *const CFG.CFG,
        stack_layout: *const StackLayout,
        dialect: *const EVMDialect,
    ) !Self {
        var result: Self = .{
            .allocator = allocator,
            .assembly = assembly,
            .builtin_context = builtin_context,
            .graph = graph,
            .stack_layout = stack_layout,
            .dialect = dialect,
            .return_labels = std.AutoHashMap(
                *const AST.FunctionCall,
                AbstractModule.LabelID,
            ).init(allocator),
            .block_labels = std.AutoHashMap(
                *const CFG.BasicBlock,
                AbstractModule.LabelID,
            ).init(allocator),
            .function_labels = std.AutoHashMap(
                *const CFG.FunctionInfo,
                AbstractModule.LabelID,
            ).init(allocator),
            .generated = std.AutoHashMap(*const CFG.BasicBlock, void).init(allocator),
            .reachable_stack_depth = dialect.reachableStackDepth(),
        };
        errdefer result.deinit();

        var assigned_function_names = std.AutoHashMap(YulName, void).init(allocator);
        defer assigned_function_names.deinit();
        for (graph.functions.items) |function| {
            const function_info = graph.function_info.get(function) orelse
                return error.InvalidControlFlow;
            const inserted = try assigned_function_names.getOrPut(function.name);
            const name_already_seen = inserted.found_existing;
            if (use_named_labels == .yes_and_force_unique and name_already_seen)
                return error.DuplicateFunctionName;
            const use_named_label = use_named_labels != .never and !name_already_seen;
            const label = if (use_named_label)
                try assembly.namedLabel(
                    try function.name.str(),
                    function.num_arguments,
                    function.num_returns,
                    try astId(function_info.debug_data),
                )
            else
                try assembly.newLabelId();
            try result.function_labels.put(function_info, label);
        }
        return result;
    }

    fn deinit(self: *Self) void {
        self.stack.deinit(self.allocator);
        self.return_labels.deinit();
        self.block_labels.deinit();
        self.function_labels.deinit();
        self.generated.deinit();
        deinitStackErrors(self.allocator, &self.stack_errors);
        self.* = undefined;
    }

    fn getFunctionLabel(self: *const Self, function: *const ScopeModule.Function) !AbstractModule.LabelID {
        const function_info = self.graph.function_info.get(function) orelse return error.InvalidControlFlow;
        return self.function_labels.get(function_info) orelse error.MissingFunctionLabel;
    }

    fn emitFunctionCall(self: *Self, call: *const CFG.FunctionCall) anyerror!void {
        const use_return_label = call.can_continue;
        try self.assertAssemblyHeight();
        const argument_count = call.function.num_arguments;
        const consumed = argument_count + @intFromBool(use_return_label);
        if (self.stack.items.len < consumed or
            call.function_call.arguments.items.len != argument_count)
            return error.InvalidFunctionCallLayout;

        for (0..argument_count) |index| {
            const argument = &call.function_call.arguments.items[argument_count - index - 1];
            const slot = self.stack.items[self.stack.items.len - argument_count + index];
            try validateSlot(slot, argument);
        }
        if (use_return_label) {
            const slot = self.stack.items[self.stack.items.len - argument_count - 1];
            if (slot != .function_call_return_label or
                slot.function_call_return_label.call != call.function_call)
                return error.InvalidReturnLabelLayout;
        }

        try self.assembly.setSourceLocation(originLocation(call.debug_data));
        const stack_difference = try signedDifference(
            call.function.num_returns,
            argument_count + @intFromBool(call.can_continue),
        );
        try self.assembly.appendJumpTo(
            try self.getFunctionLabel(call.function),
            stack_difference,
            .into_function,
        );
        if (use_return_label) try self.assembly.appendLabel(
            self.return_labels.get(call.function_call) orelse return error.MissingReturnLabel,
        );

        self.stack.shrinkRetainingCapacity(self.stack.items.len - consumed);
        for (0..call.function.num_returns) |index| try self.stack.append(self.allocator, .{
            .temporary = .{ .call = call.function_call, .index = index },
        });
        try self.assertAssemblyHeight();
    }

    fn emitBuiltinCall(self: *Self, call: *const CFG.BuiltinCall) anyerror!void {
        try self.assertAssemblyHeight();
        if (self.stack.items.len < call.arguments) return error.InvalidBuiltinCallLayout;
        var slot_index = self.stack.items.len - call.arguments;
        var argument_index = call.function_call.arguments.items.len;
        while (argument_index != 0) {
            argument_index -= 1;
            if (call.builtin.literalArgument(argument_index) == null) {
                if (slot_index >= self.stack.items.len) return error.InvalidBuiltinCallLayout;
                try validateSlot(
                    self.stack.items[slot_index],
                    &call.function_call.arguments.items[argument_index],
                );
                slot_index += 1;
            }
        }
        if (slot_index != self.stack.items.len) return error.InvalidBuiltinCallLayout;

        try self.assembly.setSourceLocation(originLocation(call.debug_data));
        const handle = switch (call.function_call.function_name) {
            .builtin => |builtin_name| builtin_name.handle,
            .identifier => return error.ExpectedBuiltinFunction,
        };
        const concrete_builtin = self.dialect.builtin(handle) orelse return error.UnknownBuiltin;
        try concrete_builtin.generateCode(call.function_call, self.assembly, self.builtin_context);

        self.stack.shrinkRetainingCapacity(self.stack.items.len - call.arguments);
        for (0..call.builtin.num_returns) |index| try self.stack.append(self.allocator, .{
            .temporary = .{ .call = call.function_call, .index = index },
        });
        try self.assertAssemblyHeight();
    }

    fn emitAssignment(self: *Self, assignment: *const CFG.Assignment) !void {
        try self.assertAssemblyHeight();
        for (self.stack.items) |*current_slot| if (current_slot.* == .variable) {
            if (containsVariable(assignment.variables.items, current_slot.variable.variable))
                current_slot.* = .{ .junk = .{} };
        };
        if (self.stack.items.len < assignment.variables.items.len)
            return error.InvalidAssignmentLayout;
        const base = self.stack.items.len - assignment.variables.items.len;
        for (assignment.variables.items, 0..) |variable, index|
            self.stack.items[base + index] = .{ .variable = variable };
    }

    fn createStackLayout(
        self: *Self,
        debug_data: ?DebugData,
        target_stack: []const CFG.StackSlot,
    ) anyerror!void {
        try self.assertAssemblyHeight();
        const location = originLocation(debug_data);
        try self.assembly.setSourceLocation(location);
        try StackHelpers.createStackLayout(
            self.allocator,
            &self.stack,
            target_stack,
            ShuffleCallbacks{ .transform = self, .source_location = location },
            self.reachable_stack_depth,
        );
        try self.assertAssemblyHeight();
    }

    fn appendSwap(self: *Self, depth: usize) !void {
        if (depth == 0 or depth > 16) return error.UnreachableStackDepth;
        try self.assembly.appendInstruction(InstructionModule.swapInstruction(@intCast(depth)));
    }

    fn appendDup(self: *Self, depth: usize) !void {
        if (depth == 0 or depth > 16) return error.UnreachableStackDepth;
        try self.assembly.appendInstruction(InstructionModule.dupInstruction(@intCast(depth)));
    }

    fn visitBasicBlock(self: *Self, block: *const CFG.BasicBlock) anyerror!void {
        const inserted = try self.generated.getOrPut(block);
        if (inserted.found_existing) return error.BlockAlreadyGenerated;

        try self.assembly.setSourceLocation(originLocation(block.debug_data));
        const block_info = self.stack_layout.block_infos.get(block) orelse
            return error.InvalidStackLayout;
        try assertLayoutCompatibility(self.stack.items, block_info.entry_layout.items);
        self.stack.clearRetainingCapacity();
        try self.stack.appendSlice(self.allocator, block_info.entry_layout.items);
        try self.assertAssemblyHeight();

        if (self.block_labels.get(block)) |label| try self.assembly.appendLabel(label);

        for (block.operations.items) |*operation| {
            const entry_layout = self.stack_layout.operation_entry_layout.get(operation) orelse
                return error.InvalidStackLayout;
            try self.createStackLayout(operationDebugData(&operation.operation), entry_layout.items);
            try self.assertAssemblyHeight();
            if (self.stack.items.len < operation.input.items.len)
                return error.InvalidOperationLayout;
            const base_height = self.stack.items.len - operation.input.items.len;
            try assertLayoutCompatibility(self.stack.items[base_height..], operation.input.items);

            switch (operation.operation) {
                .function_call => |*call| try self.emitFunctionCall(call),
                .builtin_call => |*call| try self.emitBuiltinCall(call),
                .assignment => |*assignment| try self.emitAssignment(assignment),
            }

            try self.assertAssemblyHeight();
            if (self.stack.items.len != base_height + operation.output.items.len)
                return error.InvalidOperationOutput;
            try assertLayoutCompatibility(
                self.stack.items[self.stack.items.len - operation.output.items.len ..],
                operation.output.items,
            );
        }

        try self.assembly.setSourceLocation(originLocation(block.debug_data));
        switch (block.exit) {
            .main_exit => try self.assembly.appendInstruction(.STOP),
            .jump => |*jump| try self.emitJump(jump),
            .conditional_jump => |*jump| try self.emitConditionalJump(block_info, jump),
            .function_return => |*function_return| try self.emitFunctionReturn(function_return),
            .terminated => try self.validateTerminated(block),
        }
        self.stack.clearRetainingCapacity();
        try self.assembly.setStackHeight(0);
    }

    fn emitJump(self: *Self, jump: *const CFG.Jump) anyerror!void {
        const target_info = self.stack_layout.block_infos.get(jump.target) orelse
            return error.InvalidStackLayout;
        try self.createStackLayout(jump.debug_data, target_info.entry_layout.items);
        if (!self.block_labels.contains(jump.target) and jump.target.entries.items.len == 1) {
            if (jump.backwards) return error.InvalidBackwardFallthrough;
            return self.visitBasicBlock(jump.target);
        }
        if (!self.block_labels.contains(jump.target))
            try self.block_labels.put(jump.target, try self.assembly.newLabelId());
        if (self.generated.contains(jump.target))
            try self.assembly.appendJumpTo(
                self.block_labels.get(jump.target).?,
                0,
                .ordinary,
            )
        else
            try self.visitBasicBlock(jump.target);
    }

    fn emitConditionalJump(
        self: *Self,
        block_info: StackLayoutModule.BlockInfo,
        jump: *const CFG.ConditionalJump,
    ) anyerror!void {
        try self.createStackLayout(jump.debug_data, block_info.exit_layout.items);
        if (!self.block_labels.contains(jump.non_zero))
            try self.block_labels.put(jump.non_zero, try self.assembly.newLabelId());
        if (!self.block_labels.contains(jump.zero))
            try self.block_labels.put(jump.zero, try self.assembly.newLabelId());

        if (self.stack.items.len == 0 or !self.stack.items[self.stack.items.len - 1].eql(jump.condition))
            return error.InvalidConditionalLayout;
        try self.assembly.appendJumpToIf(self.block_labels.get(jump.non_zero).?, .ordinary);
        _ = self.stack.pop();

        const non_zero_info = self.stack_layout.block_infos.get(jump.non_zero) orelse
            return error.InvalidStackLayout;
        const zero_info = self.stack_layout.block_infos.get(jump.zero) orelse
            return error.InvalidStackLayout;
        try assertLayoutCompatibility(self.stack.items, non_zero_info.entry_layout.items);
        try assertLayoutCompatibility(self.stack.items, zero_info.entry_layout.items);

        var stored_stack = try cloneStack(self.allocator, self.stack.items);
        defer stored_stack.deinit(self.allocator);
        if (self.generated.contains(jump.zero))
            try self.assembly.appendJumpTo(self.block_labels.get(jump.zero).?, 0, .ordinary)
        else
            try self.visitBasicBlock(jump.zero);

        self.stack.clearRetainingCapacity();
        try self.stack.appendSlice(self.allocator, stored_stack.items);
        try self.assembly.setStackHeight(@intCast(self.stack.items.len));
        if (!self.generated.contains(jump.non_zero))
            try self.visitBasicBlock(jump.non_zero);
    }

    fn emitFunctionReturn(self: *Self, function_return: *const CFG.FunctionReturn) anyerror!void {
        const current = self.current_function_info orelse return error.FunctionReturnOutsideFunction;
        if (current != function_return.info or !current.can_continue)
            return error.InvalidFunctionReturn;
        var exit_stack: CFG.Stack = .empty;
        defer exit_stack.deinit(self.allocator);
        for (current.return_variables.items) |variable| try exit_stack.append(
            self.allocator,
            .{ .variable = variable },
        );
        try exit_stack.append(self.allocator, .{
            .function_return_label = .{ .function = current.function },
        });
        try self.createStackLayout(function_return.debug_data, exit_stack.items);
        try self.assembly.appendJump(0, .out_of_function);
    }

    fn validateTerminated(_: *Self, block: *const CFG.BasicBlock) !void {
        if (block.operations.items.len == 0) return error.InvalidTerminatedBlock;
        const operation = &block.operations.items[block.operations.items.len - 1].operation;
        switch (operation.*) {
            .builtin_call => |call| if (!call.builtin.control_flow_side_effects.terminatesOrReverts())
                return error.InvalidTerminatedBlock,
            .function_call => |call| if (call.can_continue)
                return error.InvalidTerminatedBlock,
            .assignment => return error.InvalidTerminatedBlock,
        }
    }

    fn visitFunction(self: *Self, function_info: *const CFG.FunctionInfo) anyerror!void {
        if (self.current_function_info != null) return error.NestedFunctionGeneration;
        self.current_function_info = function_info;
        defer self.current_function_info = null;
        if (self.stack.items.len != 0 or try self.assembly.stackHeight() != 0)
            return error.InvalidFunctionEntryStack;

        if (function_info.can_continue) try self.stack.append(self.allocator, .{
            .function_return_label = .{ .function = function_info.function },
        });
        var index = function_info.parameters.items.len;
        while (index != 0) {
            index -= 1;
            try self.stack.append(self.allocator, .{
                .variable = function_info.parameters.items[index],
            });
        }
        try self.assembly.setStackHeight(@intCast(self.stack.items.len));
        try self.assembly.setSourceLocation(originLocation(function_info.debug_data));
        try self.assembly.appendLabel(try self.getFunctionLabel(function_info.function));

        const entry_info = self.stack_layout.block_infos.get(function_info.entry) orelse
            return error.InvalidStackLayout;
        try self.createStackLayout(function_info.debug_data, entry_info.entry_layout.items);
        try self.visitBasicBlock(function_info.entry);
        self.stack.clearRetainingCapacity();
        try self.assembly.setStackHeight(0);
    }

    fn assertAssemblyHeight(self: *const Self) !void {
        const height = try self.assembly.stackHeight();
        if (height < 0 or @as(usize, @intCast(height)) != self.stack.items.len)
            return error.InvalidAssemblyStackHeight;
    }

    const ShuffleCallbacks = struct {
        transform: *Self,
        source_location: SourceLocation,

        pub fn swap(self: @This(), depth: usize) anyerror!void {
            try self.transform.assertAssemblyHeight();
            if (depth == 0 or depth >= self.transform.stack.items.len)
                return error.InvalidSwapDepth;
            if (depth <= self.transform.reachable_stack_depth) {
                try self.transform.appendSwap(depth);
                return;
            }

            const deficit = depth - self.transform.reachable_stack_depth;
            const deep_slot = self.transform.stack.items[self.transform.stack.items.len - depth - 1];
            const top_slot = self.transform.stack.items[self.transform.stack.items.len - 1];
            const deep_name = slotVariableName(deep_slot);
            const top_name = slotVariableName(top_slot);
            const deep_description = if (deep_name.empty()) blk: {
                const slot_text = try StackHelpers.stackSlotToStringAlloc(
                    self.transform.allocator,
                    deep_slot,
                    self.transform.dialect.dialect(),
                );
                defer self.transform.allocator.free(slot_text);
                break :blk try std.fmt.allocPrint(self.transform.allocator, "Slot {s}", .{slot_text});
            } else try std.fmt.allocPrint(
                self.transform.allocator,
                "Variable {s}",
                .{try deep_name.str()},
            );
            defer self.transform.allocator.free(deep_description);
            const top_description = if (top_name.empty()) blk: {
                const slot_text = try StackHelpers.stackSlotToStringAlloc(
                    self.transform.allocator,
                    top_slot,
                    self.transform.dialect.dialect(),
                );
                defer self.transform.allocator.free(slot_text);
                break :blk try std.fmt.allocPrint(self.transform.allocator, "Slot {s}", .{slot_text});
            } else try std.fmt.allocPrint(
                self.transform.allocator,
                "Variable {s}",
                .{try top_name.str()},
            );
            defer self.transform.allocator.free(top_description);
            const stack_text = try StackHelpers.stackToStringAlloc(
                self.transform.allocator,
                self.transform.stack.items,
                self.transform.dialect.dialect(),
            );
            defer self.transform.allocator.free(stack_text);
            const message = try std.fmt.allocPrint(
                self.transform.allocator,
                "Cannot swap {s} with {s}: too deep in the stack by {d} slots in {s}",
                .{ deep_description, top_description, deficit, stack_text },
            );
            defer self.transform.allocator.free(message);
            try self.transform.appendStackError(
                if (deep_name.empty()) top_name else deep_name,
                deficit,
                message,
            );
            try self.transform.assembly.markAsInvalid();
        }

        pub fn pushOrDup(self: @This(), slot: CFG.StackSlot) anyerror!void {
            try self.transform.assertAssemblyHeight();
            if (findOffsetReverse(self.transform.stack.items, slot)) |depth| {
                if (depth < self.transform.reachable_stack_depth) {
                    try self.transform.appendDup(depth + 1);
                    return;
                }
                if (!slot.canBeFreelyGenerated()) {
                    const deficit = depth - (self.transform.reachable_stack_depth - 1);
                    const variable_name = slotVariableName(slot);
                    const slot_description = if (variable_name.empty()) blk: {
                        const slot_text = try StackHelpers.stackSlotToStringAlloc(
                            self.transform.allocator,
                            slot,
                            self.transform.dialect.dialect(),
                        );
                        defer self.transform.allocator.free(slot_text);
                        break :blk try std.fmt.allocPrint(self.transform.allocator, "Slot {s}", .{slot_text});
                    } else try std.fmt.allocPrint(
                        self.transform.allocator,
                        "Variable {s}",
                        .{try variable_name.str()},
                    );
                    defer self.transform.allocator.free(slot_description);
                    const stack_text = try StackHelpers.stackToStringAlloc(
                        self.transform.allocator,
                        self.transform.stack.items,
                        self.transform.dialect.dialect(),
                    );
                    defer self.transform.allocator.free(stack_text);
                    const message = try std.fmt.allocPrint(
                        self.transform.allocator,
                        "{s} is {d} too deep in the stack {s}",
                        .{ slot_description, deficit, stack_text },
                    );
                    defer self.transform.allocator.free(message);
                    try self.transform.appendStackError(variable_name, deficit, message);
                    try self.transform.assembly.markAsInvalid();
                    try self.transform.assembly.appendConstant(0xCAFFEE);
                    return;
                }
            }

            switch (slot) {
                .literal => |literal| {
                    try self.transform.assembly.setSourceLocation(originLocation(literal.debug_data));
                    try self.transform.assembly.appendConstant(literal.value);
                    try self.transform.assembly.setSourceLocation(self.source_location);
                },
                .function_return_label => return error.CannotProduceFunctionReturnLabel,
                .function_call_return_label => |return_label| {
                    if (!self.transform.return_labels.contains(return_label.call))
                        try self.transform.return_labels.put(
                            return_label.call,
                            try self.transform.assembly.newLabelId(),
                        );
                    try self.transform.assembly.setSourceLocation(originLocation(return_label.call.debug_data));
                    try self.transform.assembly.appendLabelReference(
                        self.transform.return_labels.get(return_label.call).?,
                    );
                    try self.transform.assembly.setSourceLocation(self.source_location);
                },
                .variable => |variable| {
                    const current = self.transform.current_function_info orelse
                        return error.VariableNotFoundOnStack;
                    if (!containsVariable(current.return_variables.items, variable.variable))
                        return error.VariableNotFoundOnStack;
                    try self.transform.assembly.setSourceLocation(originLocation(variable.debug_data));
                    try self.transform.assembly.appendConstant(0);
                    try self.transform.assembly.setSourceLocation(self.source_location);
                },
                .temporary => return error.FunctionResultNotFoundOnStack,
                .junk => {
                    if ((try self.transform.assembly.evmVersion()).hasPush0())
                        try self.transform.assembly.appendConstant(0)
                    else
                        try self.transform.assembly.appendInstruction(.CODESIZE);
                },
            }
        }

        pub fn pop(self: @This()) anyerror!void {
            try self.transform.assembly.appendInstruction(.POP);
        }
    };

    fn appendStackError(
        self: *Self,
        variable: YulName,
        deficit: usize,
        message: []const u8,
    ) !void {
        try self.stack_errors.append(self.allocator, try StackTooDeepError.initInFunction(
            self.allocator,
            if (self.current_function_info) |info| info.function.name else .{},
            variable,
            @intCast(deficit),
            message,
        ));
    }
};

fn assertLayoutCompatibility(current: []const CFG.StackSlot, desired: []const CFG.StackSlot) !void {
    if (current.len != desired.len) return error.IncompatibleStackLayout;
    for (current, desired) |current_slot, desired_slot|
        if (desired_slot != .junk and !current_slot.eql(desired_slot))
            return error.IncompatibleStackLayout;
}

fn validateSlot(slot: CFG.StackSlot, expression: *const AST.Expression) !void {
    switch (expression.*) {
        .literal => |*literal| {
            if (slot != .literal or slot.literal.value != try literal.value.value())
                return error.InvalidLiteralSlot;
        },
        .identifier => |*identifier| {
            if (slot != .variable or !slot.variable.variable.name.eql(identifier.name))
                return error.InvalidVariableSlot;
        },
        .function_call => |*call| {
            if (slot != .temporary or slot.temporary.call != call or slot.temporary.index != 0)
                return error.InvalidTemporarySlot;
        },
    }
}

fn operationDebugData(operation: *const CFG.OperationKind) ?DebugData {
    return switch (operation.*) {
        .function_call => |call| call.debug_data,
        .builtin_call => |call| call.debug_data,
        .assignment => |assignment| assignment.debug_data,
    };
}

fn originLocation(debug_data: ?DebugData) SourceLocation {
    return if (debug_data) |debug| debug.origin_location else .{};
}

fn astId(debug_data: ?DebugData) !?usize {
    const raw = if (debug_data) |debug| debug.ast_id else null;
    if (raw) |value| {
        if (value < 0) return error.InvalidAstId;
        return @intCast(value);
    }
    return null;
}

fn containsVariable(variables: []const CFG.VariableSlot, variable: *const ScopeModule.Variable) bool {
    for (variables) |candidate| if (candidate.variable == variable) return true;
    return false;
}

fn findOffsetReverse(stack: []const CFG.StackSlot, slot: CFG.StackSlot) ?usize {
    var depth: usize = 0;
    var index = stack.len;
    while (index != 0) : (depth += 1) {
        index -= 1;
        if (stack[index].eql(slot)) return depth;
    }
    return null;
}

fn slotVariableName(slot: CFG.StackSlot) YulName {
    return if (slot == .variable) slot.variable.variable.name else .{};
}

fn cloneStack(allocator: std.mem.Allocator, source: []const CFG.StackSlot) !CFG.Stack {
    var result: CFG.Stack = .empty;
    errdefer result.deinit(allocator);
    try result.appendSlice(allocator, source);
    return result;
}

fn signedDifference(positive: usize, negative: usize) !i32 {
    if (positive > std.math.maxInt(i32) or negative > std.math.maxInt(i32))
        return error.StackDifferenceOverflow;
    return @as(i32, @intCast(positive)) - @as(i32, @intCast(negative));
}
