// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Backward symbolic stack-layout propagation for optimized Yul EVM code
//! generation, including join stitching, loop stabilization, junk insertion,
//! and stack-too-deep reporting.

const std = @import("std");
const CFG = @import("control_flow_graph.zig");
const EVMDialect = @import("evm_dialect.zig").EVMDialect;
const GasMeter = @import("../../../libevmasm/gas_meter.zig");
const Instruction = @import("../../../libevmasm/instruction.zig");
const ScopeModule = @import("../../scope.zig");
const StackHelpers = @import("stack_helpers.zig");
const YulName = @import("../../yul_name.zig").YulName;

pub const BlockInfo = struct {
    entry_layout: CFG.Stack = .empty,
    exit_layout: CFG.Stack = .empty,

    fn deinit(self: *BlockInfo, allocator: std.mem.Allocator) void {
        self.entry_layout.deinit(allocator);
        self.exit_layout.deinit(allocator);
        self.* = undefined;
    }
};

pub const StackLayout = struct {
    allocator: std.mem.Allocator,
    block_infos: std.AutoHashMap(*const CFG.BasicBlock, BlockInfo),
    operation_entry_layout: std.AutoHashMap(*const CFG.Operation, CFG.Stack),

    pub fn init(allocator: std.mem.Allocator) StackLayout {
        return .{
            .allocator = allocator,
            .block_infos = std.AutoHashMap(*const CFG.BasicBlock, BlockInfo).init(allocator),
            .operation_entry_layout = std.AutoHashMap(*const CFG.Operation, CFG.Stack).init(allocator),
        };
    }

    pub fn deinit(self: *StackLayout) void {
        var block_infos = self.block_infos.valueIterator();
        while (block_infos.next()) |info| info.deinit(self.allocator);
        self.block_infos.deinit();
        var operation_layouts = self.operation_entry_layout.valueIterator();
        while (operation_layouts.next()) |layout| layout.deinit(self.allocator);
        self.operation_entry_layout.deinit();
        self.* = undefined;
    }

    fn setBlockInfo(self: *StackLayout, block: *const CFG.BasicBlock, info: BlockInfo) !void {
        if (self.block_infos.getPtr(block)) |existing| {
            existing.deinit(self.allocator);
            existing.* = info;
        } else try self.block_infos.put(block, info);
    }

    fn setOperationLayout(self: *StackLayout, operation: *const CFG.Operation, layout: CFG.Stack) !void {
        if (self.operation_entry_layout.getPtr(operation)) |existing| {
            existing.deinit(self.allocator);
            existing.* = layout;
        } else try self.operation_entry_layout.put(operation, layout);
    }
};

pub const StackTooDeep = struct {
    deficit: usize = 0,
    variable_choices: std.ArrayList(YulName) = .empty,

    pub fn deinit(self: *StackTooDeep, allocator: std.mem.Allocator) void {
        self.variable_choices.deinit(allocator);
        self.* = undefined;
    }
};

pub const StackTooDeepByFunction = std.AutoHashMap(YulName, std.ArrayList(StackTooDeep));

pub const StackLayoutGenerator = struct {
    allocator: std.mem.Allocator,
    layout: *StackLayout,
    current_function_info: ?*const CFG.FunctionInfo,
    evm_dialect: *const EVMDialect,

    pub fn run(
        allocator: std.mem.Allocator,
        graph: *const CFG.CFG,
        evm_dialect: *const EVMDialect,
    ) !StackLayout {
        var layout = StackLayout.init(allocator);
        errdefer layout.deinit();
        var main_generator: StackLayoutGenerator = .{
            .allocator = allocator,
            .layout = &layout,
            .current_function_info = null,
            .evm_dialect = evm_dialect,
        };
        try main_generator.processEntryPoint(graph.entry orelse return error.InvalidControlFlow, null);
        for (graph.functions.items) |function| {
            const info = graph.function_info.get(function) orelse return error.InvalidControlFlow;
            var function_generator: StackLayoutGenerator = .{
                .allocator = allocator,
                .layout = &layout,
                .current_function_info = info,
                .evm_dialect = evm_dialect,
            };
            try function_generator.processEntryPoint(info.entry, info);
        }
        return layout;
    }

    pub fn reportStackTooDeepForFunction(
        allocator: std.mem.Allocator,
        graph: *const CFG.CFG,
        function_name: YulName,
        evm_dialect: *const EVMDialect,
    ) !std.ArrayList(StackTooDeep) {
        var layout = StackLayout.init(allocator);
        defer layout.deinit();
        var function_info: ?*const CFG.FunctionInfo = null;
        if (!function_name.empty()) {
            for (graph.functions.items) |function| if (function.name.eql(function_name)) {
                function_info = graph.function_info.get(function) orelse return error.InvalidControlFlow;
                break;
            };
            if (function_info == null) return error.FunctionNotFound;
        }
        var generator: StackLayoutGenerator = .{
            .allocator = allocator,
            .layout = &layout,
            .current_function_info = function_info,
            .evm_dialect = evm_dialect,
        };
        const entry = if (function_info) |info| info.entry else graph.entry orelse return error.InvalidControlFlow;
        try generator.processEntryPoint(entry, function_info);
        return generator.reportStackTooDeepFromEntry(entry);
    }

    pub fn reportStackTooDeepAll(
        allocator: std.mem.Allocator,
        graph: *const CFG.CFG,
        evm_dialect: *const EVMDialect,
    ) !StackTooDeepByFunction {
        var result = StackTooDeepByFunction.init(allocator); // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStackTooDeepByFunction(allocator, &result);
        {
            var errors = try reportStackTooDeepForFunction(allocator, graph, .{}, evm_dialect);
            errdefer deinitStackTooDeepList(allocator, &errors);
            try result.put(.{}, errors);
        }
        for (graph.functions.items) |function| {
            var errors = try reportStackTooDeepForFunction(allocator, graph, function.name, evm_dialect);
            errdefer deinitStackTooDeepList(allocator, &errors);
            if (errors.items.len == 0) {
                errors.deinit(allocator);
            } else try result.put(function.name, errors);
        }
        return result;
    }

    fn reachableStackDepth(self: *const StackLayoutGenerator) usize {
        return self.evm_dialect.reachableStackDepth();
    }

    fn propagateStackThroughOperation(
        self: *StackLayoutGenerator,
        exit_stack: []const CFG.StackSlot,
        operation: *const CFG.Operation,
        aggressive_stack_compression: bool,
    ) !CFG.Stack {
        var aggressive = aggressive_stack_compression;
        if (operation.operation == .function_call and operation.operation.function_call.recursive)
            aggressive = true;
        var stack = try createIdealLayout(
            self.allocator,
            operation.output.items,
            exit_stack,
            aggressive,
            self.reachableStackDepth(),
        );
        errdefer stack.deinit(self.allocator);
        if (operation.operation == .assignment) {
            for (stack.items) |slot| if (slot == .variable) {
                for (operation.operation.assignment.variables.items) |assigned|
                    if (slot.variable.variable == assigned.variable) return error.InvalidAssignedVariableLayout;
            };
        }
        try stack.appendSlice(self.allocator, operation.input.items);
        {
            var operation_layout = try cloneStack(self.allocator, stack.items);
            errdefer operation_layout.deinit(self.allocator);
            try self.layout.setOperationLayout(operation, operation_layout);
        }
        while (stack.items.len != 0) {
            const top = stack.items[stack.items.len - 1];
            if (top.canBeFreelyGenerated()) {
                _ = stack.pop();
            } else if (findOffsetReverse(stack.items[0 .. stack.items.len - 1], top)) |offset| {
                if (offset + 2 < self.reachableStackDepth())
                    _ = stack.pop()
                else
                    break;
            } else break;
        }
        return stack;
    }

    fn propagateStackThroughBlock(
        self: *StackLayoutGenerator,
        exit_stack: []const CFG.StackSlot,
        block: *const CFG.BasicBlock,
        aggressive_stack_compression: bool,
    ) !CFG.Stack {
        var stack = try cloneStack(self.allocator, exit_stack);
        errdefer stack.deinit(self.allocator);
        var index = block.operations.items.len;
        while (index != 0) {
            index -= 1;
            var new_stack = try self.propagateStackThroughOperation(
                stack.items,
                &block.operations.items[index],
                aggressive_stack_compression,
            );
            errdefer new_stack.deinit(self.allocator);
            if (!aggressive_stack_compression) {
                var stack_errors = try findStackTooDeep(
                    self.allocator,
                    new_stack.items,
                    stack.items,
                    self.reachableStackDepth(),
                );
                const has_errors = stack_errors.items.len != 0;
                deinitStackTooDeepList(self.allocator, &stack_errors);
                if (has_errors) {
                    const compressed = try self.propagateStackThroughBlock(exit_stack, block, true);
                    new_stack.deinit(self.allocator);
                    stack.deinit(self.allocator);
                    return compressed;
                }
            }
            stack.deinit(self.allocator);
            stack = new_stack;
        }
        return stack;
    }

    fn processEntryPoint(
        self: *StackLayoutGenerator,
        entry: *const CFG.BasicBlock,
        function_info: ?*const CFG.FunctionInfo,
    ) !void {
        var to_visit: std.ArrayList(*const CFG.BasicBlock) = .empty;
        defer to_visit.deinit(self.allocator);
        try to_visit.append(self.allocator, entry);
        var visited = std.AutoHashMap(*const CFG.BasicBlock, void).init(self.allocator);
        defer visited.deinit();
        var backwards_jumps = try collectBackwardsJumps(self.allocator, entry);
        defer backwards_jumps.deinit(self.allocator);
        while (to_visit.items.len != 0) {
            while (to_visit.items.len != 0) {
                const block = to_visit.orderedRemove(0);
                if (visited.contains(block)) continue;
                const maybe_exit = try self.getExitLayoutOrStageDependencies(block, &visited, &to_visit);
                if (maybe_exit) |exit_value| {
                    var exit_layout = exit_value;
                    var owns_exit = true;
                    errdefer if (owns_exit) exit_layout.deinit(self.allocator);
                    try visited.put(block, {});
                    var entry_layout = try self.propagateStackThroughBlock(exit_layout.items, block, false);
                    var owns_entry = true;
                    errdefer if (owns_entry) entry_layout.deinit(self.allocator);
                    try self.layout.setBlockInfo(block, .{
                        .entry_layout = entry_layout,
                        .exit_layout = exit_layout,
                    });
                    owns_entry = false;
                    owns_exit = false;
                    for (block.entries.items) |predecessor| try to_visit.append(self.allocator, predecessor);
                }
            }
            for (backwards_jumps.items) |backwards_jump| {
                const target_info = self.layout.block_infos.get(backwards_jump.target) orelse return error.InvalidStackLayout;
                const jumping_info = self.layout.block_infos.get(backwards_jump.jumping_block) orelse return error.InvalidStackLayout;
                var missing = false;
                for (target_info.entry_layout.items) |slot| if (!containsSlot(jumping_info.exit_layout.items, slot)) {
                    missing = true;
                    break;
                };
                if (!missing) continue;
                try to_visit.insert(self.allocator, 0, backwards_jump.jumping_block);
                for (backwards_jump.target.entries.items) |predecessor| _ = visited.remove(predecessor);
                var reverse_queue: std.ArrayList(*const CFG.BasicBlock) = .empty;
                defer reverse_queue.deinit(self.allocator);
                var reverse_seen = std.AutoHashMap(*const CFG.BasicBlock, void).init(self.allocator);
                defer reverse_seen.deinit();
                try reverse_queue.append(self.allocator, backwards_jump.jumping_block);
                var cursor: usize = 0;
                while (cursor < reverse_queue.items.len) : (cursor += 1) {
                    const block = reverse_queue.items[cursor];
                    const inserted = try reverse_seen.getOrPut(block);
                    if (inserted.found_existing) continue;
                    _ = visited.remove(block);
                    if (block == backwards_jump.target) continue;
                    try reverse_queue.appendSlice(self.allocator, block.entries.items);
                }
            }
        }
        try self.stitchConditionalJumps(entry);
        try self.fillInJunk(entry, function_info);
    }

    fn getExitLayoutOrStageDependencies(
        self: *StackLayoutGenerator,
        block: *const CFG.BasicBlock,
        visited: *const std.AutoHashMap(*const CFG.BasicBlock, void),
        to_visit: *std.ArrayList(*const CFG.BasicBlock),
    ) !?CFG.Stack {
        return switch (block.exit) {
            .main_exit, .terminated => CFG.Stack.empty,
            .jump => |jump| blk: {
                if (jump.backwards) {
                    if (self.layout.block_infos.get(jump.target)) |info|
                        break :blk try cloneStack(self.allocator, info.entry_layout.items);
                    break :blk CFG.Stack.empty;
                }
                if (visited.contains(jump.target)) {
                    const info = self.layout.block_infos.get(jump.target) orelse return error.InvalidStackLayout;
                    break :blk try cloneStack(self.allocator, info.entry_layout.items);
                }
                try to_visit.insert(self.allocator, 0, jump.target);
                break :blk null;
            },
            .conditional_jump => |jump| blk: {
                const zero_visited = visited.contains(jump.zero);
                const non_zero_visited = visited.contains(jump.non_zero);
                if (zero_visited and non_zero_visited) {
                    const zero_info = self.layout.block_infos.get(jump.zero) orelse return error.InvalidStackLayout;
                    const non_zero_info = self.layout.block_infos.get(jump.non_zero) orelse return error.InvalidStackLayout;
                    var stack = try combineStack(
                        self.allocator,
                        zero_info.entry_layout.items,
                        non_zero_info.entry_layout.items,
                        self.reachableStackDepth(),
                    );
                    errdefer stack.deinit(self.allocator);
                    try stack.append(self.allocator, jump.condition);
                    break :blk stack;
                }
                if (!zero_visited) try to_visit.insert(self.allocator, 0, jump.zero);
                if (!non_zero_visited) try to_visit.insert(self.allocator, 0, jump.non_zero);
                break :blk null;
            },
            .function_return => |function_return| blk: {
                var stack: CFG.Stack = .empty;
                errdefer stack.deinit(self.allocator);
                for (function_return.info.return_variables.items) |variable|
                    try stack.append(self.allocator, .{ .variable = variable });
                try stack.append(self.allocator, .{ .function_return_label = .{
                    .function = function_return.info.function,
                } });
                break :blk stack;
            },
        };
    }

    fn stitchConditionalJumps(self: *StackLayoutGenerator, entry: *const CFG.BasicBlock) !void {
        var queue: std.ArrayList(*const CFG.BasicBlock) = .empty;
        defer queue.deinit(self.allocator);
        var visited = std.AutoHashMap(*const CFG.BasicBlock, void).init(self.allocator);
        defer visited.deinit();
        try queue.append(self.allocator, entry);
        var cursor: usize = 0;
        while (cursor < queue.items.len) : (cursor += 1) {
            const block = queue.items[cursor];
            const inserted = try visited.getOrPut(block);
            if (inserted.found_existing) continue;
            switch (block.exit) {
                .jump => |jump| if (!jump.backwards) try queue.append(self.allocator, jump.target),
                .conditional_jump => |jump| {
                    const info = self.layout.block_infos.get(block) orelse return error.InvalidStackLayout;
                    var exit_layout = try cloneStack(self.allocator, info.exit_layout.items);
                    defer exit_layout.deinit(self.allocator);
                    if (exit_layout.items.len == 0 or !exit_layout.items[exit_layout.items.len - 1].eql(jump.condition))
                        return error.InvalidConditionalLayout;
                    _ = exit_layout.pop();
                    try self.fixJumpTargetEntry(jump.zero, exit_layout.items);
                    try self.fixJumpTargetEntry(jump.non_zero, exit_layout.items);
                    try queue.append(self.allocator, jump.zero);
                    try queue.append(self.allocator, jump.non_zero);
                },
                else => {},
            }
        }
    }

    fn fixJumpTargetEntry(
        self: *StackLayoutGenerator,
        target: *const CFG.BasicBlock,
        exit_layout: []const CFG.StackSlot,
    ) !void {
        const target_info = self.layout.block_infos.getPtr(target) orelse return error.InvalidStackLayout;
        var new_layout = try cloneStack(self.allocator, exit_layout);
        errdefer new_layout.deinit(self.allocator);
        for (new_layout.items) |*slot| {
            if (!containsSlot(target_info.entry_layout.items, slot.*))
                slot.* = .{ .junk = .{} };
        }
        for (target_info.entry_layout.items) |slot| {
            if (!slot.canBeFreelyGenerated() and !containsSlot(new_layout.items, slot))
                return error.InvalidConditionalLayout;
        }
        target_info.entry_layout.deinit(self.allocator);
        target_info.entry_layout = new_layout;
    }

    fn reportStackTooDeepFromEntry(
        self: *StackLayoutGenerator,
        entry: *const CFG.BasicBlock,
    ) !std.ArrayList(StackTooDeep) {
        var result: std.ArrayList(StackTooDeep) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStackTooDeepList(self.allocator, &result);
        var queue: std.ArrayList(*const CFG.BasicBlock) = .empty;
        defer queue.deinit(self.allocator);
        var visited = std.AutoHashMap(*const CFG.BasicBlock, void).init(self.allocator);
        defer visited.deinit();
        try queue.append(self.allocator, entry);
        var cursor: usize = 0;
        while (cursor < queue.items.len) : (cursor += 1) {
            const block = queue.items[cursor];
            const inserted = try visited.getOrPut(block);
            if (inserted.found_existing) continue;
            const block_info = self.layout.block_infos.get(block) orelse return error.InvalidStackLayout;
            var current = try cloneStack(self.allocator, block_info.entry_layout.items);
            defer current.deinit(self.allocator);
            for (block.operations.items) |*operation| {
                const operation_entry = self.layout.operation_entry_layout.get(operation) orelse return error.InvalidStackLayout;
                var errors = try findStackTooDeep(
                    self.allocator,
                    current.items,
                    operation_entry.items,
                    self.reachableStackDepth(),
                );
                try moveErrors(self.allocator, &result, &errors);
                current.clearRetainingCapacity();
                try current.appendSlice(self.allocator, operation_entry.items);
                if (current.items.len < operation.input.items.len) return error.InvalidStackLayout;
                current.shrinkRetainingCapacity(current.items.len - operation.input.items.len);
                try current.appendSlice(self.allocator, operation.output.items);
            }
            switch (block.exit) {
                .jump => |jump| {
                    const target = self.layout.block_infos.get(jump.target) orelse return error.InvalidStackLayout;
                    var errors = try findStackTooDeep(
                        self.allocator,
                        current.items,
                        target.entry_layout.items,
                        self.reachableStackDepth(),
                    );
                    try moveErrors(self.allocator, &result, &errors);
                    if (!jump.backwards) try queue.append(self.allocator, jump.target);
                },
                .conditional_jump => |jump| {
                    for ([_]*const CFG.BasicBlock{ jump.zero, jump.non_zero }) |target_block| {
                        const target = self.layout.block_infos.get(target_block) orelse return error.InvalidStackLayout;
                        var errors = try findStackTooDeep(
                            self.allocator,
                            current.items,
                            target.entry_layout.items,
                            self.reachableStackDepth(),
                        );
                        try moveErrors(self.allocator, &result, &errors);
                    }
                    try queue.append(self.allocator, jump.zero);
                    try queue.append(self.allocator, jump.non_zero);
                },
                else => {},
            }
        }
        return result;
    }

    fn fillInJunk(
        self: *StackLayoutGenerator,
        entry: *const CFG.BasicBlock,
        function_info: ?*const CFG.FunctionInfo,
    ) !void {
        if (function_info) |info| {
            if (!info.can_continue and entry.allowsJunk()) {
                var source: CFG.Stack = .empty;
                defer source.deinit(self.allocator);
                var index = info.parameters.items.len;
                while (index != 0) {
                    index -= 1;
                    try source.append(self.allocator, .{ .variable = info.parameters.items[index] });
                }
                const target = self.layout.block_infos.get(entry) orelse return error.InvalidStackLayout;
                const best = try self.getBestNumJunk(source.items, target.entry_layout.items);
                if (best > 0) try self.addJunkRecursive(entry, best);
            }
        }

        var queue: std.ArrayList(*const CFG.BasicBlock) = .empty;
        defer queue.deinit(self.allocator);
        var visited = std.AutoHashMap(*const CFG.BasicBlock, void).init(self.allocator);
        defer visited.deinit();
        try queue.append(self.allocator, entry);
        var cursor: usize = 0;
        while (cursor < queue.items.len) : (cursor += 1) {
            const block = queue.items[cursor];
            const inserted = try visited.getOrPut(block);
            if (inserted.found_existing) continue;
            if (block.allowsJunk()) {
                const block_info = self.layout.block_infos.getPtr(block) orelse return error.InvalidStackLayout;
                var saved_entry = try cloneStack(self.allocator, block_info.entry_layout.items);
                var saved_entry_owned = true;
                defer if (saved_entry_owned) saved_entry.deinit(self.allocator);
                const next_layout = if (block.operations.items.len == 0)
                    block_info.exit_layout.items
                else
                    (self.layout.operation_entry_layout.get(&block.operations.items[0]) orelse
                        return error.InvalidStackLayout).items;
                if (!stacksEqual(block_info.entry_layout.items, next_layout)) {
                    const best = try self.getBestNumJunk(block_info.entry_layout.items, next_layout);
                    if (best > 0) {
                        try self.addJunkRecursive(block, best);
                        const updated = self.layout.block_infos.getPtr(block) orelse return error.InvalidStackLayout;
                        updated.entry_layout.deinit(self.allocator);
                        updated.entry_layout = saved_entry;
                        saved_entry_owned = false;
                    }
                }
            }
            switch (block.exit) {
                .jump => |jump| try queue.append(self.allocator, jump.target),
                .conditional_jump => |jump| {
                    try queue.append(self.allocator, jump.zero);
                    try queue.append(self.allocator, jump.non_zero);
                },
                else => {},
            }
        }
    }

    fn addJunkRecursive(
        self: *StackLayoutGenerator,
        entry: *const CFG.BasicBlock,
        count: usize,
    ) !void {
        var queue: std.ArrayList(*const CFG.BasicBlock) = .empty;
        defer queue.deinit(self.allocator);
        var visited = std.AutoHashMap(*const CFG.BasicBlock, void).init(self.allocator);
        defer visited.deinit();
        try queue.append(self.allocator, entry);
        var cursor: usize = 0;
        while (cursor < queue.items.len) : (cursor += 1) {
            const block = queue.items[cursor];
            const inserted = try visited.getOrPut(block);
            if (inserted.found_existing) continue;
            const info = self.layout.block_infos.getPtr(block) orelse return error.InvalidStackLayout;
            try prependJunk(self.allocator, &info.entry_layout, count);
            for (block.operations.items) |*operation| {
                const operation_layout = self.layout.operation_entry_layout.getPtr(operation) orelse
                    return error.InvalidStackLayout;
                try prependJunk(self.allocator, operation_layout, count);
            }
            try prependJunk(self.allocator, &info.exit_layout, count);
            switch (block.exit) {
                .jump => |jump| try queue.append(self.allocator, jump.target),
                .conditional_jump => |jump| {
                    try queue.append(self.allocator, jump.zero);
                    try queue.append(self.allocator, jump.non_zero);
                },
                .function_return => return error.UnexpectedFunctionReturnInJunkSubgraph,
                else => {},
            }
        }
    }

    fn evaluateTransform(
        self: *StackLayoutGenerator,
        source_slice: []const CFG.StackSlot,
        target: []const CFG.StackSlot,
    ) !usize {
        var source = try cloneStack(self.allocator, source_slice);
        defer source.deinit(self.allocator);
        const Callbacks = struct {
            generator: *StackLayoutGenerator,
            source: *CFG.Stack,
            op_gas: *usize,

            pub fn swap(callbacks: @This(), depth: usize) !void {
                callbacks.op_gas.* += if (depth > callbacks.generator.reachableStackDepth())
                    1000
                else
                    try GasMeter.swapGas(depth, callbacks.generator.evm_dialect.evmVersion());
            }

            pub fn pushOrDup(callbacks: @This(), slot: CFG.StackSlot) !void {
                if (slot.canBeFreelyGenerated()) {
                    callbacks.op_gas.* += try GasMeter.runGas(
                        Instruction.pushInstruction(32),
                        callbacks.generator.evm_dialect.evmVersion(),
                    );
                } else if (findOffsetReverse(callbacks.source.items, slot)) |depth| {
                    callbacks.op_gas.* += if (depth < callbacks.generator.reachableStackDepth())
                        try GasMeter.dupGas(depth + 1, callbacks.generator.evm_dialect.evmVersion())
                    else
                        1000;
                } else {
                    const function_info = callbacks.generator.current_function_info orelse
                        return error.MissingReturnVariable;
                    if (slot != .variable or !containsVariable(function_info.return_variables.items, slot.variable.variable))
                        return error.MissingReturnVariable;
                    callbacks.op_gas.* += try GasMeter.pushGas(0, callbacks.generator.evm_dialect.evmVersion());
                }
            }

            pub fn pop(callbacks: @This()) !void {
                callbacks.op_gas.* += try GasMeter.runGas(
                    .POP,
                    callbacks.generator.evm_dialect.evmVersion(),
                );
            }
        };
        var gas: usize = 0;
        try StackHelpers.createStackLayout(
            self.allocator,
            &source,
            target,
            Callbacks{ .generator = self, .source = &source, .op_gas = &gas },
            self.reachableStackDepth(),
        );
        return gas;
    }

    fn getBestNumJunk(
        self: *StackLayoutGenerator,
        entry_layout: []const CFG.StackSlot,
        target_layout: []const CFG.StackSlot,
    ) !usize {
        var best_cost = try self.evaluateTransform(entry_layout, target_layout);
        var best_num_junk: usize = 0;
        var count: usize = 1;
        while (count <= entry_layout.len) : (count += 1) {
            var target: CFG.Stack = .empty;
            defer target.deinit(self.allocator);
            try appendJunk(self.allocator, &target, count);
            try target.appendSlice(self.allocator, target_layout);
            const cost = try self.evaluateTransform(entry_layout, target.items);
            if (cost < best_cost) {
                best_cost = cost;
                best_num_junk = count;
            }
        }
        return best_num_junk;
    }
};

pub fn deinitStackTooDeepByFunction(
    allocator: std.mem.Allocator,
    errors_by_function: *StackTooDeepByFunction,
) void {
    var values = errors_by_function.valueIterator();
    while (values.next()) |errors| deinitStackTooDeepList(allocator, errors);
    errors_by_function.deinit();
}

fn deinitStackTooDeepList(allocator: std.mem.Allocator, errors: *std.ArrayList(StackTooDeep)) void {
    for (errors.items) |*stack_error| stack_error.deinit(allocator);
    errors.deinit(allocator);
}

fn moveErrors(
    allocator: std.mem.Allocator,
    destination: *std.ArrayList(StackTooDeep),
    source: *std.ArrayList(StackTooDeep),
) !void {
    errdefer deinitStackTooDeepList(allocator, source);
    try destination.appendSlice(allocator, source.items);
    source.clearRetainingCapacity();
    source.deinit(allocator);
}

fn cloneStack(allocator: std.mem.Allocator, source: []const CFG.StackSlot) !CFG.Stack {
    var result: CFG.Stack = .empty;
    errdefer result.deinit(allocator);
    try result.appendSlice(allocator, source);
    return result;
}

fn stacksEqual(left: []const CFG.StackSlot, right: []const CFG.StackSlot) bool {
    if (left.len != right.len) return false;
    for (left, right) |left_slot, right_slot| if (!left_slot.eql(right_slot)) return false;
    return true;
}

fn containsSlot(stack: []const CFG.StackSlot, slot: CFG.StackSlot) bool {
    for (stack) |candidate| if (candidate.eql(slot)) return true;
    return false;
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

fn appendUniqueName(allocator: std.mem.Allocator, names: *std.ArrayList(YulName), name: YulName) !void {
    for (names.items) |existing| if (existing.eql(name)) return;
    try names.append(allocator, name);
}

fn variableChoices(
    allocator: std.mem.Allocator,
    stack: []const CFG.StackSlot,
) !std.ArrayList(YulName) {
    var result: std.ArrayList(YulName) = .empty;
    errdefer result.deinit(allocator);
    for (stack) |slot| if (slot == .variable)
        try appendUniqueName(allocator, &result, slot.variable.variable.name);
    return result;
}

fn findStackTooDeep(
    allocator: std.mem.Allocator,
    source: []const CFG.StackSlot,
    target: []const CFG.StackSlot,
    reachable_stack_depth: usize,
) !std.ArrayList(StackTooDeep) {
    var current = try cloneStack(allocator, source);
    defer current.deinit(allocator);
    var errors: std.ArrayList(StackTooDeep) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
    errdefer deinitStackTooDeepList(allocator, &errors);
    const Callbacks = struct {
        allocator: std.mem.Allocator,
        current: *CFG.Stack,
        errors: *std.ArrayList(StackTooDeep),
        reachable: usize,

        fn appendError(callbacks: @This(), deficit: usize, depth: usize) !void {
            const start = callbacks.current.items.len - @min(callbacks.current.items.len, depth + 1);
            try callbacks.errors.ensureUnusedCapacity(callbacks.allocator, 1);
            callbacks.errors.appendAssumeCapacity(.{
                .deficit = deficit,
                .variable_choices = try variableChoices(callbacks.allocator, callbacks.current.items[start..]),
            });
        }

        pub fn swap(callbacks: @This(), depth: usize) !void {
            if (depth > callbacks.reachable)
                try callbacks.appendError(depth - callbacks.reachable, depth);
        }

        pub fn pushOrDup(callbacks: @This(), slot: CFG.StackSlot) !void {
            if (slot.canBeFreelyGenerated()) return;
            if (findOffsetReverse(callbacks.current.items, slot)) |depth| {
                if (depth >= callbacks.reachable)
                    try callbacks.appendError(depth - (callbacks.reachable - 1), depth);
            }
        }

        pub fn pop(_: @This()) !void {}
    };
    try StackHelpers.createStackLayout(
        allocator,
        &current,
        target,
        Callbacks{
            .allocator = allocator,
            .current = &current,
            .errors = &errors,
            .reachable = reachable_stack_depth,
        },
        reachable_stack_depth,
    );
    return errors;
}

test "stack-too-deep diagnostics release variable choices on allocation failure" {
    const variables = [_]ScopeModule.Variable{
        .{ .name = try YulName.init("deep_a") },
        .{ .name = try YulName.init("deep_b") },
        .{ .name = try YulName.init("deep_c") },
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseStackTooDeep, .{&variables});
}

fn exerciseStackTooDeep(allocator: std.mem.Allocator, variables: *const [3]ScopeModule.Variable) !void {
    const source = [_]CFG.StackSlot{
        .{ .variable = .{ .variable = &variables[0] } },
        .{ .variable = .{ .variable = &variables[1] } },
        .{ .variable = .{ .variable = &variables[2] } },
    };
    var errors = try findStackTooDeep(allocator, &source, &.{ source[0], source[1], source[2], source[0] }, 1);
    defer deinitStackTooDeepList(allocator, &errors);
    try std.testing.expect(errors.items.len > 0);
    try std.testing.expect(errors.items[0].variable_choices.items.len > 0);
}

const LayoutItem = union(enum) {
    previous: usize,
    slot: CFG.StackSlot,
};

fn createIdealLayout(
    allocator: std.mem.Allocator,
    operation_output: []const CFG.StackSlot,
    post: []const CFG.StackSlot,
    aggressive: bool,
    reachable_stack_depth: usize,
) !CFG.Stack {
    var pre_size = post.len;
    for (post) |slot| {
        if (containsSlot(operation_output, slot) or
            (aggressive and slot.canBeFreelyGenerated()))
            pre_size -= 1;
    }
    var layout: std.ArrayList(LayoutItem) = .empty;
    defer layout.deinit(allocator);
    for (0..pre_size) |index| try layout.append(allocator, .{ .previous = index });
    for (operation_output) |slot| try layout.append(allocator, .{ .slot = slot });
    if (layout.items.len == 0) return CFG.Stack.empty;

    const IdealOperations = struct {
        allocator: std.mem.Allocator,
        layout: *std.ArrayList(LayoutItem),
        post: []const CFG.StackSlot,
        operation_output: []const CFG.StackSlot,
        aggressive: bool,
        reachable_stack_depth: usize,

        fn generated(self: *const @This(), slot: CFG.StackSlot) bool {
            return self.aggressive and slot.canBeFreelyGenerated();
        }
        fn output(self: *const @This(), slot: CFG.StackSlot) bool {
            return containsSlot(self.operation_output, slot);
        }
        fn multiplicity(self: *const @This(), slot: CFG.StackSlot) i32 {
            var result: i32 = 0;
            for (self.layout.items) |item| {
                if (item == .slot and item.slot.eql(slot)) result -= 1;
            }
            for (self.post) |post_slot| {
                if ((self.output(post_slot) or self.generated(post_slot)) and post_slot.eql(slot))
                    result += 1;
            }
            return result;
        }
        pub fn isCompatible(self: *const @This(), source: usize, target: usize) bool {
            if (source >= self.layout.items.len or target >= self.post.len) return false;
            if (self.post[target] == .junk) return true;
            return switch (self.layout.items[source]) {
                .previous => !self.output(self.post[target]) and !self.generated(self.post[target]),
                .slot => |slot| slot.eql(self.post[target]),
            };
        }
        pub fn sourceIsSame(self: *const @This(), left: usize, right: usize) bool {
            const left_item = self.layout.items[left];
            const right_item = self.layout.items[right];
            return switch (left_item) {
                .previous => right_item == .previous,
                .slot => |slot| right_item == .slot and slot.eql(right_item.slot),
            };
        }
        pub fn sourceMultiplicity(self: *const @This(), offset: usize) i32 {
            return switch (self.layout.items[offset]) {
                .previous => 0,
                .slot => |slot| self.multiplicity(slot),
            };
        }
        pub fn targetMultiplicity(self: *const @This(), offset: usize) i32 {
            if (!self.output(self.post[offset]) and !self.generated(self.post[offset])) return 0;
            return self.multiplicity(self.post[offset]);
        }
        pub fn targetIsArbitrary(self: *const @This(), offset: usize) bool {
            return offset < self.post.len and self.post[offset] == .junk;
        }
        pub fn sourceSize(self: *const @This()) usize {
            return self.layout.items.len;
        }
        pub fn targetSize(self: *const @This()) usize {
            return self.post.len;
        }
        pub fn swap(self: *@This(), depth: usize) !void {
            const top = self.layout.items.len - 1;
            if (self.layout.items[top - depth] == .previous and self.layout.items[top] == .previous)
                return error.InvalidIdealLayoutSwap;
            std.mem.swap(LayoutItem, &self.layout.items[top - depth], &self.layout.items[top]);
        }
        pub fn pop(self: *@This()) !void {
            _ = self.layout.pop();
        }
        pub fn pushOrDupTarget(self: *@This(), offset: usize) !void {
            try self.layout.append(self.allocator, .{ .slot = self.post[offset] });
        }
    };
    var operations: IdealOperations = .{
        .allocator = allocator,
        .layout = &layout,
        .post = post,
        .operation_output = operation_output,
        .aggressive = aggressive,
        .reachable_stack_depth = reachable_stack_depth,
    };
    try StackHelpers.shuffleWithOperations(&operations);
    var ideal = try allocator.alloc(?CFG.StackSlot, post.len);
    defer allocator.free(ideal);
    @memset(ideal, null);
    for (post, layout.items) |slot, item| {
        if (item == .previous) ideal[item.previous] = slot;
    }
    var ideal_len = ideal.len;
    while (ideal_len != 0 and ideal[ideal_len - 1] == null) ideal_len -= 1;
    if (ideal_len != pre_size) return error.InvalidIdealLayout;
    var result: CFG.Stack = .empty;
    errdefer result.deinit(allocator);
    for (ideal[0..ideal_len]) |slot| try result.append(allocator, slot orelse return error.InvalidIdealLayout);
    return result;
}

const BackwardsJump = struct {
    jumping_block: *const CFG.BasicBlock,
    target: *const CFG.BasicBlock,
};

fn collectBackwardsJumps(
    allocator: std.mem.Allocator,
    entry: *const CFG.BasicBlock,
) !std.ArrayList(BackwardsJump) {
    var result: std.ArrayList(BackwardsJump) = .empty;
    errdefer result.deinit(allocator);
    var queue: std.ArrayList(*const CFG.BasicBlock) = .empty;
    defer queue.deinit(allocator);
    var visited = std.AutoHashMap(*const CFG.BasicBlock, void).init(allocator);
    defer visited.deinit();
    try queue.append(allocator, entry);
    var cursor: usize = 0;
    while (cursor < queue.items.len) : (cursor += 1) {
        const block = queue.items[cursor];
        const inserted = try visited.getOrPut(block);
        if (inserted.found_existing) continue;
        switch (block.exit) {
            .jump => |jump| {
                if (jump.backwards) try result.append(allocator, .{
                    .jumping_block = block,
                    .target = jump.target,
                });
                try queue.append(allocator, jump.target);
            },
            .conditional_jump => |jump| {
                try queue.append(allocator, jump.zero);
                try queue.append(allocator, jump.non_zero);
            },
            else => {},
        }
    }
    return result;
}

fn compressStack(
    allocator: std.mem.Allocator,
    stack_slice: []const CFG.StackSlot,
    reachable_stack_depth: usize,
) !CFG.Stack {
    var stack = try cloneStack(allocator, stack_slice);
    errdefer stack.deinit(allocator);
    var first_duplicate_offset: ?usize = null;
    while (true) {
        if (first_duplicate_offset) |offset| {
            std.mem.swap(CFG.StackSlot, &stack.items[offset], &stack.items[stack.items.len - 1]);
            _ = stack.pop();
            first_duplicate_offset = null;
        }
        var depth: usize = 0;
        var index = stack.items.len;
        while (index != 0) : (depth += 1) {
            index -= 1;
            const slot = stack.items[index];
            if (slot.canBeFreelyGenerated()) {
                first_duplicate_offset = index;
                break;
            }
            const prefix_end = stack.items.len - depth - 1;
            if (findOffsetReverse(stack.items[0..prefix_end], slot)) |duplicate_depth| {
                if (depth + duplicate_depth <= reachable_stack_depth) {
                    first_duplicate_offset = index;
                    break;
                }
            }
        }
        if (first_duplicate_offset == null) break;
    }
    return stack;
}

fn combineStack(
    allocator: std.mem.Allocator,
    first: []const CFG.StackSlot,
    second: []const CFG.StackSlot,
    reachable_stack_depth: usize,
) !CFG.Stack {
    var common_len: usize = 0;
    while (common_len < @min(first.len, second.len) and first[common_len].eql(second[common_len]))
        common_len += 1;
    const first_tail = first[common_len..];
    const second_tail = second[common_len..];
    if (first_tail.len == 0 or second_tail.len == 0) {
        const tail = if (first_tail.len == 0) second_tail else first_tail;
        var compressed = try compressStack(allocator, tail, reachable_stack_depth);
        defer compressed.deinit(allocator);
        var result = try cloneStack(allocator, first[0..common_len]);
        errdefer result.deinit(allocator);
        try result.appendSlice(allocator, compressed.items);
        return result;
    }
    var candidate: CFG.Stack = .empty;
    defer candidate.deinit(allocator);
    for (first_tail) |slot| if (!containsSlot(candidate.items, slot)) try candidate.append(allocator, slot);
    for (second_tail) |slot| if (!containsSlot(candidate.items, slot)) try candidate.append(allocator, slot);
    var write: usize = 0;
    for (candidate.items) |slot| if (slot != .literal and slot != .function_call_return_label) {
        candidate.items[write] = slot;
        write += 1;
    };
    candidate.shrinkRetainingCapacity(write);

    const Evaluate = struct {
        allocator: std.mem.Allocator,
        common_prefix: []const CFG.StackSlot,
        reachable: usize,

        fn run(self: @This(), candidate_slice: []const CFG.StackSlot, target: []const CFG.StackSlot, cost: *usize) !void {
            var test_stack = try cloneStack(self.allocator, candidate_slice);
            defer test_stack.deinit(self.allocator);
            const Callbacks = struct {
                allocator: std.mem.Allocator,
                common_prefix: []const CFG.StackSlot,
                reachable: usize,
                test_stack: *CFG.Stack,
                cost: *usize,
                pub fn swap(callbacks: @This(), depth: usize) !void {
                    callbacks.cost.* += 1;
                    if (depth > callbacks.reachable) callbacks.cost.* += 1000;
                }
                pub fn pushOrDup(callbacks: @This(), slot: CFG.StackSlot) !void {
                    if (slot.canBeFreelyGenerated()) return;
                    var combined: CFG.Stack = .empty;
                    defer combined.deinit(callbacks.allocator);
                    try combined.appendSlice(callbacks.allocator, callbacks.common_prefix);
                    try combined.appendSlice(callbacks.allocator, callbacks.test_stack.items);
                    if (findOffsetReverse(combined.items, slot)) |depth| {
                        if (depth >= callbacks.reachable) callbacks.cost.* += 1000;
                    }
                }
                pub fn pop(_: @This()) !void {}
            };
            try StackHelpers.createStackLayout(
                self.allocator,
                &test_stack,
                target,
                Callbacks{
                    .allocator = self.allocator,
                    .common_prefix = self.common_prefix,
                    .reachable = self.reachable,
                    .test_stack = &test_stack,
                    .cost = cost,
                },
                self.reachable,
            );
        }

        fn both(self: @This(), candidate_slice: []const CFG.StackSlot, first_target: []const CFG.StackSlot, second_target: []const CFG.StackSlot) !usize {
            var cost: usize = 0;
            try self.run(candidate_slice, first_target, &cost);
            try self.run(candidate_slice, second_target, &cost);
            return cost;
        }
    };
    const evaluator: Evaluate = .{
        .allocator = allocator,
        .common_prefix = first[0..common_len],
        .reachable = reachable_stack_depth,
    };
    var best = try cloneStack(allocator, candidate.items);
    defer best.deinit(allocator);
    var best_cost = try evaluator.both(candidate.items, first_tail, second_tail);
    var counters = try allocator.alloc(usize, candidate.items.len);
    defer allocator.free(counters);
    @memset(counters, 0);
    var index: usize = 1;
    while (index < candidate.items.len) {
        if (counters[index] < index) {
            if ((index & 1) != 0)
                std.mem.swap(CFG.StackSlot, &candidate.items[0], &candidate.items[index])
            else
                std.mem.swap(CFG.StackSlot, &candidate.items[counters[index]], &candidate.items[index]);
            const cost = try evaluator.both(candidate.items, first_tail, second_tail);
            if (cost < best_cost) {
                best_cost = cost;
                best.deinit(allocator);
                best = try cloneStack(allocator, candidate.items);
            }
            counters[index] += 1;
            index += 1;
        } else {
            counters[index] = 0;
            index += 1;
        }
    }
    var result = try cloneStack(allocator, first[0..common_len]);
    errdefer result.deinit(allocator);
    try result.appendSlice(allocator, best.items);
    return result;
}

fn appendJunk(allocator: std.mem.Allocator, stack: *CFG.Stack, count: usize) !void {
    for (0..count) |_| try stack.append(allocator, .{ .junk = .{} });
}

fn prependJunk(allocator: std.mem.Allocator, stack: *CFG.Stack, count: usize) !void {
    var replacement: CFG.Stack = .empty;
    errdefer replacement.deinit(allocator);
    try appendJunk(allocator, &replacement, count);
    try replacement.appendSlice(allocator, stack.items);
    stack.deinit(allocator);
    stack.* = replacement;
}

test "stack layouts propagate through analyzed CFG operations and joins" {
    const Parser = @import("../../asm_parser.zig").Parser;
    const AsmAnalysis = @import("../../asm_analysis.zig");
    const AsmAnalysisInfo = @import("../../asm_analysis_info.zig").AsmAnalysisInfo;
    const CFGBuilder = @import("control_flow_graph_builder.zig").ControlFlowGraphBuilder;
    const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialectModule = @import("evm_dialect.zig");
    const allocator = std.testing.allocator;
    const dialect = try EVMDialectModule.strictAssemblyForEVM(EVMVersion.init(.Cancun));
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a) -> r { let x := add(a, 1) if x { r := x leave } r := 7 } pop(f(2)) }",
        "layout.yul",
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
    var graph = try CFGBuilder.build(allocator, &info, dialect.dialect(), ast.root());
    defer graph.deinit();
    try std.testing.checkAllAllocationFailures(allocator, exerciseStackTooDeepReport, .{ &graph, dialect });
    var layout = try StackLayoutGenerator.run(allocator, &graph, dialect);
    defer layout.deinit();
    try std.testing.expect(layout.block_infos.contains(graph.entry.?));
    for (graph.functions.items) |function|
        try std.testing.expect(layout.block_infos.contains(graph.function_info.get(function).?.entry));
}

fn exerciseStackTooDeepReport(allocator: std.mem.Allocator, graph: *const CFG.CFG, dialect: *const EVMDialect) !void {
    var errors = try StackLayoutGenerator.reportStackTooDeepAll(allocator, graph, dialect);
    defer deinitStackTooDeepByFunction(allocator, &errors);
    try std.testing.expect(errors.contains(.{}));
}
