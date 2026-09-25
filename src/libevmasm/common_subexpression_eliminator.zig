// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Common-subexpression analysis and stack code regeneration.

const std = @import("std");
const cxx = @import("cxx_compat");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const AssemblyItemModule = @import("assembly_item.zig");
const ExpressionClassesModule = @import("expression_classes.zig");
const InstructionModule = @import("instruction.zig");
const KnownStateModule = @import("known_state.zig");
const SemanticInformation = @import("semantic_information.zig");

const AssemblyItem = AssemblyItemModule.AssemblyItem;
const ExpressionClasses = ExpressionClassesModule.ExpressionClasses;
const Id = ExpressionClassesModule.Id;
const KnownState = KnownStateModule.KnownState;
const StoreOperation = KnownStateModule.StoreOperation;

fn lessI32(left: i32, right: i32) bool {
    return left < right;
}

fn lessId(left: Id, right: Id) bool {
    return left < right;
}

const StackMap = cxx.OrderedMap(i32, Id, lessI32);
const IdSet = cxx.OrderedSet(Id, lessId);
const PositionSet = cxx.OrderedSet(i32, lessI32);

pub const CSEError = KnownStateModule.KnownStateError || std.mem.Allocator.Error || error{
    ElementAlreadyRemoved,
    ElementNotPresent,
    IncorrectFinalStackHeight,
    InvalidBreakingItem,
    InvalidNumberOfReturnValues,
    InvalidStackAccess,
    InvalidUse,
    ItemNotAvailable,
    SequenceConstraint,
    StackTooDeep,
    TooManyArguments,
};

pub const CommonSubexpressionEliminator = struct {
    allocator: std.mem.Allocator,
    initial_state: KnownState,
    state: KnownState,
    evm_version: EVMVersion,
    store_operations: std.ArrayList(StoreOperation) = .empty,
    breaking_item: ?AssemblyItem = null,

    pub fn init(
        allocator: std.mem.Allocator,
        state: *const KnownState,
        evm_version: EVMVersion,
    ) std.mem.Allocator.Error!CommonSubexpressionEliminator {
        var initial = try state.clone();
        errdefer initial.deinit();
        var current = try state.clone();
        errdefer current.deinit();
        return .{
            .allocator = allocator,
            .initial_state = initial,
            .state = current,
            .evm_version = evm_version,
        };
    }

    pub fn deinit(self: *CommonSubexpressionEliminator) void {
        if (self.breaking_item) |*item| item.deinit(self.allocator);
        self.store_operations.deinit(self.allocator);
        self.state.deinit();
        self.initial_state.deinit();
        self.* = undefined;
    }

    /// Returns the number of consumed input items. At most 2000 ordinary
    /// items plus one breaking item are consumed per block, matching C++.
    pub fn feedItems(
        self: *CommonSubexpressionEliminator,
        items: []const AssemblyItem,
        msize_important: bool,
    ) CSEError!usize {
        if (self.breaking_item != null) return error.InvalidUse;
        var consumed: usize = 0;
        while (consumed < items.len and consumed < 2000 and
            !SemanticInformation.breaksCSEAnalysisBlock(&items[consumed], msize_important)) : (consumed += 1)
            try self.feedItem(&items[consumed], false);
        if (consumed < items.len and consumed < 2000) {
            self.breaking_item = try items[consumed].clone(self.allocator);
            consumed += 1;
        }
        return consumed;
    }

    pub fn getOptimizedItems(self: *CommonSubexpressionEliminator) CSEError!std.ArrayList(AssemblyItem) {
        return self.generateOptimizedItems(true);
    }

    /// Consumes this analysis on success or error. Returned items belong to the
    /// caller and must be destroyed with this object's allocator. Do not deinit
    /// or otherwise use this object again after calling finish.
    pub fn finish(self: *CommonSubexpressionEliminator) CSEError!std.ArrayList(AssemblyItem) {
        defer self.deinit();
        return self.generateOptimizedItems(false);
    }

    fn generateOptimizedItems(self: *CommonSubexpressionEliminator, comptime continue_analysis: bool) CSEError!std.ArrayList(AssemblyItem) {
        try self.optimizeBreakingItem();

        // Feeding the breaking item can intern expressions used by code
        // generation. Preserve that work even when no later state is needed.
        var next_initial = try self.state.clone();
        defer if (!continue_analysis) next_initial.deinit();
        errdefer if (continue_analysis) next_initial.deinit();
        if (self.breaking_item) |*breaking| _ = try next_initial.feedItem(breaking, false);
        var next_state = if (continue_analysis) try next_initial.clone() else {}; // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value when continuation state is unnecessary
        errdefer if (continue_analysis) next_state.deinit();

        var initial_stack: StackMap = .{};
        defer initial_stack.deinit(self.allocator);
        var target_stack: StackMap = .{};
        defer target_stack.deinit(self.allocator);
        var minimum_height = self.state.stack_height + 1;
        if (!self.state.stack_elements.isEmpty())
            minimum_height = @min(minimum_height, self.state.stack_elements.items()[0].key);
        var height = minimum_height;
        while (height <= self.initial_state.stack_height) : (height += 1)
            _ = try initial_stack.insert(
                self.allocator,
                height,
                try self.initial_state.stackElement(height, .{}),
            );
        height = minimum_height;
        while (height <= self.state.stack_height) : (height += 1)
            _ = try target_stack.insert(
                self.allocator,
                height,
                try self.state.stackElement(height, .{}),
            );

        var generator = try CSECodeGenerator.init(
            self.allocator,
            self.state.expressionClasses(),
            self.store_operations.items,
            self.evm_version,
        );
        defer generator.deinit();
        var output = try generator.generateCode(
            self.initial_state.sequence_number,
            self.initial_state.stack_height,
            &initial_stack,
            &target_stack,
        );
        errdefer deinitItems(self.allocator, &output);
        if (self.breaking_item) |*breaking| {
            var cloned_breaking = try breaking.clone(self.allocator);
            errdefer cloned_breaking.deinit(self.allocator);
            try output.append(self.allocator, cloned_breaking);
        }

        if (continue_analysis) {
            self.initial_state.deinit();
            self.state.deinit();
            self.initial_state = next_initial;
            self.state = next_state;
            self.store_operations.clearRetainingCapacity();
            if (self.breaking_item) |*breaking| breaking.deinit(self.allocator);
            self.breaking_item = null;
        }
        return output;
    }

    fn feedItem(
        self: *CommonSubexpressionEliminator,
        item: *const AssemblyItem,
        copy_item: bool,
    ) CSEError!void {
        const operation = try self.state.feedItem(item, copy_item);
        if (operation.isValid()) try self.store_operations.append(self.allocator, operation);
    }

    fn optimizeBreakingItem(self: *CommonSubexpressionEliminator) CSEError!void {
        const breaking = if (self.breaking_item) |*item| item else return;
        const classes = self.state.expressionClasses();
        const debug_data = breaking.debug_data;
        if (breaking.eqlInstruction(.JUMPI)) {
            const jump_type = breaking.jump_type;
            const condition = try self.state.stackElement(self.state.stack_height - 1, debug_data);
            if (try classes.knownNonZero(condition)) {
                var item = AssemblyItem.initInstruction(.SWAP1, debug_data);
                try self.feedItem(&item, true);
                item = AssemblyItem.initInstruction(.POP, debug_data);
                try self.feedItem(&item, true);
                breaking.deinit(self.allocator);
                breaking.* = AssemblyItem.initInstruction(.JUMP, debug_data);
                breaking.jump_type = jump_type;
            } else if (try classes.knownZero(condition)) {
                const pop = AssemblyItem.initInstruction(.POP, debug_data);
                try self.feedItem(&pop, true);
                try self.feedItem(&pop, true);
                breaking.deinit(self.allocator);
                self.breaking_item = null;
            }
        } else if (breaking.eqlInstruction(.RETURN)) {
            const size = try self.state.stackElement(self.state.stack_height - 1, debug_data);
            if (try classes.knownZero(size)) {
                const pop = AssemblyItem.initInstruction(.POP, debug_data);
                try self.feedItem(&pop, true);
                try self.feedItem(&pop, true);
                breaking.deinit(self.allocator);
                breaking.* = AssemblyItem.initInstruction(.STOP, debug_data);
            }
        }
    }
};

const NeededBy = struct { dependency: Id, result: Id };

const ClassPositions = struct {
    const Entry = struct { id: Id, positions: PositionSet };
    entries: std.ArrayList(Entry) = .empty,

    fn deinit(self: *ClassPositions, allocator: std.mem.Allocator) void {
        for (self.entries.items) |*entry| entry.positions.deinit(allocator);
        self.entries.deinit(allocator);
        self.* = undefined;
    }

    fn search(self: *const ClassPositions, id: Id) struct { index: usize, found: bool } {
        var lower: usize = 0;
        var upper = self.entries.items.len;
        while (lower < upper) {
            const middle = lower + (upper - lower) / 2;
            if (self.entries.items[middle].id < id) lower = middle + 1 else upper = middle;
        }
        return .{
            .index = lower,
            .found = lower < self.entries.items.len and self.entries.items[lower].id == id,
        };
    }

    fn contains(self: *const ClassPositions, id: Id) bool {
        return self.search(id).found;
    }

    fn get(self: *const ClassPositions, id: Id) ?*const PositionSet {
        const found = self.search(id);
        return if (found.found) &self.entries.items[found.index].positions else null;
    }

    fn getPtr(self: *ClassPositions, id: Id) ?*PositionSet {
        const found = self.search(id);
        return if (found.found) &self.entries.items[found.index].positions else null;
    }

    fn getOrPut(self: *ClassPositions, allocator: std.mem.Allocator, id: Id) !*PositionSet {
        const found = self.search(id);
        if (!found.found) try self.entries.insert(allocator, found.index, .{ .id = id, .positions = .{} });
        return &self.entries.items[found.index].positions;
    }
};

const StoreGroup = struct {
    target: StoreOperation.Target,
    slot: Id,
    operations: std.ArrayList(StoreOperation) = .empty,

    fn deinit(self: *StoreGroup, allocator: std.mem.Allocator) void {
        self.operations.deinit(allocator);
        self.* = undefined;
    }
};

const SequencedExpression = struct { sequence_number: u32, id: Id };

pub const CSECodeGenerator = struct {
    allocator: std.mem.Allocator,
    generated_items: std.ArrayList(AssemblyItem) = .empty,
    stack_height: i32 = 0,
    needed_by: std.ArrayList(NeededBy) = .empty,
    stack: StackMap = .{},
    class_positions: ClassPositions = .{},
    expression_classes: *ExpressionClasses,
    store_groups: std.ArrayList(StoreGroup) = .empty,
    final_classes: IdSet = .{},
    target_stack: StackMap = .{},
    evm_version: EVMVersion,

    pub fn init(
        allocator: std.mem.Allocator,
        expression_classes: *ExpressionClasses,
        store_operations: []const StoreOperation,
        evm_version: EVMVersion,
    ) std.mem.Allocator.Error!CSECodeGenerator {
        var result: CSECodeGenerator = .{
            .allocator = allocator,
            .expression_classes = expression_classes,
            .evm_version = evm_version,
        };
        errdefer result.deinit();
        for (store_operations) |operation| try result.addStoreOperation(operation);
        return result;
    }

    pub fn deinit(self: *CSECodeGenerator) void {
        deinitItems(self.allocator, &self.generated_items);
        self.needed_by.deinit(self.allocator);
        self.stack.deinit(self.allocator);
        self.class_positions.deinit(self.allocator);
        for (self.store_groups.items) |*group| group.deinit(self.allocator);
        self.store_groups.deinit(self.allocator);
        self.final_classes.deinit(self.allocator);
        self.target_stack.deinit(self.allocator);
        self.* = undefined;
    }

    fn addStoreOperation(self: *CSECodeGenerator, operation: StoreOperation) !void {
        var index: usize = 0;
        while (index < self.store_groups.items.len) : (index += 1) {
            const group = &self.store_groups.items[index];
            const group_target = @intFromEnum(group.target);
            const operation_target = @intFromEnum(operation.target);
            if (group_target > operation_target or
                (group_target == operation_target and group.slot >= operation.slot)) break;
        }
        if (index == self.store_groups.items.len or
            self.store_groups.items[index].target != operation.target or
            self.store_groups.items[index].slot != operation.slot)
        {
            try self.store_groups.insert(self.allocator, index, .{
                .target = operation.target,
                .slot = operation.slot,
            });
        }
        try self.store_groups.items[index].operations.append(self.allocator, operation);
    }

    pub fn generateCode(
        self: *CSECodeGenerator,
        initial_sequence_number: u32,
        initial_stack_height: i32,
        initial_stack: *const StackMap,
        target_stack: *const StackMap,
    ) CSEError!std.ArrayList(AssemblyItem) {
        self.stack_height = initial_stack_height;
        self.stack = try initial_stack.clone(self.allocator);
        self.target_stack = try target_stack.clone(self.allocator);
        for (self.stack.items()) |entry|
            _ = try (try self.class_positions.getOrPut(self.allocator, entry.value)).insert(
                self.allocator,
                entry.key,
            );

        for (self.store_groups.items) |group|
            try self.addDependencies(group.operations.items[group.operations.items.len - 1].expression);
        for (self.target_stack.items()) |entry| {
            _ = try self.final_classes.insert(self.allocator, entry.value);
            try self.addDependencies(entry.value);
        }

        var sequenced: std.ArrayList(SequencedExpression) = .empty;
        defer sequenced.deinit(self.allocator);
        for (self.needed_by.items) |relation| {
            for ([_]Id{ relation.dependency, relation.result }) |id| {
                const expression = try self.expression_classes.representative(id);
                if (expression.sequence_number == 0) continue;
                if (expression.sequence_number < initial_sequence_number) return error.StackTooDeep;
                try insertSequenced(self.allocator, &sequenced, .{
                    .sequence_number = expression.sequence_number,
                    .id = id,
                });
            }
        }
        for (sequenced.items) |entry|
            if (!self.class_positions.contains(entry.id))
                try self.generateClassElement(entry.id, true);

        for (self.target_stack.items()) |target| {
            if (self.stack.get(target.key)) |existing| if (existing.* == target.value) continue;
            try self.generateClassElement(target.value, false);
            const positions = self.class_positions.get(target.value) orelse return error.ElementNotPresent;
            if (positions.isEmpty()) return error.ElementAlreadyRemoved;
            if (positions.contains(target.key)) continue;
            const expression = try self.expression_classes.representative(target.value);
            const position = try self.classElementPosition(target.value);
            if (position < target.key) {
                try self.appendDup(position, expression.item.debug_data);
            } else {
                try self.appendOrRemoveSwap(position, expression.item.debug_data);
            }
            try self.appendOrRemoveSwap(target.key, expression.item.debug_data);
        }

        while (try self.removeStackTopIfPossible()) {}

        const final_height = if (!self.target_stack.isEmpty())
            self.target_stack.items()[self.target_stack.len() - 1].key
        else if (!initial_stack.isEmpty())
            initial_stack.items()[0].key - 1
        else
            initial_stack_height;
        if (final_height != self.stack_height) return error.IncorrectFinalStackHeight;

        const result = self.generated_items;
        self.generated_items = .empty;
        return result;
    }

    fn addDependencies(self: *CSECodeGenerator, id: Id) CSEError!void {
        if (self.class_positions.contains(id)) return;
        for (self.needed_by.items) |relation| if (relation.dependency == id) return;
        // Upstream copies the representative here. Recursive dependency
        // discovery can intern new expressions and grow the representative
        // array, so retaining a pointer to its element would be invalid.
        // The item's allocation and argument slice are independently stable.
        const expression = (try self.expression_classes.representative(id)).*;
        if (expression.item.item_type == .UndefinedItem) return error.ItemNotAvailable;
        for (expression.arguments) |argument| {
            try self.addDependencies(argument);
            try self.needed_by.append(self.allocator, .{ .dependency = argument, .result = id });
        }

        const instruction = if (expression.item.item_type == .Operation)
            expression.item.instruction_value.?
        else
            return;
        if (instruction != .SLOAD and instruction != .MLOAD and instruction != .KECCAK256) return;

        const target: StoreOperation.Target = if (instruction == .SLOAD) .Storage else .Memory;
        const slot_to_load = expression.arguments[0];
        for (self.store_groups.items) |group| {
            if (group.target != target) continue;
            const operations = group.operations.items;
            if (operations[0].sequence_number > expression.sequence_number) continue;
            var independent = false;
            switch (instruction) {
                .SLOAD => independent = try self.expression_classes.knownToBeDifferent(group.slot, slot_to_load),
                .MLOAD => independent = try self.expression_classes.knownToBeDifferentBy32(group.slot, slot_to_load),
                .KECCAK256 => {
                    const offset = try self.expression_classes.makeOperation(
                        .SUB,
                        &.{ group.slot, slot_to_load },
                        expression.item.debug_data,
                    );
                    const offset_value = self.expression_classes.knownConstantValue(offset);
                    const length = self.expression_classes.knownConstantValue(expression.arguments[1]);
                    if (length != null and length.? == 0) {
                        independent = true;
                    } else if (offset_value) |value| {
                        const signed: i256 = @bitCast(value);
                        if (signed <= -32) independent = true else if (length != null and signed >= 0 and value >= length.?)
                            independent = true;
                    }
                },
                else => unreachable,
            }
            if (independent) continue;
            var latest = operations[0].expression;
            for (operations[1..]) |operation| {
                if (operation.sequence_number < expression.sequence_number)
                    latest = operation.expression;
            }
            try self.addDependencies(latest);
            try self.needed_by.append(self.allocator, .{ .dependency = latest, .result = id });
        }
    }

    fn generateClassElement(
        self: *CSECodeGenerator,
        id: Id,
        allow_sequenced: bool,
    ) CSEError!void {
        for (self.class_positions.entries.items) |entry|
            for (entry.positions.map.items()) |position|
                if (position.key > self.stack_height) return error.InvalidStackAccess;
        _ = try self.removeStackTopIfPossible();

        if (self.class_positions.get(id)) |positions| {
            if (positions.isEmpty()) return error.ElementAlreadyRemoved;
            return;
        }
        const expression = try self.expression_classes.representative(id);
        if (!allow_sequenced and expression.sequence_number != 0) return error.SequenceConstraint;
        if (expression.item.item_type == .UndefinedItem) return error.ItemNotAvailable;
        const arguments = expression.arguments;
        var reverse_index = arguments.len;
        while (reverse_index != 0) {
            reverse_index -= 1;
            try self.generateClassElement(arguments[reverse_index], false);
        }

        const debug_data = expression.item.debug_data;
        if (arguments.len == 1) {
            const position = try self.classElementPosition(arguments[0]);
            if (try self.canBeRemoved(arguments[0], id, null))
                try self.appendOrRemoveSwap(position, debug_data)
            else
                try self.appendDup(position, debug_data);
        } else if (arguments.len == 2) {
            if (try self.canBeRemoved(arguments[1], id, null)) {
                try self.appendOrRemoveSwap(try self.classElementPosition(arguments[1]), debug_data);
                if (arguments[0] == arguments[1]) {
                    try self.appendDup(self.stack_height, debug_data);
                } else if (try self.canBeRemoved(arguments[0], id, null)) {
                    try self.appendOrRemoveSwap(self.stack_height - 1, debug_data);
                    try self.appendOrRemoveSwap(try self.classElementPosition(arguments[0]), debug_data);
                } else {
                    try self.appendDup(try self.classElementPosition(arguments[0]), debug_data);
                }
            } else {
                if (arguments[0] == arguments[1]) {
                    try self.appendDup(try self.classElementPosition(arguments[0]), debug_data);
                    try self.appendDup(self.stack_height, debug_data);
                } else if (try self.canBeRemoved(arguments[0], id, null)) {
                    try self.appendOrRemoveSwap(try self.classElementPosition(arguments[0]), debug_data);
                    try self.appendDup(try self.classElementPosition(arguments[1]), debug_data);
                    try self.appendOrRemoveSwap(self.stack_height - 1, debug_data);
                } else {
                    try self.appendDup(try self.classElementPosition(arguments[1]), debug_data);
                    try self.appendDup(try self.classElementPosition(arguments[0]), debug_data);
                }
            }
        } else if (arguments.len > 2) return error.TooManyArguments;

        for (arguments, 0..) |argument, index| {
            const stack_value = self.stack.get(self.stack_height - @as(i32, @intCast(index))) orelse
                return error.ElementNotPresent;
            if (stack_value.* != argument) return error.ElementNotPresent;
        }

        while (SemanticInformation.isCommutativeOperation(expression.item) and
            self.generated_items.items.len != 0 and
            self.generated_items.items[self.generated_items.items.len - 1].eqlInstruction(.SWAP1))
            try self.appendOrRemoveSwap(self.stack_height - 1, debug_data);

        for (arguments, 0..) |_, index| {
            const height = self.stack_height - @as(i32, @intCast(index));
            const stack_id = self.stack.get(height).?.*;
            _ = self.class_positions.getPtr(stack_id).?.remove(height);
            _ = self.stack.remove(height);
        }
        try self.appendItem(expression.item);
        if (expression.item.item_type != .Operation or
            InstructionModule.instructionInfo(expression.item.instruction_value.?, self.evm_version).ret == 1)
        {
            _ = try self.stack.fetchPut(self.allocator, self.stack_height, id);
            _ = try (try self.class_positions.getOrPut(self.allocator, id)).insert(
                self.allocator,
                self.stack_height,
            );
        } else {
            if (InstructionModule.instructionInfo(expression.item.instruction_value.?, self.evm_version).ret != 0)
                return error.InvalidNumberOfReturnValues;
            _ = try self.class_positions.getOrPut(self.allocator, id);
        }
    }

    fn classElementPosition(self: *const CSECodeGenerator, id: Id) CSEError!i32 {
        const positions = self.class_positions.get(id) orelse return error.ElementNotPresent;
        if (positions.isEmpty()) return error.ElementNotPresent;
        return positions.at(positions.len() - 1);
    }

    fn canBeRemoved(
        self: *CSECodeGenerator,
        element: Id,
        result: Id,
        from_position: ?i32,
    ) CSEError!bool {
        const position = from_position orelse try self.classElementPosition(element);
        const positions = self.class_positions.get(element) orelse return error.ElementNotPresent;
        const have_copy = positions.len() > 1;
        if (self.final_classes.contains(element)) {
            const target = self.target_stack.get(position);
            return have_copy and (target == null or target.?.* != element);
        }
        if (!have_copy) {
            for (self.needed_by.items) |relation| {
                if (relation.dependency != element) continue;
                if (relation.result != result and !self.class_positions.contains(relation.result)) return false;
            }
        }
        return true;
    }

    fn removeStackTopIfPossible(self: *CSECodeGenerator) CSEError!bool {
        if (self.stack.isEmpty()) return false;
        const top = self.stack.get(self.stack_height) orelse return error.ElementNotPresent;
        if (!try self.canBeRemoved(top.*, ExpressionClassesModule.invalid_id, self.stack_height)) return false;
        _ = self.class_positions.getPtr(top.*).?.remove(self.stack_height);
        _ = self.stack.remove(self.stack_height);
        const pop = AssemblyItem.initInstruction(.POP, .{});
        try self.appendItem(&pop);
        return true;
    }

    fn appendDup(self: *CSECodeGenerator, from_position: i32, debug_data: DebugData) CSEError!void {
        const instruction_number = 1 + self.stack_height - from_position;
        if (instruction_number > @as(i32, @intCast(self.evm_version.reachableStackDepth())))
            return error.StackTooDeep;
        if (instruction_number < 1) return error.InvalidStackAccess;
        const item = AssemblyItem.initInstruction(
            InstructionModule.dupInstruction(@intCast(instruction_number)),
            debug_data,
        );
        const value = (self.stack.get(from_position) orelse return error.ElementNotPresent).*;
        try self.appendItem(&item);
        _ = try self.stack.fetchPut(self.allocator, self.stack_height, value);
        _ = try (try self.class_positions.getOrPut(self.allocator, value)).insert(
            self.allocator,
            self.stack_height,
        );
    }

    fn appendOrRemoveSwap(
        self: *CSECodeGenerator,
        from_position: i32,
        debug_data: DebugData,
    ) CSEError!void {
        if (from_position == self.stack_height) return;
        const instruction_number = self.stack_height - from_position;
        if (instruction_number > @as(i32, @intCast(self.evm_version.reachableStackDepth())))
            return error.StackTooDeep;
        if (instruction_number < 1) return error.InvalidStackAccess;
        const item = AssemblyItem.initInstruction(
            InstructionModule.swapInstruction(@intCast(instruction_number)),
            debug_data,
        );
        try self.appendItem(&item);

        const top = self.stack.get(self.stack_height) orelse return error.ElementNotPresent;
        const other = self.stack.get(from_position) orelse return error.ElementNotPresent;
        const top_id = top.*;
        const other_id = other.*;
        if (top_id != other_id) {
            _ = self.class_positions.getPtr(top_id).?.remove(self.stack_height);
            _ = try self.class_positions.getPtr(top_id).?.insert(self.allocator, from_position);
            _ = self.class_positions.getPtr(other_id).?.remove(from_position);
            _ = try self.class_positions.getPtr(other_id).?.insert(self.allocator, self.stack_height);
            _ = try self.stack.fetchPut(self.allocator, self.stack_height, other_id);
            _ = try self.stack.fetchPut(self.allocator, from_position, top_id);
        }

        if (self.generated_items.items.len >= 2) {
            const last = &self.generated_items.items[self.generated_items.items.len - 1];
            const previous = &self.generated_items.items[self.generated_items.items.len - 2];
            if (SemanticInformation.isSwapItem(last) and previous.eql(last)) {
                last.deinit(self.allocator);
                previous.deinit(self.allocator);
                self.generated_items.items.len -= 2;
            }
        }
    }

    fn appendItem(self: *CSECodeGenerator, item: *const AssemblyItem) std.mem.Allocator.Error!void {
        var cloned_item = try item.clone(self.allocator);
        errdefer cloned_item.deinit(self.allocator);
        try self.generated_items.append(self.allocator, cloned_item);
        self.stack_height += @intCast(item.deposit());
    }
};

fn insertSequenced(
    allocator: std.mem.Allocator,
    list: *std.ArrayList(SequencedExpression),
    value: SequencedExpression,
) std.mem.Allocator.Error!void {
    var index: usize = 0;
    while (index < list.items.len and (list.items[index].sequence_number < value.sequence_number or
        (list.items[index].sequence_number == value.sequence_number and list.items[index].id < value.id))) : (index += 1)
    {}
    if (index < list.items.len and list.items[index].sequence_number == value.sequence_number and
        list.items[index].id == value.id) return;
    try list.insert(allocator, index, value);
}

fn deinitItems(allocator: std.mem.Allocator, items: *std.ArrayList(AssemblyItem)) void {
    for (items.items) |*item| item.deinit(allocator);
    items.deinit(allocator);
    items.* = .empty;
}

test "CSE eliminates duplicate constants and folds arithmetic" {
    var state = try KnownState.init(std.testing.allocator);
    defer state.deinit();
    var cse = try CommonSubexpressionEliminator.init(
        std.testing.allocator,
        &state,
        EVMVersion.init(.London),
    );
    defer cse.deinit();
    const I = AssemblyItem;
    const input = [_]I{
        I.initPush(7, .{}),
        I.initPush(7, .{}),
        I.initInstruction(.ADD, .{}),
    };
    try std.testing.expectEqual(input.len, try cse.feedItems(&input, false));
    var output = try cse.getOptimizedItems();
    defer deinitItems(std.testing.allocator, &output);
    try std.testing.expect(output.items.len < input.len);
    try std.testing.expect(output.items[0].item_type == .Push);
    try std.testing.expectEqual(@as(u256, 14), output.items[0].data_value);
}

test "assembly CSE final output survives every analysis owner and allocation failure" {
    const Stats = struct { bytes: usize = 0, calls: usize = 0 };
    const Check = struct {
        fn output(
            allocator: std.mem.Allocator,
            input: []const AssemblyItem,
            version: EVMVersion,
            final: bool,
            separate_state: bool,
            clone_stats: ?*Stats,
        ) !std.ArrayList(AssemblyItem) {
            var owned_input: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent cleanup releases the container and owned payloads on failure
            defer deinitItems(allocator, &owned_input);
            try owned_input.ensureTotalCapacity(allocator, input.len);
            for (input) |*item| owned_input.appendAssumeCapacity(try item.clone(allocator));
            var arena = std.heap.ArenaAllocator.init(allocator);
            defer arena.deinit();
            var state = try KnownState.init(if (separate_state) arena.allocator() else allocator);
            defer state.deinit();
            var cse = try CommonSubexpressionEliminator.init(allocator, &state, version);
            const consumed = cse.feedItems(owned_input.items, false) catch |err| {
                cse.deinit();
                return err;
            };
            if (consumed != input.len) {
                cse.deinit();
                return error.UnexpectedChunkBoundary;
            }
            if (final) return cse.finish();
            defer cse.deinit();
            var result = try cse.getOptimizedItems();
            errdefer deinitItems(allocator, &result);
            if (clone_stats) |stats| {
                // A borrowed view selects a counting allocator only for this
                // temporary clone. No copied allocator context escapes.
                var counter = std.testing.FailingAllocator.init(cse.state.allocator, .{});
                var view = cse.state;
                view.allocator = counter.allocator();
                {
                    var copy = try view.clone();
                    defer copy.deinit();
                    try std.testing.expect(cse.state.eql(&copy));
                }
                try std.testing.expectEqual(counter.allocated_bytes, counter.freed_bytes);
                stats.* = .{ .bytes = counter.allocated_bytes, .calls = counter.allocations };
            }
            return result;
        }

        fn run(
            backing: std.mem.Allocator,
            input: []const AssemblyItem,
            version: EVMVersion,
            final: bool,
            separate_state: bool,
            expected: []const AssemblyItem,
            stats: ?*Stats,
        ) !void {
            var counter = std.testing.FailingAllocator.init(backing, .{});
            defer if (counter.allocated_bytes != counter.freed_bytes)
                @panic("CSE result or analysis owner leaked");
            var result = try output(counter.allocator(), input, version, final, separate_state, null);
            defer deinitItems(counter.allocator(), &result);
            // Input copies, the CSE object, shared expression classes, and the
            // optional state arena have all died before these values are read.
            try std.testing.expectEqualDeep(expected, result.items);
            if (stats) |value| value.* = .{ .bytes = counter.allocated_bytes, .calls = counter.allocations };
        }
    };
    const allocator = std.testing.allocator;
    const I = AssemblyItem;
    var payload = try I.initVerbatim(allocator, &.{ 0x60, 0x2a }, 0, 1);
    defer payload.deinit(allocator);
    const cases = [_][]const I{
        &.{},
        &.{ I.initPush(7, .{}), I.initPush(7, .{}), I.initInstruction(.ADD, .{}) },
        &.{ I.initPush(0, .{}), I.initType(.PushTag, 9, .{}), I.initInstruction(.JUMPI, .{}) },
        &.{ I.initPush(1, .{}), I.initType(.PushTag, 9, .{}), I.initInstruction(.JUMPI, .{}) },
        &.{ I.initPush(0, .{}), I.initInstruction(.CALLDATALOAD, .{}), I.initType(.PushTag, 9, .{}), I.initInstruction(.JUMPI, .{}) },
        &.{ I.initPush(0, .{}), I.initPush(0, .{}), I.initInstruction(.RETURN, .{}) },
        &.{ I.initPush(32, .{}), I.initPush(0, .{}), I.initInstruction(.RETURN, .{}) },
        &.{ I.initInstruction(.DUP1, .{}), I.initInstruction(.DUP1, .{}), I.initInstruction(.ADD, .{}) },
        &.{I.initType(.Tag, 1, .{})},
        &.{I.initInstruction(.MSIZE, .{})},
        &.{payload},
        &.{
            I.initPush(17, .{}), I.initPush(0, .{}),             I.initInstruction(.MSTORE, .{}),
            I.initPush(32, .{}), I.initPush(0, .{}),             I.initInstruction(.KECCAK256, .{}),
            I.initPush(11, .{}), I.initPush(1, .{}),             I.initInstruction(.SSTORE, .{}),
            I.initPush(1, .{}),  I.initInstruction(.SLOAD, .{}),
        },
    };
    var unused: Stats = .{};
    var baseline: Stats = .{};
    var final_output: Stats = .{};
    for (cases, 0..) |input, case_index| {
        // A non-owning descriptor copy adds distinct annotations. The original
        // fixture remains the sole owner of its verbatim payload.
        const annotated = try allocator.dupe(I, input);
        defer allocator.free(annotated);
        for (annotated, 0..) |*item, index| {
            item.debug_data = .{
                .native_location = .{ .start = @intCast(index), .end = @intCast(index + 1), .source_name = "native.yul" },
                .origin_location = .{ .start = @intCast(case_index), .end = @intCast(case_index + 1), .source_name = "origin.sol" },
                .ast_id = @intCast(100 + index),
            };
            item.modifier_depth = index + 1;
        }
        for ([_]EVMVersion{ .init(.London), .init(.Shanghai) }) |version| {
            var clone_stats: Stats = .{};
            var expected = try Check.output(allocator, annotated, version, false, false, &clone_stats);
            defer deinitItems(allocator, &expected);
            unused.bytes += clone_stats.bytes;
            unused.calls += clone_stats.calls;
            var reference_stats: Stats = .{};
            var finish_stats: Stats = .{};
            try Check.run(allocator, annotated, version, false, false, expected.items, &reference_stats);
            try Check.run(allocator, annotated, version, true, false, expected.items, &finish_stats);
            baseline.bytes += reference_stats.bytes;
            baseline.calls += reference_stats.calls;
            final_output.bytes += finish_stats.bytes;
            final_output.calls += finish_stats.calls;
            for ([_]bool{ false, true }) |final| for ([_]bool{ false, true }) |separate_state|
                try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ annotated, version, final, separate_state, expected.items, null });
        }
    }
    try std.testing.expect(unused.bytes > 0 and unused.calls > 0);
    try std.testing.expectEqual(unused.bytes, baseline.bytes - final_output.bytes);
    try std.testing.expectEqual(unused.calls, baseline.calls - final_output.calls);
    std.debug.print("CSE fixtures: continuation clone {d} bytes / {d} allocations; ordinary output {d} / {d}; final output {d} / {d}\n", .{
        unused.bytes, unused.calls, baseline.bytes, baseline.calls, final_output.bytes, final_output.calls,
    });
}

test "assembly CSE generation preserves input maps through owner destruction and allocation failure" {
    const Shape = enum { empty, constant, unchanged, duplicate, drop, swap, zero, unavailable, invalid, deep };
    const Stats = struct { bytes: usize = 0, calls: usize = 0, clone_bytes: usize = 0, clone_calls: usize = 0 };
    const Check = struct {
        fn debug(value: i64) DebugData {
            return .{
                .native_location = .{ .start = 1, .end = 4, .source_name = "native.yul" },
                .origin_location = .{ .start = 5, .end = 9, .source_name = "origin.sol" },
                .ast_id = value,
            };
        }

        fn output(allocator: std.mem.Allocator, shape: Shape, version: EVMVersion, separate_maps: bool, stats: ?*Stats) !std.ArrayList(AssemblyItem) {
            var classes = ExpressionClasses.init(allocator);
            defer classes.deinit();
            var generator = try CSECodeGenerator.init(allocator, &classes, &.{}, version);
            defer generator.deinit();
            // Maps and their optional arena die before the generator, on every
            // exit. Only generated items may outlive all these owners.
            var arena = std.heap.ArenaAllocator.init(allocator);
            defer arena.deinit();
            const map_allocator = if (separate_maps) arena.allocator() else allocator;
            var initial: StackMap = .{};
            defer initial.deinit(map_allocator);
            var target: StackMap = .{};
            defer target.deinit(map_allocator);
            const seven = try classes.makeConstant(7, debug(7));
            const eight = try classes.makeConstant(8, debug(8));
            switch (shape) {
                .empty => {},
                .constant => _ = try target.insert(map_allocator, 1, seven),
                .unchanged, .duplicate, .drop => {
                    _ = try initial.insert(map_allocator, 1, seven);
                    if (shape != .drop) _ = try target.insert(map_allocator, 1, seven);
                    if (shape == .duplicate) _ = try target.insert(map_allocator, 2, seven);
                },
                .swap => {
                    _ = try initial.insert(map_allocator, 1, seven);
                    _ = try initial.insert(map_allocator, 2, eight);
                    _ = try target.insert(map_allocator, 1, eight);
                    _ = try target.insert(map_allocator, 2, seven);
                },
                .zero => _ = try target.insert(map_allocator, 1, try classes.makeConstant(0, debug(0))),
                .unavailable => _ = try target.insert(map_allocator, 1, try classes.newClass(debug(10))),
                .invalid => _ = try target.insert(map_allocator, 1, ExpressionClassesModule.invalid_id),
                .deep => {
                    for (1..18) |position| {
                        const id = try classes.newClass(debug(@intCast(position)));
                        _ = try initial.insert(map_allocator, @intCast(position), id);
                        _ = try target.insert(map_allocator, @intCast(position), id);
                    }
                    _ = try target.insert(map_allocator, 18, initial.items()[0].value);
                },
            }
            var initial_snapshot: [18]StackMap.Entry = undefined;
            var target_snapshot: [18]StackMap.Entry = undefined;
            @memcpy(initial_snapshot[0..initial.len()], initial.items());
            @memcpy(target_snapshot[0..target.len()], target.items());
            const initial_view = initial.entries;
            const target_view = target.entries;
            if (stats) |value| {
                var counter = std.testing.FailingAllocator.init(allocator, .{});
                {
                    var clone = try target.clone(counter.allocator());
                    defer clone.deinit(counter.allocator());
                    try std.testing.expectEqualDeep(target.items(), clone.items());
                }
                try std.testing.expectEqual(counter.allocated_bytes, counter.freed_bytes);
                value.clone_bytes = counter.allocated_bytes;
                value.clone_calls = counter.allocations;
            }
            const result = generator.generateCode(1, @intCast(initial.len()), &initial, &target);
            errdefer if (result) |items| {
                var owned = items;
                deinitItems(allocator, &owned);
            } else |_| {};
            try std.testing.expectEqual(initial_view.items.ptr, initial.entries.items.ptr);
            try std.testing.expectEqual(target_view.items.ptr, target.entries.items.ptr);
            try std.testing.expectEqual(initial_view.capacity, initial.entries.capacity);
            try std.testing.expectEqual(target_view.capacity, target.entries.capacity);
            try std.testing.expectEqualDeep(initial_snapshot[0..initial_view.items.len], initial.items());
            try std.testing.expectEqualDeep(target_snapshot[0..target_view.items.len], target.items());
            if (result) |items| {
                try std.testing.expect(shape != .unavailable and shape != .invalid and shape != .deep);
                return items;
            } else |err| {
                if (err == error.OutOfMemory) return err;
                const expected: CSEError = switch (shape) {
                    .unavailable => error.ItemNotAvailable,
                    .invalid => error.InvalidExpressionId,
                    .deep => error.StackTooDeep,
                    else => return err,
                };
                try std.testing.expectEqual(expected, err);
                return .empty;
            }
        }

        fn run(backing: std.mem.Allocator, shape: Shape, version: EVMVersion, separate_maps: bool, expected: []const AssemblyItem, stats: ?*Stats) !void {
            var counter = std.testing.FailingAllocator.init(backing, .{});
            defer if (counter.allocated_bytes != counter.freed_bytes) @panic("CSE generator or output leaked");
            var items = try output(counter.allocator(), shape, version, separate_maps, stats);
            defer deinitItems(counter.allocator(), &items);
            try std.testing.expectEqualDeep(expected, items.items);
            if (stats) |value| {
                value.bytes = counter.allocated_bytes;
                value.calls = counter.allocations;
            }
        }
    };
    const allocator = std.testing.allocator;
    const I = AssemblyItem;
    var total: Stats = .{};
    for (std.enums.values(Shape)) |shape| {
        const expected: []const I = switch (shape) {
            .constant => &.{I.initPush(7, Check.debug(7))},
            .duplicate => &.{I.initInstruction(.DUP1, Check.debug(7))},
            .drop => &.{I.initInstruction(.POP, .{})},
            .swap => &.{I.initInstruction(.SWAP1, Check.debug(8))},
            .zero => &.{I.initPush(0, Check.debug(0))},
            else => &.{},
        };
        for ([_]EVMVersion{ .init(.London), .init(.Shanghai) }) |version| {
            var stats: Stats = .{};
            try Check.run(allocator, shape, version, false, expected, &stats);
            total.bytes += stats.bytes;
            total.calls += stats.calls;
            total.clone_bytes += stats.clone_bytes;
            total.clone_calls += stats.clone_calls;
            for ([_]bool{ false, true }) |separate_maps|
                try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ shape, version, separate_maps, expected, null });
        }
    }
    std.debug.print("CSE target fixtures: clone {d} bytes / {d} allocations; whole helper {d} / {d}\n", .{
        total.clone_bytes, total.clone_calls, total.bytes, total.calls,
    });
}

test "assembly CSE preserves reusable continuation states across blocks" {
    const allocator = std.testing.allocator;
    var state = try KnownState.init(allocator);
    defer state.deinit();
    var cse = try CommonSubexpressionEliminator.init(allocator, &state, .current());
    defer cse.deinit();
    const I = AssemblyItem;
    const first = [_]I{ I.initPush(7, .{}), I.initInstruction(.MSIZE, .{}) };
    try std.testing.expectEqual(first.len, try cse.feedItems(&first, false));
    var first_output = try cse.getOptimizedItems();
    defer deinitItems(allocator, &first_output);
    try std.testing.expect(cse.initial_state.eql(&cse.state));
    try std.testing.expect(cse.initial_state.stack_elements.items().ptr != cse.state.stack_elements.items().ptr);
    const height = cse.initial_state.stack_height;
    const next = [_]I{I.initInstruction(.DUP1, .{})};
    try std.testing.expectEqual(next.len, try cse.feedItems(&next, false));
    try std.testing.expectEqual(height, cse.initial_state.stack_height);
    try std.testing.expectEqual(height + 1, cse.state.stack_height);
    var next_output = try cse.getOptimizedItems();
    defer deinitItems(allocator, &next_output);
    try std.testing.expect(cse.initial_state.eql(&cse.state));
    try std.testing.expect(cse.breaking_item == null);
    try std.testing.expectEqual(@as(usize, 0), cse.store_operations.items.len);
}

test "CSE specializes constant conditional breaking items" {
    var state = try KnownState.init(std.testing.allocator);
    defer state.deinit();
    var cse = try CommonSubexpressionEliminator.init(
        std.testing.allocator,
        &state,
        EVMVersion.init(.London),
    );
    defer cse.deinit();
    const I = AssemblyItem;
    const input = [_]I{
        I.initPush(0, .{}),
        I.initType(.PushTag, 1, .{}),
        I.initInstruction(.JUMPI, .{}),
    };
    try std.testing.expectEqual(input.len, try cse.feedItems(&input, false));
    var output = try cse.getOptimizedItems();
    defer deinitItems(std.testing.allocator, &output);
    for (output.items) |item| try std.testing.expect(!item.eqlInstruction(.JUMPI));
}

test "CSE dependency discovery survives expression-table growth" {
    var classes = ExpressionClasses.init(std.testing.allocator);
    defer classes.deinit();

    const zero = try classes.makeConstant(0, .{});
    const thirty_two = try classes.makeConstant(32, .{});
    const start = try classes.makeOperation(.CALLDATALOAD, &.{zero}, .{});
    const length = try classes.makeConstant(64, .{});
    const hash = try classes.makeOperation(.KECCAK256, &.{ start, length }, .{});
    const root = try classes.makeOperation(.ISZERO, &.{hash}, .{});
    const store_slot = try classes.makeOperation(.CALLDATALOAD, &.{thirty_two}, .{});
    const store_value = try classes.makeConstant(1, .{});

    classes.representatives.shrinkAndFree(
        std.testing.allocator,
        classes.representatives.items.len,
    );
    const representatives_before = classes.size();

    var generator = try CSECodeGenerator.init(
        std.testing.allocator,
        &classes,
        &.{.{
            .target = .Memory,
            .slot = store_slot,
            .sequence_number = 0,
            .expression = store_value,
        }},
        EVMVersion.init(.London),
    );
    defer generator.deinit();

    try generator.addDependencies(root);
    try std.testing.expect(classes.size() > representatives_before);
    try std.testing.expect(generator.needed_by.items.len != 0);
}
