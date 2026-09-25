// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Stateful EVM stack, storage, memory, and expression knowledge.

const std = @import("std");
const cxx = @import("cxx_compat");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const Keccak256 = @import("../libsolutil/keccak256.zig");
const AssemblyItemModule = @import("assembly_item.zig");
const ExpressionClassesModule = @import("expression_classes.zig");
const GasMeterModule = @import("gas_meter.zig");
const InstructionModule = @import("instruction.zig");
const SemanticInformation = @import("semantic_information.zig");

const AssemblyItem = AssemblyItemModule.AssemblyItem;
const ExpressionClasses = ExpressionClassesModule.ExpressionClasses;
pub const Id = ExpressionClassesModule.Id;

fn lessI32(left: i32, right: i32) bool {
    return left < right;
}

fn lessId(left: Id, right: Id) bool {
    return left < right;
}

fn lessWord(left: u256, right: u256) bool {
    return left < right;
}

pub const StackMap = cxx.OrderedMap(i32, Id, lessI32);
pub const ContentMap = cxx.OrderedMap(Id, Id, lessId);
pub const TagSet = cxx.OrderedSet(u256, lessWord);

pub const StoreOperation = struct {
    pub const Target = enum(c_int) {
        Invalid,
        Memory,
        Storage,
    };

    target: Target = .Invalid,
    slot: Id = ExpressionClassesModule.invalid_id,
    sequence_number: u32 = std.math.maxInt(u32),
    expression: Id = ExpressionClassesModule.invalid_id,

    pub fn isValid(self: StoreOperation) bool {
        return self.target != .Invalid;
    }
};

const SharedExpressionClasses = struct {
    allocator: std.mem.Allocator,
    references: usize = 1,
    value: ExpressionClasses,

    fn create(allocator: std.mem.Allocator) std.mem.Allocator.Error!*SharedExpressionClasses {
        const shared = try allocator.create(SharedExpressionClasses);
        shared.* = .{
            .allocator = allocator,
            .value = ExpressionClasses.init(allocator),
        };
        return shared;
    }

    fn retain(self: *SharedExpressionClasses) void {
        std.debug.assert(self.references != std.math.maxInt(usize));
        self.references += 1;
    }

    fn release(self: *SharedExpressionClasses) void {
        std.debug.assert(self.references != 0);
        self.references -= 1;
        if (self.references != 0) return;
        const allocator = self.allocator;
        self.value.deinit();
        allocator.destroy(self);
    }
};

const KnownHash = struct {
    memory_words: []Id,
    length: u32,
    value: Id,

    fn deinit(self: *KnownHash, allocator: std.mem.Allocator) void {
        allocator.free(self.memory_words);
        self.* = undefined;
    }
};

const TagUnion = struct {
    id: Id,
    tags: TagSet,

    fn deinit(self: *TagUnion, allocator: std.mem.Allocator) void {
        self.tags.deinit(allocator);
        self.* = undefined;
    }
};

pub const KnownStateError = ExpressionClassesModule.ExpressionError || std.mem.Allocator.Error || error{
    IncompatibleExpressionClasses,
    InvalidStackOperation,
};

pub const KnownState = struct {
    allocator: std.mem.Allocator,
    shared_expressions: *SharedExpressionClasses,
    stack_height: i32 = 0,
    stack_elements: StackMap = .{},
    sequence_number: u32 = 1,
    storage_content: ContentMap = .{},
    memory_content: ContentMap = .{},
    known_keccak256_hashes: std.ArrayList(KnownHash) = .empty,
    tag_unions: std.ArrayList(TagUnion) = .empty,

    pub fn init(allocator: std.mem.Allocator) std.mem.Allocator.Error!KnownState {
        return .{
            .allocator = allocator,
            .shared_expressions = try SharedExpressionClasses.create(allocator),
        };
    }

    pub fn deinit(self: *KnownState) void {
        self.resetKnownKeccak256Hashes();
        self.known_keccak256_hashes.deinit(self.allocator);
        for (self.tag_unions.items) |*tag_union| tag_union.deinit(self.allocator);
        self.tag_unions.deinit(self.allocator);
        self.memory_content.deinit(self.allocator);
        self.storage_content.deinit(self.allocator);
        self.stack_elements.deinit(self.allocator);
        self.shared_expressions.release();
        self.* = undefined;
    }

    pub fn clone(self: *const KnownState) std.mem.Allocator.Error!KnownState {
        self.shared_expressions.retain();
        var result: KnownState = .{
            .allocator = self.allocator,
            .shared_expressions = self.shared_expressions,
            .stack_height = self.stack_height,
            .sequence_number = self.sequence_number,
        };
        errdefer result.deinit();
        result.stack_elements = try self.stack_elements.clone(self.allocator);
        result.storage_content = try self.storage_content.clone(self.allocator);
        result.memory_content = try self.memory_content.clone(self.allocator);
        for (self.known_keccak256_hashes.items) |known_hash| {
            const words = try self.allocator.dupe(Id, known_hash.memory_words);
            errdefer self.allocator.free(words);
            try result.known_keccak256_hashes.append(self.allocator, .{
                .memory_words = words,
                .length = known_hash.length,
                .value = known_hash.value,
            });
        }
        for (self.tag_unions.items) |tag_union| {
            var tags = try tag_union.tags.clone(self.allocator);
            errdefer tags.deinit(self.allocator);
            try result.tag_unions.append(self.allocator, .{ .id = tag_union.id, .tags = tags });
        }
        return result;
    }

    pub fn expressionClasses(self: *const KnownState) *ExpressionClasses {
        return &self.shared_expressions.value;
    }

    pub fn gasState(self: *KnownState) GasMeterModule.GasState {
        return .{ .context = self, .vtable = &gas_state_vtable };
    }

    pub fn feedItem(
        self: *KnownState,
        item: *const AssemblyItem,
        copy_item: bool,
    ) KnownStateError!StoreOperation {
        var operation: StoreOperation = .{};
        switch (item.item_type) {
            .Tag => {},
            .AssignImmutable => {
                const pop = AssemblyItem.initInstruction(.POP, .{});
                _ = try self.feedItem(&pop, copy_item);
                return self.feedItem(&pop, copy_item);
            },
            .VerbatimBytecode => {
                self.sequence_number +%= 2;
                self.resetMemory();
                self.resetKnownKeccak256Hashes();
                self.resetStorage();
                eraseStackAbove(
                    &self.stack_elements,
                    self.stack_height - @as(i32, @intCast(item.arguments())),
                );
                self.stack_height += @intCast(item.deposit());
                for (0..item.returnValues()) |index| {
                    try self.setStackElement(
                        self.stack_height - @as(i32, @intCast(index)),
                        try self.expressionClasses().newClass(item.debug_data),
                    );
                }
            },
            .Operation => operation = try self.feedOperation(item, copy_item),
            else => {
                std.debug.assert(item.deposit() == 1);
                self.stack_height += 1;
                const expression = if (item.pushed_value) |value|
                    try self.expressionClasses().makeConstant(value, item.debug_data)
                else
                    try self.expressionClasses().find(item, &.{}, copy_item, 0);
                try self.setStackElement(self.stack_height, expression);
            },
        }
        return operation;
    }

    fn feedOperation(
        self: *KnownState,
        item: *const AssemblyItem,
        copy_item: bool,
    ) KnownStateError!StoreOperation {
        const instruction = item.instruction_value.?;
        const info = InstructionModule.instructionInfo(instruction, EVMVersion.current());
        var operation: StoreOperation = .{};

        if (InstructionModule.isDupInstruction(instruction)) {
            const depth: i32 = @intCast(InstructionModule.getDupNumber(instruction));
            try self.setStackElement(
                self.stack_height + 1,
                try self.stackElement(self.stack_height - (depth - 1), item.debug_data),
            );
        } else if (InstructionModule.isSwapInstruction(instruction)) {
            const depth: i32 = @intCast(InstructionModule.getSwapNumber(instruction));
            try self.swapStackElements(
                self.stack_height,
                self.stack_height - depth,
                item.debug_data,
            );
        } else if (instruction != .POP) {
            var argument_storage: [7]Id = undefined;
            const arguments = argument_storage[0..info.args];
            for (arguments, 0..) |*argument, index|
                argument.* = try self.stackElement(
                    self.stack_height - @as(i32, @intCast(index)),
                    item.debug_data,
                );

            switch (instruction) {
                .SSTORE => operation = try self.storeInStorage(arguments[0], arguments[1], item.debug_data),
                .SLOAD => try self.setStackElement(
                    self.stack_height + @as(i32, @intCast(item.deposit())),
                    try self.loadFromStorage(arguments[0], item.debug_data),
                ),
                .MSTORE => operation = try self.storeInMemory(arguments[0], arguments[1], item.debug_data),
                .MLOAD => try self.setStackElement(
                    self.stack_height + @as(i32, @intCast(item.deposit())),
                    try self.loadFromMemory(arguments[0], item.debug_data),
                ),
                .KECCAK256 => try self.setStackElement(
                    self.stack_height + @as(i32, @intCast(item.deposit())),
                    try self.applyKeccak256(arguments[0], arguments[1], item.debug_data),
                ),
                else => {
                    const invalidates_memory = SemanticInformation.memory(instruction) == .Write;
                    const invalidates_storage = SemanticInformation.storage(instruction) == .Write;
                    if (invalidates_memory) {
                        self.resetMemory();
                        self.resetKnownKeccak256Hashes();
                    }
                    if (invalidates_storage) self.resetStorage();
                    if (invalidates_memory or invalidates_storage) self.sequence_number +%= 2;
                    std.debug.assert(info.ret <= 1);
                    if (info.ret == 1) try self.setStackElement(
                        self.stack_height + @as(i32, @intCast(item.deposit())),
                        try self.expressionClasses().find(item, arguments, copy_item, 0),
                    );
                },
            }
        }

        const new_height = self.stack_height + @as(i32, @intCast(item.deposit()));
        eraseStackAbove(&self.stack_elements, new_height);
        self.stack_height = new_height;
        return operation;
    }

    pub fn resetStorage(self: *KnownState) void {
        self.storage_content.clearRetainingCapacity();
    }

    pub fn resetMemory(self: *KnownState) void {
        self.memory_content.clearRetainingCapacity();
    }

    pub fn resetKnownKeccak256Hashes(self: *KnownState) void {
        for (self.known_keccak256_hashes.items) |*known_hash| known_hash.deinit(self.allocator);
        self.known_keccak256_hashes.clearRetainingCapacity();
    }

    pub fn resetStack(self: *KnownState) void {
        self.stack_elements.clearRetainingCapacity();
        self.stack_height = 0;
    }

    pub fn reset(self: *KnownState) void {
        self.resetStorage();
        self.resetMemory();
        self.resetKnownKeccak256Hashes();
        self.resetStack();
    }

    pub fn reduceToCommonKnowledge(
        self: *KnownState,
        other: *KnownState,
        combine_sequence_numbers: bool,
    ) KnownStateError!void {
        if (self.shared_expressions != other.shared_expressions)
            return error.IncompatibleExpressionClasses;
        const stack_difference = self.stack_height - other.stack_height;
        var index: usize = 0;
        while (index < self.stack_elements.entries.items.len) {
            const entry = &self.stack_elements.entries.items[index];
            const other_id = other.stack_elements.get(entry.key - stack_difference);
            if (other_id == null) {
                _ = self.stack_elements.entries.orderedRemove(index);
                continue;
            }
            if (entry.value == other_id.?.*) {
                index += 1;
                continue;
            }

            var these_tags = try self.tagsInExpression(entry.value);
            defer these_tags.deinit(self.allocator);
            var other_tags = try self.tagsInExpression(other_id.?.*);
            defer other_tags.deinit(self.allocator);
            if (!these_tags.isEmpty() and !other_tags.isEmpty()) {
                for (other_tags.map.items()) |tag| _ = try these_tags.insert(self.allocator, tag.key);
                entry.value = try self.tagUnion(&these_tags);
                index += 1;
            } else {
                _ = self.stack_elements.entries.orderedRemove(index);
            }
        }

        if (self.stack_height > other.stack_height) {
            for (self.stack_elements.mutableItems()) |*entry| entry.key -= stack_difference;
            self.stack_height = other.stack_height;
        }

        intersectContent(&self.storage_content, &other.storage_content);
        intersectContent(&self.memory_content, &other.memory_content);
        if (combine_sequence_numbers)
            self.sequence_number = @max(self.sequence_number, other.sequence_number);
    }

    pub fn eql(self: *const KnownState, other: *const KnownState) bool {
        if (!contentMapsEqual(&self.storage_content, &other.storage_content) or
            !contentMapsEqual(&self.memory_content, &other.memory_content)) return false;
        if (self.stack_elements.len() != other.stack_elements.len()) return false;
        const stack_difference = self.stack_height - other.stack_height;
        for (self.stack_elements.items(), other.stack_elements.items()) |left, right| {
            if (left.key - stack_difference != right.key or left.value != right.value) return false;
        }
        return true;
    }

    pub fn stackElement(
        self: *KnownState,
        stack_height: i32,
        debug_data: DebugData,
    ) KnownStateError!Id {
        if (self.stack_elements.get(stack_height)) |existing| return existing.*;
        const signed_height: i256 = stack_height;
        const item = AssemblyItem.initType(.UndefinedItem, @bitCast(signed_height), debug_data);
        const id = try self.expressionClasses().findDefault(&item, &.{});
        try self.setStackElement(stack_height, id);
        return id;
    }

    pub fn relativeStackElement(
        self: *KnownState,
        stack_offset: i32,
        debug_data: DebugData,
    ) KnownStateError!Id {
        return self.stackElement(self.stack_height + stack_offset, debug_data);
    }

    pub fn tagsInExpression(self: *KnownState, expression_id: Id) KnownStateError!TagSet {
        for (self.tag_unions.items) |tag_union|
            if (tag_union.id == expression_id) return tag_union.tags.clone(self.allocator);
        const expression = try self.expressionClasses().representative(expression_id);
        var result: TagSet = .{};
        errdefer result.deinit(self.allocator);
        if (expression.item.item_type == .PushTag)
            _ = try result.insert(self.allocator, expression.item.data_value);
        return result;
    }

    pub fn clearTagUnions(self: *KnownState) void {
        var index: usize = 0;
        while (index < self.stack_elements.entries.items.len) {
            const id = self.stack_elements.entries.items[index].value;
            if (self.isTagUnion(id)) {
                _ = self.stack_elements.entries.orderedRemove(index);
            } else {
                index += 1;
            }
        }
    }

    fn isTagUnion(self: *const KnownState, id: Id) bool {
        for (self.tag_unions.items) |tag_union| if (tag_union.id == id) return true;
        return false;
    }

    fn tagUnion(self: *KnownState, tags: *const TagSet) KnownStateError!Id {
        for (self.tag_unions.items) |tag_union|
            if (tagSetsEqual(&tag_union.tags, tags)) return tag_union.id;
        const id = try self.expressionClasses().newClass(.{});
        var owned_tags = try tags.clone(self.allocator);
        errdefer owned_tags.deinit(self.allocator);
        try self.tag_unions.append(self.allocator, .{ .id = id, .tags = owned_tags });
        return id;
    }

    fn setStackElement(self: *KnownState, stack_height: i32, class: Id) std.mem.Allocator.Error!void {
        _ = try self.stack_elements.fetchPut(self.allocator, stack_height, class);
    }

    fn swapStackElements(
        self: *KnownState,
        height_a: i32,
        height_b: i32,
        debug_data: DebugData,
    ) KnownStateError!void {
        if (height_a == height_b) return error.InvalidStackOperation;
        const class_a = try self.stackElement(height_a, debug_data);
        const class_b = try self.stackElement(height_b, debug_data);
        try self.setStackElement(height_a, class_b);
        try self.setStackElement(height_b, class_a);
    }

    fn storeInStorage(
        self: *KnownState,
        slot: Id,
        value: Id,
        debug_data: DebugData,
    ) KnownStateError!StoreOperation {
        if (self.storage_content.get(slot)) |existing| if (existing.* == value) return .{};
        self.sequence_number +%= 1;
        var retained: ContentMap = .{};
        errdefer retained.deinit(self.allocator);
        for (self.storage_content.items()) |entry| {
            if (try self.expressionClasses().knownToBeDifferent(entry.key, slot) or entry.value == value)
                _ = try retained.insert(self.allocator, entry.key, entry.value);
        }
        self.storage_content.deinit(self.allocator);
        self.storage_content = retained.take();

        const item = AssemblyItem.initInstruction(.SSTORE, debug_data);
        const expression = try self.expressionClasses().find(
            &item,
            &.{ slot, value },
            true,
            self.sequence_number,
        );
        const operation: StoreOperation = .{
            .target = .Storage,
            .slot = slot,
            .sequence_number = self.sequence_number,
            .expression = expression,
        };
        _ = try self.storage_content.fetchPut(self.allocator, slot, value);
        self.sequence_number +%= 1;
        return operation;
    }

    fn loadFromStorage(
        self: *KnownState,
        slot: Id,
        debug_data: DebugData,
    ) KnownStateError!Id {
        if (self.storage_content.get(slot)) |existing| return existing.*;
        const item = AssemblyItem.initInstruction(.SLOAD, debug_data);
        const expression = try self.expressionClasses().find(
            &item,
            &.{slot},
            true,
            self.sequence_number,
        );
        _ = try self.storage_content.fetchPut(self.allocator, slot, expression);
        return expression;
    }

    fn storeInMemory(
        self: *KnownState,
        slot: Id,
        value: Id,
        debug_data: DebugData,
    ) KnownStateError!StoreOperation {
        if (self.memory_content.get(slot)) |existing| if (existing.* == value) return .{};
        self.sequence_number +%= 1;
        var retained: ContentMap = .{};
        errdefer retained.deinit(self.allocator);
        for (self.memory_content.items()) |entry| {
            if (try self.expressionClasses().knownToBeDifferentBy32(entry.key, slot))
                _ = try retained.insert(self.allocator, entry.key, entry.value);
        }
        self.memory_content.deinit(self.allocator);
        self.memory_content = retained.take();

        const item = AssemblyItem.initInstruction(.MSTORE, debug_data);
        const expression = try self.expressionClasses().find(
            &item,
            &.{ slot, value },
            true,
            self.sequence_number,
        );
        const operation: StoreOperation = .{
            .target = .Memory,
            .slot = slot,
            .sequence_number = self.sequence_number,
            .expression = expression,
        };
        _ = try self.memory_content.fetchPut(self.allocator, slot, value);
        self.sequence_number +%= 1;
        return operation;
    }

    fn loadFromMemory(
        self: *KnownState,
        slot: Id,
        debug_data: DebugData,
    ) KnownStateError!Id {
        if (self.memory_content.get(slot)) |existing| return existing.*;
        const item = AssemblyItem.initInstruction(.MLOAD, debug_data);
        const expression = try self.expressionClasses().find(
            &item,
            &.{slot},
            true,
            self.sequence_number,
        );
        _ = try self.memory_content.fetchPut(self.allocator, slot, expression);
        return expression;
    }

    fn applyKeccak256(
        self: *KnownState,
        start: Id,
        length_id: Id,
        debug_data: DebugData,
    ) KnownStateError!Id {
        const item = AssemblyItem.initInstruction(.KECCAK256, debug_data);
        const known_length = self.expressionClasses().knownConstantValue(length_id);
        if (known_length == null or known_length.? > 128)
            return self.expressionClasses().find(
                &item,
                &.{ start, length_id },
                true,
                self.sequence_number,
            );

        const length: u32 = @intCast(known_length.?);
        var word_storage: [4]Id = undefined;
        var word_count: usize = 0;
        var offset: u32 = 0;
        while (offset < length) : (offset += 32) {
            // Analysis-created offsets have no source annotation in solc.
            // Their interned representatives may later supply emitted PUSHes.
            const offset_id = try self.expressionClasses().makeConstant(offset, .{});
            const slot = try self.expressionClasses().makeOperation(.ADD, &.{ start, offset_id }, debug_data);
            word_storage[word_count] = try self.loadFromMemory(slot, debug_data);
            word_count += 1;
        }
        const words = word_storage[0..word_count];
        for (self.known_keccak256_hashes.items) |known_hash| {
            if (known_hash.length == length and std.mem.eql(Id, known_hash.memory_words, words))
                return known_hash.value;
        }

        var all_constant = true;
        for (words) |word| if (self.expressionClasses().knownConstantValue(word) == null) {
            all_constant = false;
            break;
        };
        const value = if (all_constant) blk: {
            var bytes: [128]u8 = undefined;
            for (words, 0..) |word, index| {
                const constant = self.expressionClasses().knownConstantValue(word).?;
                std.mem.writeInt(u256, bytes[index * 32 ..][0..32], constant, .big);
            }
            const hash = Keccak256.keccak256(bytes[0..length]);
            break :blk try self.expressionClasses().makeConstant(hash.toInteger(), debug_data);
        } else try self.expressionClasses().find(
            &item,
            &.{ start, length_id },
            true,
            self.sequence_number,
        );

        const owned_words = try self.allocator.dupe(Id, words);
        errdefer self.allocator.free(owned_words);
        try self.known_keccak256_hashes.append(self.allocator, .{
            .memory_words = owned_words,
            .length = length,
            .value = value,
        });
        return value;
    }

    pub fn streamAlloc(self: *const KnownState, allocator: std.mem.Allocator) ![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(allocator);
        const writer = output.writer(allocator);
        try writer.print("=== State ===\nStack height: {d}\nEquivalence classes:\n", .{self.stack_height});
        for (0..self.expressionClasses().size()) |id| {
            const dag = try self.expressionClasses().fullDAGToStringAlloc(allocator, @intCast(id));
            defer allocator.free(dag);
            try writer.print("  {s}\n", .{dag});
        }
        try writer.writeAll("Stack:\n");
        for (self.stack_elements.items()) |entry| try writer.print("  {d}: {d}\n", .{ entry.key, entry.value });
        try writer.writeAll("Storage:\n");
        for (self.storage_content.items()) |entry| try writer.print("  {d}: {d}\n", .{ entry.key, entry.value });
        try writer.writeAll("Memory:\n");
        for (self.memory_content.items()) |entry| try writer.print("  {d}: {d}\n", .{ entry.key, entry.value });
        return output.toOwnedSlice(allocator);
    }

    fn fromGasContext(context: *anyopaque) *KnownState {
        return @ptrCast(@alignCast(context));
    }

    fn gasRelativeStackElement(context: *anyopaque, offset: i32) !Id {
        return fromGasContext(context).relativeStackElement(offset, .{});
    }

    fn gasKnownConstant(context: *anyopaque, id: Id) ?*const u256 {
        return fromGasContext(context).expressionClasses().knownConstant(id);
    }

    fn gasKnownZero(context: *anyopaque, id: Id) !bool {
        return fromGasContext(context).expressionClasses().knownZero(id);
    }

    fn gasKnownNonZero(context: *anyopaque, id: Id) !bool {
        return fromGasContext(context).expressionClasses().knownNonZero(id);
    }

    fn gasConstantExpression(context: *anyopaque, value: u256) !Id {
        return fromGasContext(context).expressionClasses().makeConstant(value, .{});
    }

    fn gasFindAdd(context: *anyopaque, left: Id, right: Id) !Id {
        return fromGasContext(context).expressionClasses().makeOperation(.ADD, &.{ left, right }, .{});
    }

    fn gasStorageContent(context: *anyopaque, slot: Id) ?Id {
        const value = fromGasContext(context).storage_content.get(slot) orelse return null;
        return value.*;
    }

    fn gasFeedItem(context: *anyopaque, item: *const AssemblyItem) !void {
        _ = try fromGasContext(context).feedItem(item, false);
    }

    const gas_state_vtable: GasMeterModule.GasState.VTable = .{
        .relative_stack_element = gasRelativeStackElement,
        .known_constant = gasKnownConstant,
        .known_zero = gasKnownZero,
        .known_non_zero = gasKnownNonZero,
        .constant_expression = gasConstantExpression,
        .find_add = gasFindAdd,
        .storage_content = gasStorageContent,
        .feed_item = gasFeedItem,
    };
};

fn eraseStackAbove(stack: *StackMap, height: i32) void {
    const search = stack.search(height);
    const first = search.index + @intFromBool(search.found);
    stack.entries.items.len = first;
}

fn intersectContent(target: *ContentMap, other: *const ContentMap) void {
    var index: usize = 0;
    while (index < target.entries.items.len) {
        const entry = target.entries.items[index];
        const other_value = other.get(entry.key);
        if (other_value != null and other_value.?.* == entry.value) {
            index += 1;
        } else {
            _ = target.entries.orderedRemove(index);
        }
    }
}

fn contentMapsEqual(left: *const ContentMap, right: *const ContentMap) bool {
    if (left.len() != right.len()) return false;
    for (left.items(), right.items()) |a, b|
        if (a.key != b.key or a.value != b.value) return false;
    return true;
}

fn tagSetsEqual(left: *const TagSet, right: *const TagSet) bool {
    if (left.len() != right.len()) return false;
    for (0..left.len()) |index| if (left.at(index) != right.at(index)) return false;
    return true;
}

test "known state tracks stack, duplicate, swap, memory, and storage" {
    var state = try KnownState.init(std.testing.allocator);
    defer state.deinit();

    var item = AssemblyItem.initPush(7, .{});
    _ = try state.feedItem(&item, true);
    item = AssemblyItem.initPush(9, .{});
    _ = try state.feedItem(&item, true);
    const top = try state.relativeStackElement(0, .{});
    item = AssemblyItem.initInstruction(.DUP2, .{});
    _ = try state.feedItem(&item, true);
    try std.testing.expectEqual(@as(i32, 3), state.stack_height);
    try std.testing.expectEqual(@as(?u256, 7), state.expressionClasses().knownConstantValue(
        try state.relativeStackElement(0, .{}),
    ));
    item = AssemblyItem.initInstruction(.SWAP1, .{});
    _ = try state.feedItem(&item, true);
    try std.testing.expectEqual(top, try state.relativeStackElement(0, .{}));

    item = AssemblyItem.initInstruction(.MSTORE, .{});
    const memory_store = try state.feedItem(&item, true);
    try std.testing.expect(memory_store.target == .Memory);
    try std.testing.expectEqual(@as(i32, 1), state.stack_height);

    item = AssemblyItem.initPush(9, .{});
    _ = try state.feedItem(&item, true);
    item = AssemblyItem.initInstruction(.MLOAD, .{});
    _ = try state.feedItem(&item, true);
    try std.testing.expectEqual(@as(?u256, 7), state.expressionClasses().knownConstantValue(
        try state.relativeStackElement(0, .{}),
    ));
}

test "known state copies share expressions but own mutable maps" {
    var state = try KnownState.init(std.testing.allocator);
    defer state.deinit();
    var item = AssemblyItem.initType(.PushTag, 1, .{});
    _ = try state.feedItem(&item, true);
    var copy = try state.clone();
    defer copy.deinit();
    copy.resetStack();
    item = AssemblyItem.initType(.PushTag, 2, .{});
    _ = try copy.feedItem(&item, true);
    try state.reduceToCommonKnowledge(&copy, true);
    try std.testing.expectEqual(@as(i32, 1), state.stack_height);
    var tags = try state.tagsInExpression(try state.relativeStackElement(0, .{}));
    defer tags.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 2), tags.len());

    var merged_copy = try state.clone();
    defer merged_copy.deinit();
    try std.testing.expect(state.eql(&merged_copy));
    merged_copy.resetStack();
    try std.testing.expectEqual(@as(i32, 1), state.stack_height);
}

test "source locations for Keccak analysis offsets preserve existing representatives" {
    var state = try KnownState.init(std.testing.allocator);
    defer state.deinit();
    const debug_data: DebugData = .{
        .origin_location = .{ .start = 1, .end = 10, .source_name = "C.sol" },
    };
    const classes = state.expressionClasses();
    const start = try classes.makeConstant(64, debug_data);
    const length = try classes.makeConstant(96, debug_data);
    const hash = try state.applyKeccak256(start, length, debug_data);
    for ([_]u256{ 0, 32 }) |offset| {
        const id = try classes.makeConstant(offset, debug_data);
        const item = (try classes.representative(id)).item;
        try std.testing.expect(item.debug_data.origin_location.eql(.{}));
    }
    // The already-interned 64 keeps its original annotation, as does the
    // KECCAK256 instruction; only newly introduced offset constants are empty.
    try std.testing.expect((try classes.representative(start)).item.debug_data.origin_location.eql(debug_data.origin_location));
    try std.testing.expect((try classes.representative(hash)).item.debug_data.origin_location.eql(debug_data.origin_location));
}

test "gas meter consumes and updates the concrete known state" {
    var state = try KnownState.init(std.testing.allocator);
    defer state.deinit();

    var item = AssemblyItem.initPush(0xfeed, .{});
    _ = try state.feedItem(&item, true);
    item = AssemblyItem.initPush(0, .{});
    _ = try state.feedItem(&item, true);

    var meter: GasMeterModule.GasMeter = .{
        .state = state.gasState(),
        .evm_version = EVMVersion.init(.Berlin),
    };
    item = AssemblyItem.initInstruction(.MSTORE, .{});
    const store_gas = try meter.estimateMax(&item, false);
    try std.testing.expectEqual(@as(u256, 6), store_gas.value);
    try std.testing.expectEqual(@as(i32, 0), state.stack_height);

    item = AssemblyItem.initPush(0, .{});
    _ = try state.feedItem(&item, true);
    item = AssemblyItem.initInstruction(.MLOAD, .{});
    const load_gas = try meter.estimateMax(&item, false);
    try std.testing.expectEqual(@as(u256, 3), load_gas.value);
    try std.testing.expectEqual(@as(?u256, 0xfeed), state.expressionClasses().knownConstantValue(
        try state.relativeStackElement(0, .{}),
    ));
}
