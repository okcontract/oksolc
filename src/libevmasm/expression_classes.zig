// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned expression-equivalence classes and ordered simplification.

const std = @import("std");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const AssemblyItemModule = @import("assembly_item.zig");
const InstructionModule = @import("instruction.zig");
const RuleList = @import("rule_list.zig");
const SemanticInformation = @import("semantic_information.zig");

const AssemblyItem = AssemblyItemModule.AssemblyItem;
const AssemblyItemType = AssemblyItemModule.AssemblyItemType;
const Instruction = InstructionModule.Instruction;

pub const Id = u32;
pub const invalid_id = std.math.maxInt(Id);

pub const Expression = struct {
    id: Id,
    /// Stable, allocator-owned item. Keeping it separately allocated preserves
    /// pointers returned by `knownConstant()` as the representative list grows.
    item: *AssemblyItem,
    arguments: []Id,
    sequence_number: u32 = 0,

    fn deinit(self: *Expression, allocator: std.mem.Allocator) void {
        self.item.deinit(allocator);
        allocator.destroy(self.item);
        allocator.free(self.arguments);
        self.* = undefined;
    }

    pub fn eql(self: *const Expression, other: *const Expression) bool {
        if (self.item.item_type != other.item.item_type) return false;
        if (self.sequence_number != other.sequence_number or
            !std.mem.eql(Id, self.arguments, other.arguments)) return false;
        return if (self.item.item_type == .Operation)
            self.item.instruction_value == other.item.instruction_value
        else
            self.item.data_value == other.item.data_value;
    }
};

const ExpressionKey = struct {
    item_type: AssemblyItemType,
    instruction: u8,
    data: u256,
    arguments: []const Id,
    sequence_number: u32,
};

const ExpressionKeyContext = struct {
    pub fn hash(_: @This(), key: ExpressionKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&key.item_type));
        hasher.update(std.mem.asBytes(&key.instruction));
        hasher.update(std.mem.asBytes(&key.data));
        hasher.update(std.mem.sliceAsBytes(key.arguments));
        hasher.update(std.mem.asBytes(&key.sequence_number));
        return hasher.final();
    }

    pub fn eql(_: @This(), left: ExpressionKey, right: ExpressionKey) bool {
        return left.item_type == right.item_type and
            left.instruction == right.instruction and
            left.data == right.data and
            left.sequence_number == right.sequence_number and
            std.mem.eql(Id, left.arguments, right.arguments);
    }
};

const ExpressionMap = std.HashMapUnmanaged(ExpressionKey, Id, ExpressionKeyContext, 80);

/// A lookup borrows its input or caller-local normalization storage. Larger
/// commutative argument lists own a temporary buffer, transferable on a miss.
const NormalizedArguments = struct {
    items: []const Id,
    owned: ?[]Id = null,

    fn init(allocator: std.mem.Allocator, item: *const AssemblyItem, arguments: []const Id, buffer: []Id) !NormalizedArguments {
        if (!SemanticInformation.isCommutativeOperation(item) or arguments.len < 2)
            return .{ .items = arguments };
        const normalized = if (arguments.len <= buffer.len)
            buffer[0..arguments.len]
        else
            try allocator.alloc(Id, arguments.len);
        @memcpy(normalized, arguments);
        std.sort.insertion(Id, normalized, {}, std.sort.asc(Id));
        return .{
            .items = normalized,
            .owned = if (arguments.len > buffer.len) normalized else null,
        };
    }

    fn deinit(self: *NormalizedArguments, allocator: std.mem.Allocator) void {
        if (self.owned) |owned| allocator.free(owned);
        self.* = undefined;
    }

    fn takeOwned(self: *NormalizedArguments, allocator: std.mem.Allocator) ![]Id {
        if (self.owned) |owned| {
            self.owned = null;
            return owned;
        }
        return allocator.dupe(Id, self.items);
    }
};

pub const ExpressionError = std.mem.Allocator.Error || SemanticInformation.SemanticError || error{
    InvalidExpressionId,
    ExpressionCapacity,
};

pub const ExpressionClasses = struct {
    allocator: std.mem.Allocator,
    representatives: std.ArrayList(Expression) = .empty,
    expressions: ExpressionMap = .empty,

    pub fn init(allocator: std.mem.Allocator) ExpressionClasses {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *ExpressionClasses) void {
        for (self.representatives.items) |*expression| expression.deinit(self.allocator);
        self.representatives.deinit(self.allocator);
        var keys = self.expressions.keyIterator();
        while (keys.next()) |key| self.allocator.free(key.arguments);
        self.expressions.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn size(self: *const ExpressionClasses) usize {
        return self.representatives.items.len;
    }

    pub fn representative(self: *const ExpressionClasses, id: Id) ExpressionError!*const Expression {
        if (id >= self.representatives.items.len) return error.InvalidExpressionId;
        return &self.representatives.items[id];
    }

    pub fn representativeMut(self: *ExpressionClasses, id: Id) ExpressionError!*Expression {
        if (id >= self.representatives.items.len) return error.InvalidExpressionId;
        return &self.representatives.items[id];
    }

    /// `_copy_item` remains for source compatibility. Zig always takes a deep
    /// copy so no representative can outlive borrowed C++-style storage.
    pub fn find(
        self: *ExpressionClasses,
        item: *const AssemblyItem,
        arguments: []const Id,
        _: bool,
        sequence_number: u32,
    ) ExpressionError!Id {
        if (self.representatives.items.len >= std.math.maxInt(Id))
            return error.ExpressionCapacity;

        var argument_buffer: [2]Id = undefined;
        var lookup = try NormalizedArguments.init(self.allocator, item, arguments, &argument_buffer);
        defer lookup.deinit(self.allocator);
        const deterministic = try SemanticInformation.isDeterministic(item);
        if (deterministic)
            if (self.expressions.get(makeKey(item, lookup.items, sequence_number))) |existing| return existing;

        const normalized = try lookup.takeOwned(self.allocator);
        var normalized_owned = true;
        defer if (normalized_owned) self.allocator.free(normalized);
        const lookup_key = makeKey(item, normalized, sequence_number);

        if (deterministic and item.item_type == .Operation) {
            if (try RuleList.simplify(
                self,
                item.instruction_value.?,
                normalized,
                item.debug_data,
            )) |simplified| {
                try self.expressions.put(self.allocator, lookup_key, simplified);
                normalized_owned = false;
                return simplified;
            }
        }

        const representative_arguments = if (deterministic)
            try self.allocator.dupe(Id, normalized)
        else blk: {
            normalized_owned = false;
            break :blk normalized;
        };
        var representative_arguments_owned = true;
        errdefer if (representative_arguments_owned) self.allocator.free(representative_arguments);

        const owned_item = try self.allocator.create(AssemblyItem);
        var item_allocation_owned = true;
        errdefer if (item_allocation_owned) self.allocator.destroy(owned_item);
        owned_item.* = try item.clone(self.allocator);
        var item_value_owned = true;
        errdefer if (item_value_owned) owned_item.deinit(self.allocator);

        const id: Id = @intCast(self.representatives.items.len);
        try self.representatives.append(self.allocator, .{
            .id = id,
            .item = owned_item,
            .arguments = representative_arguments,
            .sequence_number = sequence_number,
        });
        representative_arguments_owned = false;
        item_allocation_owned = false;
        item_value_owned = false;
        errdefer {
            self.representatives.items[self.representatives.items.len - 1].deinit(self.allocator);
            self.representatives.items.len -= 1;
        }

        if (deterministic) {
            try self.expressions.put(self.allocator, lookup_key, id);
            normalized_owned = false;
        }
        return id;
    }

    pub fn findDefault(
        self: *ExpressionClasses,
        item: *const AssemblyItem,
        arguments: []const Id,
    ) ExpressionError!Id {
        return self.find(item, arguments, true, 0);
    }

    pub fn forceEqual(
        self: *ExpressionClasses,
        id: Id,
        item: *const AssemblyItem,
        arguments: []const Id,
        _: bool,
    ) ExpressionError!void {
        _ = try self.representative(id);
        var argument_buffer: [2]Id = undefined;
        var lookup = try NormalizedArguments.init(self.allocator, item, arguments, &argument_buffer);
        defer lookup.deinit(self.allocator);
        if (self.expressions.get(makeKey(item, lookup.items, 0)) != null) return;

        const normalized = try lookup.takeOwned(self.allocator);
        var owned = true;
        defer if (owned) self.allocator.free(normalized);
        const key = makeKey(item, normalized, 0);
        try self.expressions.put(self.allocator, key, id);
        owned = false;
    }

    pub fn newClass(self: *ExpressionClasses, debug_data: DebugData) ExpressionError!Id {
        const id: Id = @intCast(self.representatives.items.len);
        const item = AssemblyItem.initType(
            .UndefinedItem,
            (@as(u256, 1) << 255) + id,
            debug_data,
        );
        return self.findDefault(&item, &.{});
    }

    pub fn knownToBeDifferent(self: *ExpressionClasses, left: Id, right: Id) ExpressionError!bool {
        const difference = try self.makeOperation(.SUB, &.{ left, right }, .{});
        return try self.knownNonZero(difference);
    }

    pub fn knownToBeDifferentBy32(self: *ExpressionClasses, left: Id, right: Id) ExpressionError!bool {
        const difference = try self.makeOperation(.SUB, &.{ left, right }, .{});
        const value = self.knownConstantValue(difference) orelse return false;
        return value +% 31 > 62;
    }

    pub fn knownZero(self: *const ExpressionClasses, id: Id) ExpressionError!bool {
        _ = try self.representative(id);
        return self.knownConstantValue(id) == 0;
    }

    pub fn knownNonZero(self: *ExpressionClasses, id: Id) ExpressionError!bool {
        _ = try self.representative(id);
        const inverted = try self.makeOperation(.ISZERO, &.{id}, .{});
        return self.knownConstantValue(inverted) == 0;
    }

    pub fn knownConstant(self: *const ExpressionClasses, id: Id) ?*const u256 {
        const expression = self.representative(id) catch return null;
        if (expression.item.item_type != .Push) return null;
        return &expression.item.data_value;
    }

    pub fn knownConstantValue(self: *const ExpressionClasses, id: Id) ?u256 {
        const value = self.knownConstant(id) orelse return null;
        return value.*;
    }

    pub fn operationArguments(
        self: *const ExpressionClasses,
        id: Id,
        instruction: Instruction,
    ) ?[]const Id {
        const expression = self.representative(id) catch return null;
        if (expression.item.item_type != .Operation or
            expression.item.instruction_value.? != instruction) return null;
        return expression.arguments;
    }

    pub fn makeConstant(
        self: *ExpressionClasses,
        value: u256,
        debug_data: DebugData,
    ) ExpressionError!Id {
        const item = AssemblyItem.initPush(value, debug_data);
        return self.findDefault(&item, &.{});
    }

    pub fn materializeConstant(
        self: *ExpressionClasses,
        _: Id,
        value: u256,
        debug_data: DebugData,
    ) ExpressionError!Id {
        return self.makeConstant(value, debug_data);
    }

    pub fn makeOperation(
        self: *ExpressionClasses,
        instruction: Instruction,
        arguments: []const Id,
        debug_data: DebugData,
    ) ExpressionError!Id {
        const item = AssemblyItem.initInstruction(instruction, debug_data);
        return self.findDefault(&item, arguments);
    }

    pub fn fullDAGToStringAlloc(
        self: *const ExpressionClasses,
        allocator: std.mem.Allocator,
        id: Id,
    ) ExpressionError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(allocator);
        try self.writeDAG(output.writer(allocator), id);
        return output.toOwnedSlice(allocator);
    }

    fn writeDAG(self: *const ExpressionClasses, writer: anytype, id: Id) !void {
        const expression = try self.representative(id);
        try writer.print("{d}:", .{id});
        if (expression.item.item_type == .Operation) {
            const info = InstructionModule.instructionInfo(
                expression.item.instruction_value.?,
                @import("../liblangutil/evm_version.zig").EVMVersion.current(),
            );
            try writer.writeAll(info.name);
        } else {
            try writer.print("{s} {x}", .{ @tagName(expression.item.item_type), expression.item.data_value });
        }
        try writer.writeByte('(');
        for (expression.arguments) |argument| {
            try self.writeDAG(writer, argument);
            try writer.writeByte(',');
        }
        try writer.writeByte(')');
    }
};

fn makeKey(item: *const AssemblyItem, arguments: []const Id, sequence_number: u32) ExpressionKey {
    return .{
        .item_type = item.item_type,
        .instruction = if (item.item_type == .Operation) @intFromEnum(item.instruction_value.?) else 0,
        .data = if (item.item_type == .Operation) 0 else item.data_value,
        .arguments = arguments,
        .sequence_number = sequence_number,
    };
}

test "expression classes intern, simplify, and retain stable constants" {
    var classes = ExpressionClasses.init(std.testing.allocator);
    defer classes.deinit();

    const seven = try classes.makeConstant(7, .{});
    const five = try classes.makeConstant(5, .{});
    const sum = try classes.makeOperation(.ADD, &.{ seven, five }, .{});
    try std.testing.expectEqual(@as(?u256, 12), classes.knownConstantValue(sum));
    try std.testing.expectEqual(sum, try classes.makeOperation(.ADD, &.{ five, seven }, .{}));

    const unknown = try classes.newClass(.{});
    const identity = try classes.makeOperation(.ADD, &.{ unknown, try classes.makeConstant(0, .{}) }, .{});
    try std.testing.expectEqual(unknown, identity);
    const before = classes.knownConstant(seven).?;
    for (0..128) |_| _ = try classes.newClass(.{});
    try std.testing.expectEqual(@as(u256, 7), before.*);
}

test "nested logical and arithmetic rules retain first-match semantics" {
    var classes = ExpressionClasses.init(std.testing.allocator);
    defer classes.deinit();

    const x = try classes.newClass(.{});
    const y = try classes.newClass(.{});
    const xor = try classes.makeOperation(.XOR, &.{ x, y }, .{});
    try std.testing.expectEqual(y, try classes.makeOperation(.XOR, &.{ x, xor }, .{}));

    const three = try classes.makeConstant(3, .{});
    const five = try classes.makeConstant(5, .{});
    const x_plus_three = try classes.makeOperation(.ADD, &.{ x, three }, .{});
    const reassociated = try classes.makeOperation(.ADD, &.{ x_plus_three, five }, .{});
    const expected = try classes.makeOperation(.ADD, &.{ x, try classes.makeConstant(8, .{}) }, .{});
    try std.testing.expectEqual(expected, reassociated);

    try std.testing.expect(try classes.knownToBeDifferent(three, five));
    try std.testing.expect(!(try classes.knownToBeDifferentBy32(three, five)));
}

test "expression classes cache hits borrow arguments without allocations" {
    var classes = ExpressionClasses.init(std.testing.allocator);
    defer classes.deinit();
    const x = try classes.newClass(.{});
    const y = try classes.newClass(.{});
    var arguments = [_]Id{ y, x };
    const sum = try classes.makeOperation(.ADD, &arguments, .{});
    const difference = try classes.makeOperation(.SUB, &arguments, .{});
    const add = AssemblyItem.initInstruction(.ADD, .{});
    const sub = AssemblyItem.initInstruction(.SUB, .{});
    var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{ .fail_index = 0 });
    classes.allocator = failing.allocator();
    defer classes.allocator = std.testing.allocator;
    try std.testing.expectEqual(sum, try classes.findDefault(&add, &arguments));
    try std.testing.expectEqual(sum, try classes.findDefault(&add, &.{ x, y }));
    try std.testing.expectEqual(difference, try classes.findDefault(&sub, &arguments));
    try classes.forceEqual(x, &add, &arguments, true);
    try classes.forceEqual(x, &sub, &arguments, true);
    try std.testing.expectEqualSlices(Id, &.{ y, x }, &arguments);
    try std.testing.expect(!failing.has_induced_failure);
}

test "expression classes misses retain owned arguments through allocation failures" {
    const Check = struct {
        fn run(allocator: std.mem.Allocator) !void {
            var classes = ExpressionClasses.init(allocator);
            defer classes.deinit();
            const x = try classes.newClass(.{});
            const y = try classes.newClass(.{});
            var arguments = [_]Id{ y, x };
            const difference = try classes.makeOperation(.SUB, &arguments, .{});
            arguments[0] = x;
            try std.testing.expectEqualSlices(Id, &.{ y, x }, (try classes.representative(difference)).arguments);
            const three = try classes.makeConstant(3, .{});
            const sum = try classes.makeOperation(.ADD, &.{ x, three }, .{});
            const five = try classes.makeConstant(5, .{});
            _ = try classes.makeOperation(.ADD, &.{ sum, five }, .{});
            const add = AssemblyItem.initInstruction(.ADD, .{});
            // Keep the public API's arbitrary-arity interning behavior, including
            // the heap normalization fallback, without invoking binary rules.
            try classes.forceEqual(x, &add, &.{ y, x, three }, true);
            try std.testing.expectEqual(x, try classes.findDefault(&add, &.{ three, y, x }));
            try std.testing.expectEqualSlices(Id, &.{ y, x }, (try classes.representative(difference)).arguments);
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{});
}
