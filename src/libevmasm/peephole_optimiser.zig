// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Priority-ordered local rewrite pass from `PeepholeOptimiser.cpp`.

const std = @import("std");
const AssemblyItemModule = @import("assembly_item.zig");
const InstructionModule = @import("instruction.zig");
const SemanticInformation = @import("semantic_information.zig");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;

const AssemblyItem = AssemblyItemModule.AssemblyItem;

// A rewrite borrows unique indices from its consumed window. The nineteen
// local rules emit at most five items, and only generate plain instructions.
// Descriptors keep planning allocation-free without copying complete items.
const Replacement = union(enum) {
    kept: usize,
    generated: struct { opcode: InstructionModule.Instruction, debug_index: ?usize },

    fn materialize(self: Replacement, input: []const AssemblyItem) AssemblyItem {
        return switch (self) {
            .kept => |index| input[index],
            .generated => |item| AssemblyItem.initInstruction(item.opcode, if (item.debug_index) |index| input[index].debug_data else .{}),
        };
    }

    fn bytesRequired(self: Replacement, input: []const AssemblyItem, evm_version: EVMVersion) error{ MissingImmutableOccurrences, InvalidItem }!usize {
        return switch (self) {
            .kept => |index| input[index].bytesRequired(3, evm_version, .Approximate),
            .generated => 1,
        };
    }

    fn isPop(self: Replacement, input: []const AssemblyItem) bool {
        return switch (self) {
            .kept => |index| input[index].eqlInstruction(.POP),
            .generated => |item| item.opcode == .POP,
        };
    }
};

const Rewrite = struct {
    const max_items = 5;
    storage: [max_items]Replacement = undefined,
    len: usize = 0,

    fn entries(self: *const Rewrite) []const Replacement {
        return self.storage[0..self.len];
    }

    fn keep(self: *Rewrite, index: usize) void {
        std.debug.assert(!self.keeps(index));
        self.append(.{ .kept = index });
    }

    fn instruction(self: *Rewrite, opcode: InstructionModule.Instruction, debug_index: ?usize) void {
        self.append(.{ .generated = .{ .opcode = opcode, .debug_index = debug_index } });
    }

    fn append(self: *Rewrite, item: Replacement) void {
        std.debug.assert(self.len < self.storage.len);
        self.storage[self.len] = item;
        self.len += 1;
    }

    fn keeps(self: *const Rewrite, index: usize) bool {
        for (self.entries()) |item| switch (item) {
            .kept => |kept| if (kept == index) return true,
            .generated => {},
        };
        return false;
    }
};

pub fn optimise(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(AssemblyItem),
    evm_version: EVMVersion,
) (std.mem.Allocator.Error || error{ MissingImmutableOccurrences, InvalidItem })!bool {
    var output_len: usize = 0;
    var headroom: usize = 0;
    var any_rewrite = false;
    var index: usize = 0;
    while (index < items.items.len) {
        var rewrite: Rewrite = .{};
        const consumed = applyAt(items.items, index, &rewrite, evm_version);
        std.debug.assert(consumed > 0 and consumed <= items.items.len - index);
        index += consumed;
        output_len = std.math.add(usize, output_len, rewrite.len) catch return error.OutOfMemory;
        headroom = @max(headroom, output_len -| index);
        // Every matching rule consumes at least two items. Identity emits one.
        any_rewrite = any_rewrite or consumed != 1;
    }

    if (!any_rewrite) {
        // The previous candidate was identical, but still validated byte size.
        _ = try AssemblyItemModule.bytesRequired(items.items, 3, evm_version, .Approximate);
        return false;
    }
    if (output_len > items.items.len) return false;
    if (output_len == items.items.len) {
        // Preserve candidate-before-input validation and the global POP rule.
        // Shrinking and growing candidates deliberately skip this validation.
        var candidate_bytes: usize = 0;
        var candidate_pops: usize = 0;
        index = 0;
        while (index < items.items.len) {
            var rewrite: Rewrite = .{};
            index += applyAt(items.items, index, &rewrite, evm_version);
            for (rewrite.entries()) |item| {
                candidate_bytes += try item.bytesRequired(items.items, evm_version);
                candidate_pops += @intFromBool(item.isPop(items.items));
            }
        }
        const original_bytes = try AssemblyItemModule.bytesRequired(items.items, 3, evm_version, .Approximate);
        if (candidate_bytes >= original_bytes and candidate_pops <= numberOfPops(items.items)) return false;
    }
    if (output_len == 0) {
        deinitItems(allocator, items);
        items.* = .empty;
        return true;
    }

    const input_len = items.items.len;
    const needed = std.math.add(usize, input_len, headroom) catch return error.OutOfMemory;
    var separate_output: ?[]AssemblyItem = null;
    if (items.capacity < needed) {
        if (allocator.resize(items.allocatedSlice(), needed))
            items.capacity = needed
        else
            // A new buffer needs only the final output, not space for shifting
            // all original descriptors. No payload cloning is needed either.
            separate_output = try allocator.alloc(AssemblyItem, output_len);
    }
    // No fallible work follows reservation. Expanding local rules can precede
    // shrinking ones; headroom keeps every write before the next unread item.
    const input = if (separate_output != null) items.items else items.allocatedSlice()[headroom..][0..input_len];
    const output = separate_output orelse items.allocatedSlice();
    if (separate_output == null and headroom != 0) @memmove(input, items.items);
    index = 0;
    var written: usize = 0;
    while (index < input.len) {
        var rewrite: Rewrite = .{};
        const consumed = applyAt(input, index, &rewrite, evm_version);
        if (separate_output == null and consumed == 1 and written == headroom + index) {
            // An unchanged prefix already occupies its final storage.
            index += 1;
            written += 1;
            continue;
        }
        var replacement: [Rewrite.max_items]AssemblyItem = undefined;
        for (rewrite.entries(), 0..) |item, position|
            replacement[position] = item.materialize(input);
        for (input[index..][0..consumed], index..) |*item, original_index| {
            // Verbatim is the only owned AssemblyItem payload. Value-only
            // discarded instructions need neither an owner lookup nor writes.
            if (item.verbatim != null and !rewrite.keeps(original_index)) item.deinit(allocator);
        }
        std.debug.assert(written + rewrite.len <= if (separate_output == null) headroom + index + consumed else output_len);
        @memcpy(output[written..][0..rewrite.len], replacement[0..rewrite.len]);
        written += rewrite.len;
        index += consumed;
    }
    std.debug.assert(written == output_len);
    // Descriptors outside the final live slice were moved, not cloned owners.
    if (separate_output) |buffer| {
        allocator.free(items.allocatedSlice());
        items.* = .{ .items = buffer, .capacity = buffer.len };
    } else items.items.len = written;
    return true;
}

fn applyAt(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
    evm_version: EVMVersion,
) usize {
    if (pushPop(items, index)) return 2;
    if (opPop(items, index, output)) return 2;
    if (opStop(items, index, output)) return 2;
    if (opReturnRevert(items, index, output)) return 4;
    if (doublePush(items, index, output, evm_version)) return 2;
    if (doubleSwap(items, index)) return 2;
    if (commutativeSwap(items, index, output)) return 2;
    if (swapComparison(items, index, output)) return 2;
    if (dupSwap(items, index, output)) return 2;
    if (isZeroIsZeroJumpI(items, index, output)) return 4;
    if (eqIsZeroJumpI(items, index, output)) return 4;
    if (doubleJump(items, index, output)) return 5;
    if (jumpToNext(items, index, output)) return 3;
    if (unreachableCode(items, index, output)) |consumed| return consumed;
    if (deduplicateNextTag3(items, index, output)) return 8;
    if (deduplicateNextTag2(items, index, output)) return 6;
    if (deduplicateNextTag1(items, index, output)) return 4;
    if (tagConjunctions(items, index, output)) return 3;
    if (truthyAnd(items, index)) return 3;
    output.keep(index);
    return 1;
}

fn hasWindow(items: []const AssemblyItem, index: usize, size: usize) bool {
    return index <= items.len and size <= items.len - index;
}

fn pushPop(items: []const AssemblyItem, index: usize) bool {
    if (!hasWindow(items, index, 2)) return false;
    const push = &items[index];
    const pop = &items[index + 1];
    return pop.eqlInstruction(.POP) and (SemanticInformation.isDupItem(push) or switch (push.item_type) {
        .Push, .PushTag, .PushSub, .PushSubSize, .PushProgramSize, .PushData, .PushLibraryAddress => true,
        else => false,
    });
}

fn opPop(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 2) or !items[index + 1].eqlInstruction(.POP) or
        items[index].item_type != .Operation)
    {
        return false;
    }
    const info = InstructionModule.instructionInfo(items[index].instruction_value.?, EVMVersion.current());
    if (info.ret != 1 or info.side_effects) return false;
    for (0..info.args) |_| {
        output.instruction(.POP, index);
    }
    return true;
}

fn opStop(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 2) or !items[index + 1].eqlInstruction(.STOP)) return false;
    const operation = &items[index];
    if (operation.item_type == .Operation) {
        if (InstructionModule.instructionInfo(operation.instruction_value.?, EVMVersion.current()).side_effects) {
            return false;
        }
    } else if (operation.item_type != .Push) return false;
    output.instruction(.STOP, index);
    return true;
}

fn opReturnRevert(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 4)) return false;
    const operation = &items[index];
    const push = &items[index + 1];
    const push_or_dup = &items[index + 2];
    const terminator = &items[index + 3];
    if ((!terminator.eqlInstruction(.RETURN) and !terminator.eqlInstruction(.REVERT)) or
        push.item_type != .Push or
        (push_or_dup.item_type != .Push and !push_or_dup.eqlInstruction(.DUP1)))
    {
        return false;
    }
    if (operation.item_type == .Operation) {
        if (InstructionModule.instructionInfo(operation.instruction_value.?, EVMVersion.current()).side_effects) {
            return false;
        }
    } else if (operation.item_type != .Push) return false;
    output.keep(index + 1);
    output.keep(index + 2);
    output.keep(index + 3);
    return true;
}

fn doublePush(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
    evm_version: EVMVersion,
) bool {
    if (!hasWindow(items, index, 2)) return false;
    const first = &items[index];
    const second = &items[index + 1];
    if (first.item_type != .Push or second.item_type != .Push or
        first.data_value != second.data_value or
        (evm_version.hasPush0() and first.data_value == 0))
    {
        return false;
    }
    output.keep(index);
    output.instruction(.DUP1, index + 1);
    return true;
}

fn doubleSwap(items: []const AssemblyItem, index: usize) bool {
    return hasWindow(items, index, 2) and
        items[index].eql(&items[index + 1]) and
        SemanticInformation.isSwapItem(&items[index]);
}

fn commutativeSwap(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 2) or
        !items[index].eqlInstruction(.SWAP1) or
        !SemanticInformation.isCommutativeOperation(&items[index + 1]))
    {
        return false;
    }
    output.keep(index + 1);
    return true;
}

fn swapComparison(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 2) or !items[index].eqlInstruction(.SWAP1) or
        items[index + 1].item_type != .Operation)
    {
        return false;
    }
    const replacement: InstructionModule.Instruction = switch (items[index + 1].instruction_value.?) {
        .LT => .GT,
        .GT => .LT,
        .SLT => .SGT,
        .SGT => .SLT,
        else => return false,
    };
    output.instruction(replacement, null);
    return true;
}

fn dupSwap(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 2) or
        !SemanticInformation.isDupItem(&items[index]) or
        !SemanticInformation.isSwapItem(&items[index + 1]) or
        (SemanticInformation.getDupNumber(&items[index]) catch unreachable) != // zlinter-disable-current-line no_swallow_error - opcode category predicates prove the conversion valid
            (SemanticInformation.getSwapNumber(&items[index + 1]) catch unreachable)) // zlinter-disable-current-line no_swallow_error - opcode category predicates prove the conversion valid
    {
        return false;
    }
    output.keep(index);
    return true;
}

fn isZeroIsZeroJumpI(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 4) or
        !items[index].eqlInstruction(.ISZERO) or
        !items[index + 1].eqlInstruction(.ISZERO) or
        items[index + 2].item_type != .PushTag or
        !items[index + 3].eqlInstruction(.JUMPI))
    {
        return false;
    }
    output.keep(index + 2);
    output.keep(index + 3);
    return true;
}

fn eqIsZeroJumpI(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 4) or
        !items[index].eqlInstruction(.EQ) or
        !items[index + 1].eqlInstruction(.ISZERO) or
        items[index + 2].item_type != .PushTag or
        !items[index + 3].eqlInstruction(.JUMPI))
    {
        return false;
    }
    output.instruction(.SUB, index);
    output.keep(index + 2);
    output.keep(index + 3);
    return true;
}

fn doubleJump(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 5) or
        items[index].item_type != .PushTag or
        !items[index + 1].eqlInstruction(.JUMPI) or
        items[index + 2].item_type != .PushTag or
        !items[index + 3].eqlInstruction(.JUMP) or
        items[index + 4].item_type != .Tag or
        items[index].data_value != items[index + 4].data_value)
    {
        return false;
    }
    output.instruction(.ISZERO, index + 1);
    output.keep(index + 2);
    output.keep(index + 1);
    output.keep(index + 4);
    return true;
}

fn jumpToNext(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 3) or
        items[index].item_type != .PushTag or
        (!items[index + 1].eqlInstruction(.JUMP) and !items[index + 1].eqlInstruction(.JUMPI)) or
        items[index + 2].item_type != .Tag or
        items[index].data_value != items[index + 2].data_value)
    {
        return false;
    }
    if (items[index + 1].eqlInstruction(.JUMPI)) {
        output.instruction(.POP, index + 1);
    }
    output.keep(index + 2);
    return true;
}

fn unreachableCode(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) ?usize {
    const terminal = &items[index];
    if (!terminal.eqlInstruction(.JUMP) and !terminal.eqlInstruction(.RETURN) and
        !terminal.eqlInstruction(.STOP) and !terminal.eqlInstruction(.INVALID) and
        !terminal.eqlInstruction(.SELFDESTRUCT) and !terminal.eqlInstruction(.REVERT))
    {
        return null;
    }
    var count: usize = 1;
    while (index + count < items.len and items[index + count].item_type != .Tag) count += 1;
    if (count <= 1) return null;
    output.keep(index);
    return count;
}

fn deduplicateNextTag3(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 8) or items[index].item_type == .Tag or
        !items[index + 1].eql(&items[index + 5]) or
        !items[index + 2].eql(&items[index + 6]) or
        !items[index + 3].eql(&items[index + 7]) or
        items[index + 4].item_type != .Tag or
        !SemanticInformation.terminatesControlFlowItem(&items[index + 3]))
    {
        return false;
    }
    for ([_]usize{ index, index + 4, index + 5, index + 6, index + 7 }) |item_index| {
        output.keep(item_index);
    }
    return true;
}

fn deduplicateNextTag2(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 6) or items[index].item_type == .Tag or
        !items[index + 1].eql(&items[index + 4]) or
        !items[index + 2].eql(&items[index + 5]) or
        items[index + 3].item_type != .Tag or
        !SemanticInformation.terminatesControlFlowItem(&items[index + 2]))
    {
        return false;
    }
    for ([_]usize{ index, index + 3, index + 4, index + 5 }) |item_index| {
        output.keep(item_index);
    }
    return true;
}

fn deduplicateNextTag1(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 4) or items[index].item_type == .Tag or
        !items[index + 1].eql(&items[index + 3]) or
        items[index + 2].item_type != .Tag or
        !SemanticInformation.terminatesControlFlowItem(&items[index + 1]))
    {
        return false;
    }
    for ([_]usize{ index, index + 2, index + 3 }) |item_index| {
        output.keep(item_index);
    }
    return true;
}

fn tagConjunctions(
    items: []const AssemblyItem,
    index: usize,
    output: *Rewrite,
) bool {
    if (!hasWindow(items, index, 3) or !items[index + 2].eqlInstruction(.AND)) return false;
    if (items[index].item_type == .PushTag and items[index + 1].item_type == .Push and
        (items[index + 1].data_value & 0xffff_ffff) == 0xffff_ffff)
    {
        output.keep(index);
        return true;
    }
    if (items[index + 1].item_type == .PushTag and items[index].item_type == .Push and
        (items[index].data_value & 0xffff_ffff) == 0xffff_ffff)
    {
        output.keep(index + 1);
        return true;
    }
    return false;
}

fn truthyAnd(items: []const AssemblyItem, index: usize) bool {
    return hasWindow(items, index, 3) and
        items[index].item_type == .Push and items[index].data_value == 0 and
        items[index + 1].eqlInstruction(.NOT) and items[index + 2].eqlInstruction(.AND);
}

fn numberOfPops(items: []const AssemblyItem) usize {
    var count: usize = 0;
    for (items) |*item| if (item.eqlInstruction(.POP)) {
        count += 1;
    };
    return count;
}

fn deinitItems(allocator: std.mem.Allocator, items: *std.ArrayList(AssemblyItem)) void {
    for (items.items) |*item| item.deinit(allocator);
    items.deinit(allocator);
}

test "peephole rules preserve priority and debug attribution" {
    var items: std.ArrayList(AssemblyItem) = .empty;
    defer deinitItems(std.testing.allocator, &items);
    try items.appendSlice(std.testing.allocator, &.{
        AssemblyItem.initPush(7, .{}),
        AssemblyItem.initPush(7, .{ .ast_id = 12 }),
        AssemblyItem.initInstruction(.SWAP1, .{}),
        AssemblyItem.initInstruction(.ADD, .{}),
        AssemblyItem.initType(.PushTag, 3, .{}),
        AssemblyItem.initInstruction(.JUMP, .{}),
        AssemblyItem.initType(.Tag, 3, .{}),
    });
    try std.testing.expect(try optimise(std.testing.allocator, &items, EVMVersion.init(.London)));
    try std.testing.expectEqual(@as(usize, 4), items.items.len);
    try std.testing.expect(items.items[1].eqlInstruction(.DUP1));
    try std.testing.expectEqual(@as(?i64, 12), items.items[1].debug_data.ast_id);
    try std.testing.expect(items.items[2].eqlInstruction(.ADD));
    try std.testing.expectEqual(AssemblyItemModule.AssemblyItemType.Tag, items.items[3].item_type);
}

test "peephole PUSH0 prevents the double-zero rewrite from growing bytecode" {
    var items: std.ArrayList(AssemblyItem) = .empty;
    defer deinitItems(std.testing.allocator, &items);
    try items.appendSlice(std.testing.allocator, &.{
        AssemblyItem.initPush(0, .{}),
        AssemblyItem.initPush(0, .{}),
    });
    try std.testing.expect(!(try optimise(std.testing.allocator, &items, EVMVersion.init(.Shanghai))));
    try std.testing.expectEqual(@as(usize, 2), items.items.len);
}

test "peephole verbatim ownership survives identity and unreachable-code passes" {
    var items: std.ArrayList(AssemblyItem) = .empty;
    defer deinitItems(std.testing.allocator, &items);
    try items.append(std.testing.allocator, try AssemblyItem.initVerbatim(
        std.testing.allocator,
        &.{ 1, 2, 3 },
        0,
        0,
    ));
    try items.append(std.testing.allocator, AssemblyItem.initInstruction(.STOP, .{}));
    try items.append(std.testing.allocator, try AssemblyItem.initVerbatim(
        std.testing.allocator,
        &.{ 4, 5, 6 },
        0,
        0,
    ));
    try std.testing.expect(try optimise(std.testing.allocator, &items, EVMVersion.current()));
    try std.testing.expectEqual(@as(usize, 2), items.items.len);
    try std.testing.expectEqualSlices(u8, &.{ 1, 2, 3 }, try items.items[0].verbatimData());
}

test "peephole frozen rules retain full annotations and global acceptance" {
    const Check = struct {
        const Expected = union(enum) {
            kept: usize,
            generated: struct { opcode: InstructionModule.Instruction, debug_index: ?usize },
        };

        fn op(opcode: InstructionModule.Instruction) AssemblyItem {
            return AssemblyItem.initInstruction(opcode, .{});
        }
        fn push(value: u256) AssemblyItem {
            return AssemblyItem.initPush(value, .{});
        }
        fn tag(value: u256) AssemblyItem {
            return AssemblyItem.initType(.Tag, value, .{});
        }
        fn pushTag(value: u256) AssemblyItem {
            return AssemblyItem.initType(.PushTag, value, .{});
        }
        fn keep(index: usize) Expected {
            return .{ .kept = index };
        }
        fn generated(opcode: InstructionModule.Instruction, debug_index: ?usize) Expected {
            return .{ .generated = .{ .opcode = opcode, .debug_index = debug_index } };
        }
        fn run(name: []const u8, version: EVMVersion, input: []const AssemblyItem, expected: []const Expected, changed: bool) !void {
            errdefer std.debug.print("peephole fixture: {s}\n", .{name});
            const allocator = std.testing.allocator;
            var items: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent cleanup releases the container and owned payloads on failure
            defer deinitItems(allocator, &items);
            try items.appendSlice(allocator, input);
            for (items.items, 0..) |*item, index| {
                // These fixtures have value-only payloads. Deliberately distinct
                // annotations distinguish retaining an item from generating one.
                try std.testing.expect(item.verbatim == null);
                const offset: i32 = @intCast(index * 10);
                item.debug_data = .{
                    .native_location = .{ .start = offset, .end = offset + 5, .source_name = "native.yul" },
                    .origin_location = .{ .start = offset + 1, .end = offset + 4, .source_name = "origin.sol" },
                    .ast_id = @intCast(index + 100),
                };
                item.jump_type = if (index % 2 == 0) .IntoFunction else .OutOfFunction;
                item.pushed_value = index + 7;
                item.immutable_occurrences = index + 1;
                item.modifier_depth = index + 2;
            }
            var wanted: std.ArrayList(AssemblyItem) = .empty;
            defer wanted.deinit(allocator);
            for (expected) |value| try wanted.append(allocator, switch (value) {
                .kept => |index| items.items[index],
                .generated => |instruction| AssemblyItem.initInstruction(instruction.opcode, if (instruction.debug_index) |index| items.items[index].debug_data else .{}),
            });
            const original_pointer = items.items.ptr;
            const original_capacity = items.capacity;
            try std.testing.expectEqual(changed, try optimise(allocator, &items, version));
            try std.testing.expectEqualDeep(wanted.items, items.items);
            if (!changed) {
                try std.testing.expectEqual(original_pointer, items.items.ptr);
                try std.testing.expectEqual(original_capacity, items.capacity);
            }
        }
    };
    const o = Check.op;
    const p = Check.push;
    const t = Check.tag;
    const pt = Check.pushTag;
    const k = Check.keep;
    const g = Check.generated;
    const london = EVMVersion.init(.London);
    try Check.run("push/pop", london, &.{ p(7), o(.POP) }, &.{}, true);
    try Check.run("operation/pop", london, &.{ o(.ADD), o(.POP) }, &.{ g(.POP, 0), g(.POP, 0) }, true);
    try Check.run("operation/stop", london, &.{ p(7), o(.STOP) }, &.{g(.STOP, 0)}, true);
    try Check.run("operation/return", london, &.{ p(7), p(0), o(.DUP1), o(.RETURN) }, &.{ k(1), k(2), k(3) }, true);
    try Check.run("operation/revert", london, &.{ o(.ADD), p(0), p(0), o(.REVERT) }, &.{ k(1), k(2), k(3) }, true);
    try Check.run("double push", london, &.{ p(256), p(256) }, &.{ k(0), g(.DUP1, 1) }, true);
    try Check.run("pre-PUSH0 double-zero rewrite", london, &.{ p(0), p(0) }, &.{ k(0), g(.DUP1, 1) }, true);
    try Check.run("PUSH0 double push rejected", .init(.Shanghai), &.{ p(0), p(0) }, &.{ k(0), k(1) }, false);
    try Check.run("double swap", london, &.{ o(.SWAP2), o(.SWAP2) }, &.{}, true);
    try Check.run("commutative swap", london, &.{ o(.SWAP1), o(.ADD) }, &.{k(1)}, true);
    try Check.run("swap comparison", london, &.{ o(.SWAP1), o(.LT) }, &.{g(.GT, null)}, true);
    try Check.run("dup/swap", london, &.{ o(.DUP2), o(.SWAP2) }, &.{k(0)}, true);
    try Check.run("double iszero jumpi", london, &.{ o(.ISZERO), o(.ISZERO), pt(2), o(.JUMPI) }, &.{ k(2), k(3) }, true);
    try Check.run("eq/iszero jumpi", london, &.{ o(.EQ), o(.ISZERO), pt(2), o(.JUMPI) }, &.{ g(.SUB, 0), k(2), k(3) }, true);
    try Check.run("double jump", london, &.{ pt(2), o(.JUMPI), pt(3), o(.JUMP), t(2) }, &.{ g(.ISZERO, 1), k(2), k(1), k(4) }, true);
    try Check.run("jump to next", london, &.{ pt(2), o(.JUMP), t(2) }, &.{k(2)}, true);
    try Check.run("conditional jump to next", london, &.{ pt(2), o(.JUMPI), t(2) }, &.{ g(.POP, 1), k(2) }, true);
    try Check.run("unreachable code", london, &.{ o(.STOP), p(5), t(6) }, &.{ k(0), k(2) }, true);
    try Check.run("deduplicate three", london, &.{ o(.SSTORE), p(0), o(.DUP1), o(.RETURN), t(2), p(0), o(.DUP1), o(.RETURN) }, &.{ k(0), k(4), k(5), k(6), k(7) }, true);
    try Check.run("deduplicate two", london, &.{ o(.SSTORE), p(9), o(.STOP), t(2), p(9), o(.STOP) }, &.{ k(0), k(3), k(4), k(5) }, true);
    try Check.run("jump is not a terminating suffix", london, &.{ o(.SSTORE), pt(9), o(.JUMP), t(2), pt(9), o(.JUMP) }, &.{ k(0), k(1), k(2), k(3), k(4), k(5) }, false);
    try Check.run("deduplicate one", london, &.{ o(.SSTORE), o(.STOP), t(2), o(.STOP) }, &.{ k(0), k(2), k(3) }, true);
    try Check.run("tag/mask conjunction", london, &.{ pt(2), p(0xffff_ffff), o(.AND) }, &.{k(0)}, true);
    try Check.run("mask/tag conjunction", london, &.{ p(0xffff_ffff), pt(2), o(.AND) }, &.{k(1)}, true);
    try Check.run("truthy conjunction", london, &.{ p(0), o(.NOT), o(.AND) }, &.{}, true);
    try Check.run("expanding prefix then shrink", london, &.{ o(.ADDMOD), o(.POP), p(7), o(.POP) }, &.{ g(.POP, 0), g(.POP, 0), g(.POP, 0) }, true);
    try Check.run("whole expansion rejected", london, &.{ o(.MULMOD), o(.POP) }, &.{ k(0), k(1) }, false);
    try Check.run("identity", london, &.{ o(.SLOAD), t(2), o(.SSTORE) }, &.{ k(0), k(1), k(2) }, false);
    try Check.run("empty", london, &.{}, &.{}, false);
    // Earlier rules win even where a suffix-deduplication rule also matches.
    try Check.run("return precedes deduplication", london, &.{ p(7), p(0), o(.DUP1), o(.RETURN), t(2), p(0), o(.DUP1), o(.RETURN) }, &.{ k(1), k(2), k(3), k(4), k(5), k(6), k(7) }, true);
}

test "peephole validation depends on final candidate instruction count" {
    const allocator = std.testing.allocator;
    const bad = AssemblyItem.initType(.UndefinedItem, 0, .{});
    const malformed_verbatim = AssemblyItem.initType(.VerbatimBytecode, 0, .{});
    const push = AssemblyItem.initPush(7, .{});
    const pop = AssemblyItem.initInstruction(.POP, .{});
    const add = AssemblyItem.initInstruction(.ADD, .{});
    const addmod = AssemblyItem.initInstruction(.ADDMOD, .{});
    const Case = struct { input: []const AssemblyItem, invalid: bool, changed: bool, length: usize };
    for ([_]Case{
        .{ .input = &.{bad}, .invalid = true, .changed = false, .length = 1 },
        .{ .input = &.{malformed_verbatim}, .invalid = true, .changed = false, .length = 1 },
        .{ .input = &.{ bad, add, pop }, .invalid = true, .changed = false, .length = 3 },
        .{ .input = &.{ bad, push, pop }, .invalid = false, .changed = true, .length = 1 },
        .{ .input = &.{ bad, addmod, pop }, .invalid = false, .changed = false, .length = 3 },
    }) |case| {
        var items: std.ArrayList(AssemblyItem) = .empty;
        defer deinitItems(allocator, &items);
        try items.appendSlice(allocator, case.input);
        const original_pointer = items.items.ptr;
        if (case.invalid)
            try std.testing.expectError(error.InvalidItem, optimise(allocator, &items, .current()))
        else
            try std.testing.expectEqual(case.changed, try optimise(allocator, &items, .current()));
        try std.testing.expectEqual(case.length, items.items.len);
        if (!case.changed) {
            try std.testing.expectEqual(original_pointer, items.items.ptr);
            try std.testing.expectEqualDeep(case.input, items.items);
        }
    }
}

test "peephole transfers payload owners and reserves before mutation" {
    const Check = struct {
        const Case = enum { identity, shrink, expanding_prefix, expanding_twice, shrink_then_expand, same_length_growth, expansion_rejected, deduplication, empty };
        const Input = union(enum) { operation: InstructionModule.Instruction, push: u256, tag: u256, payload: []const u8 };

        fn make(allocator: std.mem.Allocator, case: Case, spare_capacity: bool) !std.ArrayList(AssemblyItem) {
            const input: []const Input = switch (case) {
                .identity => &.{ .{ .payload = "keep" }, .{ .tag = 1 }, .{ .operation = .SSTORE } },
                .shrink => &.{ .{ .payload = "first" }, .{ .operation = .STOP }, .{ .payload = "drop" }, .{ .tag = 1 }, .{ .payload = "last" } },
                .expanding_prefix => &.{ .{ .payload = "first" }, .{ .operation = .ADDMOD }, .{ .operation = .POP }, .{ .push = 7 }, .{ .operation = .POP }, .{ .payload = "last" } },
                .expanding_twice => &.{ .{ .payload = "first" }, .{ .operation = .ADDMOD }, .{ .operation = .POP }, .{ .operation = .MULMOD }, .{ .operation = .POP }, .{ .push = 7 }, .{ .operation = .POP }, .{ .push = 8 }, .{ .operation = .POP }, .{ .payload = "last" } },
                .shrink_then_expand => &.{ .{ .payload = "first" }, .{ .push = 7 }, .{ .operation = .POP }, .{ .operation = .ADDMOD }, .{ .operation = .POP }, .{ .payload = "last" } },
                .same_length_growth => &.{ .{ .payload = "first" }, .{ .operation = .ADDMOD }, .{ .operation = .POP }, .{ .operation = .SWAP1 }, .{ .operation = .ADD }, .{ .payload = "last" } },
                .expansion_rejected => &.{ .{ .payload = "first" }, .{ .operation = .MULMOD }, .{ .operation = .POP }, .{ .payload = "last" } },
                .deduplication => &.{ .{ .payload = "prefix" }, .{ .payload = "duplicate" }, .{ .push = 0 }, .{ .operation = .RETURN }, .{ .tag = 2 }, .{ .payload = "duplicate" }, .{ .push = 0 }, .{ .operation = .RETURN } },
                .empty => &.{ .{ .push = 7 }, .{ .operation = .POP } },
            };
            var items: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent cleanup releases the container and owned payloads on failure
            errdefer deinitItems(allocator, &items);
            try items.ensureTotalCapacityPrecise(allocator, input.len + @as(usize, if (spare_capacity) 16 else 0));
            for (input, 0..) |value, index| {
                var item = switch (value) {
                    .operation => |opcode| AssemblyItem.initInstruction(opcode, .{}),
                    .push => |word| AssemblyItem.initPush(word, .{}),
                    .tag => |tag| AssemblyItem.initType(.Tag, tag, .{}),
                    .payload => |bytes| try AssemblyItem.initVerbatim(allocator, bytes, index, index + 1),
                };
                // The repeated payloads must compare equal for suffix matching.
                if (case == .deduplication and (index == 1 or index == 5)) {
                    item.verbatim.?.arguments = 0;
                    item.verbatim.?.return_variables = 1;
                }
                item.debug_data = .{ .ast_id = @intCast(index + 100) };
                item.modifier_depth = index + 7;
                items.appendAssumeCapacity(item);
            }
            return items;
        }

        fn run(allocator: std.mem.Allocator, case: Case, spare_capacity: bool, allow_resize: bool) !void {
            var items = try make(allocator, case, spare_capacity);
            defer deinitItems(allocator, &items);
            // Borrow descriptors only. Failure must preserve these owners;
            // success checks retained pointers before inspecting their payloads.
            const original = try allocator.dupe(AssemblyItem, items.items);
            defer allocator.free(original);
            const original_pointer = items.items.ptr;
            const original_capacity = items.capacity;
            var measured = std.testing.FailingAllocator.init(allocator, .{
                .resize_fail_index = if (allow_resize) std.math.maxInt(usize) else 0,
            });
            const changed = optimise(measured.allocator(), &items, .current()) catch |err| {
                try std.testing.expectEqual(original_pointer, items.items.ptr);
                try std.testing.expectEqual(original_capacity, items.capacity);
                try std.testing.expectEqualDeep(original, items.items);
                return err;
            };
            try std.testing.expectEqual(case != .identity and case != .expansion_rejected, changed);
            const indices: []const ?usize = switch (case) {
                .identity => &.{ 0, 1, 2 },
                .shrink => &.{ 0, 1, 3, 4 },
                .expanding_prefix => &.{ 0, null, null, null, 5 },
                .expanding_twice => &.{ 0, null, null, null, null, null, null, 9 },
                .shrink_then_expand => &.{ 0, null, null, null, 5 },
                .same_length_growth => &.{ 0, null, null, null, 4, 5 },
                .expansion_rejected => &.{ 0, 1, 2, 3 },
                .deduplication => &.{ 0, 4, 5, 6, 7 },
                .empty => &.{},
            };
            try std.testing.expectEqual(indices.len, items.items.len);
            for (indices, items.items, 0..) |source, *actual, position| {
                if (source) |index| {
                    if (original[index].verbatim) |verbatim|
                        try std.testing.expectEqual(verbatim.data.ptr, actual.verbatim.?.data.ptr);
                    try std.testing.expectEqualDeep(original[index], actual.*);
                } else {
                    const debug_index: usize = if (case == .shrink_then_expand or (case == .expanding_twice and position >= 4)) 3 else 1;
                    const wanted = AssemblyItem.initInstruction(.POP, original[debug_index].debug_data);
                    try std.testing.expectEqualDeep(wanted, actual.*);
                }
            }
            const headroom: usize = switch (case) {
                .expanding_prefix, .same_length_growth => 1,
                .expanding_twice => 2,
                else => 0,
            };
            if (headroom != 0 and !spare_capacity) {
                if (measured.allocations == 0) {
                    try std.testing.expect(allow_resize);
                    try std.testing.expectEqual(original_pointer, items.items.ptr);
                    try std.testing.expectEqual(original.len + headroom, items.capacity);
                    try std.testing.expectEqual(headroom * @sizeOf(AssemblyItem), measured.allocated_bytes);
                } else {
                    try std.testing.expectEqual(@as(usize, 1), measured.allocations);
                    try std.testing.expectEqual(indices.len, items.capacity);
                    try std.testing.expectEqual(indices.len * @sizeOf(AssemblyItem), measured.allocated_bytes);
                }
            } else {
                try std.testing.expectEqual(@as(usize, 0), measured.allocations);
                try std.testing.expectEqual(@as(usize, 0), measured.allocated_bytes);
                if (case == .empty)
                    try std.testing.expectEqual(@as(usize, 0), items.capacity)
                else {
                    try std.testing.expectEqual(original_pointer, items.items.ptr);
                    try std.testing.expectEqual(original_capacity, items.capacity);
                }
            }
        }
    };
    for (std.enums.values(Check.Case)) |case| {
        for ([_]bool{ false, true }) |spare_capacity| {
            for ([_]bool{ false, true }) |allow_resize|
                try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{ case, spare_capacity, allow_resize });
        }
    }
}
