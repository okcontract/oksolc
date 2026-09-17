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

pub fn optimise(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(AssemblyItem),
    evm_version: EVMVersion,
) (std.mem.Allocator.Error || error{ MissingImmutableOccurrences, InvalidItem })!bool {
    var optimized: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
    errdefer deinitItems(allocator, &optimized);

    var index: usize = 0;
    while (index < items.items.len) {
        index += try applyAt(allocator, items.items, index, &optimized, evm_version);
    }

    const accept = optimized.items.len < items.items.len or
        (optimized.items.len == items.items.len and
            ((try AssemblyItemModule.bytesRequired(optimized.items, 3, evm_version, .Approximate)) <
                (try AssemblyItemModule.bytesRequired(items.items, 3, evm_version, .Approximate)) or
                numberOfPops(optimized.items) > numberOfPops(items.items)));
    if (!accept) {
        deinitItems(allocator, &optimized);
        return false;
    }

    for (items.items) |*item| item.deinit(allocator);
    items.deinit(allocator);
    items.* = optimized;
    return true;
}

fn applyAt(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
    evm_version: EVMVersion,
) std.mem.Allocator.Error!usize {
    if (try pushPop(items, index)) return 2;
    if (try opPop(allocator, items, index, output)) return 2;
    if (try opStop(allocator, items, index, output)) return 2;
    if (try opReturnRevert(allocator, items, index, output)) return 4;
    if (try doublePush(allocator, items, index, output, evm_version)) return 2;
    if (doubleSwap(items, index)) return 2;
    if (try commutativeSwap(allocator, items, index, output)) return 2;
    if (try swapComparison(allocator, items, index, output)) return 2;
    if (try dupSwap(allocator, items, index, output)) return 2;
    if (try isZeroIsZeroJumpI(allocator, items, index, output)) return 4;
    if (try eqIsZeroJumpI(allocator, items, index, output)) return 4;
    if (try doubleJump(allocator, items, index, output)) return 5;
    if (try jumpToNext(allocator, items, index, output)) return 3;
    if (try unreachableCode(allocator, items, index, output)) |consumed| return consumed;
    if (try deduplicateNextTag3(allocator, items, index, output)) return 8;
    if (try deduplicateNextTag2(allocator, items, index, output)) return 6;
    if (try deduplicateNextTag1(allocator, items, index, output)) return 4;
    if (try tagConjunctions(allocator, items, index, output)) return 3;
    if (truthyAnd(items, index)) return 3;
    try appendClone(allocator, output, &items[index]);
    return 1;
}

fn hasWindow(items: []const AssemblyItem, index: usize, size: usize) bool {
    return index <= items.len and size <= items.len - index;
}

fn pushPop(items: []const AssemblyItem, index: usize) !bool {
    if (!hasWindow(items, index, 2)) return false;
    const push = &items[index];
    const pop = &items[index + 1];
    return pop.eqlInstruction(.POP) and (SemanticInformation.isDupItem(push) or switch (push.item_type) {
        .Push, .PushTag, .PushSub, .PushSubSize, .PushProgramSize, .PushData, .PushLibraryAddress => true,
        else => false,
    });
}

fn opPop(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 2) or !items[index + 1].eqlInstruction(.POP) or
        items[index].item_type != .Operation)
    {
        return false;
    }
    const info = InstructionModule.instructionInfo(items[index].instruction_value.?, EVMVersion.current());
    if (info.ret != 1 or info.side_effects) return false;
    for (0..info.args) |_| {
        try output.append(allocator, AssemblyItem.initInstruction(.POP, items[index].debug_data));
    }
    return true;
}

fn opStop(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 2) or !items[index + 1].eqlInstruction(.STOP)) return false;
    const operation = &items[index];
    if (operation.item_type == .Operation) {
        if (InstructionModule.instructionInfo(operation.instruction_value.?, EVMVersion.current()).side_effects) {
            return false;
        }
    } else if (operation.item_type != .Push) return false;
    try output.append(allocator, AssemblyItem.initInstruction(.STOP, operation.debug_data));
    return true;
}

fn opReturnRevert(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
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
    try appendClone(allocator, output, push);
    try appendClone(allocator, output, push_or_dup);
    try appendClone(allocator, output, terminator);
    return true;
}

fn doublePush(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
    evm_version: EVMVersion,
) !bool {
    if (!hasWindow(items, index, 2)) return false;
    const first = &items[index];
    const second = &items[index + 1];
    if (first.item_type != .Push or second.item_type != .Push or
        first.data_value != second.data_value or
        (evm_version.hasPush0() and first.data_value == 0))
    {
        return false;
    }
    try appendClone(allocator, output, first);
    try output.append(allocator, AssemblyItem.initInstruction(.DUP1, second.debug_data));
    return true;
}

fn doubleSwap(items: []const AssemblyItem, index: usize) bool {
    return hasWindow(items, index, 2) and
        items[index].eql(&items[index + 1]) and
        SemanticInformation.isSwapItem(&items[index]);
}

fn commutativeSwap(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 2) or
        !items[index].eqlInstruction(.SWAP1) or
        !SemanticInformation.isCommutativeOperation(&items[index + 1]))
    {
        return false;
    }
    try appendClone(allocator, output, &items[index + 1]);
    return true;
}

fn swapComparison(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
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
    try output.append(allocator, AssemblyItem.initInstruction(replacement, .{}));
    return true;
}

fn dupSwap(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 2) or
        !SemanticInformation.isDupItem(&items[index]) or
        !SemanticInformation.isSwapItem(&items[index + 1]) or
        (SemanticInformation.getDupNumber(&items[index]) catch unreachable) != // zlinter-disable-current-line no_swallow_error - opcode category predicates prove the conversion valid
            (SemanticInformation.getSwapNumber(&items[index + 1]) catch unreachable)) // zlinter-disable-current-line no_swallow_error - opcode category predicates prove the conversion valid
    {
        return false;
    }
    try appendClone(allocator, output, &items[index]);
    return true;
}

fn isZeroIsZeroJumpI(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 4) or
        !items[index].eqlInstruction(.ISZERO) or
        !items[index + 1].eqlInstruction(.ISZERO) or
        items[index + 2].item_type != .PushTag or
        !items[index + 3].eqlInstruction(.JUMPI))
    {
        return false;
    }
    try appendClone(allocator, output, &items[index + 2]);
    try appendClone(allocator, output, &items[index + 3]);
    return true;
}

fn eqIsZeroJumpI(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 4) or
        !items[index].eqlInstruction(.EQ) or
        !items[index + 1].eqlInstruction(.ISZERO) or
        items[index + 2].item_type != .PushTag or
        !items[index + 3].eqlInstruction(.JUMPI))
    {
        return false;
    }
    try output.append(allocator, AssemblyItem.initInstruction(.SUB, items[index].debug_data));
    try appendClone(allocator, output, &items[index + 2]);
    try appendClone(allocator, output, &items[index + 3]);
    return true;
}

fn doubleJump(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
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
    try output.append(allocator, AssemblyItem.initInstruction(.ISZERO, items[index + 1].debug_data));
    try appendClone(allocator, output, &items[index + 2]);
    try appendClone(allocator, output, &items[index + 1]);
    try appendClone(allocator, output, &items[index + 4]);
    return true;
}

fn jumpToNext(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 3) or
        items[index].item_type != .PushTag or
        (!items[index + 1].eqlInstruction(.JUMP) and !items[index + 1].eqlInstruction(.JUMPI)) or
        items[index + 2].item_type != .Tag or
        items[index].data_value != items[index + 2].data_value)
    {
        return false;
    }
    if (items[index + 1].eqlInstruction(.JUMPI)) {
        try output.append(allocator, AssemblyItem.initInstruction(.POP, items[index + 1].debug_data));
    }
    try appendClone(allocator, output, &items[index + 2]);
    return true;
}

fn unreachableCode(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !?usize {
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
    try appendClone(allocator, output, terminal);
    return count;
}

fn deduplicateNextTag3(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
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
        try appendClone(allocator, output, &items[item_index]);
    }
    return true;
}

fn deduplicateNextTag2(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 6) or items[index].item_type == .Tag or
        !items[index + 1].eql(&items[index + 4]) or
        !items[index + 2].eql(&items[index + 5]) or
        items[index + 3].item_type != .Tag or
        !SemanticInformation.terminatesControlFlowItem(&items[index + 2]))
    {
        return false;
    }
    for ([_]usize{ index, index + 3, index + 4, index + 5 }) |item_index| {
        try appendClone(allocator, output, &items[item_index]);
    }
    return true;
}

fn deduplicateNextTag1(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 4) or items[index].item_type == .Tag or
        !items[index + 1].eql(&items[index + 3]) or
        items[index + 2].item_type != .Tag or
        !SemanticInformation.terminatesControlFlowItem(&items[index + 1]))
    {
        return false;
    }
    for ([_]usize{ index, index + 2, index + 3 }) |item_index| {
        try appendClone(allocator, output, &items[item_index]);
    }
    return true;
}

fn tagConjunctions(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    index: usize,
    output: *std.ArrayList(AssemblyItem),
) !bool {
    if (!hasWindow(items, index, 3) or !items[index + 2].eqlInstruction(.AND)) return false;
    if (items[index].item_type == .PushTag and items[index + 1].item_type == .Push and
        (items[index + 1].data_value & 0xffff_ffff) == 0xffff_ffff)
    {
        try appendClone(allocator, output, &items[index]);
        return true;
    }
    if (items[index + 1].item_type == .PushTag and items[index].item_type == .Push and
        (items[index].data_value & 0xffff_ffff) == 0xffff_ffff)
    {
        try appendClone(allocator, output, &items[index + 1]);
        return true;
    }
    return false;
}

fn truthyAnd(items: []const AssemblyItem, index: usize) bool {
    return hasWindow(items, index, 3) and
        items[index].item_type == .Push and items[index].data_value == 0 and
        items[index + 1].eqlInstruction(.NOT) and items[index + 2].eqlInstruction(.AND);
}

fn appendClone(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(AssemblyItem),
    item: *const AssemblyItem,
) std.mem.Allocator.Error!void {
    const cloned = try item.clone(allocator);
    errdefer {
        var mutable = cloned;
        mutable.deinit(allocator);
    }
    try output.append(allocator, cloned);
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

test "PUSH0 prevents the double-zero rewrite from growing bytecode" {
    var items: std.ArrayList(AssemblyItem) = .empty;
    defer deinitItems(std.testing.allocator, &items);
    try items.appendSlice(std.testing.allocator, &.{
        AssemblyItem.initPush(0, .{}),
        AssemblyItem.initPush(0, .{}),
    });
    try std.testing.expect(!(try optimise(std.testing.allocator, &items, EVMVersion.init(.Shanghai))));
    try std.testing.expectEqual(@as(usize, 2), items.items.len);
}

test "verbatim ownership survives identity and unreachable-code passes" {
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
