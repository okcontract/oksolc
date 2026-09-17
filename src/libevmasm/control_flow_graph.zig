// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Control-flow splitting, reachability, and joined-state analysis.

const std = @import("std");
const cxx = @import("cxx_compat");
const AssemblyItem = @import("assembly_item.zig").AssemblyItem;
const KnownStateModule = @import("known_state.zig");
const KnownState = KnownStateModule.KnownState;
const SemanticInformation = @import("semantic_information.zig");

pub const BlockId = struct {
    value: u32 = std.math.maxInt(u32),

    pub fn init(value: u32) BlockId {
        return .{ .value = value };
    }

    pub fn fromWord(value: u256) CFGError!BlockId {
        if (value >= initial().value) return error.TagNumberTooLarge;
        return .{ .value = @intCast(value) };
    }

    pub fn initial() BlockId {
        return .{ .value = std.math.maxInt(u32) - 1 };
    }

    pub fn invalid() BlockId {
        return .{};
    }

    pub fn isValid(self: BlockId) bool {
        return self.value != invalid().value;
    }

    pub fn eql(self: BlockId, other: BlockId) bool {
        return self.value == other.value;
    }

    pub fn lessThan(self: BlockId, other: BlockId) bool {
        return self.value < other.value;
    }
};

pub const BasicBlock = struct {
    begin: u32 = 0,
    end: u32 = 0,
    pushed_tags: std.ArrayList(BlockId) = .empty,
    next: BlockId = BlockId.invalid(),
    prev: BlockId = BlockId.invalid(),
    end_type: EndType = .Handover,
    start_state: ?KnownState = null,
    end_state: ?KnownState = null,

    pub const EndType = enum(c_int) {
        Jump,
        JumpI,
        Stop,
        Handover,
    };

    pub fn deinit(self: *BasicBlock, allocator: std.mem.Allocator) void {
        if (self.start_state) |*state| state.deinit();
        if (self.end_state) |*state| state.deinit();
        self.pushed_tags.deinit(allocator);
        self.* = undefined;
    }

    fn clone(self: *const BasicBlock, allocator: std.mem.Allocator) std.mem.Allocator.Error!BasicBlock {
        var result: BasicBlock = .{
            .begin = self.begin,
            .end = self.end,
            .next = self.next,
            .prev = self.prev,
            .end_type = self.end_type,
        };
        errdefer result.deinit(allocator);
        try result.pushed_tags.appendSlice(allocator, self.pushed_tags.items);
        if (self.start_state) |*state| result.start_state = try state.clone();
        if (self.end_state) |*state| result.end_state = try state.clone();
        return result;
    }
};

pub const BasicBlocks = std.ArrayList(BasicBlock);

fn lessBlockId(left: BlockId, right: BlockId) bool {
    return left.lessThan(right);
}

fn lessU32(left: u32, right: u32) bool {
    return left < right;
}

const BlockMap = cxx.OrderedMap(BlockId, BasicBlock, lessBlockId);
const BlockSet = cxx.OrderedSet(BlockId, lessBlockId);
const PositionMap = cxx.OrderedMap(u32, BlockId, lessU32);

pub const CFGError = KnownStateModule.KnownStateError || std.mem.Allocator.Error || error{
    BlockNotFound,
    InvalidBlock,
    InvalidControlFlow,
    OutOfBlockIds,
    SuccessorAlreadyHasPredecessor,
    SuccessorBlockNotFound,
    TagNumberTooLarge,
};

pub const ControlFlowGraph = struct {
    allocator: std.mem.Allocator,
    last_used_id: u32 = 0,
    items: []const AssemblyItem,
    join_knowledge: bool = true,
    blocks: BlockMap = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        items: []const AssemblyItem,
        join_knowledge: bool,
    ) ControlFlowGraph {
        return .{
            .allocator = allocator,
            .items = items,
            .join_knowledge = join_knowledge,
        };
    }

    pub fn deinit(self: *ControlFlowGraph) void {
        self.clearBlocks();
        self.blocks.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn optimisedBlocks(self: *ControlFlowGraph) CFGError!BasicBlocks {
        if (self.items.len == 0) return .empty;
        try self.findLargestTag();
        try self.splitBlocks();
        try self.resolveNextLinks();
        try self.removeUnusedBlocks();
        try self.setPrevLinks();
        try self.gatherKnowledge();
        return self.rebuildCode();
    }

    fn clearBlocks(self: *ControlFlowGraph) void {
        for (self.blocks.mutableItems()) |*entry| entry.value.deinit(self.allocator);
        self.blocks.clearRetainingCapacity();
    }

    fn findLargestTag(self: *ControlFlowGraph) CFGError!void {
        self.last_used_id = 0;
        for (self.items) |*item| {
            if (item.item_type != .Tag and item.item_type != .PushTag) continue;
            const id = try BlockId.fromWord(item.data_value);
            self.last_used_id = @max(id.value, self.last_used_id);
        }
    }

    fn getOrPutBlock(self: *ControlFlowGraph, id: BlockId) std.mem.Allocator.Error!*BasicBlock {
        if (!self.blocks.contains(id)) _ = try self.blocks.insert(self.allocator, id, .{});
        return self.blocks.getPtr(id).?;
    }

    fn splitBlocks(self: *ControlFlowGraph) CFGError!void {
        self.clearBlocks();
        var id = BlockId.initial();
        (try self.getOrPutBlock(id)).begin = 0;
        for (self.items, 0..) |*item, index| {
            if (item.item_type == .Tag) {
                if (id.isValid()) (self.blocks.getPtr(id) orelse return error.BlockNotFound).end = @intCast(index);
                id = BlockId.invalid();
            }
            if (!id.isValid()) {
                id = if (item.item_type == .Tag)
                    try BlockId.fromWord(item.data_value)
                else
                    try self.generateNewId();
                (try self.getOrPutBlock(id)).begin = @intCast(index);
            }
            const block = self.blocks.getPtr(id) orelse return error.BlockNotFound;
            if (item.item_type == .PushTag)
                try block.pushed_tags.append(self.allocator, try BlockId.fromWord(item.data_value));
            if (SemanticInformation.altersControlFlow(item)) {
                block.end = @intCast(index + 1);
                block.end_type = if (item.eqlInstruction(.JUMP))
                    .Jump
                else if (item.eqlInstruction(.JUMPI))
                    .JumpI
                else
                    .Stop;
                id = BlockId.invalid();
            }
        }
        if (id.isValid()) {
            const block = self.blocks.getPtr(id) orelse return error.BlockNotFound;
            block.end = @intCast(self.items.len);
            if (block.end_type == .Handover) block.end_type = .Stop;
        }
    }

    fn resolveNextLinks(self: *ControlFlowGraph) CFGError!void {
        var block_by_begin: PositionMap = .{};
        defer block_by_begin.deinit(self.allocator);
        for (self.blocks.items()) |entry| {
            if (entry.value.begin != entry.value.end)
                _ = try block_by_begin.insert(self.allocator, entry.value.begin, entry.key);
        }
        for (self.blocks.mutableItems()) |*entry| {
            const block = &entry.value;
            if (block.end_type != .JumpI and block.end_type != .Handover) continue;
            block.next = (block_by_begin.get(block.end) orelse return error.SuccessorBlockNotFound).*;
        }
    }

    fn removeUnusedBlocks(self: *ControlFlowGraph) CFGError!void {
        var to_process: std.ArrayList(BlockId) = .empty;
        defer to_process.deinit(self.allocator);
        var needed: BlockSet = .{};
        defer needed.deinit(self.allocator);
        try to_process.append(self.allocator, BlockId.initial());
        _ = try needed.insert(self.allocator, BlockId.initial());
        while (to_process.pop()) |id| {
            const block = self.blocks.get(id) orelse return error.BlockNotFound;
            for (block.pushed_tags.items) |tag| {
                if (needed.contains(tag) or !self.blocks.contains(tag)) continue;
                _ = try needed.insert(self.allocator, tag);
                try to_process.append(self.allocator, tag);
            }
            if (block.next.isValid() and !needed.contains(block.next)) {
                _ = try needed.insert(self.allocator, block.next);
                try to_process.append(self.allocator, block.next);
            }
        }
        var index: usize = 0;
        while (index < self.blocks.entries.items.len) {
            if (needed.contains(self.blocks.entries.items[index].key)) {
                index += 1;
            } else {
                var removed = self.blocks.entries.orderedRemove(index);
                removed.value.deinit(self.allocator);
            }
        }
    }

    fn setPrevLinks(self: *ControlFlowGraph) CFGError!void {
        var index: usize = 0;
        while (index < self.blocks.entries.items.len) : (index += 1) {
            const next = self.blocks.entries.items[index].value.next;
            const end_type = self.blocks.entries.items[index].value.end_type;
            if (end_type != .JumpI and end_type != .Handover) continue;
            const successor = self.blocks.getPtr(next) orelse return error.BlockNotFound;
            if (successor.prev.isValid()) return error.SuccessorAlreadyHasPredecessor;
            successor.prev = self.blocks.entries.items[index].key;
        }

        index = 0;
        while (index < self.blocks.entries.items.len) : (index += 1) {
            const block_id = self.blocks.entries.items[index].key;
            const block = &self.blocks.entries.items[index].value;
            if (block.end_type != .Jump or block.end - block.begin < 2) continue;
            const push = &self.items[block.end - 2];
            if (push.item_type != .PushTag) continue;
            const next_id = try BlockId.fromWord(push.data_value);
            if (self.blocks.get(next_id)) |next_block| if (next_block.prev.isValid()) continue;

            var has_loop = false;
            var cursor = next_id;
            while (cursor.isValid() and self.blocks.get(cursor) != null and !has_loop) {
                has_loop = cursor.eql(block_id);
                cursor = self.blocks.get(cursor).?.next;
            }
            if (has_loop or !self.blocks.contains(next_id)) continue;

            self.blocks.getPtr(next_id).?.prev = block_id;
            block.next = next_id;
            block.end -= 2;
            if (block.pushed_tags.items.len == 0 or
                !block.pushed_tags.items[block.pushed_tags.items.len - 1].eql(next_id))
                return error.InvalidControlFlow;
            _ = block.pushed_tags.pop();
            block.end_type = .Handover;
        }
    }

    const WorkQueueItem = struct {
        block_id: BlockId,
        state: KnownState,
        blocks_seen: BlockSet = .{},

        fn deinit(self: *WorkQueueItem, allocator: std.mem.Allocator) void {
            self.blocks_seen.deinit(allocator);
            self.state.deinit();
            self.* = undefined;
        }
    };

    fn appendWork(
        self: *ControlFlowGraph,
        queue: *std.ArrayList(WorkQueueItem),
        current: *const WorkQueueItem,
        to: BlockId,
        state: *const KnownState,
    ) std.mem.Allocator.Error!void {
        var next_state = try state.clone();
        errdefer next_state.deinit();
        var seen = try current.blocks_seen.clone(self.allocator);
        errdefer seen.deinit(self.allocator);
        _ = try seen.insert(self.allocator, current.block_id);
        try queue.append(self.allocator, .{
            .block_id = to,
            .state = next_state,
            .blocks_seen = seen,
        });
    }

    fn appendEmptyWork(
        self: *ControlFlowGraph,
        queue: *std.ArrayList(WorkQueueItem),
        id: BlockId,
        empty_state: *const KnownState,
    ) std.mem.Allocator.Error!void {
        var state = try empty_state.clone();
        errdefer state.deinit();
        try queue.append(self.allocator, .{ .block_id = id, .state = state });
    }

    fn gatherKnowledge(self: *ControlFlowGraph) CFGError!void {
        var empty_state = try KnownState.init(self.allocator);
        defer empty_state.deinit();
        var unknown_jump_encountered = false;
        var work_queue: std.ArrayList(WorkQueueItem) = .empty;
        defer {
            for (work_queue.items) |*item| item.deinit(self.allocator);
            work_queue.deinit(self.allocator);
        }
        try self.appendEmptyWork(&work_queue, BlockId.initial(), &empty_state);

        while (work_queue.pop()) |popped| {
            var item = popped;
            defer item.deinit(self.allocator);
            if (!item.block_id.isValid()) return error.InvalidBlock;
            const block = self.blocks.getPtr(item.block_id) orelse continue;
            if (block.start_state) |*start_state| {
                if (!self.join_knowledge) item.state.reset();
                try item.state.reduceToCommonKnowledge(start_state, !item.blocks_seen.contains(item.block_id));
                if (item.state.eql(start_state)) continue;
            }
            if (block.start_state) |*old| old.deinit();
            block.start_state = try item.state.clone();

            var pc: u32 = block.begin;
            while (pc < block.end and !SemanticInformation.altersControlFlow(&self.items[pc])) : (pc += 1)
                _ = try item.state.feedItem(&self.items[pc], false);

            if (block.end_type == .Jump or block.end_type == .JumpI) {
                if (block.begin > pc or pc != block.end - 1) return error.InvalidControlFlow;
                const target = try item.state.stackElement(item.state.stack_height, .{});
                var tags = try item.state.tagsInExpression(target);
                defer tags.deinit(self.allocator);
                _ = try item.state.feedItem(&self.items[pc], false);
                pc += 1;

                if (tags.isEmpty()) {
                    if (!unknown_jump_encountered) {
                        unknown_jump_encountered = true;
                        for (self.blocks.items()) |entry| {
                            if (entry.value.begin < entry.value.end and self.items[entry.value.begin].item_type == .Tag)
                                try self.appendEmptyWork(&work_queue, entry.key, &empty_state);
                        }
                    }
                } else {
                    for (tags.map.items()) |tag|
                        try self.appendWork(&work_queue, &item, try BlockId.fromWord(tag.key), &item.state);
                }
            } else if (block.begin <= pc and pc < block.end) {
                _ = try item.state.feedItem(&self.items[pc], false);
                pc += 1;
            }
            if (block.end > block.begin and pc != block.end) return error.InvalidControlFlow;

            if (block.end_state) |*old| old.deinit();
            block.end_state = try item.state.clone();
            if (block.end_type == .Handover or block.end_type == .JumpI)
                try self.appendWork(&work_queue, &item, block.next, &item.state);
        }

        var index: usize = 0;
        while (index < self.blocks.entries.items.len) {
            if (self.blocks.entries.items[index].value.start_state != null) {
                index += 1;
            } else {
                var removed = self.blocks.entries.orderedRemove(index);
                removed.value.deinit(self.allocator);
            }
        }
    }

    fn rebuildCode(self: *ControlFlowGraph) CFGError!BasicBlocks {
        const PushMap = cxx.OrderedMap(BlockId, u32, lessBlockId);
        var pushes: PushMap = .{};
        defer pushes.deinit(self.allocator);
        for (self.blocks.items()) |entry| {
            for (entry.value.pushed_tags.items) |reference| {
                if (!self.blocks.contains(reference)) continue;
                if (pushes.getPtr(reference)) |count| count.* += 1 else _ = try pushes.insert(self.allocator, reference, 1);
            }
        }

        var blocks_to_add: BlockSet = .{};
        defer blocks_to_add.deinit(self.allocator);
        for (self.blocks.items()) |entry| _ = try blocks_to_add.insert(self.allocator, entry.key);

        var result: BasicBlocks = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitBasicBlocks(self.allocator, &result);
        var block_id = BlockId.initial();
        while (block_id.isValid()) {
            var previous_handed_over = block_id.eql(BlockId.initial());
            while ((self.blocks.get(block_id) orelse return error.BlockNotFound).prev.isValid())
                block_id = self.blocks.get(block_id).?.prev;

            while (block_id.isValid()) {
                const block = self.blocks.getPtr(block_id) orelse return error.BlockNotFound;
                _ = blocks_to_add.remove(block_id);
                if (block.begin != block.end) {
                    if (previous_handed_over and !pushes.contains(block_id) and
                        self.items[block.begin].item_type == .Tag)
                        block.begin += 1;
                    if (block.begin < block.end) {
                        var copy = try block.clone(self.allocator);
                        errdefer copy.deinit(self.allocator);
                        copy.start_state.?.clearTagUnions();
                        copy.end_state.?.clearTagUnions();
                        try result.append(self.allocator, copy);
                    }
                }
                previous_handed_over = block.end_type == .Handover;
                block_id = block.next;
            }
            block_id = if (blocks_to_add.isEmpty()) BlockId.invalid() else blocks_to_add.at(0);
        }
        return result;
    }

    fn generateNewId(self: *ControlFlowGraph) CFGError!BlockId {
        if (self.last_used_id == std.math.maxInt(u32)) return error.OutOfBlockIds;
        self.last_used_id += 1;
        const id = BlockId.init(self.last_used_id);
        if (!id.lessThan(BlockId.initial())) return error.OutOfBlockIds;
        return id;
    }
};

pub fn deinitBasicBlocks(allocator: std.mem.Allocator, blocks: *BasicBlocks) void {
    for (blocks.items) |*block| block.deinit(allocator);
    blocks.deinit(allocator);
    blocks.* = .empty;
}

test "control-flow graph removes unreachable blocks and joins conditional paths" {
    const I = AssemblyItem;
    const items = [_]I{
        I.initPush(1, .{}),
        I.initType(.PushTag, 1, .{}),
        I.initInstruction(.JUMPI, .{}),
        I.initPush(9, .{}),
        I.initType(.PushTag, 2, .{}),
        I.initInstruction(.JUMP, .{}),
        I.initType(.Tag, 1, .{}),
        I.initPush(7, .{}),
        I.initType(.Tag, 2, .{}),
        I.initInstruction(.STOP, .{}),
        I.initType(.Tag, 99, .{}),
        I.initInstruction(.STOP, .{}),
    };
    var graph = ControlFlowGraph.init(std.testing.allocator, &items, true);
    defer graph.deinit();
    var blocks = try graph.optimisedBlocks();
    defer deinitBasicBlocks(std.testing.allocator, &blocks);
    try std.testing.expect(blocks.items.len >= 3);
    for (blocks.items) |block| try std.testing.expect(block.begin < 10);
}
