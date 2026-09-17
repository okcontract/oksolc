// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Legacy assembly block and function-body inliner.

const std = @import("std");
const AssemblyItemModule = @import("assembly_item.zig");
const AssemblyItem = AssemblyItemModule.AssemblyItem;
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const GasMeterModule = @import("gas_meter.zig");
const KnownState = @import("known_state.zig").KnownState;
const SemanticInformation = @import("semantic_information.zig");

pub const Inliner = struct {
    allocator: std.mem.Allocator,
    items: *std.ArrayList(AssemblyItem),
    tags_referenced_from_outside: []const usize,
    runs: u64 = 200,
    is_creation: bool = false,
    evm_version: EVMVersion,

    const InlinableBlock = struct {
        tag: usize,
        begin: usize,
        end: usize,
        push_tag_count: u64,
    };

    pub fn init(
        allocator: std.mem.Allocator,
        items: *std.ArrayList(AssemblyItem),
        tags_referenced_from_outside: []const usize,
        runs: u64,
        is_creation: bool,
        evm_version: EVMVersion,
    ) Inliner {
        return .{
            .allocator = allocator,
            .items = items,
            .tags_referenced_from_outside = tags_referenced_from_outside,
            .runs = runs,
            .is_creation = is_creation,
            .evm_version = evm_version,
        };
    }

    pub fn optimise(self: *Inliner) !void {
        var blocks = try self.determineInlinableBlocks();
        defer blocks.deinit(self.allocator);
        if (blocks.items.len == 0) return;

        var new_items: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitItems(self.allocator, &new_items);
        var index: usize = 0;
        while (index < self.items.items.len) : (index += 1) {
            const item = &self.items.items[index];
            if (index + 1 < self.items.items.len and item.item_type == .PushTag and
                self.items.items[index + 1].eqlInstruction(.JUMP))
            {
                if (getLocalTag(item)) |tag| {
                    if (findBlock(&blocks, tag)) |block| {
                        if (try self.shouldInline(tag, &self.items.items[index + 1], block)) |exit_item| {
                            for (self.items.items[block.begin .. block.end - 1]) |*inlined|
                                try appendClone(self.allocator, &new_items, inlined);
                            try appendClone(self.allocator, &new_items, &exit_item);

                            block.push_tag_count -= 1;
                            for (self.items.items[block.begin..block.end]) |*inlined| {
                                if (inlined.item_type != .PushTag) continue;
                                if (getLocalTag(inlined)) |duplicated_tag| {
                                    if (findBlock(&blocks, duplicated_tag)) |duplicated_block| {
                                        duplicated_block.push_tag_count += 1;
                                    }
                                }
                            }
                            index += 1;
                            continue;
                        }
                    }
                }
            }
            try appendClone(self.allocator, &new_items, item);
        }

        deinitItems(self.allocator, self.items);
        self.items.* = new_items;
    }

    fn isInlineCandidate(self: *const Inliner, tag: usize, items: []const AssemblyItem) bool {
        _ = self;
        std.debug.assert(items.len != 0);
        const last = &items[items.len - 1];
        if (last.item_type != .Operation) return false;
        if (!last.eqlInstruction(.JUMP) and !SemanticInformation.terminatesControlFlow(last.instruction_value.?))
            return false;
        for (items) |*item| {
            if (item.item_type == .PushTag and getLocalTag(item) == tag) return false;
        }
        return true;
    }

    fn determineInlinableBlocks(self: *const Inliner) std.mem.Allocator.Error!std.ArrayList(InlinableBlock) {
        const TagCount = struct { tag: usize, count: u64 };
        var candidates: std.ArrayList(InlinableBlock) = .empty;
        errdefer candidates.deinit(self.allocator);
        var counts: std.ArrayList(TagCount) = .empty;
        defer counts.deinit(self.allocator);
        var last_tag: ?usize = null;
        for (self.items.items, 0..) |*item, index| {
            if (item.item_type == .PushTag) {
                if (getLocalTag(item)) |tag| {
                    const position = searchTagCount(counts.items, tag);
                    if (position.found) counts.items[position.index].count += 1 else try counts.insert(self.allocator, position.index, .{ .tag = tag, .count = 1 });
                }
            }

            if (last_tag) |tag_index| {
                if (SemanticInformation.breaksCSEAnalysisBlock(item, false)) {
                    const block = self.items.items[tag_index + 1 .. index + 1];
                    if (getLocalTag(&self.items.items[tag_index])) |tag| {
                        if (self.isInlineCandidate(tag, block)) {
                            const existing = searchBlock(candidates.items, tag);
                            const candidate: InlinableBlock = .{
                                .tag = tag,
                                .begin = tag_index + 1,
                                .end = index + 1,
                                .push_tag_count = 0,
                            };
                            if (existing.found)
                                candidates.items[existing.index] = candidate
                            else
                                try candidates.insert(self.allocator, existing.index, candidate);
                        }
                    }
                    last_tag = null;
                }
            }
            if (item.item_type == .Tag) {
                std.debug.assert(getLocalTag(item) != null);
                last_tag = index;
            }
        }

        var index: usize = 0;
        while (index < candidates.items.len) {
            const count = searchTagCount(counts.items, candidates.items[index].tag);
            if (!count.found) {
                _ = candidates.orderedRemove(index);
            } else {
                candidates.items[index].push_tag_count = counts.items[count.index].count;
                index += 1;
            }
        }
        return candidates;
    }

    fn shouldInlineFullFunctionBody(
        self: *const Inliner,
        tag: usize,
        block: []const AssemblyItem,
        push_tag_count: u64,
    ) !bool {
        const function_body_size = try codeSize(block[0 .. block.len - 1], self.evm_version);
        const call_site_pattern = [_]AssemblyItem{
            AssemblyItem.initType(.PushTag, 0, .{}),
            AssemblyItem.initType(.PushTag, 0, .{}),
            AssemblyItem.initInstruction(.JUMP, .{}),
            AssemblyItem.initType(.Tag, 0, .{}),
        };
        const function_pattern = [_]AssemblyItem{
            AssemblyItem.initType(.Tag, 0, .{}),
            AssemblyItem.initInstruction(.JUMP, .{}),
        };
        const uninlined_execution_cost = @as(u512, push_tag_count) *
            (@as(u512, try executionCost(self.allocator, &call_site_pattern, self.evm_version)) +
                @as(u512, try executionCost(self.allocator, &function_pattern, self.evm_version)));
        const call_site_size = try codeSize(&call_site_pattern, self.evm_version);
        const function_pattern_size = try codeSize(&function_pattern, self.evm_version);
        const uninlined_size = push_tag_count * call_site_size + function_pattern_size + function_body_size;
        const uninlined_deposit_cost = GasMeterModule.dataGasLength(
            uninlined_size,
            self.is_creation,
            self.evm_version,
        );
        var inlined_deposit_cost = GasMeterModule.dataGasLength(
            push_tag_count * function_body_size,
            self.is_creation,
            self.evm_version,
        );
        if (containsTag(self.tags_referenced_from_outside, tag))
            inlined_deposit_cost += GasMeterModule.dataGasLength(
                function_pattern_size + function_body_size,
                self.is_creation,
                self.evm_version,
            );
        return @as(u512, self.runs) * uninlined_execution_cost + uninlined_deposit_cost >
            inlined_deposit_cost;
    }

    fn shouldInline(
        self: *const Inliner,
        tag: usize,
        jump: *const AssemblyItem,
        block: *InlinableBlock,
    ) !?AssemblyItem {
        std.debug.assert(jump.eqlInstruction(.JUMP));
        var block_exit = self.items.items[block.end - 1];
        const block_items = self.items.items[block.begin..block.end];
        if (jump.jump_type == .IntoFunction and block_exit.eqlInstruction(.JUMP) and
            block_exit.jump_type == .OutOfFunction and
            try self.shouldInlineFullFunctionBody(tag, block_items, block.push_tag_count))
        {
            block_exit.jump_type = .Ordinary;
            return block_exit;
        }

        if (jump.jump_type == .Ordinary or
            SemanticInformation.terminatesControlFlow(block_exit.instruction_value.?))
        {
            const jump_pattern = [_]AssemblyItem{
                AssemblyItem.initType(.PushTag, 0, .{}),
                AssemblyItem.initInstruction(.JUMP, .{}),
            };
            if (GasMeterModule.dataGasLength(
                try codeSize(block_items, self.evm_version),
                self.is_creation,
                self.evm_version,
            ) <= GasMeterModule.dataGasLength(
                try codeSize(&jump_pattern, self.evm_version),
                self.is_creation,
                self.evm_version,
            )) return block_exit;
        }
        return null;
    }
};

fn getLocalTag(item: *const AssemblyItem) ?usize {
    if (item.item_type != .PushTag and item.item_type != .Tag) return null;
    const split = item.splitForeignPushTag() catch return null;
    if (!split[0].empty()) return null;
    return split[1];
}

fn executionCost(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    evm_version: EVMVersion,
) !u256 {
    var state = try KnownState.init(allocator);
    defer state.deinit();
    var meter: GasMeterModule.GasMeter = .{
        .state = state.gasState(),
        .evm_version = evm_version,
    };
    var result: GasMeterModule.GasConsumption = .{};
    for (items) |*item| result.add(try meter.estimateMax(item, false));
    return if (result.is_infinite) std.math.maxInt(u256) else result.value;
}

fn codeSize(items: []const AssemblyItem, evm_version: EVMVersion) !u64 {
    var result: u64 = 0;
    for (items) |*item| result += @intCast(try item.bytesRequired(2, evm_version, .Approximate));
    return result;
}

fn containsTag(tags: []const usize, tag: usize) bool {
    for (tags) |candidate| if (candidate == tag) return true;
    return false;
}

const SearchResult = struct { index: usize, found: bool };

fn searchTagCount(items: anytype, tag: usize) SearchResult {
    var lower: usize = 0;
    var upper: usize = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (items[middle].tag < tag) lower = middle + 1 else upper = middle;
    }
    return .{ .index = lower, .found = lower < items.len and items[lower].tag == tag };
}

fn searchBlock(items: []const Inliner.InlinableBlock, tag: usize) SearchResult {
    return searchTagCount(items, tag);
}

fn findBlock(blocks: *std.ArrayList(Inliner.InlinableBlock), tag: usize) ?*Inliner.InlinableBlock {
    const result = searchBlock(blocks.items, tag);
    return if (result.found) &blocks.items[result.index] else null;
}

fn appendClone(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(AssemblyItem),
    item: *const AssemblyItem,
) std.mem.Allocator.Error!void {
    var clone = try item.clone(allocator);
    errdefer clone.deinit(allocator);
    try output.append(allocator, clone);
}

fn deinitItems(allocator: std.mem.Allocator, items: *std.ArrayList(AssemblyItem)) void {
    for (items.items) |*item| item.deinit(allocator);
    items.deinit(allocator);
    items.* = .empty;
}

test "inliner replaces a small ordinary jump target" {
    const I = AssemblyItem;
    var items: std.ArrayList(I) = .empty;
    defer deinitItems(std.testing.allocator, &items);
    try items.appendSlice(std.testing.allocator, &.{
        I.initType(.PushTag, 1, .{}),
        I.initInstruction(.JUMP, .{}),
        I.initType(.Tag, 1, .{}),
        I.initInstruction(.STOP, .{}),
    });
    var inliner = Inliner.init(
        std.testing.allocator,
        &items,
        &.{},
        200,
        false,
        EVMVersion.init(.London),
    );
    try inliner.optimise();
    try std.testing.expect(items.items[0].eqlInstruction(.STOP));
}
