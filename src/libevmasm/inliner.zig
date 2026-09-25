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
        var did_inline = false;
        var index: usize = 0;
        while (index < self.items.items.len) : (index += 1) {
            const item = &self.items.items[index];
            if (index + 1 < self.items.items.len and item.item_type == .PushTag and
                self.items.items[index + 1].eqlInstruction(.JUMP))
            {
                if (getLocalTag(item)) |tag| {
                    if (findBlock(&blocks, tag)) |block| {
                        if (try self.shouldInline(tag, &self.items.items[index + 1], block)) |exit_item| {
                            if (!did_inline) {
                                // Until a rewrite is accepted, the original list
                                // remains the only output owner. Catch up once.
                                for (self.items.items[0..index]) |*unchanged|
                                    try appendClone(self.allocator, &new_items, unchanged);
                                did_inline = true;
                            }
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
            if (did_inline) try appendClone(self.allocator, &new_items, item);
        }

        if (!did_inline) return;
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

test "assembly inliner replaces a small ordinary jump target" {
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

test "assembly inliner frozen decisions preserve instruction annotations and order" {
    const Check = struct {
        const Config = struct {
            version: EVMVersion = .init(.London),
            runs: u64 = 200,
            creation: bool = false,
            outside: []const usize = &.{},
        };
        const Expected = struct { index: usize, ordinary_exit: bool = false };
        fn op(instruction: @import("instruction.zig").Instruction) AssemblyItem {
            return AssemblyItem.initInstruction(instruction, .{});
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
        fn jump(kind: AssemblyItemModule.JumpType) AssemblyItem {
            var item = op(.JUMP);
            item.jump_type = kind;
            return item;
        }
        fn keep(index: usize) Expected {
            return .{ .index = index };
        }
        fn exit(index: usize) Expected {
            return .{ .index = index, .ordinary_exit = true };
        }
        fn run(name: []const u8, input: []const AssemblyItem, expected: []const Expected, config: Config) !void {
            errdefer std.debug.print("inliner fixture: {s}\n", .{name});
            const allocator = std.testing.allocator;
            var items: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent cleanup releases the container and owned payloads on failure
            defer deinitItems(allocator, &items);
            try items.appendSlice(allocator, input);
            for (items.items, 0..) |*item, index| {
                const offset: i32 = @intCast(index * 10);
                item.debug_data = .{
                    .native_location = .{ .start = offset, .end = offset + 5, .source_name = "native.yul" },
                    .origin_location = .{ .start = offset + 1, .end = offset + 4, .source_name = "origin.sol" },
                    .ast_id = @intCast(index + 100),
                };
                item.pushed_value = index + 7;
                item.immutable_occurrences = index + 1;
                item.modifier_depth = index + 2;
            }
            var wanted: std.ArrayList(AssemblyItem) = .empty;
            defer wanted.deinit(allocator);
            for (expected) |value| {
                var item = items.items[value.index];
                if (value.ordinary_exit) item.jump_type = .Ordinary;
                try wanted.append(allocator, item);
            }
            var inliner = Inliner.init(allocator, &items, config.outside, config.runs, config.creation, config.version);
            try inliner.optimise();
            try std.testing.expectEqualDeep(wanted.items, items.items);
        }
    };
    const o = Check.op;
    const p = Check.push;
    const t = Check.tag;
    const pt = Check.pushTag;
    const j = Check.jump;
    const k = Check.keep;
    const e = Check.exit;
    try Check.run("empty", &.{}, &.{}, .{});
    try Check.run("unreferenced", &.{ t(1), o(.STOP) }, &.{ k(0), k(1) }, .{});
    try Check.run("small target", &.{ pt(1), o(.JUMP), t(1), o(.STOP) }, &.{ k(3), k(2), k(3) }, .{});
    try Check.run("terminal body", &.{ pt(1), o(.JUMP), t(1), p(7), o(.STOP) }, &.{ k(3), k(4), k(2), k(3), k(4) }, .{});
    try Check.run("large target rejected", &.{ pt(1), o(.JUMP), t(1), p(256), p(512), o(.ADD), o(.STOP) }, &.{ k(0), k(1), k(2), k(3), k(4), k(5), k(6) }, .{});
    try Check.run("later accepted target", &.{ pt(1), o(.JUMP), pt(2), o(.JUMP), t(1), p(256), p(512), o(.ADD), o(.STOP), t(2), o(.STOP) }, &.{ k(0), k(1), k(10), k(4), k(5), k(6), k(7), k(8), k(9), k(10) }, .{});
    try Check.run("multiple call sites", &.{ pt(1), o(.JUMP), pt(1), o(.JUMP), t(1), o(.STOP) }, &.{ k(5), k(5), k(4), k(5) }, .{});
    try Check.run("duplicated tag references", &.{ pt(1), o(.JUMP), pt(2), o(.JUMP), t(1), pt(2), o(.JUMP), t(2), o(.STOP) }, &.{ k(5), k(6), k(8), k(4), k(8), k(7), k(8) }, .{});
    try Check.run("recursive target rejected", &.{ pt(1), o(.JUMP), t(1), pt(1), o(.JUMP) }, &.{ k(0), k(1), k(2), k(3), k(4) }, .{});
    try Check.run("function exit annotation", &.{ pt(1), j(.IntoFunction), t(1), p(7), o(.POP), j(.OutOfFunction) }, &.{ k(3), k(4), e(5), k(2), k(3), k(4), k(5) }, .{});
    const external_function = [_]AssemblyItem{ pt(1), j(.IntoFunction), t(1), p(256), p(512), p(768), o(.ADD), o(.ADD), j(.OutOfFunction) };
    try Check.run("external function low runs", &external_function, &.{ k(0), k(1), k(2), k(3), k(4), k(5), k(6), k(7), k(8) }, .{ .runs = 0, .outside = &.{1} });
    try Check.run("external function high runs", &external_function, &.{ k(3), k(4), k(5), k(6), k(7), e(8), k(2), k(3), k(4), k(5), k(6), k(7), k(8) }, .{ .runs = 1_000_000, .creation = true, .outside = &.{1} });
    const zeros = [_]AssemblyItem{ pt(1), o(.JUMP), t(1), p(0), p(0), o(.STOP) };
    try Check.run("pre-PUSH0 target rejected", &zeros, &.{ k(0), k(1), k(2), k(3), k(4), k(5) }, .{});
    try Check.run("PUSH0 target accepted", &zeros, &.{ k(3), k(4), k(5), k(2), k(3), k(4), k(5) }, .{ .version = .init(.Shanghai) });
}

test "assembly inliner retains rejected output and cleans private copies on failure" {
    const Check = struct {
        const Case = enum { no_blocks, rejected, first, late, multiple, function_body };
        fn op(instruction: @import("instruction.zig").Instruction) AssemblyItem {
            return AssemblyItem.initInstruction(instruction, .{});
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
        fn make(allocator: std.mem.Allocator, case: Case) !std.ArrayList(AssemblyItem) {
            const middle: []const AssemblyItem = switch (case) {
                .no_blocks => &.{},
                .rejected => &.{ pushTag(1), op(.JUMP), tag(1), push(256), push(512), op(.ADD), op(.STOP) },
                .first => &.{ pushTag(1), op(.JUMP), tag(1), op(.STOP) },
                .late => &.{ pushTag(1), op(.JUMP), pushTag(2), op(.JUMP), tag(1), push(256), push(512), op(.ADD), op(.STOP), tag(2), op(.STOP) },
                .multiple => &.{ pushTag(1), op(.JUMP), pushTag(1), op(.JUMP), tag(1), op(.STOP) },
                .function_body => &.{ pushTag(1), op(.JUMP), tag(1), push(7), op(.POP), op(.JUMP) },
            };
            var items: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent cleanup releases the container and owned payloads on failure
            errdefer deinitItems(allocator, &items);
            try items.ensureTotalCapacity(allocator, middle.len + 2);
            items.appendAssumeCapacity(try AssemblyItem.initVerbatim(allocator, "prefix payload", 2, 1));
            items.appendSliceAssumeCapacity(middle);
            items.appendAssumeCapacity(try AssemblyItem.initVerbatim(allocator, "suffix payload", 0, 3));
            if (case == .function_body) {
                items.items[2].jump_type = .IntoFunction;
                items.items[6].jump_type = .OutOfFunction;
            }
            for (items.items, 0..) |*item, index| {
                item.debug_data = .{ .ast_id = @intCast(index + 100) };
                item.modifier_depth = index + 7;
            }
            return items;
        }
        fn run(allocator: std.mem.Allocator, case: Case, version: EVMVersion, creation: bool) !void {
            var items = try make(allocator, case);
            defer deinitItems(allocator, &items);
            const original = try allocator.dupe(AssemblyItem, items.items);
            defer allocator.free(original);
            const original_pointer = items.items.ptr;
            const original_capacity = items.capacity;
            const indices: []const usize = switch (case) {
                .no_blocks => &.{ 0, 1 },
                .rejected => &.{ 0, 1, 2, 3, 4, 5, 6, 7, 8 },
                .first => &.{ 0, 4, 3, 4, 5 },
                .late => &.{ 0, 1, 2, 11, 5, 6, 7, 8, 9, 10, 11, 12 },
                .multiple => &.{ 0, 6, 6, 5, 6, 7 },
                .function_body => &.{ 0, 4, 5, 6, 3, 4, 5, 6, 7 },
            };
            var expected: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent cleanup releases the container and owned payloads on failure
            defer deinitItems(allocator, &expected);
            for (indices, 0..) |index, position| {
                try appendClone(allocator, &expected, &items.items[index]);
                if (case == .function_body and position == 3)
                    expected.items[position].jump_type = .Ordinary;
            }

            // Measure unavoidable block discovery separately. For ordinary
            // rejected targets the pass must request no additional storage.
            var discovery = std.testing.FailingAllocator.init(allocator, .{});
            {
                const analysis = Inliner.init(discovery.allocator(), &items, &.{}, 200, creation, version);
                var blocks = try analysis.determineInlinableBlocks();
                defer blocks.deinit(discovery.allocator());
                try std.testing.expectEqual(@as(usize, switch (case) {
                    .no_blocks => 0,
                    .late => 2,
                    else => 1,
                }), blocks.items.len);
            }
            var measured = std.testing.FailingAllocator.init(allocator, .{});
            var inliner = Inliner.init(measured.allocator(), &items, &.{}, 200, creation, version);
            inliner.optimise() catch |err| {
                try std.testing.expectEqual(original_pointer, items.items.ptr);
                try std.testing.expectEqual(original_capacity, items.capacity);
                try std.testing.expectEqualDeep(original, items.items);
                return err;
            };
            try std.testing.expectEqualDeep(expected.items, items.items);
            if (case == .no_blocks or case == .rejected) {
                try std.testing.expectEqual(original_pointer, items.items.ptr);
                try std.testing.expectEqual(original_capacity, items.capacity);
                try std.testing.expectEqual(original[0].verbatim.?.data.ptr, items.items[0].verbatim.?.data.ptr);
                try std.testing.expectEqual(original[original.len - 1].verbatim.?.data.ptr, items.items[items.items.len - 1].verbatim.?.data.ptr);
                try std.testing.expectEqual(discovery.allocations, measured.allocations);
                try std.testing.expectEqual(discovery.allocated_bytes, measured.allocated_bytes);
            }
        }
    };
    for (std.enums.values(Check.Case)) |case| {
        for ([_]EVMVersion{ .init(.London), .init(.Shanghai) }) |version| {
            for ([_]bool{ false, true }) |creation|
                try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{ case, version, creation });
        }
    }
}
