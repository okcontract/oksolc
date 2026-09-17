// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Upper-bound gas traversal across statically known assembly paths.

const std = @import("std");
const cxx = @import("cxx_compat");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const AssemblyItem = @import("assembly_item.zig").AssemblyItem;
const GasMeterModule = @import("gas_meter.zig");
const KnownStateModule = @import("known_state.zig");
const SemanticInformation = @import("semantic_information.zig");

const GasConsumption = GasMeterModule.GasConsumption;
const KnownState = KnownStateModule.KnownState;

fn lessUsize(left: usize, right: usize) bool {
    return left < right;
}

fn lessWord(left: u256, right: u256) bool {
    return left < right;
}

const VisitedSet = cxx.OrderedSet(usize, lessUsize);
const QueueMap = cxx.OrderedMap(usize, *GasPath, lessUsize);
const HighestGasMap = cxx.OrderedMap(usize, GasConsumption, lessUsize);
const TagPositionMap = cxx.OrderedMap(u256, usize, lessWord);

pub const GasPath = struct {
    index: usize = 0,
    state: KnownState,
    largest_memory_access: u256 = 0,
    gas: GasConsumption = .{},
    visited_jumpdests: VisitedSet = .{},

    fn deinit(self: *GasPath, allocator: std.mem.Allocator) void {
        self.visited_jumpdests.deinit(allocator);
        self.state.deinit();
        self.* = undefined;
    }
};

/// GasState deliberately accepts foreign state implementations, so estimator
/// callbacks use Zig's global error set. Path traversal preserves that set.
pub const PathGasError = anyerror;

pub const PathGasMeter = struct {
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    evm_version: EVMVersion,
    queue_items: QueueMap = .{},
    highest_gas_usage_per_jumpdest: HighestGasMap = .{},
    tag_positions: TagPositionMap = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        items: []const AssemblyItem,
        evm_version: EVMVersion,
    ) std.mem.Allocator.Error!PathGasMeter {
        var result: PathGasMeter = .{
            .allocator = allocator,
            .items = items,
            .evm_version = evm_version,
        };
        errdefer result.deinit();
        for (items, 0..) |item, index| {
            if (item.item_type == .Tag)
                _ = try result.tag_positions.fetchPut(allocator, item.data_value, index);
        }
        return result;
    }

    pub fn deinit(self: *PathGasMeter) void {
        for (self.queue_items.mutableItems()) |entry| self.destroyPath(entry.value);
        self.queue_items.deinit(self.allocator);
        self.highest_gas_usage_per_jumpdest.deinit(self.allocator);
        self.tag_positions.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn estimateMax(
        self: *PathGasMeter,
        start_index: usize,
        state: *const KnownState,
    ) PathGasError!GasConsumption {
        const path = try self.allocator.create(GasPath);
        var allocation_owned = true;
        errdefer if (allocation_owned) self.allocator.destroy(path);
        path.* = .{ .index = start_index, .state = try state.clone() };
        var path_owned = true;
        allocation_owned = false;
        errdefer if (path_owned) self.destroyPath(path);
        try self.queue(path);
        path_owned = false;

        var gas: GasConsumption = .{};
        while (!self.queue_items.isEmpty() and !gas.is_infinite) {
            const candidate = try self.handleQueueItem();
            if (gas.lessThan(candidate)) gas = candidate;
        }
        return gas;
    }

    pub fn estimate(
        allocator: std.mem.Allocator,
        items: []const AssemblyItem,
        evm_version: EVMVersion,
        start_index: usize,
        state: *const KnownState,
    ) PathGasError!GasConsumption {
        var meter = try PathGasMeter.init(allocator, items, evm_version);
        defer meter.deinit();
        return meter.estimateMax(start_index, state);
    }

    fn queue(self: *PathGasMeter, new_path: *GasPath) std.mem.Allocator.Error!void {
        if (self.highest_gas_usage_per_jumpdest.get(new_path.index)) |highest| {
            if (new_path.gas.lessThan(highest.*)) {
                self.destroyPath(new_path);
                return;
            }
        }
        _ = try self.highest_gas_usage_per_jumpdest.fetchPut(
            self.allocator,
            new_path.index,
            new_path.gas,
        );
        if (try self.queue_items.fetchPut(self.allocator, new_path.index, new_path)) |displaced|
            self.destroyPath(displaced.value);
    }

    fn handleQueueItem(self: *PathGasMeter) PathGasError!GasConsumption {
        if (self.queue_items.isEmpty()) return error.EmptyPathQueue;
        const entry = self.queue_items.entries.orderedRemove(self.queue_items.len() - 1);
        const path = entry.value;
        defer self.destroyPath(path);

        var meter: GasMeterModule.GasMeter = .{
            .state = path.state.gasState(),
            .evm_version = self.evm_version,
            .largest_memory_access = path.largest_memory_access,
        };
        var gas = path.gas;
        var index = path.index;

        if (index >= self.items.len or
            (index > 0 and self.items[index].item_type != .Tag)) return gas;

        while (index < self.items.len and !gas.is_infinite) : (index += 1) {
            var branch_stops = false;
            var jump_tags: KnownStateModule.TagSet = .{};
            defer jump_tags.deinit(self.allocator);
            const item = &self.items[index];

            if (item.item_type == .Tag or item.eqlInstruction(.JUMPDEST)) {
                if (path.visited_jumpdests.contains(index)) return GasConsumption.infinite();
                _ = try path.visited_jumpdests.insert(self.allocator, index);
            } else if (item.eqlInstruction(.JUMP)) {
                branch_stops = true;
                jump_tags = try path.state.tagsInExpression(
                    try path.state.relativeStackElement(0, .{}),
                );
                if (jump_tags.isEmpty()) return GasConsumption.infinite();
            } else if (item.eqlInstruction(.JUMPI)) {
                const condition = try path.state.relativeStackElement(-1, .{});
                const known_non_zero = try path.state.expressionClasses().knownNonZero(condition);
                if (known_non_zero or !(try path.state.expressionClasses().knownZero(condition))) {
                    jump_tags = try path.state.tagsInExpression(
                        try path.state.relativeStackElement(0, .{}),
                    );
                    if (jump_tags.isEmpty()) return GasConsumption.infinite();
                }
                branch_stops = try path.state.expressionClasses().knownNonZero(condition);
            } else if (SemanticInformation.altersControlFlow(item)) {
                branch_stops = true;
            }

            gas.add(try meter.estimateMax(item, true));
            for (jump_tags.map.items()) |tag_entry| {
                const new_path = try self.allocator.create(GasPath);
                var allocation_owned = true;
                errdefer if (allocation_owned) self.allocator.destroy(new_path);
                var cloned_state = try path.state.clone();
                var state_owned = true;
                errdefer if (state_owned) cloned_state.deinit();
                var visited = try path.visited_jumpdests.clone(self.allocator);
                var visited_owned = true;
                errdefer if (visited_owned) visited.deinit(self.allocator);
                new_path.* = .{
                    .index = if (self.tag_positions.get(tag_entry.key)) |position| position.* else self.items.len,
                    .state = cloned_state,
                    .gas = gas,
                    .largest_memory_access = meter.largest_memory_access,
                    .visited_jumpdests = visited,
                };
                state_owned = false;
                visited_owned = false;
                allocation_owned = false;
                var path_owned = true;
                errdefer if (path_owned) self.destroyPath(new_path);
                try self.queue(new_path);
                path_owned = false;
            }

            if (branch_stops) break;
        }
        return gas;
    }

    fn destroyPath(self: *PathGasMeter, path: *GasPath) void {
        path.deinit(self.allocator);
        self.allocator.destroy(path);
    }
};

test "path gas handles straight, conditional, forward, and cyclic control flow" {
    const I = AssemblyItem;
    const london = EVMVersion.init(.London);
    var state = try KnownState.init(std.testing.allocator);
    defer state.deinit();

    const straight = [_]I{
        I.initPush(1, .{}),
        I.initPush(2, .{}),
        I.initInstruction(.ADD, .{}),
        I.initInstruction(.STOP, .{}),
    };
    var straight_meter = try PathGasMeter.init(std.testing.allocator, &straight, london);
    defer straight_meter.deinit();
    try std.testing.expectEqual(@as(u256, 9), (try straight_meter.estimateMax(0, &state)).value);

    const conditional = [_]I{
        I.initPush(0, .{}),
        I.initType(.PushTag, 1, .{}),
        I.initInstruction(.JUMPI, .{}),
        I.initInstruction(.STOP, .{}),
        I.initType(.Tag, 1, .{}),
        I.initInstruction(.STOP, .{}),
    };
    var conditional_meter = try PathGasMeter.init(std.testing.allocator, &conditional, london);
    defer conditional_meter.deinit();
    try std.testing.expectEqual(@as(u256, 16), (try conditional_meter.estimateMax(0, &state)).value);

    const forward = [_]I{
        I.initType(.PushTag, 1, .{}),
        I.initInstruction(.JUMP, .{}),
        I.initInstruction(.STOP, .{}),
        I.initType(.Tag, 1, .{}),
        I.initInstruction(.STOP, .{}),
    };
    var forward_meter = try PathGasMeter.init(std.testing.allocator, &forward, london);
    defer forward_meter.deinit();
    try std.testing.expectEqual(@as(u256, 12), (try forward_meter.estimateMax(0, &state)).value);

    const cyclic = [_]I{
        I.initType(.Tag, 1, .{}),
        I.initType(.PushTag, 1, .{}),
        I.initInstruction(.JUMP, .{}),
    };
    var cyclic_meter = try PathGasMeter.init(std.testing.allocator, &cyclic, london);
    defer cyclic_meter.deinit();
    try std.testing.expect((try cyclic_meter.estimateMax(0, &state)).is_infinite);
}
