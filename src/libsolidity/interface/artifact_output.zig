// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Contract artifact publication across frontend and worker allocation owners.

const std = @import("std");
const Json = std.json.Value;

/// Allocator contexts point to the arena header, so allocate it in stable
/// invocation storage before lending allocators to managed JSON containers.
/// Deinitialize the arena before releasing its header through owner_allocator.
pub fn createArena(owner_allocator: std.mem.Allocator, backing_allocator: std.mem.Allocator) !*std.heap.ArenaAllocator {
    const arena = try owner_allocator.create(std.heap.ArenaAllocator);
    arena.* = .init(backing_allocator);
    return arena;
}

/// Destination owns its top-level and `evm` maps through allocator. Source keys
/// and values are borrowed without copying their payloads; their owners must
/// remain alive until publication is serialized. Published nested values are
/// read-only. Existing frontend `evm` fields survive the backend merge.
pub fn mergeContract(allocator: std.mem.Allocator, destination: *Json, source: *const Json) !void {
    if (destination.* != .object or source.* != .object)
        return error.InvalidSolidityParserState;
    for (source.object.keys(), source.object.values()) |key, value| {
        if (!std.mem.eql(u8, key, "evm")) {
            try destination.object.put(allocator, key, value);
            continue;
        }
        if (value != .object) return error.InvalidSolidityParserState;
        const entry = try destination.object.getOrPut(allocator, key);
        if (!entry.found_existing) entry.value_ptr.* = .{ .object = .empty };
        const evm = entry.value_ptr;
        if (evm.* != .object) return error.InvalidSolidityParserState;
        for (value.object.keys(), value.object.values()) |field, artifact|
            try evm.object.put(allocator, field, artifact);
    }
}

test "contract artifact merge preserves frontend fields and allocation owners" {
    const allocator = std.testing.allocator;
    var source_arena = std.heap.ArenaAllocator.init(allocator);
    defer source_arena.deinit();
    const source_allocator = source_arena.allocator();
    var source: Json = .{ .object = .empty };
    try source.object.put(source_allocator, "evm", .{ .object = .empty });
    const source_evm = source.object.getPtr("evm").?;
    // Force destination map growth using storage independent of the source.
    for (0..20) |index| {
        const field = try std.fmt.allocPrint(source_allocator, "field{d}", .{index});
        try source_evm.object.put(source_allocator, field, .{ .string = try source_allocator.dupe(u8, field) });
    }
    try source.object.put(source_allocator, "metadata", .{ .string = try source_allocator.dupe(u8, "backend") });

    const Check = struct {
        fn run(failing: std.mem.Allocator, input: *const Json, has_frontend: bool) !void {
            var destination: Json = .{ .object = .empty };
            defer {
                if (destination.object.getPtr("evm")) |evm| evm.object.deinit(failing);
                destination.object.deinit(failing);
            }
            try destination.object.put(failing, "metadata", .{ .string = "frontend" });
            if (has_frontend) {
                try destination.object.put(failing, "evm", .{ .object = .empty });
                try destination.object.getPtr("evm").?.object.put(failing, "methodIdentifiers", .{ .string = "existing selectors" });
            }
            try mergeContract(failing, &destination, input);
            const original_evm = &input.object.getPtr("evm").?.object;
            const merged_evm = &destination.object.getPtr("evm").?.object;
            try std.testing.expect(merged_evm.values().ptr != original_evm.values().ptr);
            try std.testing.expectEqual(@as(usize, 20), original_evm.count());
            try std.testing.expectEqual(@as(usize, if (has_frontend) 21 else 20), merged_evm.count());
            if (has_frontend)
                try std.testing.expectEqualStrings("existing selectors", merged_evm.get("methodIdentifiers").?.string);
            for (original_evm.keys(), original_evm.values()) |key, value|
                try std.testing.expect(value.string.ptr == merged_evm.get(key).?.string.ptr);
            try std.testing.expect(input.object.get("metadata").?.string.ptr == destination.object.get("metadata").?.string.ptr);
        }
    };
    for ([_]bool{ false, true }) |has_frontend|
        try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ &source, has_frontend });
}

test "contract artifact merge rejects invalid object boundaries" {
    var destination: Json = .{ .object = .empty };
    defer destination.object.deinit(std.testing.allocator);
    var invalid: Json = .null;
    try std.testing.expectError(error.InvalidSolidityParserState, mergeContract(std.testing.allocator, &destination, &invalid));
    var source: Json = .{ .object = .empty };
    defer source.object.deinit(std.testing.allocator);
    try source.object.put(std.testing.allocator, "evm", .null);
    try std.testing.expectError(error.InvalidSolidityParserState, mergeContract(std.testing.allocator, &destination, &source));
    try std.testing.expectEqual(@as(usize, 0), destination.object.count());
    try source.object.put(std.testing.allocator, "evm", .{ .object = .empty });
    try std.testing.expectError(error.InvalidSolidityParserState, mergeContract(std.testing.allocator, &invalid, &source));
    try destination.object.put(std.testing.allocator, "evm", .null);
    try std.testing.expectError(error.InvalidSolidityParserState, mergeContract(std.testing.allocator, &destination, &source));
    try std.testing.expect(destination.object.get("evm").? == .null);
}

test "contract artifact arena outlives moved and destroyed job headers" {
    const Job = struct {
        arena: *std.heap.ArenaAllocator,
        output: std.json.Array,
    };
    const Check = struct {
        fn run(failing: std.mem.Allocator, fail_owner: bool) !void {
            const owner_allocator = if (fail_owner) failing else std.testing.allocator;
            const backing_allocator = if (fail_owner) std.testing.allocator else failing;
            var owner = std.heap.ArenaAllocator.init(owner_allocator);
            defer owner.deinit();
            const arena = try createArena(owner.allocator(), backing_allocator);
            defer arena.deinit();
            var published = value: {
                var jobs: std.ArrayList(Job) = .empty;
                defer jobs.deinit(owner_allocator);
                try jobs.append(owner_allocator, .{ .arena = arena, .output = std.json.Array.init(arena.allocator()) });
                try jobs.items[0].output.append(.{ .integer = 7 });
                const moved = try owner_allocator.dupe(Job, jobs.items);
                defer owner_allocator.free(moved);
                try std.testing.expect(moved.ptr != jobs.items.ptr);
                try std.testing.expect(moved[0].arena == arena);
                break :value moved[0].output;
            };
            // Both copies of the job header are gone. Force the published
            // managed array to use its stored allocator context again.
            const expected_context: *anyopaque = arena;
            try std.testing.expect(published.allocator.ptr == expected_context);
            try published.ensureTotalCapacity(8192);
            try published.append(.{ .integer = 9 });
            try std.testing.expectEqual(@as(i64, 7), published.items[0].integer);
            try std.testing.expectEqual(@as(i64, 9), published.items[1].integer);
        }
    };
    for ([_]bool{ false, true }) |fail_owner|
        try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{fail_owner});
}
