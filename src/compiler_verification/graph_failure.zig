// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Allocation-cut observations of the real recursive interner. Observation is
//! separate from semantic acceptance by `Compiler.Validation.Failure.certify`.
const std = @import("std");
const Graph = @import("graph.zig");

pub const max_allocations = 128;
pub const Observation = struct {
    failureAt: ?usize,
    successfulAllocations: usize,
    inducedFailure: bool,
    attempt: Graph.Attempt,
};

fn observe(arena: *std.heap.ArenaAllocator, allocator: std.mem.Allocator, input: []const Graph.Node, root: u32, failure_at: ?usize) !Observation {
    var failing = std.testing.FailingAllocator.init(allocator, .{
        .fail_index = failure_at orelse std.math.maxInt(usize),
        .resize_fail_index = 0,
    });
    const attempt = try Graph.captureAttempt(arena, failing.allocator(), input, root);
    if (failing.allocated_bytes != failing.freed_bytes or failing.allocations != failing.deallocations)
        return error.UnreleasedCompilerAllocation;
    if (attempt.outcome == .outOfMemory and !failing.has_induced_failure) return error.OutOfMemory;
    if (failure_at) |index| {
        if (!failing.has_induced_failure or failing.alloc_index != index or attempt.outcome != .outOfMemory)
            return error.MissingAllocationFailure;
    } else if (failing.has_induced_failure or attempt.outcome != .complete) return error.FailedBaseline;
    return .{ .failureAt = failure_at, .successfulAllocations = failing.alloc_index, .inducedFailure = failing.has_induced_failure, .attempt = attempt };
}

pub fn sweep(arena: *std.heap.ArenaAllocator, allocator: std.mem.Allocator, input: []const Graph.Node, root: u32) ![]const Observation {
    const baseline = try observe(arena, allocator, input, root, null);
    if (baseline.successfulAllocations == 0 or baseline.successfulAllocations > max_allocations)
        return error.AllocationSweepLimit;
    const observations = try arena.allocator().alloc(Observation, baseline.successfulAllocations + 1);
    for (observations[0..baseline.successfulAllocations], 0..) |*observation, index|
        observation.* = try observe(arena, allocator, input, root, index);
    observations[baseline.successfulAllocations] = baseline;
    return observations;
}

test "graph export recursive failure sweep retains partial graph growth and releases every allocation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const nodes: []const Graph.Node = &.{ .{ .input = "x" }, .{ .literal = "3" }, .{ .binary = .{ .op = .add, .left = 0, .right = 1 } }, .{ .literal = "5" }, .{ .binary = .{ .op = .add, .left = 2, .right = 3 } } };
    const observations = try sweep(&arena, std.testing.allocator, nodes, 4);
    var retained_recursive_constant = false;
    for (observations[0 .. observations.len - 1], 0..) |observation, index| {
        try std.testing.expectEqual(index, observation.failureAt.?);
        try std.testing.expectEqual(.outOfMemory, observation.attempt.outcome);
        try std.testing.expect(observation.attempt.resultIds.len < nodes.len);
        if (observation.attempt.resultIds.len == 4) {
            for (observation.attempt.nodes) |node| switch (node) {
                .literal => |value| if (std.mem.eql(u8, value, "8")) {
                    retained_recursive_constant = true;
                },
                else => {},
            };
        }
    }
    try std.testing.expect(retained_recursive_constant);
    try std.testing.expectEqual(nodes.len, observations[observations.len - 1].attempt.resultIds.len);
}
