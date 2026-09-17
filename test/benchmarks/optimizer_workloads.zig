// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic synthetic Yul workloads shared by differential tests and
//! optimizer microbenchmarks.

const std = @import("std");

pub fn dataFlowFanoutAlloc(
    allocator: std.mem.Allocator,
    fanout: usize,
) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.appendSlice(allocator, "{ let root := calldataload(0)");
    for (0..fanout) |index| try appendFormat(
        allocator,
        &source,
        " let v{d} := add(root, {d})",
        .{ index, index + 1 },
    );
    try source.appendSlice(allocator, " root := calldataload(32)");
    for (0..fanout) |index| try appendFormat(
        allocator,
        &source,
        " pop(v{d})",
        .{index},
    );
    try source.appendSlice(allocator, " pop(root) }");
    return source.toOwnedSlice(allocator);
}

pub fn dependencyChurnAlloc(
    allocator: std.mem.Allocator,
    fanout: usize,
    reassignment_rounds: usize,
) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.appendSlice(
        allocator,
        "{ let root0 := calldataload(0) let root1 := calldataload(32)",
    );
    for (0..fanout) |index| try appendFormat(
        allocator,
        &source,
        " let v{d} := add(root0, {d})",
        .{ index, index + 1 },
    );
    for (0..reassignment_rounds) |round| {
        const root = if (round % 2 == 0) "root1" else "root0";
        for (0..fanout) |index| try appendFormat(
            allocator,
            &source,
            " v{d} := add({s}, {d})",
            .{ index, root, round + index + 1 },
        );
    }
    try source.appendSlice(
        allocator,
        " root0 := calldataload(64) root1 := calldataload(96)",
    );
    for (0..fanout) |index| try appendFormat(
        allocator,
        &source,
        " pop(v{d})",
        .{index},
    );
    try source.appendSlice(allocator, " pop(root0) pop(root1) }");
    return source.toOwnedSlice(allocator);
}

pub fn branchHeavyAlloc(
    allocator: std.mem.Allocator,
    branch_count: usize,
    fact_count: usize,
) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.appendSlice(
        allocator,
        "{ let selector := calldataload(0) let a := 1 let b := a let c := b",
    );
    for (0..fact_count) |index| try appendFormat(
        allocator,
        &source,
        " let key{d} := {d} let stored{d} := {d} mstore(key{d}, stored{d}) let loaded{d} := mload(key{d})",
        .{ index, index * 32, index, index + 1, index, index, index, index },
    );
    try source.appendSlice(allocator, " switch selector");
    for (0..branch_count) |index| try appendFormat(
        allocator,
        &source,
        " case {d} {{ a := add(a, {d}) b := add(a, {d}) c := add(b, {d}) }}",
        .{ index, index + 1, index + 2, index + 3 },
    );
    try source.appendSlice(
        allocator,
        " default { a := 0 b := 0 c := 0 } pop(add(a, add(b, c))) }",
    );
    return source.toOwnedSlice(allocator);
}

pub fn environmentInvalidationAlloc(
    allocator: std.mem.Allocator,
    fact_count: usize,
) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.appendSlice(allocator, "{ let root := calldataload(0)");
    for (0..fact_count) |index| try appendFormat(
        allocator,
        &source,
        " let key{d} := add(root, {d})" ++
            " let value{d} := add(root, {d})" ++
            " mstore(key{d}, value{d})" ++
            " sstore(key{d}, value{d})" ++
            " let memory{d} := mload(key{d})" ++
            " let storage{d} := sload(key{d})" ++
            " let hash{d} := keccak256(key{d}, value{d})",
        .{
            index, index * 32,
            index, index + 1,
            index, index,
            index, index,
            index, index,
            index, index,
            index, index,
            index,
        },
    );
    for (0..fact_count) |index| try appendFormat(
        allocator,
        &source,
        " memory{d} := add(root, {d})" ++
            " storage{d} := add(root, {d})" ++
            " hash{d} := add(root, {d})",
        .{
            index, fact_count + index,
            index, fact_count * 2 + index,
            index, fact_count * 3 + index,
        },
    );
    for (0..fact_count) |index| try appendFormat(
        allocator,
        &source,
        " pop(memory{d}) pop(storage{d}) pop(hash{d})",
        .{ index, index, index },
    );
    try source.appendSlice(allocator, " pop(root) }");
    return source.toOwnedSlice(allocator);
}

pub fn deepScopesAlloc(
    allocator: std.mem.Allocator,
    depth: usize,
) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.appendSlice(allocator, "{ let root := 1");
    for (0..depth) |index| {
        const parent = if (index == 0) "root" else try temporaryNameAlloc(
            allocator,
            "scope",
            index - 1,
        );
        defer if (index != 0) allocator.free(parent);
        try appendFormat(
            allocator,
            &source,
            " {{ let scope{d} := add({s}, {d})",
            .{ index, parent, index + 1 },
        );
    }
    if (depth == 0) {
        try source.appendSlice(allocator, " pop(root)");
    } else {
        try appendFormat(
            allocator,
            &source,
            " pop(scope{d})",
            .{depth - 1},
        );
    }
    for (0..depth) |_| try source.appendSlice(allocator, " }");
    try source.appendSlice(allocator, " pop(root) }");
    return source.toOwnedSlice(allocator);
}

pub fn cseBucketsAlloc(
    allocator: std.mem.Allocator,
    expression_depth: usize,
    repetitions: usize,
) ![]u8 {
    const expression = try nestedAddAlloc(allocator, expression_depth);
    defer allocator.free(expression);
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.appendSlice(allocator, "{");
    for (0..repetitions) |index| try appendFormat(
        allocator,
        &source,
        " let candidate{d} := {s}",
        .{ index, expression },
    );
    for (0..repetitions) |index| try appendFormat(
        allocator,
        &source,
        " pop(candidate{d})",
        .{index},
    );
    try source.appendSlice(allocator, " }");
    return source.toOwnedSlice(allocator);
}

pub fn smallSwitchesAlloc(
    allocator: std.mem.Allocator,
    switch_count: usize,
    case_count: usize,
) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.append(allocator, '{');
    for (0..switch_count) |_| {
        try source.appendSlice(allocator, " switch 0");
        for (0..case_count) |case_index| try appendFormat(
            allocator,
            &source,
            " case {d} {{ pop({d}) }}",
            .{ case_index, case_index },
        );
        try source.appendSlice(allocator, " default { pop(0) }");
    }
    try source.appendSlice(allocator, " }");
    return source.toOwnedSlice(allocator);
}

fn nestedAddAlloc(allocator: std.mem.Allocator, depth: usize) ![]u8 {
    var expression: std.ArrayList(u8) = .empty;
    errdefer expression.deinit(allocator);
    for (0..depth) |_| try expression.appendSlice(allocator, "add(1, ");
    try expression.appendSlice(allocator, "calldataload(0)");
    for (0..depth) |_| try expression.append(allocator, ')');
    return expression.toOwnedSlice(allocator);
}

fn temporaryNameAlloc(
    allocator: std.mem.Allocator,
    prefix: []const u8,
    index: usize,
) ![]u8 {
    return std.fmt.allocPrint(allocator, "{s}{d}", .{ prefix, index });
}

fn appendFormat(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    comptime format: []const u8,
    arguments: anytype,
) !void {
    const rendered = try std.fmt.allocPrint(allocator, format, arguments);
    defer allocator.free(rendered);
    try output.appendSlice(allocator, rendered);
}

test "workload generators are deterministic and structurally bounded" {
    const allocator = std.testing.allocator;
    const fanout = try dataFlowFanoutAlloc(allocator, 3);
    defer allocator.free(fanout);
    try std.testing.expectEqualStrings(
        "{ let root := calldataload(0) let v0 := add(root, 1) let v1 := add(root, 2) let v2 := add(root, 3) root := calldataload(32) pop(v0) pop(v1) pop(v2) pop(root) }",
        fanout,
    );

    const churn = try dependencyChurnAlloc(allocator, 3, 2);
    defer allocator.free(churn);
    try std.testing.expect(std.mem.count(u8, churn, " := add(root0,") == 6);
    try std.testing.expect(std.mem.count(u8, churn, " := add(root1,") == 3);

    const branches = try branchHeavyAlloc(allocator, 2, 2);
    defer allocator.free(branches);
    try std.testing.expect(std.mem.count(u8, branches, " case ") == 2);

    const environment = try environmentInvalidationAlloc(allocator, 3);
    defer allocator.free(environment);
    try std.testing.expect(std.mem.count(u8, environment, " mstore(") == 3);
    try std.testing.expect(std.mem.count(u8, environment, " sstore(") == 3);
    try std.testing.expect(std.mem.count(u8, environment, " := mload(") == 3);
    try std.testing.expect(std.mem.count(u8, environment, " := sload(") == 3);
    try std.testing.expect(std.mem.count(u8, environment, " := keccak256(") == 3);

    const scopes = try deepScopesAlloc(allocator, 4);
    defer allocator.free(scopes);
    try std.testing.expect(std.mem.count(u8, scopes, "{ let scope") == 4);

    const cse = try cseBucketsAlloc(allocator, 5, 3);
    defer allocator.free(cse);
    try std.testing.expect(std.mem.count(u8, cse, "calldataload(0)") == 3);

    const switches = try smallSwitchesAlloc(allocator, 3, 4);
    defer allocator.free(switches);
    try std.testing.expect(std.mem.count(u8, switches, " switch ") == 3);
    try std.testing.expect(std.mem.count(u8, switches, " case ") == 12);
}
