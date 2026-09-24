// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Explicit profiler owner corresponding to the optional C++ `Profiler.cpp`.

const std = @import("std");
const JSON = @import("json.zig");

pub const Metrics = struct {
    duration_microseconds: u64 = 0,
    maximum_duration_microseconds: u64 = 0,
    /// Process CPU consumed while the scope invocation was active. A zero
    /// value is also the portable unsupported-clock result from `std.Io`.
    cpu_duration_microseconds: u64 = 0,
    maximum_cpu_duration_microseconds: u64 = 0,
    call_count: usize = 0,
};

pub const CounterMetrics = struct {
    total: u64 = 0,
    maximum: u64 = 0,
    sample_count: usize = 0,
};

pub const ScopeObservation = struct {
    duration_microseconds: u64,
    cpu_duration_microseconds: u64,
};

pub const Profiler = struct {
    const Self = @This();

    allocator: std.mem.Allocator,
    io: std.Io,
    metrics: std.array_hash_map.String(Metrics) = .empty,
    counters: std.array_hash_map.String(CounterMetrics) = .empty,
    mutex: std.Io.Mutex = .init,
    /// Protected by mutex. Deferred recording cannot return an error, so both
    /// report boundaries reject an incomplete profile after the first failure.
    recording_failure: ?std.mem.Allocator.Error = null,

    pub fn init(allocator: std.mem.Allocator, io: std.Io) Self {
        return .{ .allocator = allocator, .io = io };
    }

    pub fn deinit(self: *Self) void {
        for (self.metrics.keys()) |name| self.allocator.free(name);
        self.metrics.deinit(self.allocator);
        for (self.counters.keys()) |name| self.allocator.free(name);
        self.counters.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn probe(self: *Self, scope_name: []const u8) Probe {
        return .{
            .profiler = self,
            .scope_name = scope_name,
            .start = std.Io.Clock.Timestamp.now(self.io, .awake),
            .start_cpu = std.Io.Clock.Timestamp.now(self.io, .cpu_process),
        };
    }

    fn record(
        self: *Self,
        scope_name: []const u8,
        elapsed_nanoseconds: i96,
        elapsed_cpu_nanoseconds: i96,
    ) void {
        self.recordObservation(scope_name, .{
            .duration_microseconds = microseconds(elapsed_nanoseconds),
            .cpu_duration_microseconds = microseconds(elapsed_cpu_nanoseconds),
        });
    }

    fn recordObservation(
        self: *Self,
        scope_name: []const u8,
        observation: ScopeObservation,
    ) void {
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        const metrics = self.entry(Metrics, &self.metrics, scope_name) catch |err| {
            self.recording_failure = err;
            return;
        };
        const elapsed = observation.duration_microseconds;
        const elapsed_cpu = observation.cpu_duration_microseconds;
        metrics.duration_microseconds +|= elapsed;
        metrics.maximum_duration_microseconds = @max(
            metrics.maximum_duration_microseconds,
            elapsed,
        );
        metrics.cpu_duration_microseconds +|= elapsed_cpu;
        metrics.maximum_cpu_duration_microseconds = @max(
            metrics.maximum_cpu_duration_microseconds,
            elapsed_cpu,
        );
        metrics.call_count +|= 1;
    }

    /// Individual observations remain inspectable after failure; only a
    /// successful report establishes that recording remained complete.
    pub fn metricsFor(self: *Self, name: []const u8) ?Metrics {
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        return self.metrics.get(name);
    }

    /// Records one aggregate workload observation. Optimizer passes should
    /// accumulate locally and call this once per pass invocation rather than
    /// taking the profiler lock in inner loops.
    pub fn recordCounter(self: *Self, name: []const u8, value: u64) void {
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        self.addCounter(name, value) catch |err| {
            self.recording_failure = err;
        };
    }

    /// Fallible publication for optional telemetry. A failed insertion leaves
    /// the profiler valid and does not retain a borrowed or partially owned key.
    /// The caller handles this error and may retry; unlike void recording, this
    /// call does not latch its own insertion failure. A prior latched error is
    /// still returned without publishing another observation.
    pub fn tryRecordCounter(self: *Self, name: []const u8, value: u64) std.mem.Allocator.Error!void {
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        try self.addCounter(name, value);
    }

    // Callers hold mutex across publication and any failure-state update.
    fn addCounter(self: *Self, name: []const u8, value: u64) std.mem.Allocator.Error!void {
        const counter = try self.entry(CounterMetrics, &self.counters, name);
        counter.total +|= value;
        counter.maximum = @max(counter.maximum, value);
        counter.sample_count +|= 1;
    }

    /// Own a key before publishing it. Existing names need no allocation;
    /// failed growth frees the unpublished key and preserves all prior entries.
    fn entry(self: *Self, comptime T: type, entries: *std.array_hash_map.String(T), name: []const u8) std.mem.Allocator.Error!*T {
        if (self.recording_failure) |err| return err;
        if (entries.getPtr(name)) |value| return value;
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);
        const result = try entries.getOrPut(self.allocator, owned_name);
        std.debug.assert(!result.found_existing);
        result.value_ptr.* = .{};
        return result.value_ptr;
    }

    /// Individual counter snapshot; report methods also check completeness.
    pub fn counterFor(self: *Self, name: []const u8) ?CounterMetrics {
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        return self.counters.get(name);
    }

    pub fn reportAlloc(self: *Self, allocator: std.mem.Allocator) std.mem.Allocator.Error![]u8 {
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        if (self.recording_failure) |err| return err;
        const indices = try allocator.alloc(usize, self.metrics.count());
        defer allocator.free(indices);
        for (indices, 0..) |*index, value| index.* = value;
        // Stable insertion sort by duration, matching the ascending C++ report.
        var sort_index: usize = 1;
        while (sort_index < indices.len) : (sort_index += 1) {
            const selected = indices[sort_index];
            var position = sort_index;
            while (position != 0 and
                self.metrics.values()[selected].duration_microseconds <
                    self.metrics.values()[indices[position - 1]].duration_microseconds)
            {
                indices[position] = indices[position - 1];
                position -= 1;
            }
            indices[position] = selected;
        }

        var total_duration: u64 = 0;
        var total_cpu_duration: u64 = 0;
        var total_calls: usize = 0;
        for (self.metrics.values()) |metrics| {
            total_duration +|= metrics.duration_microseconds;
            total_cpu_duration +|= metrics.cpu_duration_microseconds;
            total_calls +|= metrics.call_count;
        }
        var output = std.Io.Writer.Allocating.init(allocator);
        defer output.deinit();
        const writer = &output.writer;
        writer.writeAll("PERFORMANCE METRICS FOR PROFILED SCOPES\n\n" ++
            "| Wall % | Wall       | CPU        | Calls   | Scope                          |\n" ++
            "|-------:|-----------:|-----------:|--------:|--------------------------------|\n") catch return error.OutOfMemory;
        for (indices) |index| {
            const metrics = self.metrics.values()[index];
            const percentage = if (total_duration == 0)
                0.0
            else
                100.0 * @as(f64, @floatFromInt(metrics.duration_microseconds)) /
                    @as(f64, @floatFromInt(total_duration));
            writer.print(
                "| {d:5.1}% | {d:8.3} s | {d:8.3} s | {d:7} | {s} |\n",
                .{
                    percentage,
                    @as(f64, @floatFromInt(metrics.duration_microseconds)) / 1_000_000.0,
                    @as(f64, @floatFromInt(metrics.cpu_duration_microseconds)) / 1_000_000.0,
                    metrics.call_count,
                    self.metrics.keys()[index],
                },
            ) catch return error.OutOfMemory;
        }
        writer.print(
            "| {d:5.1}% | {d:8.3} s | {d:8.3} s | {d:7} | **TOTAL** |\n",
            .{
                100.0,
                @as(f64, @floatFromInt(total_duration)) / 1_000_000.0,
                @as(f64, @floatFromInt(total_cpu_duration)) / 1_000_000.0,
                total_calls,
            },
        ) catch return error.OutOfMemory;
        if (self.counters.count() != 0) {
            writer.writeAll(
                "\nWORKLOAD COUNTERS\n\n" ++
                    "| Total               | Maximum             | Samples | Counter |\n" ++
                    "|--------------------:|--------------------:|--------:|---------|\n",
            ) catch return error.OutOfMemory;
            for (self.counters.keys(), self.counters.values()) |name, counter| {
                writer.print(
                    "| {d:19} | {d:19} | {d:7} | {s} |\n",
                    .{ counter.total, counter.maximum, counter.sample_count, name },
                ) catch return error.OutOfMemory;
            }
        }
        return output.toOwnedSlice();
    }

    /// Returns a stable machine-readable report. Scope rows are sorted by name
    /// so repeated profiles can be diffed without timing-dependent row order.
    pub fn reportJsonAlloc(self: *Self, allocator: std.mem.Allocator) ![]u8 {
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        if (self.recording_failure) |err| return err;
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        defer arena_state.deinit();
        const arena = arena_state.allocator();

        const indices = try arena.alloc(usize, self.metrics.count());
        for (indices, 0..) |*index, value| index.* = value;
        // Names are unique map keys, so a total name order needs no stable
        // tie handling. Bound report work at O(n log n), including large SCC
        // counter profiles, without another allocation or a schema change.
        std.sort.heap(usize, indices, self, struct {
            fn lessThan(profiler: *Self, left: usize, right: usize) bool {
                return std.mem.order(
                    u8,
                    profiler.metrics.keys()[left],
                    profiler.metrics.keys()[right],
                ) == .lt;
            }
        }.lessThan);

        var scopes = std.json.Array.init(arena);
        var profiled_duration_microseconds: u64 = 0;
        var profiled_cpu_duration_microseconds: u64 = 0;
        for (indices) |index| {
            const metrics = self.metrics.values()[index];
            profiled_duration_microseconds +|= metrics.duration_microseconds;
            profiled_cpu_duration_microseconds +|= metrics.cpu_duration_microseconds;
            var scope: std.json.Value = .{ .object = .empty };
            try scope.object.put(arena, "name", .{ .string = self.metrics.keys()[index] });
            try scope.object.put(
                arena,
                "duration_microseconds",
                .{ .integer = std.math.cast(i64, metrics.duration_microseconds) orelse
                    std.math.maxInt(i64) },
            );
            try scope.object.put(
                arena,
                "maximum_duration_microseconds",
                .{ .integer = std.math.cast(i64, metrics.maximum_duration_microseconds) orelse
                    std.math.maxInt(i64) },
            );
            try scope.object.put(
                arena,
                "cpu_duration_microseconds",
                .{ .integer = std.math.cast(i64, metrics.cpu_duration_microseconds) orelse
                    std.math.maxInt(i64) },
            );
            try scope.object.put(
                arena,
                "maximum_cpu_duration_microseconds",
                .{ .integer = std.math.cast(
                    i64,
                    metrics.maximum_cpu_duration_microseconds,
                ) orelse std.math.maxInt(i64) },
            );
            try scope.object.put(
                arena,
                "call_count",
                .{ .integer = std.math.cast(i64, metrics.call_count) orelse
                    std.math.maxInt(i64) },
            );
            try scopes.append(scope);
        }

        const counter_indices = try arena.alloc(usize, self.counters.count());
        for (counter_indices, 0..) |*index, value| index.* = value;
        std.sort.heap(usize, counter_indices, self, struct {
            fn lessThan(profiler: *Self, left: usize, right: usize) bool {
                return std.mem.order(
                    u8,
                    profiler.counters.keys()[left],
                    profiler.counters.keys()[right],
                ) == .lt;
            }
        }.lessThan);
        var counters = std.json.Array.init(arena);
        for (counter_indices) |index| {
            const metrics = self.counters.values()[index];
            var counter: std.json.Value = .{ .object = .empty };
            try counter.object.put(arena, "name", .{ .string = self.counters.keys()[index] });
            try counter.object.put(
                arena,
                "total",
                .{ .integer = std.math.cast(i64, metrics.total) orelse std.math.maxInt(i64) },
            );
            try counter.object.put(
                arena,
                "maximum",
                .{ .integer = std.math.cast(i64, metrics.maximum) orelse std.math.maxInt(i64) },
            );
            try counter.object.put(
                arena,
                "sample_count",
                .{ .integer = std.math.cast(i64, metrics.sample_count) orelse std.math.maxInt(i64) },
            );
            try counters.append(counter);
        }

        var root: std.json.Value = .{ .object = .empty };
        try root.object.put(arena, "schema_version", .{ .integer = 4 });
        try root.object.put(arena, "clock", .{ .string = "awake" });
        try root.object.put(arena, "cpu_clock", .{ .string = "cpu_process" });
        try root.object.put(
            arena,
            "profiled_duration_microseconds",
            .{ .integer = std.math.cast(i64, profiled_duration_microseconds) orelse
                std.math.maxInt(i64) },
        );
        try root.object.put(
            arena,
            "profiled_cpu_duration_microseconds",
            .{ .integer = std.math.cast(
                i64,
                profiled_cpu_duration_microseconds,
            ) orelse std.math.maxInt(i64) },
        );
        try root.object.put(arena, "scopes", .{ .array = scopes });
        try root.object.put(arena, "counters", .{ .array = counters });
        return JSON.jsonCompactPrintAlloc(allocator, &root);
    }

    pub const Probe = struct {
        profiler: *Self,
        scope_name: []const u8,
        start: std.Io.Clock.Timestamp,
        start_cpu: std.Io.Clock.Timestamp,
        armed: bool = true,

        pub fn deinit(self: *@This()) void {
            _ = self.finish();
        }

        /// Ends the probe and attempts publication. Returns the measured
        /// observation even if recording fails; report methods return that
        /// failure instead of publishing partial data. A dismissed probe
        /// returns null. The borrowed scope name must remain live until here.
        pub fn finish(self: *@This()) ?ScopeObservation {
            const observation: ?ScopeObservation = if (self.armed) measured: {
                const end = std.Io.Clock.Timestamp.now(self.profiler.io, .awake);
                const end_cpu = std.Io.Clock.Timestamp.now(
                    self.profiler.io,
                    .cpu_process,
                );
                break :measured .{
                    .duration_microseconds = microseconds(
                        self.start.durationTo(end).raw.nanoseconds,
                    ),
                    .cpu_duration_microseconds = microseconds(
                        self.start_cpu.durationTo(end_cpu).raw.nanoseconds,
                    ),
                };
            } else null;
            if (observation) |measured|
                self.profiler.recordObservation(self.scope_name, measured);
            self.* = undefined;
            return observation;
        }

        pub fn dismiss(self: *@This()) void {
            self.armed = false;
        }
    };
};

fn microseconds(nanoseconds: i96) u64 {
    return if (nanoseconds <= 0)
        0
    else
        std.math.cast(u64, @divTrunc(nanoseconds, 1000)) orelse
            std.math.maxInt(u64);
}

/// An optional request-owned probe. The null case avoids reading the clock and
/// lets production compilation retain only one predictable branch per scope.
pub const OptionalProbe = struct {
    probe: ?Profiler.Probe,

    pub fn init(profiler: ?*Profiler, scope_name: []const u8) OptionalProbe {
        return .{ .probe = if (profiler) |value| value.probe(scope_name) else null };
    }

    pub fn deinit(self: *OptionalProbe) void {
        _ = self.finish();
    }

    pub fn finish(self: *OptionalProbe) ?ScopeObservation {
        const observation = if (self.probe) |*probe| probe.finish() else null;
        self.* = undefined;
        return observation;
    }
};

test "profiler probes aggregate calls and produce a deterministic report" {
    var profiler = Profiler.init(std.testing.allocator, std.testing.io);
    defer profiler.deinit();
    {
        var probe = profiler.probe("scanner");
        defer probe.deinit();
    }
    const scanner = profiler.metricsFor("scanner").?;
    try std.testing.expectEqual(@as(usize, 1), scanner.call_count);
    try std.testing.expectEqual(scanner.duration_microseconds, scanner.maximum_duration_microseconds);

    var finished_probe = profiler.probe("finished");
    const finished = finished_probe.finish().?;
    const finished_metrics = profiler.metricsFor("finished").?;
    try std.testing.expectEqual(
        finished.duration_microseconds,
        finished_metrics.duration_microseconds,
    );
    try std.testing.expectEqual(
        finished.cpu_duration_microseconds,
        finished_metrics.cpu_duration_microseconds,
    );

    profiler.record("manual", 3_000, 5_000);
    profiler.record("manual", 7_000, 11_000);
    const manual = profiler.metricsFor("manual").?;
    try std.testing.expectEqual(@as(u64, 10), manual.duration_microseconds);
    try std.testing.expectEqual(@as(u64, 7), manual.maximum_duration_microseconds);
    try std.testing.expectEqual(@as(u64, 16), manual.cpu_duration_microseconds);
    try std.testing.expectEqual(@as(u64, 11), manual.maximum_cpu_duration_microseconds);
    try std.testing.expectEqual(@as(usize, 2), manual.call_count);

    const report = try profiler.reportAlloc(std.testing.allocator);
    defer std.testing.allocator.free(report);
    try std.testing.expect(std.mem.find(u8, report, "scanner") != null);

    const json = try profiler.reportJsonAlloc(std.testing.allocator);
    defer std.testing.allocator.free(json);
    try std.testing.expect(std.mem.find(u8, json, "\"schema_version\":4") != null);
    try std.testing.expect(std.mem.find(u8, json, "\"name\":\"scanner\"") != null);
    try std.testing.expect(
        std.mem.find(u8, json, "\"maximum_duration_microseconds\":") != null,
    );
    try std.testing.expect(
        std.mem.find(u8, json, "\"cpu_duration_microseconds\":") != null,
    );

    profiler.recordCounter("items", 3);
    profiler.recordCounter("items", 5);
    const counter = profiler.counterFor("items").?;
    try std.testing.expectEqual(@as(u64, 8), counter.total);
    try std.testing.expectEqual(@as(u64, 5), counter.maximum);
    try std.testing.expectEqual(@as(usize, 2), counter.sample_count);

    var disabled = OptionalProbe.init(null, "disabled");
    disabled.deinit();
    try std.testing.expect(profiler.metricsFor("disabled") == null);
}

test "profiler JSON reports retain canonical name order for empty and large reversed inventories" {
    for ([_]usize{ 0, 1, 513 }) |count| {
        var forward = Profiler.init(std.testing.allocator, std.testing.io);
        defer forward.deinit();
        var reverse = Profiler.init(std.testing.allocator, std.testing.io);
        defer reverse.deinit();
        for (0..count) |index| {
            try recordReportFixture(&forward, index);
            try recordReportFixture(&reverse, count - index - 1);
        }
        const expected = try forward.reportJsonAlloc(std.testing.allocator);
        defer std.testing.allocator.free(expected);
        const actual = try reverse.reportJsonAlloc(std.testing.allocator);
        defer std.testing.allocator.free(actual);
        try std.testing.expectEqualStrings(expected, actual);
        const parsed = try std.json.parseFromSlice(std.json.Value, std.testing.allocator, actual, .{});
        defer parsed.deinit();
        for ([_][]const u8{ "scopes", "counters" }) |field| {
            const rows = parsed.value.object.get(field).?.array.items;
            try std.testing.expectEqual(count, rows.len);
            for (rows, 0..) |row, index| {
                var buffer: [64]u8 = undefined;
                const name = try std.fmt.bufPrint(&buffer, "item-{d:0>5}", .{index});
                try std.testing.expectEqualStrings(name, row.object.get("name").?.string);
            }
        }
        if (count != 0) {
            try std.testing.expectEqual(@as(u64, 3), reverse.counterFor("item-00000").?.total);
            try std.testing.expectEqual(@as(usize, 2), reverse.counterFor("item-00000").?.sample_count);
        }
    }
}

fn recordReportFixture(profiler: *Profiler, index: usize) !void {
    var buffer: [64]u8 = undefined;
    const name = try std.fmt.bufPrint(&buffer, "item-{d:0>5}", .{index});
    profiler.recordObservation(name, .{ .duration_microseconds = index, .cpu_duration_microseconds = index * 2 });
    profiler.recordCounter(name, index + 1);
    profiler.recordCounter(name, index + 2);
}

test "profiler report allocation failures preserve the owner" {
    var profiler = Profiler.init(std.testing.allocator, std.testing.io);
    defer profiler.deinit();
    for (0..4) |index| try recordReportFixture(&profiler, 3 - index);
    const before = try profiler.reportJsonAlloc(std.testing.allocator);
    defer std.testing.allocator.free(before);
    const before_text = try profiler.reportAlloc(std.testing.allocator);
    defer std.testing.allocator.free(before_text);
    for ([_]bool{ false, true }) |json|
        try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseReportAllocation, .{ &profiler, json });
    const after_text = try profiler.reportAlloc(std.testing.allocator);
    defer std.testing.allocator.free(after_text);
    try std.testing.expectEqualStrings(before_text, after_text);
    try std.testing.expect(profiler.recording_failure == null);
    const after = try profiler.reportJsonAlloc(std.testing.allocator);
    defer std.testing.allocator.free(after);
    try std.testing.expectEqualStrings(before, after);
}

fn exerciseReportAllocation(allocator: std.mem.Allocator, profiler: *Profiler, json: bool) !void {
    const report = if (json) try profiler.reportJsonAlloc(allocator) else try profiler.reportAlloc(allocator);
    defer allocator.free(report);
}

test "profiler deferred recording failures reject partial reports" {
    for (std.enums.values(RecordingKind)) |kind|
        try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseRecordingAllocation, .{kind});
}

const RecordingKind = enum { scope, counter, probe, deferred_probe };

fn exerciseRecordingAllocation(allocator: std.mem.Allocator, kind: RecordingKind) !void {
    var profiler = Profiler.init(allocator, std.testing.io);
    defer profiler.deinit();
    for (0..32) |index| {
        var buffer: [32]u8 = undefined;
        const name = try std.fmt.bufPrint(&buffer, "item-{d:0>5}", .{index});
        switch (kind) {
            .scope => profiler.recordObservation(name, .{ .duration_microseconds = index, .cpu_duration_microseconds = index * 2 }),
            .counter => profiler.recordCounter(name, index + 1),
            .probe => {
                var probe = profiler.probe(name);
                try std.testing.expect(probe.finish() != null);
            },
            .deferred_probe => {
                var probe = OptionalProbe.init(&profiler, name);
                defer probe.deinit();
            },
        }
        if (profiler.recording_failure) |err| {
            try std.testing.expectEqual(index, profiler.metrics.count() + profiler.counters.count());
            try std.testing.expect(profiler.metricsFor(name) == null);
            try std.testing.expect(profiler.counterFor(name) == null);
            profiler.recordCounter("after failure", 1);
            profiler.recordObservation("after failure", .{ .duration_microseconds = 1, .cpu_duration_microseconds = 1 });
            try std.testing.expectError(err, profiler.tryRecordCounter("after failure", 1));
            try std.testing.expectEqual(index, profiler.metrics.count() + profiler.counters.count());
            try expectIncompleteProfile(&profiler);
            return err;
        }
        // Every name must already be owned before this stack buffer is reused.
        @memset(&buffer, '#');
    }
    for (0..32) |index| {
        var buffer: [32]u8 = undefined;
        const name = try std.fmt.bufPrint(&buffer, "item-{d:0>5}", .{index});
        switch (kind) {
            .scope, .probe, .deferred_probe => try std.testing.expectEqual(@as(usize, 1), profiler.metricsFor(name).?.call_count),
            .counter => try std.testing.expectEqual(@as(u64, index + 1), profiler.counterFor(name).?.total),
        }
    }
    const report = try profiler.reportJsonAlloc(std.testing.allocator);
    defer std.testing.allocator.free(report);
}

fn expectIncompleteProfile(profiler: *Profiler) !void {
    try std.testing.expectError(error.OutOfMemory, profiler.reportAlloc(std.testing.allocator));
    try std.testing.expectError(error.OutOfMemory, profiler.reportJsonAlloc(std.testing.allocator));
}

test "profiler fallible counter insertion is transactional and retryable" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseCounterAllocation, .{});
    var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{ .fail_index = 0 });
    var profiler = Profiler.init(failing.allocator(), std.testing.io);
    defer profiler.deinit();
    try std.testing.expectError(error.OutOfMemory, profiler.tryRecordCounter("retry", 3));
    failing.fail_index = std.math.maxInt(usize);
    try profiler.tryRecordCounter("retry", 7);
    try std.testing.expectEqual(@as(u64, 7), profiler.counterFor("retry").?.total);
    try std.testing.expect(profiler.recording_failure == null);
    const report = try profiler.reportJsonAlloc(std.testing.allocator);
    defer std.testing.allocator.free(report);
}

fn exerciseCounterAllocation(allocator: std.mem.Allocator) !void {
    var profiler = Profiler.init(allocator, std.testing.io);
    defer profiler.deinit();
    for (0..32) |index| {
        var buffer: [32]u8 = undefined;
        const name = try std.fmt.bufPrint(&buffer, "counter-{d}", .{index});
        profiler.tryRecordCounter(name, index + 1) catch |err| {
            try std.testing.expectEqual(index, profiler.counters.count());
            try std.testing.expect(profiler.counterFor(name) == null);
            try std.testing.expect(profiler.recording_failure == null);
            for (0..index) |prior| {
                const prior_name = try std.fmt.bufPrint(&buffer, "counter-{d}", .{prior});
                try std.testing.expectEqual(@as(u64, prior + 1), profiler.counterFor(prior_name).?.total);
                try std.testing.expectEqual(@as(usize, 1), profiler.counterFor(prior_name).?.sample_count);
            }
            return err;
        };
    }
}

test "profiler existing keys update without allocation and totals saturate" {
    var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
    var profiler = Profiler.init(failing.allocator(), std.testing.io);
    defer profiler.deinit();
    var name = [_]u8{ 'o', 'w', 'n', 'e', 'd' };
    profiler.recordObservation(&name, .{ .duration_microseconds = std.math.maxInt(u64), .cpu_duration_microseconds = std.math.maxInt(u64) });
    profiler.recordCounter(&name, std.math.maxInt(u64));
    @memset(&name, '#');
    profiler.metrics.getPtr("owned").?.call_count = std.math.maxInt(usize);
    profiler.counters.getPtr("owned").?.sample_count = std.math.maxInt(usize);
    failing.fail_index = failing.alloc_index;
    failing.resize_fail_index = failing.resize_index;
    profiler.recordObservation("owned", .{ .duration_microseconds = 7, .cpu_duration_microseconds = 9 });
    profiler.recordCounter("owned", 11);
    try profiler.tryRecordCounter("owned", 13);
    try std.testing.expect(!failing.has_induced_failure);
    try std.testing.expectEqualDeep(Metrics{
        .duration_microseconds = std.math.maxInt(u64),
        .maximum_duration_microseconds = std.math.maxInt(u64),
        .cpu_duration_microseconds = std.math.maxInt(u64),
        .maximum_cpu_duration_microseconds = std.math.maxInt(u64),
        .call_count = std.math.maxInt(usize),
    }, profiler.metricsFor("owned").?);
    try std.testing.expectEqualDeep(CounterMetrics{
        .total = std.math.maxInt(u64),
        .maximum = std.math.maxInt(u64),
        .sample_count = std.math.maxInt(usize),
    }, profiler.counterFor("owned").?);
    const report = try profiler.reportJsonAlloc(std.testing.allocator);
    defer std.testing.allocator.free(report);
}

test "profiler concurrent publication preserves owned entries and failure state" {
    const Worker = struct {
        fn run(profiler: *Profiler, worker: usize) void {
            var buffer: [32]u8 = undefined;
            const name = std.fmt.bufPrint(&buffer, "worker-{d}", .{worker}) catch unreachable;
            for (0..50) |_| {
                profiler.recordObservation("shared", .{ .duration_microseconds = 1, .cpu_duration_microseconds = 2 });
                profiler.recordCounter("shared", 1);
                profiler.recordObservation(name, .{ .duration_microseconds = 3, .cpu_duration_microseconds = 4 });
                profiler.recordCounter(name, 5);
            }
        }
    };
    var threaded = std.Io.Threaded.init(std.testing.allocator, .{ .async_limit = .limited(4) });
    defer threaded.deinit();
    const io = threaded.io();
    for ([_]bool{ false, true }) |fail| {
        var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{
            .fail_index = if (fail) 2 else std.math.maxInt(usize),
        });
        var profiler = Profiler.init(failing.allocator(), io);
        defer profiler.deinit();
        var group: std.Io.Group = .init;
        defer group.cancel(io);
        for (0..4) |index| try group.concurrent(io, Worker.run, .{ &profiler, index });
        try group.await(io);
        if (fail) {
            try std.testing.expect(failing.has_induced_failure);
            try expectIncompleteProfile(&profiler);
        } else {
            var sequential = Profiler.init(std.testing.allocator, io);
            defer sequential.deinit();
            for (0..4) |index| Worker.run(&sequential, index);
            const expected = try sequential.reportJsonAlloc(std.testing.allocator);
            defer std.testing.allocator.free(expected);
            const actual = try profiler.reportJsonAlloc(std.testing.allocator);
            defer std.testing.allocator.free(actual);
            try std.testing.expectEqualStrings(expected, actual);
        }
    }
}

test "profiler text reports retain duration ties and counter insertion order" {
    var profiler = Profiler.init(std.testing.allocator, std.testing.io);
    defer profiler.deinit();
    profiler.recordObservation("last", .{ .duration_microseconds = 2_000_000, .cpu_duration_microseconds = 3_000_000 });
    profiler.recordObservation("first tie", .{ .duration_microseconds = 1_000_000, .cpu_duration_microseconds = 2_000_000 });
    profiler.recordObservation("second tie", .{ .duration_microseconds = 1_000_000, .cpu_duration_microseconds = 1_000_000 });
    profiler.recordCounter("z-counter", 3);
    profiler.recordCounter("a-counter", 9);
    profiler.recordCounter("z-counter", 5);
    const report = try profiler.reportAlloc(std.testing.allocator);
    defer std.testing.allocator.free(report);
    try std.testing.expectEqualStrings(
        "PERFORMANCE METRICS FOR PROFILED SCOPES\n\n" ++
            "| Wall % | Wall       | CPU        | Calls   | Scope                          |\n" ++
            "|-------:|-----------:|-----------:|--------:|--------------------------------|\n" ++
            "|  25.0% |    1.000 s |    2.000 s |       1 | first tie |\n" ++
            "|  25.0% |    1.000 s |    1.000 s |       1 | second tie |\n" ++
            "|  50.0% |    2.000 s |    3.000 s |       1 | last |\n" ++
            "| 100.0% |    4.000 s |    6.000 s |       3 | **TOTAL** |\n" ++
            "\nWORKLOAD COUNTERS\n\n" ++
            "| Total               | Maximum             | Samples | Counter |\n" ++
            "|--------------------:|--------------------:|--------:|---------|\n" ++
            "|                   8 |                   5 |       2 | z-counter |\n" ++
            "|                   9 |                   9 |       1 | a-counter |\n",
        report,
    );
}

test "profiler text reports support empty and counter-only inventories" {
    var profiler = Profiler.init(std.testing.allocator, std.testing.io);
    defer profiler.deinit();
    const empty = try profiler.reportAlloc(std.testing.allocator);
    defer std.testing.allocator.free(empty);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseReportAllocation, .{ &profiler, false });
    try std.testing.expectEqualStrings(
        "PERFORMANCE METRICS FOR PROFILED SCOPES\n\n" ++
            "| Wall % | Wall       | CPU        | Calls   | Scope                          |\n" ++
            "|-------:|-----------:|-----------:|--------:|--------------------------------|\n" ++
            "| 100.0% |    0.000 s |    0.000 s |       0 | **TOTAL** |\n",
        empty,
    );
    profiler.recordCounter("only counter", 7);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseReportAllocation, .{ &profiler, false });
    const counter_only = try profiler.reportAlloc(std.testing.allocator);
    defer std.testing.allocator.free(counter_only);
    const expected = try std.mem.concat(std.testing.allocator, u8, &.{
        empty,
        "\nWORKLOAD COUNTERS\n\n" ++
            "| Total               | Maximum             | Samples | Counter |\n" ++
            "|--------------------:|--------------------:|--------:|---------|\n" ++
            "|                   7 |                   7 |       1 | only counter |\n",
    });
    defer std.testing.allocator.free(expected);
    try std.testing.expectEqualStrings(expected, counter_only);
}
