// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Replays a retained counter inventory in reverse publication order. Only
//! report construction is timed; parsing, ownership setup, and file output
//! remain outside the interval. Build against either profiler revision.

const std = @import("std");
const Profiler = @import("profiler").Profiler;

const Counter = struct {
    name: []const u8,
    total: u64,
    maximum: u64,
    sample_count: usize,
};
const Input = struct { counters: []const Counter };

pub fn main(init: std.process.Init) !void {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    if (args.len != 4) return error.ExpectedInputReportAndMeasurementPaths;
    const input = try std.Io.Dir.cwd().readFileAlloc(init.io, args[1], init.gpa, .limited(64 * 1024 * 1024));
    defer init.gpa.free(input);
    const parsed = try std.json.parseFromSlice(Input, init.gpa, input, .{ .ignore_unknown_fields = true });
    defer parsed.deinit();
    var profiler = Profiler.init(init.gpa, init.io);
    defer profiler.deinit();
    for (0..parsed.value.counters.len) |index| {
        const row = parsed.value.counters[parsed.value.counters.len - index - 1];
        if (profiler.counterFor(row.name) != null) return error.DuplicateCounter;
        try profiler.tryRecordCounter(row.name, row.total);
        profiler.counters.getPtr(row.name).?.* = .{
            .total = row.total,
            .maximum = row.maximum,
            .sample_count = row.sample_count,
        };
    }
    const start = std.Io.Clock.Timestamp.now(init.io, .awake);
    const start_cpu = std.Io.Clock.Timestamp.now(init.io, .cpu_process);
    const report = try profiler.reportJsonAlloc(init.gpa);
    const end_cpu = std.Io.Clock.Timestamp.now(init.io, .cpu_process);
    const end = std.Io.Clock.Timestamp.now(init.io, .awake);
    defer init.gpa.free(report);
    const measurement = try std.json.Stringify.valueAlloc(init.gpa, .{
        .counter_count = parsed.value.counters.len,
        .report_bytes = report.len,
        .wall_nanoseconds = start.durationTo(end).raw.nanoseconds,
        .cpu_nanoseconds = start_cpu.durationTo(end_cpu).raw.nanoseconds,
    }, .{});
    defer init.gpa.free(measurement);
    try writeFile(init.io, args[2], report);
    try writeFile(init.io, args[3], measurement);
}

fn writeFile(io: std.Io, path: []const u8, bytes: []const u8) !void {
    var file = try std.Io.Dir.cwd().createFile(io, path, .{});
    defer file.close(io);
    try file.writeStreamingAll(io, bytes);
}
