// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! One sample for each of initial use, reuse without reset, and use after reset.
//! Timing includes thread startup/join; canonicality checks run afterward.
const std = @import("std");
const strings = @import("yul_string");
const YulString = strings.YulString;
pub const yul_interner_shards = @import("benchmark_options").shards;

const max_workers = 10;
const names = 8192;
const long_names = names / 32;
const Context = struct {
    start: std.atomic.Value(bool) = .init(false),
    failed: std.atomic.Value(bool) = .init(false),
    shared: [max_workers][names]YulString = undefined,
    generated: [max_workers][names]YulString = undefined,
    long_generated: [max_workers][long_names]YulString = undefined,

    fn run(self: *@This(), worker: usize) void {
        while (!self.start.load(.acquire)) std.atomic.spinLoopHint();
        self.fill(worker) catch self.failed.store(true, .release);
    }

    fn fill(self: *@This(), worker: usize) !void {
        var buffer: [64]u8 = undefined;
        const base = try YulString.init("shared_base");
        for (0..names) |i| {
            self.shared[worker][i] = try YulString.init(try std.mem.print(&buffer, "shared_{d}", .{i}));
            self.generated[worker][i] = try YulString.initGenerated(base, i);
            _ = try YulString.init(try std.mem.print(&buffer, "private_{d}_{d}", .{ worker, i }));
        }
        const long_bytes: [300]u8 = @splat('x');
        const long_base = try YulString.init(&long_bytes);
        for (0..long_names) |i|
            self.long_generated[worker][i] = try YulString.initGenerated(long_base, i);
    }

    fn validate(self: *const @This(), workers: usize) !void {
        for (1..workers) |worker| {
            for (0..names) |i| {
                if (!self.shared[0][i].eql(self.shared[worker][i]) or
                    !self.generated[0][i].eql(self.generated[worker][i])) return error.NonCanonicalYulString;
            }
            for (0..long_names) |i| {
                if (!self.long_generated[0][i].eql(self.long_generated[worker][i])) return error.NonCanonicalYulString;
            }
        }
        var buffer: [384]u8 = undefined;
        const long_bytes: [300]u8 = @splat('x');
        for (0..names) |i| {
            if (!self.generated[0][i].eql(try YulString.init(try std.mem.print(&buffer, "shared_base_{d}", .{i}))))
                return error.NonCanonicalYulString;
        }
        for (0..long_names) |i| {
            if (!self.long_generated[0][i].eql(try YulString.init(try std.mem.print(&buffer, "{s}_{d}", .{ long_bytes, i }))))
                return error.NonCanonicalYulString;
        }
    }
};

const Measurement = struct { wall_nanoseconds: u64, cumulative_peak_rss_bytes: u64 };

fn measure(io: std.Io, context: *Context, workers: usize) !Measurement {
    context.start.store(false, .release);
    context.failed.store(false, .release);
    const start = std.Io.Clock.awake.now(io);
    {
        var threads: [max_workers]std.Thread = undefined;
        var spawned: usize = 0;
        defer {
            context.start.store(true, .release);
            for (threads[0..spawned]) |thread| thread.join();
        }
        for (threads[0..workers], 0..) |*thread, worker| {
            thread.* = try std.Thread.spawn(.{}, Context.run, .{ context, worker });
            spawned += 1;
        }
    }
    const elapsed = start.durationTo(std.Io.Clock.awake.now(io)).nanoseconds;
    if (context.failed.load(.acquire)) return error.InternerWorkerFailed;
    try context.validate(workers);
    const rss: u64 = @intCast(std.posix.getrusage(std.posix.rusage.SELF).maxrss);
    return .{
        .wall_nanoseconds = @intCast(elapsed),
        .cumulative_peak_rss_bytes = if (@import("builtin").os.tag == .macos) rss else rss * 1024,
    };
}

pub fn main(init: std.process.Init) !void {
    var args = try init.minimal.args.iterateAllocator(init.gpa);
    defer args.deinit();
    _ = args.next();
    const workers = try std.fmt.parseInt(usize, args.next() orelse return error.ExpectedWorkerCount, 10);
    if (workers == 0 or workers > max_workers or args.next() != null) return error.InvalidWorkerCount;
    const context = try init.gpa.create(Context);
    defer init.gpa.destroy(context);
    context.* = .{};
    try strings.reset();
    errdefer strings.reset() catch |err| std.log.err("interner cleanup failed: {s}", .{@errorName(err)});
    try strings.setSharded(workers > 1);
    const initial = try measure(init.io, context, workers);
    const reused = try measure(init.io, context, workers);
    try strings.reset();
    try strings.setSharded(workers > 1);
    const after_reset = try measure(init.io, context, workers);
    try strings.reset();
    const report = try std.json.Stringify.valueAlloc(init.gpa, .{
        .shards = if (workers > 1) yul_interner_shards else 1,
        .workers = workers,
        .names_per_worker = names,
        .samples_per_stage = 1,
        .warmups = 0,
        .canonicality_verified = true,
        .initial = initial,
        .reused = reused,
        .after_reset = after_reset,
    }, .{ .whitespace = .indent_2 });
    defer init.gpa.free(report);
    try std.Io.File.stdout().writeStreamingAll(init.io, report);
    try std.Io.File.stdout().writeStreamingAll(init.io, "\n");
}
