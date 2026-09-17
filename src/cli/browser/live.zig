// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Small publication status shared with HTTP readers. Compiler/session state
//! stays owned by the source watcher; only immutable SQL snapshots are exposed.
const std = @import("std");
const StandardJson = @import("solidity").standard_json;

pub const Status = struct {
    pub const State = struct {
        phase: enum { starting, reading, checking, watching, compiling, publishing, stale, stopped } = .watching,
        failure: ?[]const u8 = null,
        stage: ?StandardJson.ProgressStage = null,
        completed_items: usize = 0,
        total_items: usize = 0,
        item: [512]u8 = undefined,
        item_len: usize = 0,
    };
    pub const Snapshot = struct {
        state: State = .{},
        latest: ?i64 = null,
        current: ?i64 = null,
        workspace_revision: u64 = 0,
        reused: bool = false,
    };
    io: std.Io,
    /// Borrowed immutable configuration; outlives all workers.
    source_path: []const u8,
    mutex: std.Io.Mutex = .init,
    snapshot: Snapshot = .{},

    pub fn set(self: *Status, state: State) void {
        self.mutex.lockUncancelable(self.io);
        defer self.mutex.unlock(self.io);
        self.snapshot.state = state;
    }

    pub fn get(self: *Status) Snapshot {
        self.mutex.lockUncancelable(self.io);
        defer self.mutex.unlock(self.io);
        return self.snapshot;
    }

    pub fn workspaceChanged(self: *Status) void {
        self.mutex.lockUncancelable(self.io);
        defer self.mutex.unlock(self.io);
        self.snapshot.workspace_revision += 1;
    }

    pub fn published(self: *Status, id: i64, reused: bool) void {
        self.mutex.lockUncancelable(self.io);
        defer self.mutex.unlock(self.io);
        self.snapshot.latest = id;
        self.snapshot.current = id;
        self.snapshot.reused = reused;
        self.snapshot.state = .{ .phase = .watching };
    }

    pub fn reporter(self: *Status) StandardJson.ProgressReporter {
        return .{ .context = self, .report_fn = report };
    }

    fn report(context: ?*anyopaque, update: StandardJson.ProgressUpdate) void {
        const self: *Status = @ptrCast(@alignCast(context.?));
        var state: State = .{ .phase = .compiling, .stage = update.stage, .completed_items = update.completed_items, .total_items = update.estimated_total_items };
        state.item_len = copyName(&state.item, update.item_name);
        self.mutex.lockUncancelable(self.io);
        defer self.mutex.unlock(self.io);
        self.snapshot.state = state;
    }

    fn copyName(destination: *[512]u8, name: []const u8) usize {
        var len = @min(destination.len, name.len);
        while (!std.unicode.utf8ValidateSlice(name[0..len])) len -= 1;
        @memcpy(destination[0..len], name[0..len]);
        return len;
    }
};

test "live progress owns borrowed names and keeps snapshot identity across stages" {
    var status: Status = .{ .io = std.testing.io, .source_path = "src" };
    status.published(7, false);
    var name = [_]u8{'x'} ** 520;
    status.reporter().report(.{ .stage = .generating_contracts, .completed_items = 2, .estimated_total_items = 8, .item_name = &name });
    @memset(&name, 'y');
    const snapshot = status.get();
    try std.testing.expectEqual(@as(?i64, 7), snapshot.latest);
    try std.testing.expectEqual(@as(usize, 2), snapshot.state.completed_items);
    try std.testing.expectEqual(@as(usize, 512), snapshot.state.item_len);
    try std.testing.expectEqual(@as(u8, 'x'), snapshot.state.item[0]);
    status.set(.{ .phase = .publishing });
    try std.testing.expectEqual(@as(?i64, 7), status.get().latest);
}
