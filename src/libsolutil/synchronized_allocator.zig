// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Mutex-serialized adapter for allocators shared by compiler workers.

const std = @import("std");

/// The adapter borrows `child`. It may move before `allocator()` is called,
/// but must remain at a stable address while a returned allocator is in use.
pub const SynchronizedAllocator = struct {
    child: std.mem.Allocator,
    mutex: std.Io.Mutex = .init,

    pub fn init(child: std.mem.Allocator) SynchronizedAllocator {
        return .{ .child = child };
    }

    pub fn allocator(self: *SynchronizedAllocator) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(
        opaque_self: *anyopaque,
        len: usize,
        alignment: std.mem.Alignment,
        return_address: usize,
    ) ?[*]u8 {
        const self: *SynchronizedAllocator = @ptrCast(@alignCast(opaque_self));
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        return self.child.rawAlloc(len, alignment, return_address);
    }

    fn resize(
        opaque_self: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_len: usize,
        return_address: usize,
    ) bool {
        const self: *SynchronizedAllocator = @ptrCast(@alignCast(opaque_self));
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        return self.child.rawResize(memory, alignment, new_len, return_address);
    }

    fn remap(
        opaque_self: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_len: usize,
        return_address: usize,
    ) ?[*]u8 {
        const self: *SynchronizedAllocator = @ptrCast(@alignCast(opaque_self));
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        return self.child.rawRemap(memory, alignment, new_len, return_address);
    }

    fn free(
        opaque_self: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        return_address: usize,
    ) void {
        const self: *SynchronizedAllocator = @ptrCast(@alignCast(opaque_self));
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        self.child.rawFree(memory, alignment, return_address);
    }
};

test "synchronized allocator preserves child ownership" {
    var synchronized = SynchronizedAllocator.init(std.testing.allocator);
    const allocator = synchronized.allocator();
    const bytes = try allocator.dupe(u8, "shared");
    defer allocator.free(bytes);
    try std.testing.expectEqualStrings("shared", bytes);
}
