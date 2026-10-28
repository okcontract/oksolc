// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Borrowed compilation ancestry, propagated to joined backend workers.
//! Every frame and its parents must outlive all activations on other threads.

const std = @import("std");

pub const Frame = struct {
    session: *const anyopaque,
    parent: ?*const Frame,
};

threadlocal var active: ?*const Frame = null;

pub fn capture() ?*const Frame {
    return active;
}

pub fn contains(session: *const anyopaque) bool {
    var frame = active;
    while (frame) |current| : (frame = current.parent)
        if (current.session == session) return true;
    return false;
}

pub const Activation = struct {
    frame: ?*const Frame,
    previous: ?*const Frame,

    pub fn deinit(self: Activation) void {
        std.debug.assert(active == self.frame);
        active = self.previous;
    }
};

pub fn activate(frame: ?*const Frame) Activation {
    const result: Activation = .{ .frame = frame, .previous = active };
    active = frame;
    return result;
}
