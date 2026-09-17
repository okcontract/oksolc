// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Ownership-explicit translation of the callback surface in `ReadFile.h`.

const std = @import("std");

pub const ReadCallback = struct {
    pub const Kind = enum {
        read_file,
        smt_query,

        pub fn string(self: Kind) []const u8 {
            return switch (self) {
                .read_file => "source",
                .smt_query => "smt-query",
            };
        }
    };

    /// Owned callback result. The response contains either source contents or
    /// the diagnostic suffix returned by the host callback.
    pub const Result = struct {
        allocator: std.mem.Allocator,
        success: bool,
        response_or_error_message: []u8,

        pub fn init(
            allocator: std.mem.Allocator,
            success: bool,
            response_or_error_message: []const u8,
        ) std.mem.Allocator.Error!Result {
            return .{
                .allocator = allocator,
                .success = success,
                .response_or_error_message = try allocator.dupe(
                    u8,
                    response_or_error_message,
                ),
            };
        }

        pub fn deinit(self: *Result) void {
            self.allocator.free(self.response_or_error_message);
            self.* = undefined;
        }
    };

    pub const ReadError = error{
        OutOfMemory,
        InvalidPath,
        InternalFailure,
    };

    context: ?*anyopaque,
    read_fn: *const fn (
        context: ?*anyopaque,
        allocator: std.mem.Allocator,
        kind: []const u8,
        data: []const u8,
    ) ReadError!Result,

    pub fn read(
        self: ReadCallback,
        allocator: std.mem.Allocator,
        kind: Kind,
        data: []const u8,
    ) ReadError!Result {
        return self.read_fn(self.context, allocator, kind.string(), data);
    }
};

test "read callback exposes owned success and failure results" {
    const Callback = struct {
        fn read(
            _: ?*anyopaque,
            allocator: std.mem.Allocator,
            kind: []const u8,
            data: []const u8,
        ) ReadCallback.ReadError!ReadCallback.Result {
            if (!std.mem.eql(u8, "source", kind)) return error.InternalFailure;
            return ReadCallback.Result.init(
                allocator,
                std.mem.eql(u8, data, "A.sol"),
                if (std.mem.eql(u8, data, "A.sol")) "contract A {}" else "missing",
            );
        }
    };

    const callback: ReadCallback = .{ .context = null, .read_fn = Callback.read };
    var success = try callback.read(std.testing.allocator, .read_file, "A.sol");
    defer success.deinit();
    try std.testing.expect(success.success);
    try std.testing.expectEqualStrings("contract A {}", success.response_or_error_message);

    var failure = try callback.read(std.testing.allocator, .read_file, "B.sol");
    defer failure.deinit();
    try std.testing.expect(!failure.success);
    try std.testing.expectEqualStrings("missing", failure.response_or_error_message);
}
