// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Manual-vtable translation of `CharStreamProvider.h`.

const std = @import("std");
const CharStream = @import("char_stream.zig").CharStream;

pub const ProviderError = error{SourceNameMismatch};

pub const CharStreamProvider = struct {
    context: *const anyopaque,
    get_fn: *const fn (*const anyopaque, []const u8) ProviderError!*const CharStream,

    pub fn charStream(
        self: CharStreamProvider,
        source_name: []const u8,
    ) ProviderError!*const CharStream {
        return self.get_fn(self.context, source_name);
    }
};

pub const SingletonCharStreamProvider = struct {
    stream: *const CharStream,

    pub fn init(stream: *const CharStream) SingletonCharStreamProvider {
        return .{ .stream = stream };
    }

    pub fn provider(self: *const SingletonCharStreamProvider) CharStreamProvider {
        return .{ .context = self, .get_fn = get };
    }

    fn get(context: *const anyopaque, source_name: []const u8) ProviderError!*const CharStream {
        const self: *const SingletonCharStreamProvider = @ptrCast(@alignCast(context));
        if (!std.mem.eql(u8, self.stream.name(), source_name)) {
            return error.SourceNameMismatch;
        }
        return self.stream;
    }
};

test "singleton provider validates the requested source name" {
    const stream = CharStream.initBorrowed("source", "a.sol");
    const singleton = SingletonCharStreamProvider.init(&stream);
    const provider = singleton.provider();
    try std.testing.expectEqual(&stream, try provider.charStream("a.sol"));
    try std.testing.expectError(error.SourceNameMismatch, provider.charStream("b.sol"));
}
