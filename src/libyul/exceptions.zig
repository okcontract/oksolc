// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Explicit Zig error classes and owned stack-depth diagnostic payload.

const std = @import("std");
const YulName = @import("yul_name.zig").YulName;
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;

pub const YulError = error{
    YulException,
    OptimizerException,
    CodegenException,
    YulAssertion,
    StackTooDeep,
};

pub const StackTooDeepError = struct {
    allocator: std.mem.Allocator,
    function_name: YulName = .{},
    variable: YulName,
    depth: i32,
    message: []u8,
    /// Borrows source names from the input AST, not the backend scratch arena.
    location: SourceLocation = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        variable: YulName,
        depth: i32,
        message: []const u8,
    ) std.mem.Allocator.Error!StackTooDeepError {
        return .{
            .allocator = allocator,
            .variable = variable,
            .depth = depth,
            .message = try allocator.dupe(u8, message),
        };
    }

    pub fn initInFunction(
        allocator: std.mem.Allocator,
        function_name: YulName,
        variable: YulName,
        depth: i32,
        message: []const u8,
    ) std.mem.Allocator.Error!StackTooDeepError {
        var result = try init(allocator, variable, depth, message);
        result.function_name = function_name;
        return result;
    }

    /// Consumes the owned diagnostic on both success and failure. The list
    /// becomes its sole owner only after publication succeeds.
    pub fn appendTo(
        self: StackTooDeepError,
        allocator: std.mem.Allocator,
        errors: *std.ArrayList(StackTooDeepError),
    ) std.mem.Allocator.Error!void {
        var owned = self;
        errdefer owned.deinit();
        try errors.append(allocator, owned);
    }

    pub fn deinit(self: *StackTooDeepError) void {
        self.allocator.free(self.message);
        self.* = undefined;
    }
};

test "stack diagnostic publication transfers messages and releases allocation failures" {
    const Check = struct {
        fn run(allocator: std.mem.Allocator, function: YulName, variable: YulName) !void {
            var errors: std.ArrayList(StackTooDeepError) = .empty;
            defer {
                for (errors.items) |*value| value.deinit();
                errors.deinit(allocator);
            }
            const owned = try StackTooDeepError.initInFunction(allocator, function, variable, 3, "stack diagnostic");
            const message_pointer = owned.message.ptr;
            try owned.appendTo(allocator, &errors);
            try std.testing.expectEqual(@as(usize, 1), errors.items.len);
            try std.testing.expectEqual(message_pointer, errors.items[0].message.ptr);
            try std.testing.expectEqual(function, errors.items[0].function_name);
            try std.testing.expectEqual(variable, errors.items[0].variable);
            try std.testing.expectEqual(@as(i32, 3), errors.items[0].depth);
            try std.testing.expectEqualStrings("stack diagnostic", errors.items[0].message);
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{
        try YulName.init("function"), try YulName.init("variable"),
    });
}
