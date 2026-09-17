// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Explicit Zig error classes and owned stack-depth diagnostic payload.

const std = @import("std");
const YulName = @import("yul_name.zig").YulName;

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

    pub fn deinit(self: *StackTooDeepError) void {
        self.allocator.free(self.message);
        self.* = undefined;
    }
};
