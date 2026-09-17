// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Generate-once Yul function collector translated from
//! `MultiUseYulFunctionCollector.cpp`.

const std = @import("std");
const StringUtils = @import("../../libsolutil/string_utils.zig");
const WhiskersModule = @import("../../libsolutil/whiskers.zig");

pub const CollectorError = std.mem.Allocator.Error || WhiskersModule.WhiskersError || error{
    EmptyFunctionName,
    EmptyFunction,
    ImproperFunctionName,
};

pub const FunctionCreator = struct {
    context: *anyopaque,
    create_fn: *const fn (*anyopaque, std.mem.Allocator) anyerror![]u8,

    pub fn create(self: FunctionCreator, allocator: std.mem.Allocator) ![]u8 {
        return self.create_fn(self.context, allocator);
    }
};

pub const StructuredFunctionCreator = struct {
    context: *anyopaque,
    create_fn: *const fn (
        *anyopaque,
        std.mem.Allocator,
        *std.ArrayList([]const u8),
        *std.ArrayList([]const u8),
    ) anyerror![]u8,

    pub fn create(
        self: StructuredFunctionCreator,
        allocator: std.mem.Allocator,
        arguments: *std.ArrayList([]const u8),
        returns: *std.ArrayList([]const u8),
    ) ![]u8 {
        return self.create_fn(self.context, allocator, arguments, returns);
    }
};

pub const MultiUseYulFunctionCollector = struct {
    allocator: std.mem.Allocator,
    requested_functions: std.array_hash_map.String(void) = .empty,
    code: std.ArrayList(u8) = .empty,

    pub fn init(allocator: std.mem.Allocator) MultiUseYulFunctionCollector {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *MultiUseYulFunctionCollector) void {
        self.clearRequestedNames();
        self.requested_functions.deinit(self.allocator);
        self.code.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn contains(self: *const MultiUseYulFunctionCollector, name: []const u8) bool {
        return self.requested_functions.contains(name);
    }

    /// Split-phase form of `createFunction` used by Zig generators that need
    /// to request nested helpers while constructing a function body. A true
    /// result transfers responsibility to call either `finishFunction` or
    /// `abortFunction`.
    pub fn beginFunction(
        self: *MultiUseYulFunctionCollector,
        name: []const u8,
    ) (std.mem.Allocator.Error || error{EmptyFunctionName})!bool {
        if (name.len == 0) return error.EmptyFunctionName;
        return self.register(name);
    }

    pub fn finishFunction(
        self: *MultiUseYulFunctionCollector,
        name: []const u8,
        function_code: []const u8,
    ) CollectorError!void {
        if (!self.contains(name)) return error.ImproperFunctionName;
        if (function_code.len == 0) return error.EmptyFunction;
        try self.validateFunctionName(name, function_code);
        try self.code.appendSlice(self.allocator, function_code);
    }

    pub fn abortFunction(self: *MultiUseYulFunctionCollector, name: []const u8) void {
        self.unregister(name);
    }

    pub fn copyFunctionName(
        self: *const MultiUseYulFunctionCollector,
        name: []const u8,
    ) std.mem.Allocator.Error![]u8 {
        return self.allocator.dupe(u8, name);
    }

    /// Registers before invoking the creator, preserving upstream's recursion
    /// guard when one utility requests another utility while being generated.
    pub fn createFunction(
        self: *MultiUseYulFunctionCollector,
        name: []const u8,
        creator: FunctionCreator,
    ) anyerror![]u8 {
        if (name.len == 0) return error.EmptyFunctionName;
        const inserted = try self.register(name);
        if (inserted) {
            errdefer self.unregister(name);
            const function_code = try creator.create(self.allocator);
            defer self.allocator.free(function_code);
            if (function_code.len == 0) return error.EmptyFunction;
            try self.validateFunctionName(name, function_code);
            try self.code.appendSlice(self.allocator, function_code);
        }
        return self.allocator.dupe(u8, name);
    }

    pub fn createStructuredFunction(
        self: *MultiUseYulFunctionCollector,
        name: []const u8,
        creator: StructuredFunctionCreator,
    ) anyerror![]u8 {
        if (name.len == 0) return error.EmptyFunctionName;
        const inserted = try self.register(name);
        if (inserted) {
            errdefer self.unregister(name);
            var arguments: std.ArrayList([]const u8) = .empty;
            defer arguments.deinit(self.allocator);
            var returns: std.ArrayList([]const u8) = .empty;
            defer returns.deinit(self.allocator);
            const body = try creator.create(self.allocator, &arguments, &returns);
            defer self.allocator.free(body);
            if (body.len == 0) return error.EmptyFunction;

            const joined_arguments = try StringUtils.joinHumanReadableAlloc(
                self.allocator,
                arguments.items,
                ", ",
                "",
            );
            defer self.allocator.free(joined_arguments);
            const joined_returns = try StringUtils.joinHumanReadableAlloc(
                self.allocator,
                returns.items,
                ", ",
                "",
            );
            defer self.allocator.free(joined_returns);

            var whiskers = try WhiskersModule.Whiskers.init(self.allocator,
                \\function <functionName>(<args>)<?+retParams> -> <retParams></+retParams> {
                \\    <body>
                \\}
            );
            defer whiskers.deinit();
            _ = try whiskers.setString("functionName", name);
            _ = try whiskers.setString("args", joined_arguments);
            _ = try whiskers.setString("retParams", joined_returns);
            _ = try whiskers.setString("body", body);
            const function_code = try whiskers.renderAlloc(self.allocator);
            defer self.allocator.free(function_code);
            try self.code.appendSlice(self.allocator, function_code);
        }
        return self.allocator.dupe(u8, name);
    }

    /// Returns generated code in request order and atomically resets both the
    /// code and de-duplication set, matching the move-and-clear C++ method.
    pub fn requestedFunctionsAlloc(
        self: *MultiUseYulFunctionCollector,
    ) std.mem.Allocator.Error![]u8 {
        const result = try self.code.toOwnedSlice(self.allocator);
        self.clearRequestedNames();
        self.requested_functions.clearRetainingCapacity();
        return result;
    }

    fn register(self: *MultiUseYulFunctionCollector, name: []const u8) !bool {
        if (self.contains(name)) return false;
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);
        try self.requested_functions.put(self.allocator, owned_name, {});
        return true;
    }

    fn unregister(self: *MultiUseYulFunctionCollector, name: []const u8) void {
        if (self.requested_functions.fetchOrderedRemove(name)) |removed|
            self.allocator.free(removed.key);
    }

    fn clearRequestedNames(self: *MultiUseYulFunctionCollector) void {
        for (self.requested_functions.keys()) |name| self.allocator.free(name);
    }

    fn validateFunctionName(
        self: *const MultiUseYulFunctionCollector,
        name: []const u8,
        function_code: []const u8,
    ) CollectorError!void {
        const needle = try std.fmt.allocPrint(self.allocator, "function {s}(", .{name});
        defer self.allocator.free(needle);
        if (std.mem.find(u8, function_code, needle) == null)
            return error.ImproperFunctionName;
    }
};

test "collector creates functions once and resets after consumption" {
    const Creator = struct {
        calls: usize = 0,

        fn create(raw: *anyopaque, allocator: std.mem.Allocator) ![]u8 {
            const self: *@This() = @ptrCast(@alignCast(raw));
            self.calls += 1;
            return allocator.dupe(u8, "function identity(value) -> ret { ret := value }\n");
        }
    };
    var creator: Creator = .{};
    var collector = MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    const callback: FunctionCreator = .{ .context = &creator, .create_fn = Creator.create };

    const first = try collector.createFunction("identity", callback);
    defer std.testing.allocator.free(first);
    const second = try collector.createFunction("identity", callback);
    defer std.testing.allocator.free(second);
    try std.testing.expectEqual(@as(usize, 1), creator.calls);
    try std.testing.expect(collector.contains("identity"));

    const code = try collector.requestedFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try std.testing.expectEqualStrings(
        "function identity(value) -> ret { ret := value }\n",
        code,
    );
    try std.testing.expect(!collector.contains("identity"));
    const empty = try collector.requestedFunctionsAlloc();
    defer std.testing.allocator.free(empty);
    try std.testing.expectEqual(@as(usize, 0), empty.len);
}

test "structured collector emits arguments, returns, and body" {
    const Creator = struct {
        fn create(
            _: *anyopaque,
            allocator: std.mem.Allocator,
            arguments: *std.ArrayList([]const u8),
            returns: *std.ArrayList([]const u8),
        ) ![]u8 {
            try arguments.append(allocator, "value");
            try returns.append(allocator, "ret");
            return allocator.dupe(u8, "ret := value");
        }
    };
    var marker: u8 = 0;
    var collector = MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    const name = try collector.createStructuredFunction("identity", .{
        .context = &marker,
        .create_fn = Creator.create,
    });
    defer std.testing.allocator.free(name);
    const code = try collector.requestedFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try std.testing.expect(std.mem.find(u8, code, "function identity(value) -> ret") != null);
    try std.testing.expect(std.mem.find(u8, code, "ret := value") != null);
}
