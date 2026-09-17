// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Identifier scopes with Yul function-boundary lookup semantics.

const std = @import("std");
const YulName = @import("yul_name.zig").YulName;

pub const Variable = struct {
    name: YulName,
};

pub const Function = struct {
    num_arguments: usize,
    num_returns: usize,
    name: YulName,
};

pub const Identifier = union(enum) {
    variable: Variable,
    function: Function,
};

pub const Scope = struct {
    allocator: std.mem.Allocator,
    super_scope: ?*Scope = null,
    function_scope: bool = false,
    identifiers: std.AutoHashMap(YulName, Identifier),

    pub fn init(allocator: std.mem.Allocator) Scope {
        return .{
            .allocator = allocator,
            .identifiers = std.AutoHashMap(YulName, Identifier).init(allocator),
        };
    }

    pub fn deinit(self: *Scope) void {
        self.identifiers.deinit();
        self.* = undefined;
    }

    pub fn registerVariable(self: *Scope, name: YulName) std.mem.Allocator.Error!bool {
        if (self.exists(name)) return false;
        try self.identifiers.put(name, .{ .variable = .{ .name = name } });
        return true;
    }

    pub fn registerFunction(
        self: *Scope,
        name: YulName,
        num_arguments: usize,
        num_returns: usize,
    ) std.mem.Allocator.Error!bool {
        if (self.exists(name)) return false;
        try self.identifiers.put(name, .{ .function = .{
            .num_arguments = num_arguments,
            .num_returns = num_returns,
            .name = name,
        } });
        return true;
    }

    /// Looks through super scopes, but hides variables across a function boundary.
    pub fn lookup(self: *Scope, name: YulName) ?*Identifier {
        var crossed_function_boundary = false;
        var current: ?*Scope = self;
        while (current) |scope| : (current = scope.super_scope) {
            if (scope.identifiers.getPtr(name)) |identifier| {
                if (crossed_function_boundary and identifier.* == .variable) return null;
                return identifier;
            }
            if (scope.function_scope) crossed_function_boundary = true;
        }
        return null;
    }

    pub fn lookupConst(self: *const Scope, name: YulName) ?*const Identifier {
        var crossed_function_boundary = false;
        var current: ?*const Scope = self;
        while (current) |scope| : (current = scope.super_scope) {
            if (scope.identifiers.getPtr(name)) |identifier| {
                if (crossed_function_boundary and identifier.* == .variable) return null;
                return identifier;
            }
            if (scope.function_scope) crossed_function_boundary = true;
        }
        return null;
    }

    /// Checks all super scopes, including across function boundaries.
    pub fn exists(self: *const Scope, name: YulName) bool {
        if (self.identifiers.contains(name)) return true;
        return if (self.super_scope) |scope| scope.exists(name) else false;
    }

    pub fn numberOfVariables(self: *const Scope) usize {
        var count: usize = 0;
        var iterator = self.identifiers.valueIterator();
        while (iterator.next()) |identifier| {
            if (identifier.* == .variable) count += 1;
        }
        return count;
    }

    pub fn insideFunction(self: *const Scope) bool {
        var current: ?*const Scope = self;
        while (current) |scope| : (current = scope.super_scope) {
            if (scope.function_scope) return true;
        }
        return false;
    }
};

test "scope lookup hides variables but not functions across function boundaries" {
    const allocator = std.testing.allocator;
    const outer_variable = try YulName.init("outer");
    const outer_function = try YulName.init("callable");
    const local_variable = try YulName.init("local");
    var root = Scope.init(allocator);
    defer root.deinit();
    try std.testing.expect(try root.registerVariable(outer_variable));
    try std.testing.expect(try root.registerFunction(outer_function, 2, 1));
    var function_scope = Scope.init(allocator);
    defer function_scope.deinit();
    function_scope.super_scope = &root;
    function_scope.function_scope = true;
    try std.testing.expect(try function_scope.registerVariable(local_variable));
    var body = Scope.init(allocator);
    defer body.deinit();
    body.super_scope = &function_scope;

    try std.testing.expect(body.lookup(local_variable).?.* == .variable);
    try std.testing.expect(body.lookup(outer_variable) == null);
    try std.testing.expect(body.lookup(outer_function).?.* == .function);
    try std.testing.expect(body.exists(outer_variable));
    try std.testing.expect(body.insideFunction());
    try std.testing.expect(!(try body.registerVariable(outer_variable)));
    try std.testing.expectEqual(@as(usize, 1), root.numberOfVariables());
}
