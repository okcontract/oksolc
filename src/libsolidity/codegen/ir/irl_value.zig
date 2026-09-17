// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned lvalue-location variants translated from `IRLValue.h`.

const std = @import("std");
const AST = @import("../../ast/ast.zig");
const Types = @import("../../ast/types.zig");
const IRVariable = @import("ir_variable.zig").IRVariable;

pub const Offset = union(enum) {
    runtime: []u8,
    constant: u32,

    pub fn initRuntime(
        allocator: std.mem.Allocator,
        value: []const u8,
    ) std.mem.Allocator.Error!Offset {
        return .{ .runtime = try allocator.dupe(u8, value) };
    }

    pub fn deinit(self: *Offset, allocator: std.mem.Allocator) void {
        switch (self.*) {
            .runtime => |value| allocator.free(value),
            .constant => {},
        }
        self.* = undefined;
    }

    pub fn stringAlloc(
        self: Offset,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        return switch (self) {
            .runtime => |value| allocator.dupe(u8, value),
            .constant => |value| std.fmt.allocPrint(allocator, "{d}", .{value}),
        };
    }
};

pub const GenericStorage = struct {
    slot: []u8,
    offset: Offset,

    pub fn init(
        allocator: std.mem.Allocator,
        slot: []const u8,
        offset: Offset,
    ) std.mem.Allocator.Error!GenericStorage {
        return .{
            .slot = try allocator.dupe(u8, slot),
            .offset = offset,
        };
    }

    pub fn deinit(self: *GenericStorage, allocator: std.mem.Allocator) void {
        allocator.free(self.slot);
        self.offset.deinit(allocator);
        self.* = undefined;
    }

    pub fn offsetStringAlloc(
        self: *const GenericStorage,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        return self.offset.stringAlloc(allocator);
    }
};

pub const Memory = struct {
    address: []u8,
    byte_array_element: bool = false,
};

pub const Tuple = struct {
    /// Null entries preserve Solidity tuple placeholders. Non-null components
    /// are separately allocated, which gives the recursive type finite size.
    components: []?*IRLValue,
};

pub const Kind = union(enum) {
    stack: IRVariable,
    immutable: ?*const AST.Node,
    storage: GenericStorage,
    transient_storage: GenericStorage,
    memory: Memory,
    tuple: Tuple,
};

pub const IRLValue = struct {
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
    kind: Kind,

    pub fn initStack(variable: IRVariable) IRLValue {
        return .{
            .allocator = variable.allocator,
            .type_ref = variable.type_ref,
            .kind = .{ .stack = variable },
        };
    }

    pub fn initImmutable(
        allocator: std.mem.Allocator,
        type_ref: *const Types.Type,
        variable: ?*const AST.Node,
    ) IRLValue {
        return .{
            .allocator = allocator,
            .type_ref = type_ref,
            .kind = .{ .immutable = variable },
        };
    }

    pub fn initStorage(
        allocator: std.mem.Allocator,
        type_ref: *const Types.Type,
        slot: []const u8,
        offset: Offset,
        transient: bool,
    ) std.mem.Allocator.Error!IRLValue {
        const storage = GenericStorage.init(allocator, slot, offset) catch |err| {
            var owned_offset = offset;
            owned_offset.deinit(allocator);
            return err;
        };
        return .{
            .allocator = allocator,
            .type_ref = type_ref,
            .kind = if (transient)
                .{ .transient_storage = storage }
            else
                .{ .storage = storage },
        };
    }

    pub fn initMemory(
        allocator: std.mem.Allocator,
        type_ref: *const Types.Type,
        address: []const u8,
        byte_array_element: bool,
    ) std.mem.Allocator.Error!IRLValue {
        return .{
            .allocator = allocator,
            .type_ref = type_ref,
            .kind = .{ .memory = .{
                .address = try allocator.dupe(u8, address),
                .byte_array_element = byte_array_element,
            } },
        };
    }

    pub fn initTuple(
        allocator: std.mem.Allocator,
        type_ref: *const Types.Type,
        components: []const ?*IRLValue,
    ) std.mem.Allocator.Error!IRLValue {
        return .{
            .allocator = allocator,
            .type_ref = type_ref,
            .kind = .{ .tuple = .{
                .components = try allocator.dupe(?*IRLValue, components),
            } },
        };
    }

    pub fn deinit(self: *IRLValue) void {
        switch (self.kind) {
            .stack => |*variable| variable.deinit(),
            .immutable => {},
            .storage => |*storage| storage.deinit(self.allocator),
            .transient_storage => |*storage| storage.deinit(self.allocator),
            .memory => |memory| self.allocator.free(memory.address),
            .tuple => |tuple| {
                for (tuple.components) |component| if (component) |value| {
                    value.deinit();
                    self.allocator.destroy(value);
                };
                self.allocator.free(tuple.components);
            },
        }
        self.* = undefined;
    }
};

test "storage offsets render constants and runtime expressions" {
    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    var constant = try IRLValue.initStorage(
        std.testing.allocator,
        &uint_type,
        "slot",
        .{ .constant = 7 },
        false,
    );
    defer constant.deinit();
    const constant_text = try constant.kind.storage.offsetStringAlloc(std.testing.allocator);
    defer std.testing.allocator.free(constant_text);
    try std.testing.expectEqualStrings("7", constant_text);

    const runtime_offset = try Offset.initRuntime(std.testing.allocator, "index");
    var transient = try IRLValue.initStorage(
        std.testing.allocator,
        &uint_type,
        "tslot",
        runtime_offset,
        true,
    );
    defer transient.deinit();
    const runtime_text = try transient.kind.transient_storage.offsetStringAlloc(
        std.testing.allocator,
    );
    defer std.testing.allocator.free(runtime_text);
    try std.testing.expectEqualStrings("index", runtime_text);
}

test "tuple lvalues own recursive components and placeholders" {
    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const tuple_type = Types.Type{ .payload = .{ .Tuple = .{
        .components = &.{ &uint_type, null },
    } } };
    const child = try std.testing.allocator.create(IRLValue);
    child.* = IRLValue.initStack(try IRVariable.init(
        std.testing.allocator,
        "value",
        &uint_type,
    ));
    var tuple = try IRLValue.initTuple(
        std.testing.allocator,
        &tuple_type,
        &.{ child, null },
    );
    defer tuple.deinit();
    try std.testing.expectEqual(@as(usize, 2), tuple.kind.tuple.components.len);
    try std.testing.expect(tuple.kind.tuple.components[1] == null);
}
