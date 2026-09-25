// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Lvalue locations translated from `IRLValue.h`. Stack and tuple containers are
//! owned; Yul addresses borrow the generation arena. First use transfers child
//! storage. Repeated uses copy the existing AST before optimization can mutate it.

const std = @import("std");
const AST = @import("../../ast/ast.zig");
const Types = @import("../../ast/types.zig");
const Yul = @import("../../../libyul/ast.zig");
const YulName = @import("../../../libyul/yul_name.zig").YulName;
const Builder = @import("../../../libyul/ast_builder.zig").Builder;
const Copier = @import("../../../libyul/optimiser/ast_copier.zig").ASTCopier;
const IRVariable = @import("ir_variable.zig").IRVariable;

pub const Offset = union(enum) {
    runtime: YulName,
    constant: u32,

    pub fn expression(self: Offset, builder: Builder) @import("../../../libyul/ast_template.zig").Error!Yul.Expression {
        return switch (self) {
            .runtime => |name| .{ .identifier = .{ .name = name } },
            .constant => |value| builder.expression("@0", .{value}),
        };
    }
};

pub const GenericStorage = struct {
    slot: Yul.Expression,
    offset: Offset,
    used: bool = false,

    pub fn slotExpression(self: *GenericStorage, builder: Builder) std.mem.Allocator.Error!Yul.Expression {
        return materializeAddress(builder, &self.slot, &self.used);
    }
};

pub const Memory = struct {
    address: Yul.Expression,
    byte_array_element: bool = false,
    used: bool = false,

    pub fn addressExpression(self: *Memory, builder: Builder) std.mem.Allocator.Error!Yul.Expression {
        return materializeAddress(builder, &self.address, &self.used);
    }
};

fn materializeAddress(builder: Builder, expression: *const Yul.Expression, used: *bool) std.mem.Allocator.Error!Yul.Expression {
    if (!used.*) {
        used.* = true;
        return expression.*;
    }
    var copier = Copier.init(builder.allocator());
    return copier.translateExpression(expression) catch |err| switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        else => unreachable, // No hooks: copying a constructed address cannot reject semantics.
    };
}

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
        slot: Yul.Expression,
        offset: Offset,
        transient: bool,
    ) IRLValue {
        const storage: GenericStorage = .{ .slot = slot, .offset = offset };
        return .{
            .allocator = allocator,
            .type_ref = type_ref,
            .kind = if (transient) .{ .transient_storage = storage } else .{ .storage = storage },
        };
    }

    pub fn initMemory(
        allocator: std.mem.Allocator,
        type_ref: *const Types.Type,
        address: Yul.Expression,
        byte_array_element: bool,
    ) IRLValue {
        return .{
            .allocator = allocator,
            .type_ref = type_ref,
            .kind = .{ .memory = .{ .address = address, .byte_array_element = byte_array_element } },
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
            .storage, .transient_storage, .memory => {},
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

test "Yul AST lvalue locations preserve offsets and own emitted occurrences" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    var dialect = try @import("../../../libyul/backends/evm/evm_dialect.zig").EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    const builder = Builder.init(&arena, dialect.dialect());
    const offset: Offset = .{ .constant = 7 };
    const value = try offset.expression(builder);
    try std.testing.expectEqual(@as(?u256, 7), value.literal.value.numeric_value);
    const runtime_offset: Offset = .{ .runtime = try builder.name("index") };
    const runtime = try runtime_offset.expression(builder);
    try std.testing.expectEqualStrings("index", try runtime.identifier.name.str());
    var memory: Memory = .{ .address = try builder.expression("add(base, 32)", .{}) };
    var first = try memory.addressExpression(builder);
    try std.testing.expect(first.function_call.arguments.items.ptr == memory.address.function_call.arguments.items.ptr);
    const second = try memory.addressExpression(builder);
    try std.testing.expect(first.function_call.arguments.items.ptr != second.function_call.arguments.items.ptr);
    first.function_call.arguments.items[1].literal.value.numeric_value = 64;
    try std.testing.expectEqual(@as(?u256, 32), second.function_call.arguments.items[1].literal.value.numeric_value);
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
