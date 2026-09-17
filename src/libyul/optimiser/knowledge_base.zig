// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Incremental reasoning about constant values and constant differences between
//! Yul variables.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const BuiltinHandle = @import("../builtins.zig").BuiltinHandle;
const NameCollector = @import("name_collector.zig");
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

const VariableOffset = struct {
    reference: YulName,
    offset: u256,

    fn isAbsolute(self: VariableOffset) bool {
        return self.reference.empty();
    }

    fn absoluteValue(self: VariableOffset) ?u256 {
        return if (self.isAbsolute()) self.offset else null;
    }
};

const OffsetMap = ordered.OrderedMap(YulName, VariableOffset, lessYulName);
const LastValueMap = ordered.OrderedMap(YulName, ?*const AST.Expression, lessYulName);
const GroupMap = ordered.OrderedMap(YulName, NameCollector.NameSet, lessYulName);

pub const ValueProvider = struct {
    context: ?*const anyopaque,
    get_value: *const fn (?*const anyopaque, YulName) ?*const AST.Expression,

    fn get(self: ValueProvider, name: YulName) ?*const AST.Expression {
        return self.get_value(self.context, name);
    }
};

pub const KnowledgeBase = struct {
    allocator: std.mem.Allocator,
    values_are_ssa: bool,
    variable_values: ValueProvider,
    add_builtin_handle: ?BuiltinHandle,
    sub_builtin_handle: ?BuiltinHandle,
    offsets: OffsetMap = .{},
    last_known_value: LastValueMap = .{},
    group_members: GroupMap = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        variable_values: ValueProvider,
        dialect: AST.Dialect,
        values_are_ssa: bool,
    ) KnowledgeBase {
        return .{
            .allocator = allocator,
            .values_are_ssa = values_are_ssa,
            .variable_values = variable_values,
            .add_builtin_handle = dialect.findBuiltin("add"),
            .sub_builtin_handle = dialect.findBuiltin("sub"),
        };
    }

    pub fn deinit(self: *KnowledgeBase) void {
        self.offsets.deinit(self.allocator);
        self.last_known_value.deinit(self.allocator);
        for (self.group_members.mutableItems()) |*entry| entry.value.deinit(self.allocator);
        self.group_members.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn knownToBeDifferent(self: *KnowledgeBase, a: YulName, b: YulName) anyerror!bool {
        if (try self.differenceIfKnownConstant(a, b)) |difference| return difference != 0;
        return false;
    }

    pub fn differenceIfKnownConstant(
        self: *KnowledgeBase,
        a: YulName,
        b: YulName,
    ) anyerror!?u256 {
        const offset_a = try self.exploreVariable(a);
        const offset_b = try self.exploreVariable(b);
        return if (offset_a.reference.eql(offset_b.reference))
            offset_a.offset -% offset_b.offset
        else
            null;
    }

    pub fn knownToBeDifferentByAtLeast32(
        self: *KnowledgeBase,
        a: YulName,
        b: YulName,
    ) anyerror!bool {
        if (try self.differenceIfKnownConstant(a, b)) |difference|
            return difference >= 32 and difference <= @as(u256, 0) -% 32;
        return false;
    }

    pub fn knownToBeZero(self: *KnowledgeBase, name: YulName) anyerror!bool {
        return (try self.valueIfKnownConstant(name)) == 0;
    }

    pub fn valueIfKnownConstant(self: *KnowledgeBase, name: YulName) anyerror!?u256 {
        return (try self.exploreVariable(name)).absoluteValue();
    }

    pub fn valueIfKnownConstantExpression(
        self: *KnowledgeBase,
        expression: *const AST.Expression,
    ) anyerror!?u256 {
        return switch (expression.*) {
            .identifier => |identifier| self.valueIfKnownConstant(identifier.name),
            .literal => |*literal| literal.value.value(),
            .function_call => null,
        };
    }

    fn exploreVariable(self: *KnowledgeBase, variable: YulName) anyerror!VariableOffset {
        var value: ?*const AST.Expression = null;
        if (self.values_are_ssa) {
            if (self.offsets.get(variable)) |known| return known.*;
            value = try self.valueOf(variable);
        } else {
            value = try self.valueOf(variable);
            if (self.offsets.get(variable)) |known| return known.*;
        }

        if (value) |expression|
            if (try self.exploreExpression(expression)) |offset|
                return self.setOffset(variable, offset);
        return self.setOffset(variable, .{ .reference = variable, .offset = 0 });
    }

    fn exploreExpression(
        self: *KnowledgeBase,
        expression: *const AST.Expression,
    ) anyerror!?VariableOffset {
        switch (expression.*) {
            .literal => |*literal| return .{
                .reference = .{},
                .offset = try literal.value.value(),
            },
            .identifier => |identifier| return @as(
                ?VariableOffset,
                try self.exploreVariable(identifier.name),
            ),
            .function_call => |*call| {
                const handle = switch (call.function_name) {
                    .builtin => |builtin| builtin.handle,
                    .identifier => return null,
                };
                if (call.arguments.items.len != 2) return null;
                if (optionalHandleEqual(self.add_builtin_handle, handle)) {
                    const a = (try self.exploreExpression(&call.arguments.items[0])) orelse return null;
                    const b = (try self.exploreExpression(&call.arguments.items[1])) orelse return null;
                    const offset = a.offset +% b.offset;
                    if (a.isAbsolute()) return .{ .reference = b.reference, .offset = offset };
                    if (b.isAbsolute()) return .{ .reference = a.reference, .offset = offset };
                } else if (optionalHandleEqual(self.sub_builtin_handle, handle)) {
                    const a = (try self.exploreExpression(&call.arguments.items[0])) orelse return null;
                    const b = (try self.exploreExpression(&call.arguments.items[1])) orelse return null;
                    const offset = a.offset -% b.offset;
                    if (a.reference.eql(b.reference)) return .{ .reference = .{}, .offset = offset };
                    if (b.isAbsolute()) return .{ .reference = a.reference, .offset = offset };
                }
                return null;
            },
        }
    }

    fn valueOf(self: *KnowledgeBase, variable: YulName) anyerror!?*const AST.Expression {
        const current_value = self.variable_values.get(variable);
        if (self.values_are_ssa) return current_value;

        const last_value = if (self.last_known_value.get(variable)) |known| known.* else null;
        if (last_value != current_value) try self.reset(variable);
        try self.last_known_value.put(self.allocator, variable, current_value);
        return current_value;
    }

    fn reset(self: *KnowledgeBase, variable: YulName) anyerror!void {
        std.debug.assert(!self.values_are_ssa);
        _ = self.last_known_value.remove(variable);

        if (self.offsets.get(variable)) |offset| {
            if (!offset.isAbsolute()) {
                if (self.group_members.getPtr(offset.reference)) |group|
                    _ = group.remove(variable);
            }
            _ = self.offsets.remove(variable);
        }

        if (self.group_members.remove(variable)) |removed| {
            var group = removed.value;
            defer group.deinit(self.allocator);
            if (!group.isEmpty()) {
                const new_representative = group.at(0);
                if (new_representative.eql(variable)) return error.InvalidKnowledgeGroup;
                const new_offset = (self.offsets.get(new_representative) orelse
                    return error.InvalidKnowledgeGroup).offset;
                for (0..group.len()) |index| {
                    const group_member = group.at(index);
                    const member_offset = self.offsets.getPtr(group_member) orelse
                        return error.InvalidKnowledgeGroup;
                    if (!member_offset.reference.eql(variable)) return error.InvalidKnowledgeGroup;
                    member_offset.reference = new_representative;
                    member_offset.offset -%= new_offset;
                }
                if (try self.group_members.fetchPut(
                    self.allocator,
                    new_representative,
                    group,
                )) |displaced| {
                    var old_group = displaced.value;
                    old_group.deinit(self.allocator);
                }
                group = .{};
            }
        }
    }

    fn setOffset(
        self: *KnowledgeBase,
        variable: YulName,
        value: VariableOffset,
    ) anyerror!VariableOffset {
        try self.offsets.put(self.allocator, variable, value);
        if (!value.reference.empty()) {
            if (self.group_members.getPtr(value.reference)) |group| {
                _ = try group.insert(self.allocator, variable);
            } else {
                var group: NameCollector.NameSet = .{};
                errdefer group.deinit(self.allocator);
                _ = try group.insert(self.allocator, variable);
                _ = try self.group_members.insert(self.allocator, value.reference, group);
            }
        }
        return value;
    }
};

fn optionalHandleEqual(handle: ?BuiltinHandle, expected: BuiltinHandle) bool {
    return if (handle) |value| value.eql(expected) else false;
}

test "knowledge base follows constant add/sub relations and refreshes changed values" {
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    const x = try YulName.init("knowledge_x");
    const y = try YulName.init("knowledge_y");
    var literal = AST.Expression{ .literal = .{
        .kind = .Number,
        .value = try AST.LiteralValue.initNumeric(allocator, 9, null),
    } };
    defer literal.deinit(allocator);
    const alias = AST.Expression{ .identifier = .{ .name = x } };
    const Provider = struct {
        x_name: YulName,
        y_name: YulName,
        x_value: ?*const AST.Expression,
        y_value: ?*const AST.Expression,

        fn get(context: ?*const anyopaque, name: YulName) ?*const AST.Expression {
            const self: *@This() = @ptrCast(@alignCast(@constCast(context.?)));
            if (name.eql(self.x_name)) return self.x_value;
            if (name.eql(self.y_name)) return self.y_value;
            return null;
        }
    };
    var provider: Provider = .{
        .x_name = x,
        .y_name = y,
        .x_value = &literal,
        .y_value = &alias,
    };
    var knowledge = KnowledgeBase.init(
        allocator,
        .{ .context = &provider, .get_value = Provider.get },
        dialect.dialect(),
        false,
    );
    defer knowledge.deinit();
    try std.testing.expectEqual(@as(?u256, 9), try knowledge.valueIfKnownConstant(y));
    provider.x_value = null;
    try std.testing.expectEqual(@as(?u256, null), try knowledge.valueIfKnownConstant(x));

    var malformed_add: AST.Expression = .{ .function_call = .{
        .function_name = .{ .builtin = .{
            .handle = dialect.dialect().findBuiltin("add").?,
        } },
    } };
    defer malformed_add.deinit(allocator);
    for ([_]u256{ 1, 2, 4 }) |value| try malformed_add.function_call.arguments.append(
        allocator,
        .{ .literal = .{
            .kind = .Number,
            .value = try AST.LiteralValue.initNumeric(allocator, value, null),
        } },
    );
    provider.x_value = &malformed_add;
    try std.testing.expectEqual(@as(?u256, null), try knowledge.valueIfKnownConstant(x));
}
