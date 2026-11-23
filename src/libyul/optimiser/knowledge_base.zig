// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Incremental reasoning about constant values and constant differences between
//! Yul variables.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const BuiltinHandle = @import("../builtins.zig").BuiltinHandle;
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

const VersionedVariable = struct {
    name: YulName = .{},
    version: u64 = 0,

    fn eql(self: VersionedVariable, other: VersionedVariable) bool {
        return self.version == other.version and self.name.eql(other.name);
    }
};

const VariableOffset = struct {
    reference: VersionedVariable,
    offset: u256,

    fn isAbsolute(self: VariableOffset) bool {
        return self.reference.name.empty();
    }

    fn absoluteValue(self: VariableOffset) ?u256 {
        return if (self.isAbsolute()) self.offset else null;
    }
};

const VariableKnowledge = struct {
    version: u64 = 0,
    offset: ?VariableOffset = null,
};

const VariableMap = ordered.OrderedMap(YulName, VariableKnowledge, lessYulName);

pub const ValueProvider = struct {
    context: ?*const anyopaque,
    get_value: *const fn (?*const anyopaque, YulName) ?*const AST.Expression,

    fn get(self: ValueProvider, name: YulName) ?*const AST.Expression {
        return self.get_value(self.context, name);
    }
};

pub const KnowledgeBase = struct {
    allocator: std.mem.Allocator,
    variable_values: ValueProvider,
    add_builtin_handle: ?BuiltinHandle,
    sub_builtin_handle: ?BuiltinHandle,
    variables: VariableMap = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        variable_values: ValueProvider,
        dialect: AST.Dialect,
    ) KnowledgeBase {
        return .{
            .allocator = allocator,
            .variable_values = variable_values,
            .add_builtin_handle = dialect.findBuiltin("add"),
            .sub_builtin_handle = dialect.findBuiltin("sub"),
        };
    }

    pub fn deinit(self: *KnowledgeBase) void {
        self.variables.deinit(self.allocator);
        self.* = undefined;
    }

    /// A changed value starts a new version, including when its expression
    /// was and remains unknown. Other variables retain their existing offsets.
    pub fn variableChanged(self: *KnowledgeBase, variable: YulName) void {
        if (self.variables.getPtr(variable)) |knowledge| {
            knowledge.version +%= 1;
            knowledge.offset = null;
        }
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
        var knowledge = if (self.variables.get(variable)) |known| known.* else VariableKnowledge{};
        if (knowledge.offset) |offset| return offset;

        // The provider forgets an expression when one of the variables it
        // references changes. Any offset already cached for this variable
        // remains valid until the variable itself changes.
        const offset = if (self.variable_values.get(variable)) |expression|
            try self.exploreExpression(expression)
        else
            null;
        const computed = offset orelse VariableOffset{
            .reference = .{ .name = variable, .version = knowledge.version },
            .offset = 0,
        };
        knowledge.offset = computed;
        try self.variables.put(self.allocator, variable, knowledge);
        return computed;
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
};

fn optionalHandleEqual(handle: ?BuiltinHandle, expected: BuiltinHandle) bool {
    return if (handle) |value| value.eql(expected) else false;
}

test "Yul simplification retains known offsets for unchanged variables" {
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
    );
    defer knowledge.deinit();
    try std.testing.expectEqual(@as(?u256, 9), try knowledge.valueIfKnownConstant(y));
    provider.x_value = null;
    provider.y_value = null;
    knowledge.variableChanged(x);
    try std.testing.expectEqual(@as(?u256, null), try knowledge.valueIfKnownConstant(x));
    try std.testing.expectEqual(@as(?u256, 9), try knowledge.valueIfKnownConstant(y));

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
    knowledge.variableChanged(x);
    try std.testing.expectEqual(@as(?u256, null), try knowledge.valueIfKnownConstant(x));
}
