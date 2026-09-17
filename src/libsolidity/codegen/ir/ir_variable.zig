// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Recursive Solidity-value to Yul-variable mapping translated from
//! `libsolidity/codegen/ir/IRVariable.cpp`.

const std = @import("std");
const AST = @import("../../ast/ast.zig");
const ASTAnnotations = @import("../../ast/ast_annotations.zig");
const CompatibilityIdResolver = @import("../../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Types = @import("../../ast/types.zig");
const TypeBehavior = @import("../../ast/types.zig");
const Common = @import("common.zig");
const StringUtils = @import("../../../libsolutil/string_utils.zig");

pub const VariableError = TypeBehavior.QueryError || Common.CommonError || error{
    InvalidAst,
    InvalidStackPart,
    InvalidStackLayout,
    ExpectedSingleUntypedSlot,
};

pub const OwnedStackSlots = struct {
    allocator: std.mem.Allocator,
    items: [][]u8,

    pub fn deinit(self: *OwnedStackSlots) void {
        for (self.items) |item| self.allocator.free(item);
        self.allocator.free(self.items);
        self.* = undefined;
    }

    pub fn borrowed(self: *const OwnedStackSlots) []const []const u8 {
        return self.items;
    }
};

pub const IRVariable = struct {
    allocator: std.mem.Allocator,
    base_name: []u8,
    type_ref: *const Types.Type,

    pub fn init(
        allocator: std.mem.Allocator,
        base_name: []const u8,
        type_ref: *const Types.Type,
    ) std.mem.Allocator.Error!IRVariable {
        return .{
            .allocator = allocator,
            .base_name = try allocator.dupe(u8, base_name),
            .type_ref = type_ref,
        };
    }

    pub fn fromDeclaration(
        allocator: std.mem.Allocator,
        compatibility_ids: CompatibilityIdResolver,
        declaration: *const AST.Node,
    ) VariableError!IRVariable {
        if (declaration.nodeKind() != .variable_declaration) return error.InvalidAst;
        const annotation = ASTAnnotations.annotationConst(declaration) orelse
            return error.InvalidAst;
        const type_ref = switch (annotation.*) {
            .variable_declaration => |entry| entry.type_ref,
            else => null,
        } orelse return error.InvalidAst;
        const base_name = try Common.localVariableDeclarationAlloc(
            allocator,
            compatibility_ids,
            declaration,
        );
        defer allocator.free(base_name);
        return init(allocator, base_name, type_ref);
    }

    pub fn fromExpression(
        allocator: std.mem.Allocator,
        compatibility_ids: CompatibilityIdResolver,
        expression: *const AST.Node,
    ) VariableError!IRVariable {
        const type_ref = try expressionType(expression);
        const base_name = try Common.localVariableExpressionAlloc(
            allocator,
            compatibility_ids,
            expression,
        );
        defer allocator.free(base_name);
        return init(allocator, base_name, type_ref);
    }

    pub fn clone(self: *const IRVariable) std.mem.Allocator.Error!IRVariable {
        return init(self.allocator, self.base_name, self.type_ref);
    }

    pub fn deinit(self: *IRVariable) void {
        self.allocator.free(self.base_name);
        self.* = undefined;
    }

    pub fn part(self: *const IRVariable, name: []const u8) VariableError!IRVariable {
        var items = try TypeBehavior.stackItemsAlloc(self.allocator, self.type_ref);
        defer items.deinit();
        for (items.items) |item| {
            if (!std.mem.eql(u8, item.name, name)) continue;
            if (item.name.len != 0 and item.type_ref == null)
                return error.InvalidStackLayout;
            const suffixed = try self.suffixedNameAlloc(item.name);
            defer self.allocator.free(suffixed);
            return init(self.allocator, suffixed, item.type_ref orelse self.type_ref);
        }
        return error.InvalidStackPart;
    }

    pub fn hasPart(self: *const IRVariable, name: []const u8) VariableError!bool {
        var items = try TypeBehavior.stackItemsAlloc(self.allocator, self.type_ref);
        defer items.deinit();
        for (items.items) |item| {
            if (!std.mem.eql(u8, item.name, name)) continue;
            if (item.name.len != 0 and item.type_ref == null)
                return error.InvalidStackLayout;
            return true;
        }
        return false;
    }

    pub fn stackSlotsAlloc(self: *const IRVariable) VariableError!OwnedStackSlots {
        var result: std.ArrayList([]u8) = .empty;
        errdefer {
            for (result.items) |item| self.allocator.free(item);
            result.deinit(self.allocator);
        }
        try self.appendStackSlots(self.allocator, &result);
        return .{
            .allocator = self.allocator,
            .items = try result.toOwnedSlice(self.allocator),
        };
    }

    /// Appends allocator-owned slot names. On failure, existing entries remain
    /// unchanged and any newly allocated names are freed.
    pub fn appendStackSlots(
        self: *const IRVariable,
        allocator: std.mem.Allocator,
        output: *std.ArrayList([]u8),
    ) VariableError!void {
        const original_len = output.items.len;
        errdefer {
            for (output.items[original_len..]) |item| allocator.free(item);
            output.shrinkRetainingCapacity(original_len);
        }
        try appendStackSlotsRecursive(allocator, output, self.base_name, self.type_ref, 0);
    }

    pub fn commaSeparatedListAlloc(self: *const IRVariable) VariableError![]u8 {
        var slots = try self.stackSlotsAlloc();
        defer slots.deinit();
        return StringUtils.joinHumanReadableAlloc(
            self.allocator,
            slots.borrowed(),
            ", ",
            "",
        );
    }

    pub fn commaSeparatedListPrefixedAlloc(self: *const IRVariable) VariableError![]u8 {
        var slots = try self.stackSlotsAlloc();
        defer slots.deinit();
        return StringUtils.joinHumanReadablePrefixedAlloc(
            self.allocator,
            slots.borrowed(),
            ", ",
            "",
        );
    }

    pub fn nameAlloc(self: *const IRVariable) VariableError![]u8 {
        if (try TypeBehavior.sizeOnStack(self.type_ref) != 1)
            return error.ExpectedSingleUntypedSlot;
        var items = try TypeBehavior.stackItemsAlloc(self.allocator, self.type_ref);
        defer items.deinit();
        if (items.items.len != 1 or items.items[0].type_ref != null)
            return error.ExpectedSingleUntypedSlot;
        return self.suffixedNameAlloc(items.items[0].name);
    }

    pub fn tupleComponent(
        self: *const IRVariable,
        index: usize,
    ) VariableError!IRVariable {
        if (self.type_ref.category() != .Tuple) return error.InvalidStackPart;
        const name = try Common.tupleComponentAlloc(self.allocator, index);
        defer self.allocator.free(name);
        return self.part(name);
    }

    fn suffixedNameAlloc(
        self: *const IRVariable,
        suffix: []const u8,
    ) std.mem.Allocator.Error![]u8 {
        if (suffix.len == 0) return self.allocator.dupe(u8, self.base_name);
        return std.fmt.allocPrint(self.allocator, "{s}_{s}", .{ self.base_name, suffix });
    }
};

fn appendStackSlotsRecursive(
    allocator: std.mem.Allocator,
    output: *std.ArrayList([]u8),
    base_name: []const u8,
    type_ref: *const Types.Type,
    depth: usize,
) VariableError!void {
    if (depth >= 256) return error.InvalidStackLayout;
    var items = try TypeBehavior.stackItemsAlloc(allocator, type_ref);
    defer items.deinit();
    for (items.items) |item| {
        if (item.type_ref) |item_type| {
            if (item.name.len == 0 or item_type == type_ref)
                return error.InvalidStackLayout;
            const suffixed = try std.fmt.allocPrint(
                allocator,
                "{s}_{s}",
                .{ base_name, item.name },
            );
            defer allocator.free(suffixed);
            try appendStackSlotsRecursive(allocator, output, suffixed, item_type, depth + 1);
        } else {
            if (item.name.len != 0) return error.InvalidStackLayout;
            const owned = try allocator.dupe(u8, base_name);
            errdefer allocator.free(owned);
            try output.append(allocator, owned);
        }
    }
}

fn expressionType(expression: *const AST.Node) VariableError!*const Types.Type {
    if (!expression.isExpression()) return error.InvalidAst;
    const annotation = ASTAnnotations.annotationConst(expression) orelse
        return error.InvalidAst;
    return switch (annotation.*) {
        .expression => |entry| entry.type_ref,
        .identifier => |entry| entry.expression.type_ref,
        .member_access => |entry| entry.expression.type_ref,
        .operation => |entry| entry.expression.type_ref,
        .binary_operation => |entry| entry.operation.expression.type_ref,
        .function_call => |entry| entry.expression.type_ref,
        else => null,
    } orelse error.InvalidAst;
}

test "IR variables recursively flatten tuple and calldata stack parts" {
    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const calldata_array = Types.Type{ .payload = .{ .Array = .{
        .reference = .{ .location = .CallData },
        .base_type = &uint_type,
    } } };
    const tuple = Types.Type{ .payload = .{ .Tuple = .{
        .components = &.{ &uint_type, null, &calldata_array },
    } } };
    var variable = try IRVariable.init(std.testing.allocator, "value", &tuple);
    defer variable.deinit();

    var slots = try variable.stackSlotsAlloc();
    defer slots.deinit();
    try std.testing.expectEqual(@as(usize, 3), slots.items.len);
    try std.testing.expectEqualStrings("value_component_1", slots.items[0]);
    try std.testing.expectEqualStrings("value_component_3_offset", slots.items[1]);
    try std.testing.expectEqualStrings("value_component_3_length", slots.items[2]);

    var component = try variable.tupleComponent(2);
    defer component.deinit();
    try std.testing.expectEqualStrings("value_component_3", component.base_name);
    try std.testing.expect(try component.hasPart("length"));
    const list = try component.commaSeparatedListAlloc();
    defer std.testing.allocator.free(list);
    try std.testing.expectEqualStrings(
        "value_component_3_offset, value_component_3_length",
        list,
    );
}

test "appending stack slots preserves existing names on every allocation failure" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseAppendStackSlots, .{});
}

fn exerciseAppendStackSlots(allocator: std.mem.Allocator) !void {
    const uint_type = Types.Type{ .payload = .{ .Integer = .{ .bits = 256, .modifier = .Unsigned } } };
    const array_type = Types.Type{ .payload = .{ .Array = .{
        .reference = .{ .location = .CallData },
        .base_type = &uint_type,
    } } };
    const tuple = Types.Type{ .payload = .{ .Tuple = .{ .components = &.{ &uint_type, null, &array_type } } } };
    var variable = try IRVariable.init(allocator, "value", &tuple);
    defer variable.deinit();
    var output: std.ArrayList([]u8) = .empty;
    defer {
        for (output.items) |item| allocator.free(item);
        output.deinit(allocator);
    }
    try output.ensureTotalCapacityPrecise(allocator, 1);
    output.appendAssumeCapacity(try allocator.dupe(u8, "existing"));
    variable.appendStackSlots(allocator, &output) catch |err| {
        try std.testing.expectEqual(@as(usize, 1), output.items.len);
        try std.testing.expectEqualStrings("existing", output.items[0]);
        return err;
    };
    try std.testing.expectEqual(@as(usize, 4), output.items.len);
    try std.testing.expectEqualStrings("existing", output.items[0]);
    try std.testing.expectEqualStrings("value_component_1", output.items[1]);
    try std.testing.expectEqualStrings("value_component_3_offset", output.items[2]);
    try std.testing.expectEqualStrings("value_component_3_length", output.items[3]);
}

test "single-slot primitive names reject typed wrapper layouts" {
    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    var primitive = try IRVariable.init(std.testing.allocator, "x", &uint_type);
    defer primitive.deinit();
    const name = try primitive.nameAlloc();
    defer std.testing.allocator.free(name);
    try std.testing.expectEqualStrings("x", name);

    const memory_array = Types.Type{ .payload = .{ .Array = .{
        .reference = .{ .location = .Memory },
        .base_type = &uint_type,
    } } };
    var wrapped = try IRVariable.init(std.testing.allocator, "a", &memory_array);
    defer wrapped.deinit();
    try std.testing.expectError(error.ExpectedSingleUntypedSlot, wrapped.nameAlloc());
}
