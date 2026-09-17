// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Renames declarations and all references so selected names become available.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const NameCollectorModule = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

pub const TranslationMap = ordered.OrderedMap(YulName, YulName, lessYulName);

pub const NameDisplacer = struct {
    allocator: std.mem.Allocator,
    name_dispenser: *NameDispenser,
    names_to_free: *const NameCollectorModule.NameSet,
    translation_map: TranslationMap = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        name_dispenser: *NameDispenser,
        names_to_free: *const NameCollectorModule.NameSet,
    ) !NameDisplacer {
        var result: NameDisplacer = .{
            .allocator = allocator,
            .name_dispenser = name_dispenser,
            .names_to_free = names_to_free,
        };
        errdefer result.deinit();
        for (0..names_to_free.len()) |index| try name_dispenser.markUsed(names_to_free.at(index));
        return result;
    }

    pub fn deinit(self: *NameDisplacer) void {
        self.translation_map.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn translations(self: *const NameDisplacer) *const TranslationMap {
        return &self.translation_map;
    }

    pub fn run(self: *NameDisplacer, block: *AST.Block) !void {
        try self.visitBlock(block);
    }

    fn visitBlock(self: *NameDisplacer, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| if (statement.* == .function_definition)
            try self.checkAndReplaceNew(&statement.function_definition.name);
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *NameDisplacer, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| {
                for (value.variable_names.items) |*identifier| self.checkAndReplace(&identifier.name);
                if (value.value) |expression| try self.visitExpression(expression);
            },
            .variable_declaration => |*value| {
                for (value.variables.items) |*variable| try self.checkAndReplaceNew(&variable.name);
                if (value.value) |expression| try self.visitExpression(expression);
            },
            .function_definition => |*value| {
                if (self.names_to_free.contains(value.name)) return error.FunctionNameWasNotPreprocessed;
                for (value.parameters.items) |*parameter| try self.checkAndReplaceNew(&parameter.name);
                for (value.return_variables.items) |*return_variable|
                    try self.checkAndReplaceNew(&return_variable.name);
                try self.visitBlock(&value.body);
            },
            .if_statement => |*value| {
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression| try self.visitExpression(expression);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *NameDisplacer, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .identifier => |*identifier| self.checkAndReplace(&identifier.name),
            .function_call => |*call| {
                if (call.function_name == .identifier)
                    self.checkAndReplace(&call.function_name.identifier.name);
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
            .literal => {},
        }
    }

    fn checkAndReplaceNew(self: *NameDisplacer, name: *YulName) anyerror!void {
        if (self.translation_map.contains(name.*)) return error.DuplicateDisambiguatedName;
        if (!self.names_to_free.contains(name.*)) return;
        const original = name.*;
        const replacement = try self.name_dispenser.newName(original);
        if (!try self.translation_map.insert(self.allocator, original, replacement))
            return error.DuplicateDisambiguatedName;
        name.* = replacement;
    }

    fn checkAndReplace(self: *const NameDisplacer, name: *YulName) void {
        if (self.translation_map.get(name.*)) |replacement| name.* = replacement.*;
    }
};

test "name displacer renames a definition and all of its references" {
    const allocator = std.testing.allocator;
    const x = try YulName.init("x");
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    var declaration: AST.VariableDeclaration = .{};
    try declaration.variables.append(allocator, .{ .name = x });
    try root.statements.append(allocator, .{ .variable_declaration = declaration });
    try root.statements.append(allocator, .{ .expression_statement = .{
        .expression = .{ .identifier = .{ .name = x } },
    } });
    var used: NameCollectorModule.NameSet = .{};
    defer used.deinit(allocator);
    var dispenser = try NameDispenser.initWithUsedNames(allocator, .{}, used.take());
    defer dispenser.deinit();
    var names_to_free: NameCollectorModule.NameSet = .{};
    defer names_to_free.deinit(allocator);
    _ = try names_to_free.insert(allocator, x);
    var displacer = try NameDisplacer.init(allocator, &dispenser, &names_to_free);
    defer displacer.deinit();
    try displacer.run(&root);
    const renamed = root.statements.items[0].variable_declaration.variables.items[0].name;
    try std.testing.expect(!renamed.eql(x));
    try std.testing.expect(root.statements.items[1].expression_statement.expression.identifier.name.eql(renamed));
}
