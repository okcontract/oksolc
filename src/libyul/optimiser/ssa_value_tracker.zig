// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Collects declarations that remain single-assignment and their initial
//! expression values.

const std = @import("std");
const AST = @import("../ast.zig");
const NameCollector = @import("name_collector.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const ValueMap = std.AutoHashMapUnmanaged(YulName, *const AST.Expression);

pub const SSAValueTracker = struct {
    allocator: std.mem.Allocator,
    values_map: ValueMap = .{},
    zero: AST.Expression = .{ .literal = .{
        .kind = .Number,
        .value = .{ .numeric_value = 0 },
    } },

    pub fn init(allocator: std.mem.Allocator) SSAValueTracker {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *SSAValueTracker) void {
        self.values_map.deinit(self.allocator);
        self.zero.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn run(self: *SSAValueTracker, block: *const AST.Block) anyerror!void {
        try self.visitBlock(block);
    }

    pub fn values(self: *const SSAValueTracker) *const ValueMap {
        return &self.values_map;
    }

    pub fn value(self: *const SSAValueTracker, name: YulName) error{UnknownSSAValue}!*const AST.Expression {
        return self.values_map.get(name) orelse error.UnknownSSAValue;
    }

    pub fn ssaVariables(
        allocator: std.mem.Allocator,
        block: *const AST.Block,
    ) anyerror!NameCollector.NameSet {
        var tracker = SSAValueTracker.init(allocator);
        defer tracker.deinit();
        try tracker.run(block);
        var result: NameCollector.NameSet = .{};
        errdefer result.deinit(allocator);
        var iterator = tracker.values_map.iterator();
        while (iterator.next()) |entry| _ = try result.insert(allocator, entry.key_ptr.*);
        return result;
    }

    fn setValue(
        self: *SSAValueTracker,
        name: YulName,
        expression: ?*const AST.Expression,
    ) anyerror!void {
        if (self.values_map.contains(name)) return error.SourceNotDisambiguated;
        try self.values_map.putNoClobber(self.allocator, name, expression orelse &self.zero);
    }

    fn visitBlock(self: *SSAValueTracker, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *SSAValueTracker, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .assignment => |*assignment| {
                for (assignment.variable_names.items) |variable|
                    _ = self.values_map.remove(variable.name);
            },
            .variable_declaration => |*declaration| {
                if (declaration.value == null) {
                    for (declaration.variables.items) |variable| try self.setValue(variable.name, null);
                } else if (declaration.variables.items.len == 1) {
                    try self.setValue(declaration.variables.items[0].name, declaration.value);
                }
            },
            .function_definition => |*function| {
                for (function.return_variables.items) |variable| try self.setValue(variable.name, null);
                try self.visitBlock(&function.body);
            },
            .if_statement => |*if_statement| try self.visitBlock(&if_statement.body),
            .switch_statement => |*switch_statement| for (switch_statement.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*loop| {
                try self.visitBlock(&loop.pre);
                try self.visitBlock(&loop.body);
                try self.visitBlock(&loop.post);
            },
            .block => |*nested| try self.visitBlock(nested),
            else => {},
        }
    }
};

test "SSA value tracker drops reassigned variables and keeps zero defaults" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := 1 let y x := 2 }",
        "values.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var tracker = SSAValueTracker.init(allocator);
    defer tracker.deinit();
    try tracker.run(ast.root());
    try std.testing.expect(!tracker.values().contains(try YulName.init("x")));
    try std.testing.expect(tracker.values().contains(try YulName.init("y")));
}
