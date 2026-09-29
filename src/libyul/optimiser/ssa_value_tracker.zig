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
        // The tracker already has unique interned names, so reserve once
        // and sort with the ordered set's comparator.
        try result.map.entries.ensureTotalCapacity(allocator, tracker.values_map.count());
        var iterator = tracker.values_map.keyIterator();
        while (iterator.next()) |name|
            result.map.entries.appendAssumeCapacity(.{ .key = name.*, .value = {} });
        std.sort.block(@TypeOf(result.map).Entry, result.map.entries.items, {}, struct {
            fn lessThan(_: void, left: @TypeOf(result.map).Entry, right: @TypeOf(result.map).Entry) bool {
                return left.key.lessThan(right.key);
            }
        }.lessThan);
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

test "SSA value tracker bulk set matches ordered insertion across allocation failures" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator, "{ let z := 1 let a let b, c let d, e := pair() z := 2 " ++
        "function f(p) -> r, s { s := p let local := 1 } " ++
        "if a { b := 3 let nested := a } " ++
        "for { let i := 0 } 1 { i := 1 } { let body := i } }", "ssa-set.yul", &reporter, .{}, .{})).?;
    defer ast.deinit();
    var tracker = SSAValueTracker.init(allocator);
    defer tracker.deinit();
    try tracker.run(ast.root());
    var expected: NameCollector.NameSet = .{};
    defer expected.deinit(allocator);
    var iterator = tracker.values_map.iterator();
    while (iterator.next()) |entry| _ = try expected.insert(allocator, entry.key_ptr.*);
    for ([_][]const u8{ "a", "c", "r", "local", "nested", "body" }) |name|
        try std.testing.expect(expected.contains(try YulName.init(name)));
    for ([_][]const u8{ "z", "b", "d", "e", "p", "s", "i" }) |name|
        try std.testing.expect(!expected.contains(try YulName.init(name)));
    const Check = struct {
        fn run(failing: std.mem.Allocator, block: *const AST.Block, reference: *const NameCollector.NameSet) !void {
            var actual = try SSAValueTracker.ssaVariables(failing, block);
            defer actual.deinit(failing);
            try std.testing.expectEqualDeep(reference.map.items(), actual.map.items());
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ ast.root(), &expected });
    var empty = try SSAValueTracker.ssaVariables(allocator, &.{});
    defer empty.deinit(allocator);
    try std.testing.expect(empty.isEmpty());
}
