// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic name collection and declaration-reference counters shared by
//! the Yul optimizer passes.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const Utilities = @import("../utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

fn lessFunctionHandle(left: AST.FunctionHandle, right: AST.FunctionHandle) bool {
    const left_tag = @intFromEnum(left);
    const right_tag = @intFromEnum(right);
    if (left_tag != right_tag) return left_tag < right_tag;
    return switch (left) {
        .user => |name| name.lessThan(right.user),
        .builtin => |handle| handle.id < right.builtin.id,
    };
}

const FunctionHandleContext = struct {
    pub fn hash(_: @This(), handle: AST.FunctionHandle) u64 {
        return switch (handle) {
            .user => |name| name.hashValue() ^ 0xa076_1d64_78bd_642f,
            .builtin => |builtin| @as(u64, @intCast(builtin.id)) *%
                0x9e37_79b9_7f4a_7c15 ^ 0xe703_7ed1_a0b4_28db,
        };
    }

    pub fn eql(_: @This(), left: AST.FunctionHandle, right: AST.FunctionHandle) bool {
        if (@intFromEnum(left) != @intFromEnum(right)) return false;
        return switch (left) {
            .user => |name| name.eql(right.user),
            .builtin => |handle| handle.id == right.builtin.id,
        };
    }
};

/// Temporary, unordered accumulator. Public counters sort its contents into
/// `ReferenceMap` before returning, preserving the upstream map contract.
const FunctionReferenceIndex = std.HashMapUnmanaged(
    AST.FunctionHandle,
    usize,
    FunctionHandleContext,
    80,
);

pub const NameSet = ordered.OrderedSet(YulName, lessYulName);
pub const ReferenceMap = ordered.OrderedMap(AST.FunctionHandle, usize, lessFunctionHandle);
pub const VariableReferenceMap = ordered.OrderedMap(YulName, usize, lessYulName);
pub const FunctionDefinitionMap = ordered.OrderedMap(
    YulName,
    *const AST.FunctionDefinition,
    lessYulName,
);

pub const CollectWhat = enum(c_int) {
    variables_and_functions,
    only_variables,
    only_functions,
};

pub const NameCollector = struct {
    allocator: std.mem.Allocator,
    names_set: NameSet = .{},
    collect_what: CollectWhat = .variables_and_functions,

    pub fn initBlock(
        allocator: std.mem.Allocator,
        block: *const AST.Block,
        collect_what: CollectWhat,
    ) !NameCollector {
        var result: NameCollector = .{ .allocator = allocator, .collect_what = collect_what };
        errdefer result.deinit();
        try result.visitBlock(block);
        return result;
    }

    pub fn initFunction(
        allocator: std.mem.Allocator,
        function: *const AST.FunctionDefinition,
        collect_what: CollectWhat,
    ) !NameCollector {
        var result: NameCollector = .{ .allocator = allocator, .collect_what = collect_what };
        errdefer result.deinit();
        try result.visitFunction(function);
        return result;
    }

    pub fn deinit(self: *NameCollector) void {
        self.names_set.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn names(self: *const NameCollector) *const NameSet {
        return &self.names_set;
    }

    pub fn takeNames(self: *NameCollector) NameSet {
        return self.names_set.take();
    }

    fn add(self: *NameCollector, name: YulName) !void {
        _ = try self.names_set.insert(self.allocator, name);
    }

    fn visitFunction(self: *NameCollector, function: *const AST.FunctionDefinition) anyerror!void {
        if (self.collect_what != .only_variables) try self.add(function.name);
        if (self.collect_what != .only_functions) {
            for (function.parameters.items) |parameter| try self.add(parameter.name);
            for (function.return_variables.items) |return_variable| try self.add(return_variable.name);
        }
        try self.visitBlock(&function.body);
    }

    fn visitBlock(self: *NameCollector, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| switch (statement.*) {
            .variable_declaration => |*declaration| if (self.collect_what != .only_functions)
                for (declaration.variables.items) |variable| try self.add(variable.name),
            .function_definition => |*function| try self.visitFunction(function),
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitBlock(&value.body);
                try self.visitBlock(&value.post);
            },
            .block => |*value| try self.visitBlock(value),
            else => {},
        };
    }
};

pub const ReferencesCounter = struct {
    pub fn countReferencesBlock(
        allocator: std.mem.Allocator,
        block: *const AST.Block,
    ) !ReferenceMap {
        var index: FunctionReferenceIndex = .empty;
        defer index.deinit(allocator);
        try countFunctionReferencesBlock(allocator, &index, block);
        return orderedReferenceMap(allocator, &index);
    }

    pub fn countReferencesFunction(
        allocator: std.mem.Allocator,
        function: *const AST.FunctionDefinition,
    ) !ReferenceMap {
        var index: FunctionReferenceIndex = .empty;
        defer index.deinit(allocator);
        try countFunctionReferencesBlock(allocator, &index, &function.body);
        return orderedReferenceMap(allocator, &index);
    }

    pub fn countReferencesExpression(
        allocator: std.mem.Allocator,
        expression: *const AST.Expression,
    ) !ReferenceMap {
        var index: FunctionReferenceIndex = .empty;
        defer index.deinit(allocator);
        try countFunctionReferencesExpression(allocator, &index, expression);
        return orderedReferenceMap(allocator, &index);
    }
};

pub const VariableReferencesCounter = struct {
    pub fn countReferencesBlock(
        allocator: std.mem.Allocator,
        block: *const AST.Block,
    ) !VariableReferenceMap {
        var result: VariableReferenceMap = .{};
        errdefer result.deinit(allocator);
        try countVariableReferencesBlock(allocator, &result, block);
        return result;
    }

    pub fn countReferencesFunction(
        allocator: std.mem.Allocator,
        function: *const AST.FunctionDefinition,
    ) !VariableReferenceMap {
        var result: VariableReferenceMap = .{};
        errdefer result.deinit(allocator);
        try countVariableReferencesBlock(allocator, &result, &function.body);
        return result;
    }

    pub fn countReferencesExpression(
        allocator: std.mem.Allocator,
        expression: *const AST.Expression,
    ) !VariableReferenceMap {
        var result: VariableReferenceMap = .{};
        errdefer result.deinit(allocator);
        try countVariableReferencesExpression(allocator, &result, expression);
        return result;
    }

    pub fn countReferencesStatement(
        allocator: std.mem.Allocator,
        statement: *const AST.Statement,
    ) !VariableReferenceMap {
        var result: VariableReferenceMap = .{};
        errdefer result.deinit(allocator);
        try countVariableReferencesStatement(allocator, &result, statement);
        return result;
    }
};

pub const AssignmentsSinceContinue = struct {
    allocator: std.mem.Allocator,
    names_set: NameSet = .{},
    for_loop_depth: usize = 0,
    continue_found: bool = false,

    pub fn init(allocator: std.mem.Allocator, block: *const AST.Block) !AssignmentsSinceContinue {
        var result: AssignmentsSinceContinue = .{ .allocator = allocator };
        errdefer result.deinit();
        try result.visitBlock(block);
        return result;
    }

    pub fn deinit(self: *AssignmentsSinceContinue) void {
        self.names_set.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn names(self: *const AssignmentsSinceContinue) *const NameSet {
        return &self.names_set;
    }

    pub fn empty(self: *const AssignmentsSinceContinue) bool {
        return self.names_set.isEmpty();
    }

    fn visitBlock(self: *AssignmentsSinceContinue, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| switch (statement.*) {
            .assignment => |*assignment| {
                if (self.continue_found) {
                    for (assignment.variable_names.items) |variable| {
                        _ = try self.names_set.insert(self.allocator, variable.name);
                    }
                }
            },
            .function_definition => return error.FunctionDefinitionInLoopBody,
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*value| {
                self.for_loop_depth += 1;
                defer self.for_loop_depth -= 1;
                try self.visitBlock(&value.pre);
                try self.visitBlock(&value.body);
                try self.visitBlock(&value.post);
            },
            .continue_statement => if (self.for_loop_depth == 0) {
                self.continue_found = true;
            },
            .block => |*value| try self.visitBlock(value),
            else => {},
        };
    }
};

pub fn assignedVariableNames(
    allocator: std.mem.Allocator,
    block: *const AST.Block,
) !NameSet {
    var result: NameSet = .{};
    errdefer result.deinit(allocator);
    try collectAssignedNames(allocator, &result, block);
    return result;
}

pub fn allFunctionDefinitions(
    allocator: std.mem.Allocator,
    block: *const AST.Block,
) !FunctionDefinitionMap {
    var result: FunctionDefinitionMap = .{};
    errdefer result.deinit(allocator);
    try collectFunctionDefinitions(allocator, &result, block);
    return result;
}

fn incrementFunctionReference(
    allocator: std.mem.Allocator,
    index: *FunctionReferenceIndex,
    handle: AST.FunctionHandle,
) !void {
    const result = try index.getOrPut(allocator, handle);
    if (!result.found_existing) result.value_ptr.* = 0;
    result.value_ptr.* += 1;
}

fn incrementVariableReference(
    allocator: std.mem.Allocator,
    map: *VariableReferenceMap,
    name: YulName,
) !void {
    if (map.getPtr(name)) |count| {
        count.* += 1;
    } else _ = try map.insert(allocator, name, 1);
}

fn countFunctionReferencesExpression(
    allocator: std.mem.Allocator,
    index: *FunctionReferenceIndex,
    expression: *const AST.Expression,
) anyerror!void {
    switch (expression.*) {
        .literal => {},
        .identifier => |identifier| try incrementFunctionReference(allocator, index, .{ .user = identifier.name }),
        .function_call => |*call| {
            try incrementFunctionReference(allocator, index, Utilities.functionNameToHandle(&call.function_name));
            var argument_index = call.arguments.items.len;
            while (argument_index != 0) {
                argument_index -= 1;
                try countFunctionReferencesExpression(allocator, index, &call.arguments.items[argument_index]);
            }
        },
    }
}

fn countFunctionReferencesStatement(
    allocator: std.mem.Allocator,
    index: *FunctionReferenceIndex,
    statement: *const AST.Statement,
) anyerror!void {
    switch (statement.*) {
        .expression_statement => |*value| try countFunctionReferencesExpression(allocator, index, &value.expression),
        .assignment => |*value| {
            for (value.variable_names.items) |identifier|
                try incrementFunctionReference(allocator, index, .{ .user = identifier.name });
            try countFunctionReferencesExpression(allocator, index, value.value orelse return error.InvalidAst);
        },
        .variable_declaration => |*value| if (value.value) |expression|
            try countFunctionReferencesExpression(allocator, index, expression),
        .function_definition => |*value| try countFunctionReferencesBlock(allocator, index, &value.body),
        .if_statement => |*value| {
            try countFunctionReferencesExpression(allocator, index, value.condition orelse return error.InvalidAst);
            try countFunctionReferencesBlock(allocator, index, &value.body);
        },
        .switch_statement => |*value| {
            try countFunctionReferencesExpression(allocator, index, value.expression orelse return error.InvalidAst);
            for (value.cases.items) |*case_value|
                try countFunctionReferencesBlock(allocator, index, &case_value.body);
        },
        .for_loop => |*value| {
            try countFunctionReferencesBlock(allocator, index, &value.pre);
            try countFunctionReferencesExpression(allocator, index, value.condition orelse return error.InvalidAst);
            try countFunctionReferencesBlock(allocator, index, &value.body);
            try countFunctionReferencesBlock(allocator, index, &value.post);
        },
        .block => |*value| try countFunctionReferencesBlock(allocator, index, value),
        .break_statement, .continue_statement, .leave_statement => {},
    }
}

fn countFunctionReferencesBlock(
    allocator: std.mem.Allocator,
    index: *FunctionReferenceIndex,
    block: *const AST.Block,
) anyerror!void {
    for (block.statements.items) |*statement|
        try countFunctionReferencesStatement(allocator, index, statement);
}

fn orderedReferenceMap(
    allocator: std.mem.Allocator,
    index: *const FunctionReferenceIndex,
) !ReferenceMap {
    var result: ReferenceMap = .{};
    errdefer result.deinit(allocator);
    try result.entries.ensureTotalCapacity(allocator, @intCast(index.count()));
    var iterator = index.iterator();
    while (iterator.next()) |entry|
        result.entries.appendAssumeCapacity(.{
            .key = entry.key_ptr.*,
            .value = entry.value_ptr.*,
        });
    std.sort.block(ReferenceMap.Entry, result.entries.items, {}, struct {
        fn lessThan(_: void, left: ReferenceMap.Entry, right: ReferenceMap.Entry) bool {
            return lessFunctionHandle(left.key, right.key);
        }
    }.lessThan);
    return result;
}

fn countVariableReferencesExpression(
    allocator: std.mem.Allocator,
    map: *VariableReferenceMap,
    expression: *const AST.Expression,
) anyerror!void {
    switch (expression.*) {
        .literal => {},
        .identifier => |identifier| try incrementVariableReference(allocator, map, identifier.name),
        .function_call => |*call| {
            var index = call.arguments.items.len;
            while (index != 0) {
                index -= 1;
                try countVariableReferencesExpression(allocator, map, &call.arguments.items[index]);
            }
        },
    }
}

fn countVariableReferencesStatement(
    allocator: std.mem.Allocator,
    map: *VariableReferenceMap,
    statement: *const AST.Statement,
) anyerror!void {
    switch (statement.*) {
        .expression_statement => |*value| try countVariableReferencesExpression(allocator, map, &value.expression),
        .assignment => |*value| {
            for (value.variable_names.items) |identifier|
                try incrementVariableReference(allocator, map, identifier.name);
            try countVariableReferencesExpression(allocator, map, value.value orelse return error.InvalidAst);
        },
        .variable_declaration => |*value| if (value.value) |expression|
            try countVariableReferencesExpression(allocator, map, expression),
        .function_definition => |*value| try countVariableReferencesBlock(allocator, map, &value.body),
        .if_statement => |*value| {
            try countVariableReferencesExpression(allocator, map, value.condition orelse return error.InvalidAst);
            try countVariableReferencesBlock(allocator, map, &value.body);
        },
        .switch_statement => |*value| {
            try countVariableReferencesExpression(allocator, map, value.expression orelse return error.InvalidAst);
            for (value.cases.items) |*case_value|
                try countVariableReferencesBlock(allocator, map, &case_value.body);
        },
        .for_loop => |*value| {
            try countVariableReferencesBlock(allocator, map, &value.pre);
            try countVariableReferencesExpression(allocator, map, value.condition orelse return error.InvalidAst);
            try countVariableReferencesBlock(allocator, map, &value.body);
            try countVariableReferencesBlock(allocator, map, &value.post);
        },
        .block => |*value| try countVariableReferencesBlock(allocator, map, value),
        .break_statement, .continue_statement, .leave_statement => {},
    }
}

fn countVariableReferencesBlock(
    allocator: std.mem.Allocator,
    map: *VariableReferenceMap,
    block: *const AST.Block,
) anyerror!void {
    for (block.statements.items) |*statement|
        try countVariableReferencesStatement(allocator, map, statement);
}

fn collectAssignedNames(
    allocator: std.mem.Allocator,
    result: *NameSet,
    block: *const AST.Block,
) anyerror!void {
    for (block.statements.items) |*statement| switch (statement.*) {
        .assignment => |*value| {
            for (value.variable_names.items) |variable|
                _ = try result.insert(allocator, variable.name);
        },
        .function_definition => |*value| try collectAssignedNames(allocator, result, &value.body),
        .if_statement => |*value| try collectAssignedNames(allocator, result, &value.body),
        .switch_statement => |*value| for (value.cases.items) |*case_value|
            try collectAssignedNames(allocator, result, &case_value.body),
        .for_loop => |*value| {
            try collectAssignedNames(allocator, result, &value.pre);
            try collectAssignedNames(allocator, result, &value.body);
            try collectAssignedNames(allocator, result, &value.post);
        },
        .block => |*value| try collectAssignedNames(allocator, result, value),
        else => {},
    };
}

fn collectFunctionDefinitions(
    allocator: std.mem.Allocator,
    result: *FunctionDefinitionMap,
    block: *const AST.Block,
) anyerror!void {
    for (block.statements.items) |*statement| switch (statement.*) {
        .function_definition => |*value| {
            _ = try result.fetchPut(allocator, value.name, value);
            try collectFunctionDefinitions(allocator, result, &value.body);
        },
        .if_statement => |*value| try collectFunctionDefinitions(allocator, result, &value.body),
        .switch_statement => |*value| for (value.cases.items) |*case_value|
            try collectFunctionDefinitions(allocator, result, &case_value.body),
        .for_loop => |*value| {
            try collectFunctionDefinitions(allocator, result, &value.pre);
            try collectFunctionDefinitions(allocator, result, &value.body);
            try collectFunctionDefinitions(allocator, result, &value.post);
        },
        .block => |*value| try collectFunctionDefinitions(allocator, result, value),
        else => {},
    };
}

test "name collectors preserve declarations, references, and continue boundaries" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.init(.Cancun), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := 0 function f(a) -> r { r := add(a, x) } for { let i := 0 } lt(x, 2) { x := add(x, 1) } { continue x := f(x) } }",
        "names.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var names = try NameCollector.initBlock(allocator, ast.root(), .variables_and_functions);
    defer names.deinit();
    try std.testing.expectEqual(@as(usize, 5), names.names().len());
    var references = try VariableReferencesCounter.countReferencesBlock(allocator, ast.root());
    defer references.deinit(allocator);
    try std.testing.expect((references.get(try YulName.init("x")) orelse return error.MissingXReference).* >= 5);
    var function_references = try ReferencesCounter.countReferencesBlock(allocator, ast.root());
    defer function_references.deinit(allocator);
    for (1..function_references.len()) |index|
        try std.testing.expect(lessFunctionHandle(
            function_references.items()[index - 1].key,
            function_references.items()[index].key,
        ));
    const loop = &ast.root().statements.items[2].for_loop;
    var after_continue = try AssignmentsSinceContinue.init(allocator, &loop.body);
    defer after_continue.deinit();
    try std.testing.expect(after_continue.names().contains(try YulName.init("x")));
}
