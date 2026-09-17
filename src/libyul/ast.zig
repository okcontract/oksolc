// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned Yul abstract syntax tree and literal-value implementation.

const std = @import("std");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;
const BuiltinHandle = @import("builtins.zig").BuiltinHandle;
const ControlFlowSideEffects = @import("control_flow_side_effects.zig").ControlFlowSideEffects;
const SideEffects = @import("side_effects.zig").SideEffects;
const YulName = @import("yul_name.zig").YulName;

pub const LiteralKind = enum(c_int) {
    Number,
    Boolean,
    String,
};

pub const LiteralValue = struct {
    numeric_value: ?u256 = null,
    string_value: ?[]u8 = null,

    pub fn initBuiltinString(
        allocator: std.mem.Allocator,
        string_data: []const u8,
    ) std.mem.Allocator.Error!LiteralValue {
        return .{ .string_value = try allocator.dupe(u8, string_data) };
    }

    pub fn initNumeric(
        allocator: std.mem.Allocator,
        value_data: u256,
        representation_hint: ?[]const u8,
    ) std.mem.Allocator.Error!LiteralValue {
        return .{
            .numeric_value = value_data,
            .string_value = if (representation_hint) |hint_text|
                try allocator.dupe(u8, hint_text)
            else
                null,
        };
    }

    pub fn deinit(self: *LiteralValue, allocator: std.mem.Allocator) void {
        if (self.string_value) |string| allocator.free(string);
        self.* = undefined;
    }

    pub fn clone(
        self: *const LiteralValue,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error!LiteralValue {
        return .{
            .numeric_value = self.numeric_value,
            .string_value = if (self.string_value) |string|
                try allocator.dupe(u8, string)
            else
                null,
        };
    }

    pub fn value(self: *const LiteralValue) error{UnlimitedLiteral}!u256 {
        return self.numeric_value orelse error.UnlimitedLiteral;
    }

    pub fn builtinStringLiteralValue(
        self: *const LiteralValue,
    ) error{NumericLiteral}![]const u8 {
        if (!self.unlimited()) return error.NumericLiteral;
        return self.string_value orelse error.NumericLiteral;
    }

    pub fn unlimited(self: *const LiteralValue) bool {
        return self.numeric_value == null;
    }

    pub fn hint(self: *const LiteralValue) error{UnlimitedLiteral}!?[]const u8 {
        if (self.unlimited()) return error.UnlimitedLiteral;
        return self.string_value;
    }

    pub fn eql(self: *const LiteralValue, other: *const LiteralValue) bool {
        if (self.unlimited() != other.unlimited()) return false;
        if (self.unlimited()) {
            const left = self.string_value orelse return other.string_value == null;
            const right = other.string_value orelse return false;
            return std.mem.eql(u8, left, right);
        }
        return self.numeric_value.? == other.numeric_value.?;
    }

    pub fn lessThan(self: *const LiteralValue, other: *const LiteralValue) bool {
        if (self.unlimited() != other.unlimited()) return !self.unlimited();
        if (self.unlimited()) {
            const left = self.string_value orelse "";
            const right = other.string_value orelse "";
            return std.mem.order(u8, left, right) == .lt;
        }
        return self.numeric_value.? < other.numeric_value.?;
    }
};

pub const NameWithDebugData = struct {
    debug_data: ?DebugData = null,
    name: YulName = .{},
};

pub const NameWithDebugDataList = std.ArrayList(NameWithDebugData);

pub const Literal = struct {
    debug_data: ?DebugData = null,
    kind: LiteralKind,
    value: LiteralValue,

    pub fn deinit(self: *Literal, allocator: std.mem.Allocator) void {
        self.value.deinit(allocator);
        self.* = undefined;
    }
};

pub const Identifier = struct {
    debug_data: ?DebugData = null,
    name: YulName = .{},
};

pub const BuiltinName = struct {
    debug_data: ?DebugData = null,
    handle: BuiltinHandle,
};

pub const FunctionName = union(enum) {
    identifier: Identifier,
    builtin: BuiltinName,

    pub fn debugData(self: *const FunctionName) ?*const DebugData {
        return switch (self.*) {
            .identifier => |*identifier| optionalDebugData(&identifier.debug_data),
            .builtin => |*builtin| optionalDebugData(&builtin.debug_data),
        };
    }
};

pub const FunctionHandle = union(enum) {
    user: YulName,
    builtin: BuiltinHandle,
};

pub const Assignment = struct {
    debug_data: ?DebugData = null,
    variable_names: std.ArrayList(Identifier) = .empty,
    value: ?*Expression = null,

    pub fn deinit(self: *Assignment, allocator: std.mem.Allocator) void {
        self.variable_names.deinit(allocator);
        destroyOptionalExpression(allocator, self.value);
        self.* = undefined;
    }
};

pub const FunctionCall = struct {
    debug_data: ?DebugData = null,
    function_name: FunctionName,
    arguments: std.ArrayList(Expression) = .empty,

    pub fn deinit(self: *FunctionCall, allocator: std.mem.Allocator) void {
        for (self.arguments.items) |*argument| argument.deinit(allocator);
        self.arguments.deinit(allocator);
        self.* = undefined;
    }
};

pub const Expression = union(enum) {
    function_call: FunctionCall,
    identifier: Identifier,
    literal: Literal,

    pub fn deinit(self: *Expression, allocator: std.mem.Allocator) void {
        switch (self.*) {
            .function_call => |*call| call.deinit(allocator),
            .literal => |*literal| literal.deinit(allocator),
            .identifier => {},
        }
        self.* = undefined;
    }

    pub fn debugData(self: *const Expression) ?*const DebugData {
        return switch (self.*) {
            .function_call => |*call| optionalDebugData(&call.debug_data),
            .identifier => |*identifier| optionalDebugData(&identifier.debug_data),
            .literal => |*literal| optionalDebugData(&literal.debug_data),
        };
    }
};

pub const ExpressionStatement = struct {
    debug_data: ?DebugData = null,
    expression: Expression,

    pub fn deinit(self: *ExpressionStatement, allocator: std.mem.Allocator) void {
        self.expression.deinit(allocator);
        self.* = undefined;
    }
};

pub const VariableDeclaration = struct {
    debug_data: ?DebugData = null,
    variables: NameWithDebugDataList = .empty,
    value: ?*Expression = null,

    pub fn deinit(self: *VariableDeclaration, allocator: std.mem.Allocator) void {
        self.variables.deinit(allocator);
        destroyOptionalExpression(allocator, self.value);
        self.* = undefined;
    }
};

pub const Block = struct {
    debug_data: ?DebugData = null,
    statements: std.ArrayList(Statement) = .empty,

    pub fn deinit(self: *Block, allocator: std.mem.Allocator) void {
        for (self.statements.items) |*statement| statement.deinit(allocator);
        self.statements.deinit(allocator);
        self.* = undefined;
    }
};

pub const FunctionDefinition = struct {
    debug_data: ?DebugData = null,
    name: YulName = .{},
    parameters: NameWithDebugDataList = .empty,
    return_variables: NameWithDebugDataList = .empty,
    body: Block = .{},

    pub fn deinit(self: *FunctionDefinition, allocator: std.mem.Allocator) void {
        self.parameters.deinit(allocator);
        self.return_variables.deinit(allocator);
        self.body.deinit(allocator);
        self.* = undefined;
    }
};

pub const If = struct {
    debug_data: ?DebugData = null,
    condition: ?*Expression = null,
    body: Block = .{},

    pub fn deinit(self: *If, allocator: std.mem.Allocator) void {
        destroyOptionalExpression(allocator, self.condition);
        self.body.deinit(allocator);
        self.* = undefined;
    }
};

pub const Case = struct {
    debug_data: ?DebugData = null,
    value: ?*Literal = null,
    body: Block = .{},

    pub fn deinit(self: *Case, allocator: std.mem.Allocator) void {
        if (self.value) |value| {
            value.deinit(allocator);
            allocator.destroy(value);
        }
        self.body.deinit(allocator);
        self.* = undefined;
    }
};

pub const Switch = struct {
    debug_data: ?DebugData = null,
    expression: ?*Expression = null,
    cases: std.ArrayList(Case) = .empty,

    pub fn deinit(self: *Switch, allocator: std.mem.Allocator) void {
        destroyOptionalExpression(allocator, self.expression);
        for (self.cases.items) |*case_value| case_value.deinit(allocator);
        self.cases.deinit(allocator);
        self.* = undefined;
    }
};

pub const ForLoop = struct {
    debug_data: ?DebugData = null,
    pre: Block = .{},
    condition: ?*Expression = null,
    post: Block = .{},
    body: Block = .{},

    pub fn deinit(self: *ForLoop, allocator: std.mem.Allocator) void {
        self.pre.deinit(allocator);
        destroyOptionalExpression(allocator, self.condition);
        self.post.deinit(allocator);
        self.body.deinit(allocator);
        self.* = undefined;
    }
};

pub const Break = struct { debug_data: ?DebugData = null };
pub const Continue = struct { debug_data: ?DebugData = null };
pub const Leave = struct { debug_data: ?DebugData = null };

pub const Statement = union(enum) {
    expression_statement: ExpressionStatement,
    assignment: Assignment,
    variable_declaration: VariableDeclaration,
    function_definition: FunctionDefinition,
    if_statement: If,
    switch_statement: Switch,
    for_loop: ForLoop,
    break_statement: Break,
    continue_statement: Continue,
    leave_statement: Leave,
    block: Block,

    pub fn deinit(self: *Statement, allocator: std.mem.Allocator) void {
        switch (self.*) {
            .expression_statement => |*value| value.deinit(allocator),
            .assignment => |*value| value.deinit(allocator),
            .variable_declaration => |*value| value.deinit(allocator),
            .function_definition => |*value| value.deinit(allocator),
            .if_statement => |*value| value.deinit(allocator),
            .switch_statement => |*value| value.deinit(allocator),
            .for_loop => |*value| value.deinit(allocator),
            .block => |*value| value.deinit(allocator),
            .break_statement, .continue_statement, .leave_statement => {},
        }
        self.* = undefined;
    }

    pub fn debugData(self: *const Statement) ?*const DebugData {
        return switch (self.*) {
            .expression_statement => |*value| optionalDebugData(&value.debug_data),
            .assignment => |*value| optionalDebugData(&value.debug_data),
            .variable_declaration => |*value| optionalDebugData(&value.debug_data),
            .function_definition => |*value| optionalDebugData(&value.debug_data),
            .if_statement => |*value| optionalDebugData(&value.debug_data),
            .switch_statement => |*value| optionalDebugData(&value.debug_data),
            .for_loop => |*value| optionalDebugData(&value.debug_data),
            .break_statement => |*value| optionalDebugData(&value.debug_data),
            .continue_statement => |*value| optionalDebugData(&value.debug_data),
            .leave_statement => |*value| optionalDebugData(&value.debug_data),
            .block => |*value| optionalDebugData(&value.debug_data),
        };
    }
};

pub fn createExpression(
    allocator: std.mem.Allocator,
    value: Expression,
) std.mem.Allocator.Error!*Expression {
    const result = try allocator.create(Expression);
    result.* = value;
    return result;
}

pub fn createLiteral(
    allocator: std.mem.Allocator,
    value: Literal,
) std.mem.Allocator.Error!*Literal {
    const result = try allocator.create(Literal);
    result.* = value;
    return result;
}

pub fn isBuiltinFunctionCall(call: *const FunctionCall) bool {
    return call.function_name == .builtin;
}

pub fn nativeLocationOfExpression(expression: *const Expression) SourceLocation {
    return if (expression.debugData()) |debug_data| debug_data.native_location else .{};
}

pub fn originLocationOfExpression(expression: *const Expression) SourceLocation {
    return if (expression.debugData()) |debug_data| debug_data.origin_location else .{};
}

pub fn nativeLocationOfStatement(statement: *const Statement) SourceLocation {
    return if (statement.debugData()) |debug_data| debug_data.native_location else .{};
}

pub fn originLocationOfStatement(statement: *const Statement) SourceLocation {
    return if (statement.debugData()) |debug_data| debug_data.origin_location else .{};
}

pub fn hasDefaultCase(switch_statement: *const Switch) bool {
    for (switch_statement.cases.items) |case_value| if (case_value.value == null) return true;
    return false;
}

pub const BuiltinFunction = struct {
    name: []const u8,
    num_parameters: usize,
    num_returns: usize,
    side_effects: SideEffects,
    control_flow_side_effects: ControlFlowSideEffects,
    is_msize: bool = false,
    literal_arguments: []const ?LiteralKind = &.{},

    pub fn literalArgument(self: *const BuiltinFunction, index: usize) ?LiteralKind {
        return if (self.literal_arguments.len == 0) null else self.literal_arguments[index];
    }
};

pub const DialectVTable = struct {
    find_builtin: ?*const fn (context: ?*const anyopaque, name: []const u8) ?BuiltinHandle = null,
    builtin: ?*const fn (context: ?*const anyopaque, handle: BuiltinHandle) ?*const BuiltinFunction = null,
    reserved_identifier: ?*const fn (context: ?*const anyopaque, name: []const u8) bool = null,
    discard_function_handle: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle = null,
    equality_function_handle: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle = null,
    boolean_negation_function_handle: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle = null,
    memory_store_function_handle: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle = null,
    memory_load_function_handle: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle = null,
    storage_store_function_handle: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle = null,
    storage_load_function_handle: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle = null,
    hash_function_handle: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle = null,
};

const empty_dialect_vtable: DialectVTable = .{};

pub const Dialect = struct {
    context: ?*const anyopaque = null,
    vtable: *const DialectVTable = &empty_dialect_vtable,

    pub fn findBuiltin(self: Dialect, name: []const u8) ?BuiltinHandle {
        const function = self.vtable.find_builtin orelse return null;
        return function(self.context, name);
    }

    pub fn builtin(self: Dialect, handle: BuiltinHandle) error{UnknownBuiltin}!*const BuiltinFunction {
        const function = self.vtable.builtin orelse return error.UnknownBuiltin;
        return function(self.context, handle) orelse error.UnknownBuiltin;
    }

    pub fn reservedIdentifier(self: Dialect, name: []const u8) bool {
        if (self.vtable.reserved_identifier) |function| return function(self.context, name);
        return self.findBuiltin(name) != null;
    }

    pub fn discardFunctionHandle(self: Dialect) ?BuiltinHandle {
        return optionalDialectHandle(self, self.vtable.discard_function_handle);
    }

    pub fn equalityFunctionHandle(self: Dialect) ?BuiltinHandle {
        return optionalDialectHandle(self, self.vtable.equality_function_handle);
    }

    pub fn booleanNegationFunctionHandle(self: Dialect) ?BuiltinHandle {
        return optionalDialectHandle(self, self.vtable.boolean_negation_function_handle);
    }

    pub fn memoryStoreFunctionHandle(self: Dialect) ?BuiltinHandle {
        return optionalDialectHandle(self, self.vtable.memory_store_function_handle);
    }

    pub fn memoryLoadFunctionHandle(self: Dialect) ?BuiltinHandle {
        return optionalDialectHandle(self, self.vtable.memory_load_function_handle);
    }

    pub fn storageStoreFunctionHandle(self: Dialect) ?BuiltinHandle {
        return optionalDialectHandle(self, self.vtable.storage_store_function_handle);
    }

    pub fn storageLoadFunctionHandle(self: Dialect) ?BuiltinHandle {
        return optionalDialectHandle(self, self.vtable.storage_load_function_handle);
    }

    pub fn hashFunctionHandle(self: Dialect) ?BuiltinHandle {
        return optionalDialectHandle(self, self.vtable.hash_function_handle);
    }

    pub fn zeroLiteral(self: Dialect, allocator: std.mem.Allocator) !Literal {
        _ = self;
        return .{
            .debug_data = .{},
            .kind = .Number,
            .value = try LiteralValue.initNumeric(allocator, 0, null),
        };
    }
};

pub const AST = struct {
    allocator: std.mem.Allocator,
    dialect_value: Dialect,
    root_block: Block,

    pub fn init(allocator: std.mem.Allocator, dialect_input: Dialect, root_input: Block) AST {
        return .{ .allocator = allocator, .dialect_value = dialect_input, .root_block = root_input };
    }

    pub fn deinit(self: *AST) void {
        self.root_block.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn dialect(self: *const AST) *const Dialect {
        return &self.dialect_value;
    }

    pub fn root(self: *const AST) *const Block {
        return &self.root_block;
    }
};

fn optionalDialectHandle(
    dialect: Dialect,
    function: ?*const fn (context: ?*const anyopaque) ?BuiltinHandle,
) ?BuiltinHandle {
    return if (function) |callback| callback(dialect.context) else null;
}

fn optionalDebugData(value: *const ?DebugData) ?*const DebugData {
    return if (value.* != null) &value.*.? else null;
}

fn destroyOptionalExpression(allocator: std.mem.Allocator, expression: ?*Expression) void {
    if (expression) |value| {
        value.deinit(allocator);
        allocator.destroy(value);
    }
}

test "literal values preserve unlimited strings and ignore numeric hints in equality" {
    const allocator = std.testing.allocator;
    var first = try LiteralValue.initNumeric(allocator, 42, "0x2a");
    defer first.deinit(allocator);
    var second = try LiteralValue.initNumeric(allocator, 42, "42");
    defer second.deinit(allocator);
    var unlimited = try LiteralValue.initBuiltinString(allocator, "builtin literal");
    defer unlimited.deinit(allocator);
    try std.testing.expect(first.eql(&second));
    try std.testing.expect(first.lessThan(&unlimited));
    try std.testing.expectEqualStrings("builtin literal", try unlimited.builtinStringLiteralValue());
}

test "recursive Yul AST teardown owns expression and statement containers" {
    const allocator = std.testing.allocator;
    const variable = try YulName.init("x");
    const expression = try createExpression(allocator, .{ .identifier = .{ .name = variable } });
    var root: Block = .{};
    try root.statements.append(allocator, .{ .assignment = .{ .value = expression } });
    var ast = AST.init(allocator, .{}, root);
    ast.deinit();
}
