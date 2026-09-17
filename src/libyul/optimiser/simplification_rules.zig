// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Yul expression adapter for the ordered EVM simplification rule list.
//!
//! The C++ implementation instantiates a recursive `Pattern` template. This
//! translation feeds identity-preserving expression IDs to the procedural rule
//! engine: identifiers stay distinct even when their SSA values are inspected,
//! while constants and operations can still be matched through those values.

const std = @import("std");
const Numeric = @import("../../libsolutil/numeric.zig");
const InstructionModule = @import("../../libevmasm/instruction.zig");
const RuleList = @import("../../libevmasm/rule_list.zig");
const AST = @import("../ast.zig");
const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
const ASTCopierModule = @import("ast_copier.zig");
const DataFlow = @import("data_flow_analyzer.zig");
const YulName = @import("../yul_name.zig").YulName;

const Instruction = InstructionModule.Instruction;
const ExpressionId = RuleList.ExpressionId;

pub const PatternKind = enum(c_int) {
    Operation,
    Constant,
    Any,
};

/// Callback equivalent of the C++ `_ssaValues` function. Returned pointers
/// borrow the analyzer state for the duration of `findFirstMatch`.
pub const SSAValueResolver = struct {
    context: ?*const anyopaque = null,
    resolve: ?*const fn (
        ?*const anyopaque,
        YulName,
    ) anyerror!?*const DataFlow.AssignedValue = null,

    pub fn get(self: SSAValueResolver, name: YulName) anyerror!?*const DataFlow.AssignedValue {
        const callback = self.resolve orelse return null;
        return callback(self.context, name);
    }
};

pub const InstructionAndArguments = struct {
    instruction: Instruction,
    arguments: []const AST.Expression,
};

pub const SimplificationRules = struct {
    pub fn isInitialized() bool {
        // Zig has no dynamic rule-list initialization; the procedural table is
        // immutable program code and is available as soon as this module loads.
        return true;
    }

    pub fn instructionAndArguments(
        dialect: AST.Dialect,
        expression: *const AST.Expression,
    ) ?InstructionAndArguments {
        const call = switch (expression.*) {
            .function_call => |*value| value,
            .identifier, .literal => return null,
        };
        const evm_dialect = EVMDialectModule.fromDialect(dialect) orelse return null;
        const handle = switch (call.function_name) {
            .builtin => |builtin| builtin.handle,
            .identifier => return null,
        };
        const builtin = evm_dialect.builtin(handle) orelse return null;
        return .{
            .instruction = builtin.instruction orelse return null,
            .arguments = call.arguments.items,
        };
    }

    /// Returns an owned replacement for the first matching rule, or null.
    pub fn findFirstMatch(
        allocator: std.mem.Allocator,
        expression: *const AST.Expression,
        dialect: AST.Dialect,
        ssa_values: SSAValueResolver,
    ) anyerror!?AST.Expression {
        const root = instructionAndArguments(dialect, expression) orelse return null;
        // Pattern::matches rejects a direct function-call argument before it
        // attempts any nested match. Such calls may still be inspected through
        // an SSA identifier, which ExpressionGraph handles separately.
        for (root.arguments) |argument| switch (argument) {
            .function_call => return null,
            .identifier, .literal => {},
        };

        const evm_dialect = EVMDialectModule.fromDialect(dialect) orelse
            return error.ExpectedEVMDialect;
        var graph = ExpressionGraph.init(
            allocator,
            dialect,
            evm_dialect,
            ssa_values,
            if (expression.debugData()) |debug_data| debug_data.* else null,
        );
        defer graph.deinit();
        var argument_ids: std.ArrayList(ExpressionId) = .empty;
        defer argument_ids.deinit(allocator);
        for (root.arguments) |*argument|
            try argument_ids.append(allocator, try graph.addBorrowed(argument));

        const replacement_id = try RuleList.simplifyWithOptions(
            &graph,
            root.instruction,
            argument_ids.items,
            graph.root_debug_data orelse .{},
            .{
                .for_yul_optimizer = true,
                .evm_version = evm_dialect.evmVersion(),
            },
        ) orelse return null;
        return @as(?AST.Expression, try graph.toExpression(replacement_id));
    }
};

const NodeKind = enum {
    borrowed,
    constant,
    operation,
};

const Node = struct {
    kind: NodeKind,
    source: ?*const AST.Expression = null,
    constant: u256 = 0,
    instruction: Instruction = .STOP,
    arguments: []ExpressionId = &.{},
    owns_arguments: bool = false,

    fn deinit(self: *Node, allocator: std.mem.Allocator) void {
        if (self.owns_arguments) allocator.free(self.arguments);
        self.* = undefined;
    }
};

const ExpressionGraph = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    evm_dialect: *const EVMDialectModule.EVMDialect,
    ssa_values: SSAValueResolver,
    root_debug_data: ?@import("../../liblangutil/debug_data.zig").DebugData,
    nodes: std.ArrayList(Node) = .empty,

    fn init(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        evm_dialect: *const EVMDialectModule.EVMDialect,
        ssa_values: SSAValueResolver,
        root_debug_data: ?@import("../../liblangutil/debug_data.zig").DebugData,
    ) ExpressionGraph {
        return .{
            .allocator = allocator,
            .dialect = dialect,
            .evm_dialect = evm_dialect,
            .ssa_values = ssa_values,
            .root_debug_data = root_debug_data,
        };
    }

    fn deinit(self: *ExpressionGraph) void {
        for (self.nodes.items) |*node| node.deinit(self.allocator);
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }

    fn addBorrowed(self: *ExpressionGraph, expression: *const AST.Expression) anyerror!ExpressionId {
        for (self.nodes.items, 0..) |*node, index| {
            if (node.kind != .borrowed) continue;
            if (borrowedEqual(node.source.?, expression)) return @intCast(index);
        }
        if (self.nodes.items.len >= std.math.maxInt(ExpressionId))
            return error.ExpressionCapacity;
        const id: ExpressionId = @intCast(self.nodes.items.len);
        try self.nodes.append(self.allocator, .{ .kind = .borrowed, .source = expression });

        const resolved = try self.resolvedExpression(expression);
        const operation = SimplificationRules.instructionAndArguments(self.dialect, resolved) orelse return id;
        for (operation.arguments) |argument| switch (argument) {
            .function_call => return id,
            .identifier, .literal => {},
        };
        const arguments = try self.allocator.alloc(ExpressionId, operation.arguments.len);
        var arguments_owned = true;
        errdefer if (arguments_owned) self.allocator.free(arguments);
        for (operation.arguments, 0..) |*argument, index|
            arguments[index] = try self.addBorrowed(argument);
        self.nodes.items[id].instruction = operation.instruction;
        self.nodes.items[id].arguments = arguments;
        self.nodes.items[id].owns_arguments = true;
        arguments_owned = false;
        return id;
    }

    pub fn knownConstantValue(self: *const ExpressionGraph, id: ExpressionId) ?u256 {
        const node = self.getNode(id) orelse return null;
        return switch (node.kind) {
            .constant => node.constant,
            .operation => null,
            .borrowed => blk: {
                const resolved = self.resolvedExpression(node.source.?) catch break :blk null;
                const literal = switch (resolved.*) {
                    .literal => |*value| value,
                    .identifier, .function_call => break :blk null,
                };
                if (literal.kind != .Number) break :blk null;
                break :blk literal.value.value() catch null;
            },
        };
    }

    pub fn operationArguments(
        self: *const ExpressionGraph,
        id: ExpressionId,
        instruction: Instruction,
    ) ?[]const ExpressionId {
        const node = self.getNode(id) orelse return null;
        if ((node.kind != .operation and node.kind != .borrowed) or
            node.instruction != instruction or !node.owns_arguments)
            return null;
        return node.arguments;
    }

    pub fn makeConstant(
        self: *ExpressionGraph,
        value: u256,
        _: @import("../../liblangutil/debug_data.zig").DebugData,
    ) !ExpressionId {
        for (self.nodes.items, 0..) |node, index|
            if (node.kind == .constant and node.constant == value) return @intCast(index);
        if (self.nodes.items.len >= std.math.maxInt(ExpressionId))
            return error.ExpressionCapacity;
        const id: ExpressionId = @intCast(self.nodes.items.len);
        try self.nodes.append(self.allocator, .{ .kind = .constant, .constant = value });
        return id;
    }

    /// Materializes the resolved literal captured by a C++ Constant pattern.
    /// Unlike a newly synthesized constant, this preserves the source spelling
    /// (for example `0xff`) carried by an SSA initializer.
    pub fn materializeConstant(
        self: *ExpressionGraph,
        id: ExpressionId,
        value: u256,
        debug_data: @import("../../liblangutil/debug_data.zig").DebugData,
    ) !ExpressionId {
        const node = self.getNode(id) orelse return error.InvalidExpressionID;
        if (node.kind == .borrowed) {
            const resolved = try self.resolvedExpression(node.source.?);
            if (resolved.* == .literal and
                resolved.literal.kind == .Number and
                (resolved.literal.value.value() catch null) == value)
            {
                if (self.nodes.items.len >= std.math.maxInt(ExpressionId))
                    return error.ExpressionCapacity;
                const materialized_id: ExpressionId = @intCast(self.nodes.items.len);
                try self.nodes.append(self.allocator, .{
                    .kind = .borrowed,
                    .source = resolved,
                });
                return materialized_id;
            }
        }
        return self.makeConstant(value, debug_data);
    }

    pub fn makeOperation(
        self: *ExpressionGraph,
        instruction: Instruction,
        arguments: []const ExpressionId,
        _: @import("../../liblangutil/debug_data.zig").DebugData,
    ) !ExpressionId {
        for (self.nodes.items, 0..) |node, index|
            if (node.kind == .operation and node.instruction == instruction and
                std.mem.eql(ExpressionId, node.arguments, arguments)) return @intCast(index);
        if (self.nodes.items.len >= std.math.maxInt(ExpressionId))
            return error.ExpressionCapacity;
        const owned_arguments = try self.allocator.dupe(ExpressionId, arguments);
        errdefer self.allocator.free(owned_arguments);
        const id: ExpressionId = @intCast(self.nodes.items.len);
        try self.nodes.append(self.allocator, .{
            .kind = .operation,
            .instruction = instruction,
            .arguments = owned_arguments,
            .owns_arguments = true,
        });
        return id;
    }

    fn toExpression(self: *ExpressionGraph, id: ExpressionId) anyerror!AST.Expression {
        const node = self.getNode(id) orelse return error.InvalidExpressionID;
        return switch (node.kind) {
            .borrowed => blk: {
                var copier = ASTCopierModule.ASTCopier.init(self.allocator);
                break :blk try copier.translateExpression(node.source.?);
            },
            .constant => blk: {
                const hint = try Numeric.formatNumberU256Alloc(self.allocator, node.constant);
                defer self.allocator.free(hint);
                break :blk .{ .literal = .{
                    .debug_data = self.root_debug_data,
                    .kind = .Number,
                    .value = try AST.LiteralValue.initNumeric(self.allocator, node.constant, hint),
                } };
            },
            .operation => blk: {
                const info = InstructionModule.instructionInfo(
                    node.instruction,
                    self.evm_dialect.evmVersion(),
                );
                const lowercase_name = try std.ascii.allocLowerString(self.allocator, info.name);
                defer self.allocator.free(lowercase_name);
                const handle = self.evm_dialect.findBuiltin(lowercase_name) orelse
                    return error.MissingInstructionBuiltin;
                var call: AST.FunctionCall = .{
                    .debug_data = self.root_debug_data,
                    .function_name = .{ .builtin = .{
                        .debug_data = self.root_debug_data,
                        .handle = handle,
                    } },
                };
                errdefer call.deinit(self.allocator);
                for (node.arguments) |argument_id| {
                    var argument = try self.toExpression(argument_id);
                    errdefer argument.deinit(self.allocator);
                    try call.arguments.append(self.allocator, argument);
                }
                break :blk .{ .function_call = call };
            },
        };
    }

    fn resolvedExpression(
        self: *const ExpressionGraph,
        expression: *const AST.Expression,
    ) anyerror!*const AST.Expression {
        const identifier = switch (expression.*) {
            .identifier => |*value| value,
            .literal, .function_call => return expression,
        };
        const assigned = try self.ssa_values.get(identifier.name) orelse return expression;
        return assigned.value orelse expression;
    }

    fn getNode(self: *const ExpressionGraph, id: ExpressionId) ?*const Node {
        if (id >= self.nodes.items.len) return null;
        return &self.nodes.items[id];
    }
};

fn borrowedEqual(left: *const AST.Expression, right: *const AST.Expression) bool {
    if (@intFromEnum(left.*) != @intFromEnum(right.*)) return false;
    return switch (left.*) {
        .identifier => |identifier| identifier.name.eql(right.identifier.name),
        .literal => |*literal| literal.value.eql(&right.literal.value),
        .function_call => false,
    };
}

test "Yul simplification rules preserve identifier identity while resolving SSA constants" {
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = EVMDialectModule.EVMDialect;
    const YulString = @import("../yul_string.zig").YulString;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    const add = dialect.findBuiltin("add").?;
    const x = try YulString.init("x");
    var zero: AST.Expression = .{ .literal = .{
        .kind = .Number,
        .value = try AST.LiteralValue.initNumeric(allocator, 0, "0"),
    } };
    defer zero.deinit(allocator);
    var expression: AST.Expression = .{ .function_call = .{
        .function_name = .{ .builtin = .{ .handle = add } },
    } };
    defer expression.deinit(allocator);
    try expression.function_call.arguments.append(allocator, .{ .identifier = .{ .name = x } });
    var copier = ASTCopierModule.ASTCopier.init(allocator);
    try expression.function_call.arguments.append(allocator, try copier.translateExpression(&zero));
    const replacement = (try SimplificationRules.findFirstMatch(
        allocator,
        &expression,
        dialect.dialect(),
        .{},
    )).?;
    var owned_replacement = replacement;
    defer owned_replacement.deinit(allocator);
    try std.testing.expect(owned_replacement == .identifier);
    try std.testing.expect(owned_replacement.identifier.name.eql(x));
}
