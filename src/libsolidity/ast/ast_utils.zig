// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared AST queries translated from `ASTUtils.cpp`.

const std = @import("std");
const AST = @import("ast.zig");
const ASTAnnotations = @import("ast_annotations.zig");
const ASTImplementation = @import("ast.zig");
const Types = @import("types.zig");
const TypeBehavior = @import("types.zig");
const TypeProviderModule = @import("type_provider.zig");
const ConstantEvaluator = @import("../analysis/constant_evaluator.zig");

pub const QueryError = ConstantEvaluator.EvaluateError ||
    TypeBehavior.QueryError ||
    error{InvalidAst};

pub fn locateInnermostASTNode(
    allocator: std.mem.Allocator,
    offset_in_file: i32,
    source_unit: *const AST.Node,
) QueryError!?*const AST.Node {
    if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
    var result: ?*const AST.Node = null;
    try locateRecursive(allocator, offset_in_file, source_unit, &result, 0);
    return result;
}

fn locateRecursive(
    allocator: std.mem.Allocator,
    offset: i32,
    node: *const AST.Node,
    result: *?*const AST.Node,
    depth: usize,
) QueryError!void {
    if (depth >= 4096) return error.InvalidAst;
    if (!node.location.containsOffset(offset)) return;
    result.* = node;
    var children: std.ArrayList(*const AST.Node) = .empty;
    defer children.deinit(allocator);
    try ASTImplementation.appendChildren(allocator, &children, node);
    for (children.items) |child|
        try locateRecursive(allocator, offset, child, result, depth + 1);
}

pub fn isConstantVariableRecursive(
    allocator: std.mem.Allocator,
    variable: *const AST.Node,
) QueryError!bool {
    if (!isConstantVariable(variable)) return error.InvalidAst;
    var active: std.AutoHashMap(*const AST.Node, void) = .init(allocator);
    defer active.deinit();
    return constantCycle(variable, &active, 0);
}

fn constantCycle(
    variable: *const AST.Node,
    active: *std.AutoHashMap(*const AST.Node, void),
    depth: usize,
) QueryError!bool {
    if (depth >= 256) return error.InvalidAst;
    if (active.contains(variable)) return true;
    try active.put(variable, {});
    defer _ = active.remove(variable);
    const initializer = variable.payload.variable_declaration.value orelse return false;
    const referenced = ASTImplementation.referencedDeclaration(initializer) orelse return false;
    if (!isConstantVariable(referenced)) return false;
    return constantCycle(referenced, active, depth + 1);
}

pub fn rootConstVariableDeclaration(
    allocator: std.mem.Allocator,
    variable: *const AST.Node,
) QueryError!?*const AST.Node {
    if (!isConstantVariable(variable) or
        try isConstantVariableRecursive(allocator, variable)) return error.InvalidAst;
    var root = variable;
    while (true) {
        const initializer = root.payload.variable_declaration.value orelse return error.InvalidAst;
        if (initializer.nodeKind() != .identifier) return root;
        const referenced = ASTImplementation.referencedDeclaration(initializer) orelse return null;
        if (!isConstantVariable(referenced)) return null;
        root = referenced;
    }
}

pub fn resolveOuterUnaryTuples(expression: ?*const AST.Node) ?*const AST.Node {
    var result = expression;
    while (result) |node| switch (node.payload) {
        .tuple_expression => |tuple| {
            if (tuple.components.len != 1) return result;
            result = tuple.components[0];
        },
        else => return result,
    };
    return null;
}

pub fn expressionType(expression: *const AST.Node) QueryError!*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(expression) orelse return error.InvalidAst;
    const common = switch (annotation.*) {
        .expression => |*value| value,
        .identifier => |*value| &value.expression,
        .member_access => |*value| &value.expression,
        .operation => |*value| &value.expression,
        .binary_operation => |*value| &value.operation.expression,
        .function_call => |*value| &value.expression,
        else => return error.InvalidAst,
    };
    return common.type_ref orelse error.InvalidAst;
}

pub fn variableType(variable: *const AST.Node) QueryError!*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(variable) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .variable_declaration => |value| value.type_ref orelse error.InvalidAst,
        else => error.InvalidAst,
    };
}

pub fn contractStorageSizeUpperBound(
    contract: *const AST.Node,
    location: Types.DataLocation,
) QueryError!u256 {
    return TypeBehavior.contractStorageSizeUpperBound(contract, location);
}

pub fn layoutBaseForInheritanceHierarchy(
    contract: *const AST.Node,
    location: Types.DataLocation,
) QueryError!u256 {
    return TypeBehavior.layoutBaseForInheritanceHierarchy(contract, location);
}

pub fn erc7201CompileTimeValue(
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    function_call: *const AST.Node,
) QueryError!?u256 {
    if (function_call.nodeKind() != .function_call) return error.InvalidAst;
    const declaration = ASTImplementation.referencedDeclaration(
        function_call.payload.function_call.expression,
    ) orelse return error.InvalidAst;
    if (declaration.nodeKind() != .magic_variable_declaration) return error.InvalidAst;
    const erased = declaration.payload.magic_variable_declaration.type_ref orelse
        return error.InvalidAst;
    const function_type: *const Types.Type = @ptrCast(@alignCast(erased));
    if (function_type.asFunction() == null or
        function_type.asFunction().?.kind != .ERC7201) return error.InvalidAst;
    var evaluated = try ConstantEvaluator.tryEvaluate(
        allocator,
        type_provider,
        function_call,
    );
    defer evaluated.deinit();
    const rational = evaluated.rationalValue() orelse return null;
    if (rational.denominator.compareUnsigned(1) != .eq or
        rational.numerator.isNegative() or
        rational.numerator.bitLength() > 256) return error.InvalidAst;
    return rational.numerator.toU256Wrapping();
}

fn isConstantVariable(node: *const AST.Node) bool {
    return node.nodeKind() == .variable_declaration and
        node.payload.variable_declaration.mutability == .Constant;
}
