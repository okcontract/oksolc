// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Compile-time constant evaluation translated from `ConstantEvaluator.cpp`.
//!
//! Values own their arbitrary-precision integers. The evaluator owns one
//! cached value per visited AST node and returns clones to callers.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const TokenModule = @import("../../liblangutil/token.zig");
const Keccak256 = @import("../../libsolutil/keccak256.zig");

pub const EvaluateError = TypeBehavior.BehaviorError ||
    Diagnostics.ReportError ||
    error{InvalidAst};

pub const RationalValue = TypeBehavior.RationalComputation;

pub const Value = union(enum) {
    unknown,
    rational: RationalValue,
    string: []const u8,

    pub fn deinit(self: *Value) void {
        switch (self.*) {
            .rational => |*value| value.deinit(),
            else => {},
        }
        self.* = undefined;
    }

    pub fn clone(self: *const Value) Value {
        return switch (self.*) {
            .unknown => .unknown,
            .rational => |*value| .{ .rational = value.clone() },
            .string => |value| .{ .string = value },
        };
    }
};

pub const TypedValue = struct {
    type_ref: ?*const Types.Type = null,
    value: Value = .unknown,

    pub fn deinit(self: *TypedValue) void {
        self.value.deinit();
        self.* = undefined;
    }

    pub fn clone(self: *const TypedValue) TypedValue {
        return .{
            .type_ref = self.type_ref,
            .value = self.value.clone(),
        };
    }

    pub fn rationalValue(self: *const TypedValue) ?*const RationalValue {
        return switch (self.value) {
            .rational => |*value| value,
            else => null,
        };
    }
};

pub const ConstantEvaluator = struct {
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    type_provider: *TypeProviderModule.TypeProvider,
    depth: usize = 0,
    values: std.AutoHashMap(*const AST.Node, TypedValue),

    pub fn init(
        allocator: std.mem.Allocator,
        reporter: *Diagnostics.ErrorReporter,
        type_provider: *TypeProviderModule.TypeProvider,
    ) ConstantEvaluator {
        return .{
            .allocator = allocator,
            .reporter = reporter,
            .type_provider = type_provider,
            .values = std.AutoHashMap(*const AST.Node, TypedValue).init(allocator),
        };
    }

    pub fn deinit(self: *ConstantEvaluator) void {
        var iterator = self.values.valueIterator();
        while (iterator.next()) |value| value.deinit();
        self.values.deinit();
        self.* = undefined;
    }

    pub fn evaluateNode(
        self: *ConstantEvaluator,
        node: *const AST.Node,
    ) EvaluateError!TypedValue {
        if (self.values.getPtr(node)) |cached| return cached.clone();

        var value = try self.compute(node);
        errdefer value.deinit();
        try self.values.put(node, value);
        return value.clone();
    }

    fn compute(
        self: *ConstantEvaluator,
        node: *const AST.Node,
    ) EvaluateError!TypedValue {
        return switch (node.payload) {
            .variable_declaration => self.evaluateVariable(node),
            .literal => |literal| self.evaluateLiteral(literal),
            .unary_operation => |operation| self.evaluateUnary(node, operation),
            .binary_operation => |operation| self.evaluateBinary(node, operation),
            .identifier => self.evaluateIdentifier(node),
            .tuple_expression => |tuple| self.evaluateTuple(tuple),
            .function_call => |call| self.evaluateFunctionCall(node, call),
            else => .{},
        };
    }

    fn evaluateVariable(
        self: *ConstantEvaluator,
        node: *const AST.Node,
    ) EvaluateError!TypedValue {
        const declaration = node.payload.variable_declaration;
        if (declaration.mutability != .Constant) return .{};
        const initializer = declaration.value orelse return .{};
        const annotation = ASTAnnotations.annotationConst(node) orelse return .{};
        const target_type = switch (annotation.*) {
            .variable_declaration => |value| value.type_ref orelse return .{},
            else => return error.InvalidAst,
        };

        self.depth += 1;
        defer self.depth -= 1;
        if (self.depth > 32)
            try self.reporter.fatal(
                errorId(5210),
                .TypeError,
                node.location,
                null,
                "Cyclic constant definition (or maximum recursion depth exhausted).",
            );

        var value = try self.evaluateNode(initializer);
        defer value.deinit();
        return self.convertType(&value, target_type);
    }

    fn evaluateLiteral(
        self: *ConstantEvaluator,
        literal: AST.Literal,
    ) EvaluateError!TypedValue {
        const literal_type = (try self.type_provider.forLiteral(literal)) orelse return .{};
        return constantToTypedValue(literal_type);
    }

    fn evaluateUnary(
        self: *ConstantEvaluator,
        node: *const AST.Node,
        operation: AST.UnaryOperation,
    ) EvaluateError!TypedValue {
        var input = try self.evaluateNode(operation.sub_expression);
        defer input.deinit();
        const input_type = input.type_ref orelse return .{};
        const result_type = (try TypeBehavior.unaryOperatorResult(
            self.type_provider,
            operation.operator,
            input_type,
        )) orelse return .{};

        var converted_input = try self.convertType(&input, result_type);
        defer converted_input.deinit();
        const rational = converted_input.rationalValue() orelse return .{};
        var result = evaluateUnaryOperator(operation.operator, rational) orelse return .{};
        defer result.deinit();
        const untyped_result = TypedValue{ .value = .{ .rational = result.clone() } };
        var mutable_result = untyped_result;
        defer mutable_result.deinit();
        const converted_result = try self.convertType(&mutable_result, result_type);
        if (converted_result.type_ref == null) {
            var discarded = converted_result;
            discarded.deinit();
            try self.reporter.fatal(
                errorId(3667),
                .TypeError,
                node.location,
                null,
                "Arithmetic error when computing constant value.",
            );
        }
        return converted_result;
    }

    fn evaluateBinary(
        self: *ConstantEvaluator,
        node: *const AST.Node,
        operation: AST.BinaryOperation,
    ) EvaluateError!TypedValue {
        var left = try self.evaluateNode(operation.left);
        defer left.deinit();
        var right = try self.evaluateNode(operation.right);
        defer right.deinit();
        const left_type = left.type_ref orelse return .{};
        const right_type = right.type_ref orelse return .{};
        if (TokenModule.isCompareOp(operation.operator)) return .{};

        const result_type = (try TypeBehavior.binaryOperatorResult(
            self.type_provider,
            operation.operator,
            left_type,
            right_type,
        )) orelse {
            const left_name = try TypeBehavior.toStringAlloc(
                self.allocator,
                left_type,
                false,
            );
            defer self.allocator.free(left_name);
            const right_name = try TypeBehavior.toStringAlloc(
                self.allocator,
                right_type,
                false,
            );
            defer self.allocator.free(right_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Operator {s} not compatible with types {s} and {s}",
                .{
                    TokenModule.toString(operation.operator) orelse
                        TokenModule.friendlyName(operation.operator),
                    left_name,
                    right_name,
                },
            );
            defer self.allocator.free(message);
            try self.reporter.fatal(
                errorId(6020),
                .TypeError,
                node.location,
                null,
                message,
            );
            unreachable;
        };

        var converted_left = try self.convertType(&left, result_type);
        defer converted_left.deinit();
        var converted_right = try self.convertType(&right, result_type);
        defer converted_right.deinit();
        const left_rational = converted_left.rationalValue() orelse return .{};
        const right_rational = converted_right.rationalValue() orelse return .{};
        var raw_result = (try TypeBehavior.rationalBinaryComputation(
            operation.operator,
            rationalType(left_rational),
            rationalType(right_rational),
        )) orelse return .{};
        defer raw_result.deinit();
        try normalize(&raw_result);

        var untyped_result = TypedValue{
            .value = .{ .rational = raw_result.clone() },
        };
        defer untyped_result.deinit();
        const converted_result = try self.convertType(&untyped_result, result_type);
        if (converted_result.type_ref == null) {
            var discarded = converted_result;
            discarded.deinit();
            try self.reporter.fatal(
                errorId(2643),
                .TypeError,
                node.location,
                null,
                "Arithmetic error when computing constant value.",
            );
        }
        return converted_result;
    }

    fn evaluateIdentifier(
        self: *ConstantEvaluator,
        node: *const AST.Node,
    ) EvaluateError!TypedValue {
        const declaration = ASTImplementation.referencedDeclaration(node) orelse return .{};
        if (declaration.nodeKind() != .variable_declaration or
            declaration.payload.variable_declaration.mutability != .Constant) return .{};
        return self.evaluateNode(declaration);
    }

    fn evaluateTuple(
        self: *ConstantEvaluator,
        tuple: AST.TupleExpression,
    ) EvaluateError!TypedValue {
        if (tuple.is_inline_array or tuple.components.len != 1) return .{};
        return self.evaluateNode(tuple.components[0] orelse return .{});
    }

    fn evaluateFunctionCall(
        self: *ConstantEvaluator,
        node: *const AST.Node,
        call: AST.FunctionCall,
    ) EvaluateError!TypedValue {
        const declaration = ASTImplementation.referencedDeclaration(call.expression) orelse
            return .{};
        if (declaration.nodeKind() != .magic_variable_declaration) return .{};
        const erased_type = declaration.payload.magic_variable_declaration.type_ref orelse
            return error.InvalidAst;
        const function_type_ref: *const Types.Type = @ptrCast(@alignCast(erased_type));
        const function_type = function_type_ref.asFunction() orelse return error.InvalidAst;
        if (function_type.kind != .ERC7201) return .{};

        if (call.arguments.len != 1) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "erc7201 function expects 1 parameter, but {d} were given.",
                .{call.arguments.len},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(8248), node.location, message);
            return .{};
        }
        var argument = try self.evaluateNode(call.arguments[0]);
        defer argument.deinit();
        const string_value = switch (argument.value) {
            .string => |value| value,
            else => {
                try self.reporter.typeError(
                    errorId(9796),
                    call.arguments[0].location,
                    "Invalid argument type for erc7201 function. Expected literal or constant string.",
                );
                return .{};
            },
        };

        const inner = Keccak256.keccak256(string_value);
        const encoded = Keccak256.H256.fromInteger(inner.toInteger() -% 1);
        var outer = Keccak256.keccak256(encoded.bytes());
        outer.at(31).* = 0;
        if (function_type.return_parameter_types.len != 1) return error.InvalidAst;
        return .{
            .type_ref = function_type.return_parameter_types[0],
            .value = .{ .rational = .{
                .numerator = Types.BigInt.fromU256(outer.toInteger()),
                .denominator = Types.BigInt.initUnsigned(1),
            } },
        };
    }

    fn convertType(
        self: *ConstantEvaluator,
        input: *const TypedValue,
        target_type: *const Types.Type,
    ) EvaluateError!TypedValue {
        return switch (input.value) {
            .unknown => .{},
            .string => |value| switch (target_type.category()) {
                .StringLiteral, .Array => .{
                    .type_ref = target_type,
                    .value = .{ .string = value },
                },
                else => .{},
            },
            .rational => |*value| self.convertRational(value, target_type),
        };
    }

    fn convertRational(
        self: *ConstantEvaluator,
        input: *const RationalValue,
        target_type: *const Types.Type,
    ) EvaluateError!TypedValue {
        var value = input.clone();
        errdefer value.deinit();
        try normalize(&value);
        if (target_type.category() == .RationalNumber) {
            const rational_type = try self.type_provider.rationalNumber(
                &value.numerator,
                &value.denominator,
                null,
            );
            return .{
                .type_ref = rational_type,
                .value = .{ .rational = value },
            };
        }
        const integer = target_type.asInteger() orelse return .{};
        if (!rationalFitsInteger(&value, integer.*)) return .{};
        var quotient = Types.BigInt.quotient( // zlinter-disable-current-line no_swallow_error - nonzero rational denominator is an AST invariant
            &value.numerator,
            &value.denominator,
        ) catch unreachable;
        value.deinit();
        return .{
            .type_ref = target_type,
            .value = .{ .rational = .{
                .numerator = quotient.take(),
                .denominator = Types.BigInt.initUnsigned(1),
            } },
        };
    }
};

pub fn evaluate(
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    type_provider: *TypeProviderModule.TypeProvider,
    expression: *const AST.Node,
) EvaluateError!TypedValue {
    var evaluator = ConstantEvaluator.init(allocator, reporter, type_provider);
    defer evaluator.deinit();
    return evaluator.evaluateNode(expression);
}

/// Evaluates without exposing diagnostics, matching upstream's
/// `ConstantEvaluator::tryEvaluate` fatal-error swallowing behavior.
pub fn tryEvaluate(
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    expression: *const AST.Node,
) EvaluateError!TypedValue {
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    return evaluate(allocator, &reporter, type_provider, expression) catch |err| switch (err) {
        error.FatalDiagnostic => .{},
        else => |other| other,
    };
}

pub fn evaluateUnaryOperator(
    operator: AST.Token,
    input: *const RationalValue,
) ?RationalValue {
    return switch (operator) {
        .BitNot => if (input.denominator.compareUnsigned(1) == .eq)
            .{
                .numerator = input.numerator.bitNot(),
                .denominator = Types.BigInt.initUnsigned(1),
            }
        else
            null,
        .Sub => .{
            .numerator = input.numerator.negate(),
            .denominator = input.denominator.clone(),
        },
        else => null,
    };
}

pub fn evaluateBinaryOperator(
    operator: AST.Token,
    left: *const RationalValue,
    right: *const RationalValue,
) (TypeBehavior.BehaviorError || error{InvalidAst})!?RationalValue {
    var result = (try TypeBehavior.rationalBinaryComputation(
        operator,
        rationalType(left),
        rationalType(right),
    )) orelse return null;
    errdefer result.deinit();
    try normalize(&result);
    return result;
}

fn constantToTypedValue(type_ref: *const Types.Type) TypedValue {
    return switch (type_ref.payload) {
        .RationalNumber => |value| .{
            .type_ref = type_ref,
            .value = .{ .rational = .{
                .numerator = value.numerator.clone(),
                .denominator = value.denominator.clone(),
            } },
        },
        .StringLiteral => |value| .{
            .type_ref = type_ref,
            .value = .{ .string = value.value },
        },
        else => .{},
    };
}

fn rationalType(value: *const RationalValue) Types.RationalNumberType {
    return .{
        .numerator = &value.numerator,
        .denominator = &value.denominator,
        .compatible_bytes_type = null,
    };
}

fn normalize(value: *RationalValue) error{InvalidAst}!void {
    if (value.denominator.isZero()) return error.InvalidAst;
    if (value.denominator.isNegative()) {
        var numerator = value.numerator.negate();
        var denominator = value.denominator.negate();
        value.numerator.deinit();
        value.denominator.deinit();
        value.numerator = numerator.take();
        value.denominator = denominator.take();
    }
    var divisor = Types.BigInt.gcd(&value.numerator, &value.denominator);
    defer divisor.deinit();
    if (divisor.compareUnsigned(1) == .eq) return;
    var numerator = Types.BigInt.quotient(
        &value.numerator,
        &divisor,
    ) catch return error.InvalidAst;
    var denominator = Types.BigInt.quotient(
        &value.denominator,
        &divisor,
    ) catch return error.InvalidAst;
    value.numerator.deinit();
    value.denominator.deinit();
    value.numerator = numerator.take();
    value.denominator = denominator.take();
}

fn rationalFitsInteger(
    value: *const RationalValue,
    integer: Types.IntegerType,
) bool {
    var minimum = TypeBehavior.integerMinValue(integer);
    defer minimum.deinit();
    var maximum = TypeBehavior.integerMaxValue(integer);
    defer maximum.deinit();
    var scaled_minimum = Types.BigInt.mul(&minimum, &value.denominator);
    defer scaled_minimum.deinit();
    var scaled_maximum = Types.BigInt.mul(&maximum, &value.denominator);
    defer scaled_maximum.deinit();
    return value.numerator.compare(&scaled_minimum) != .lt and
        value.numerator.compare(&scaled_maximum) != .gt;
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}

test "constant arithmetic matches upstream fractional modulo and signed powers" {
    var five_halves = RationalValue{
        .numerator = Types.BigInt.initUnsigned(5),
        .denominator = Types.BigInt.initUnsigned(2),
    };
    defer five_halves.deinit();
    var three_halves = RationalValue{
        .numerator = Types.BigInt.initUnsigned(3),
        .denominator = Types.BigInt.initUnsigned(2),
    };
    defer three_halves.deinit();
    var remainder = (try evaluateBinaryOperator(.Mod, &five_halves, &three_halves)).?;
    defer remainder.deinit();
    try std.testing.expectEqual(std.math.Order.eq, remainder.numerator.compareUnsigned(1));
    try std.testing.expectEqual(std.math.Order.eq, remainder.denominator.compareUnsigned(1));

    var two = RationalValue{
        .numerator = Types.BigInt.initUnsigned(2),
        .denominator = Types.BigInt.initUnsigned(1),
    };
    defer two.deinit();
    var minus_three = RationalValue{
        .numerator = Types.BigInt.initSigned(-3),
        .denominator = Types.BigInt.initUnsigned(1),
    };
    defer minus_three.deinit();
    var inverse_power = (try evaluateBinaryOperator(.Exp, &two, &minus_three)).?;
    defer inverse_power.deinit();
    try std.testing.expectEqual(std.math.Order.eq, inverse_power.numerator.compareUnsigned(1));
    try std.testing.expectEqual(std.math.Order.eq, inverse_power.denominator.compareUnsigned(8));
}
