// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Behavior of the closed Solidity type graph translated from `Types.cpp`.
//!
//! Formatting routines allocate their result explicitly.  Queries never
//! retain allocator-backed temporaries, and structural equality is safe for
//! provider-owned stable pointers.

const std = @import("std");
const Types = @This();
const TypeProviderModule = @import("type_provider.zig");
const AST = @import("ast.zig");
const ASTAnnotations = @import("ast_annotations.zig");
const CompatibilityIdResolver = @import("compatibility_id_resolver.zig").CompatibilityIdResolver;
const Enums = @import("ast_enums.zig");
const TokenModule = @import("../../liblangutil/token.zig");
const Keccak256 = @import("../../libsolutil/keccak256.zig");
const FunctionSelector = @import("../../libsolutil/function_selector.zig");
const Numeric = @import("../../libsolutil/numeric.zig");
const UTF8 = @import("../../libsolutil/utf8.zig");
const CompatibilityIds = @import("../../incremental/compatibility_ids.zig");

pub const QueryError = std.mem.Allocator.Error || error{
    InvalidType,
    InvalidIdentifier,
    DynamicEncoding,
    NotDynamicallyEncoded,
    NotStorable,
    Overflow,
    UnsupportedTransientReference,
};

pub const BehaviorError = QueryError || TypeProviderModule.ProviderError;

fn nodeScope(node: *const AST.Node) ?*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return (ASTAnnotations.scopableConst(annotation) orelse return null).scope;
}

pub fn equals(left: *const Types.Type, right: *const Types.Type) bool {
    if (left.category() != right.category()) return false;
    return switch (left.payload) {
        .Address => |value| value.state_mutability == right.payload.Address.state_mutability,
        .Integer => |value| value.bits == right.payload.Integer.bits and
            value.modifier == right.payload.Integer.modifier,
        .RationalNumber => |value| blk: {
            const other = right.payload.RationalNumber;
            if (value.numerator.compare(other.numerator) != .eq or
                value.denominator.compare(other.denominator) != .eq)
                break :blk false;
            break :blk optionalTypeEquals(
                value.compatible_bytes_type,
                other.compatible_bytes_type,
            );
        },
        .StringLiteral => |value| std.mem.eql(
            u8,
            value.value,
            right.payload.StringLiteral.value,
        ),
        .Bool => true,
        .FixedPoint => |value| {
            const other = right.payload.FixedPoint;
            return value.total_bits == other.total_bits and
                value.fractional_digits == other.fractional_digits and
                value.modifier == other.modifier;
        },
        .Array => |value| arrayEquals(value, right.payload.Array),
        .ArraySlice => |value| equals(
            value.array_type,
            right.payload.ArraySlice.array_type,
        ),
        .FixedBytes => |value| value.bytes == right.payload.FixedBytes.bytes,
        .Contract => |value| value.declaration == right.payload.Contract.declaration and
            value.is_super == right.payload.Contract.is_super,
        .Struct => |value| value.declaration == right.payload.Struct.declaration and
            referenceEquals(value.reference, right.payload.Struct.reference),
        .Function => |value| functionEquals(value, right.payload.Function, false),
        .Enum => |value| value.declaration == right.payload.Enum.declaration,
        .UserDefinedValueType => |value| value.declaration ==
            right.payload.UserDefinedValueType.declaration,
        .Tuple => |value| optionalTypePointerSlicesEqual(
            value.components,
            right.payload.Tuple.components,
        ),
        .Mapping => |value| equals(value.key_type, right.payload.Mapping.key_type) and
            equals(value.value_type, right.payload.Mapping.value_type),
        .TypeType => |value| equals(value.actual_type, right.payload.TypeType.actual_type),
        .Modifier => |value| typeSlicesEqual(
            value.parameter_types,
            right.payload.Modifier.parameter_types,
        ),
        // Upstream compares only MagicType::Kind, including MetaType.
        .Magic => |value| value.kind == right.payload.Magic.kind,
        .Module => |value| value.source_unit == right.payload.Module.source_unit,
        .InaccessibleDynamic => true,
    };
}

fn optionalTypeEquals(left: ?*const Types.Type, right: ?*const Types.Type) bool {
    if (left == null or right == null) return left == right;
    return equals(left.?, right.?);
}

fn typeSlicesEqual(
    left: []const *const Types.Type,
    right: []const *const Types.Type,
) bool {
    if (left.len != right.len) return false;
    for (left, right) |a, b| if (!equals(a, b)) return false;
    return true;
}

fn referenceEquals(left: Types.ReferenceData, right: Types.ReferenceData) bool {
    return left.location == right.location and left.isPointer() == right.isPointer();
}

fn arrayEquals(left: Types.ArrayType, right: Types.ArrayType) bool {
    return referenceEquals(left.reference, right.reference) and
        left.kind == right.kind and
        optionalU256Equal(left.length, right.length) and
        equals(left.base_type, right.base_type);
}

fn optionalU256Equal(left: ?u256, right: ?u256) bool {
    if (left == null or right == null) return left == right;
    return left.? == right.?;
}

fn functionEquals(
    left: Types.FunctionType,
    right: Types.FunctionType,
    exclude_state_mutability: bool,
) bool {
    if (left.kind != right.kind or
        !typeSlicesEqual(left.parameter_types, right.parameter_types) or
        !typeSlicesEqual(left.return_parameter_types, right.return_parameter_types) or
        left.options.gas_set != right.options.gas_set or
        left.options.value_set != right.options.value_set or
        left.options.salt_set != right.options.salt_set or
        left.options.has_bound_first_argument != right.options.has_bound_first_argument)
        return false;
    return exclude_state_mutability or left.state_mutability == right.state_mutability;
}

fn optionalTypePointerSlicesEqual(
    left: []const ?*const Types.Type,
    right: []const ?*const Types.Type,
) bool {
    if (left.len != right.len) return false;
    for (left, right) |a, b| if (a != b) return false;
    return true;
}

pub fn isImplicitlyConvertibleTo(
    source: *const Types.Type,
    target: *const Types.Type,
) bool {
    return switch (source.payload) {
        .Address => |value| blk: {
            const other = target.asAddress() orelse break :blk false;
            break :blk @intFromEnum(other.state_mutability) <=
                @intFromEnum(value.state_mutability);
        },
        .Integer => |value| blk: {
            if (target.asInteger()) |other|
                break :blk value.modifier == other.modifier and value.bits <= other.bits;
            if (target.asFixedPoint()) |other|
                break :blk integerFitsFixedPoint(value, other.*);
            break :blk false;
        },
        .RationalNumber => |value| rationalImplicit(value, target),
        .FixedPoint => |value| blk: {
            const other = target.asFixedPoint() orelse break :blk false;
            if (other.fractional_digits < value.fractional_digits or
                other.total_bits < value.total_bits) break :blk false;
            var source_minimum = fixedPointMinIntegerValue(value);
            defer source_minimum.deinit();
            var source_maximum = fixedPointMaxIntegerValue(value);
            defer source_maximum.deinit();
            var target_minimum = fixedPointMinIntegerValue(other.*);
            defer target_minimum.deinit();
            var target_maximum = fixedPointMaxIntegerValue(other.*);
            defer target_maximum.deinit();
            break :blk target_maximum.compare(&source_maximum) != .lt and
                target_minimum.compare(&source_minimum) != .gt;
        },
        .FixedBytes => |value| blk: {
            const other = target.asFixedBytes() orelse break :blk false;
            break :blk value.bytes <= other.bytes;
        },
        .StringLiteral => |value| stringLiteralImplicit(value.value, target),
        .Array => |value| blk: {
            const other = target.asArray() orelse break :blk false;
            break :blk arrayImplicit(value, other.*);
        },
        .ArraySlice => |value| blk: {
            if (target.category() == .ArraySlice)
                break :blk equals(value.array_type, target.payload.ArraySlice.array_type);
            const array = value.array_type.asArray() orelse break :blk false;
            break :blk array.reference.location == .CallData and
                array.isDynamicallySized() and
                isImplicitlyConvertibleTo(value.array_type, target);
        },
        .Struct => |value| blk: {
            if (target.category() != .Struct) break :blk false;
            const other = target.payload.Struct;
            if (value.declaration != other.declaration) break :blk false;
            break :blk referenceLocationConvertible(value.reference, other.reference);
        },
        .Contract => |value| contractImplicit(value, target),
        .Tuple => |value| tupleImplicit(value, target),
        .Function => |value| functionImplicit(value, target),
        .InaccessibleDynamic => false,
        else => equals(source, target),
    };
}

fn rationalImplicit(
    value: Types.RationalNumberType,
    target: *const Types.Type,
) bool {
    return switch (target.payload) {
        .Integer => |integer| blk: {
            if (value.denominator.compareUnsigned(1) != .eq) break :blk false;
            if (!value.numerator.isNegative())
                break :blk value.numerator.bitLength() <=
                    if (integer.isSigned()) integer.bits - 1 else integer.bits;
            if (!integer.isSigned()) break :blk false;
            var magnitude = value.numerator.absolute();
            defer magnitude.deinit();
            if (magnitude.bitLength() < integer.bits) break :blk true;
            if (magnitude.bitLength() != integer.bits or
                !magnitude.testBit(integer.bits - 1)) break :blk false;
            var index: usize = 0;
            while (index + 1 < integer.bits) : (index += 1)
                if (magnitude.testBit(index)) break :blk false;
            break :blk true;
        },
        .FixedBytes => if (value.numerator.isZero())
            true
        else if (value.compatible_bytes_type) |compatible|
            equals(compatible, target)
        else
            false,
        .FixedPoint => |fixed| blk: {
            if (value.numerator.isNegative() and !fixed.isSigned()) break :blk false;
            if (value.denominator.compareUnsigned(1) == .eq) {
                var minimum = fixedPointMinIntegerValue(fixed);
                defer minimum.deinit();
                var maximum = fixedPointMaxIntegerValue(fixed);
                defer maximum.deinit();
                break :blk value.numerator.compare(&minimum) != .lt and
                    value.numerator.compare(&maximum) != .gt;
            }
            var ten = Types.BigInt.initUnsigned(10);
            defer ten.deinit();
            var scale = ten.pow(fixed.fractional_digits);
            defer scale.deinit();
            var scaled = Types.BigInt.mul(value.numerator, &scale);
            defer scaled.deinit();
            var remainder = Types.BigInt.remainder( // zlinter-disable-current-line no_swallow_error - type construction guarantees a nonzero divisor
                &scaled,
                value.denominator,
            ) catch unreachable;
            defer remainder.deinit();
            if (!remainder.isZero()) break :blk false;
            var shifted = Types.BigInt.quotient( // zlinter-disable-current-line no_swallow_error - type construction guarantees a nonzero divisor
                &scaled,
                value.denominator,
            ) catch unreachable;
            defer shifted.deinit();
            break :blk fitsIntoBits(&shifted, fixed.total_bits, fixed.isSigned());
        },
        else => false,
    };
}

fn fitsIntoBits(value: *const Types.BigInt, bits: u16, signed: bool) bool {
    if (value.isNegative()) {
        if (!signed) return false;
        var minimum = Types.BigInt.initUnsigned(1);
        defer minimum.deinit();
        var shifted = minimum.shiftLeft(bits - 1);
        defer shifted.deinit();
        var negative_minimum = shifted.negate();
        defer negative_minimum.deinit();
        return value.compare(&negative_minimum) != .lt;
    }
    return value.bitLength() <= if (signed) bits - 1 else bits;
}

/// Upstream `IntegerType::minValue()`. The caller owns the returned big integer.
pub fn integerMinValue(integer: Types.IntegerType) Types.BigInt {
    if (!integer.isSigned()) return Types.BigInt.init();
    var one = Types.BigInt.initUnsigned(1);
    defer one.deinit();
    var magnitude = one.shiftLeft(integer.bits - 1);
    defer magnitude.deinit();
    return magnitude.negate();
}

/// Upstream `IntegerType::maxValue()`. The caller owns the returned big integer.
pub fn integerMaxValue(integer: Types.IntegerType) Types.BigInt {
    var one = Types.BigInt.initUnsigned(1);
    defer one.deinit();
    var limit = one.shiftLeft(integer.bits - @intFromBool(integer.isSigned()));
    defer limit.deinit();
    return Types.BigInt.sub(&limit, &one);
}

/// Upstream `IntegerType::min()`, represented in the EVM's unsigned word.
pub fn integerMin(integer: Types.IntegerType) u256 {
    var value = integerMinValue(integer);
    defer value.deinit();
    return value.toU256Wrapping();
}

/// Upstream `IntegerType::max()`, represented in the EVM's unsigned word.
pub fn integerMax(integer: Types.IntegerType) u256 {
    var value = integerMaxValue(integer);
    defer value.deinit();
    return value.toU256Wrapping();
}

/// Upstream `FixedPointType::maxIntegerValue()`. The caller owns the result.
pub fn fixedPointMaxIntegerValue(fixed: Types.FixedPointType) Types.BigInt {
    var one = Types.BigInt.initUnsigned(1);
    defer one.deinit();
    var limit = one.shiftLeft(fixed.total_bits - @intFromBool(fixed.isSigned()));
    defer limit.deinit();
    var maximum = Types.BigInt.sub(&limit, &one);
    defer maximum.deinit();
    var ten = Types.BigInt.initUnsigned(10);
    defer ten.deinit();
    var scale = ten.pow(fixed.fractional_digits);
    defer scale.deinit();
    return Types.BigInt.quotient(&maximum, &scale) catch unreachable; // zlinter-disable-current-line no_swallow_error - type construction guarantees a nonzero divisor
}

/// Upstream `FixedPointType::minIntegerValue()`. The caller owns the result.
pub fn fixedPointMinIntegerValue(fixed: Types.FixedPointType) Types.BigInt {
    if (!fixed.isSigned()) return Types.BigInt.init();
    var one = Types.BigInt.initUnsigned(1);
    defer one.deinit();
    var magnitude = one.shiftLeft(fixed.total_bits - 1);
    defer magnitude.deinit();
    var minimum = magnitude.negate();
    defer minimum.deinit();
    var ten = Types.BigInt.initUnsigned(10);
    defer ten.deinit();
    var scale = ten.pow(fixed.fractional_digits);
    defer scale.deinit();
    return Types.BigInt.quotient(&minimum, &scale) catch unreachable; // zlinter-disable-current-line no_swallow_error - type construction guarantees a nonzero divisor
}

pub fn fixedPointAsIntegerType(
    provider: *TypeProviderModule.TypeProvider,
    fixed: Types.FixedPointType,
) TypeProviderModule.ProviderError!*const Types.Type {
    return provider.integer(
        fixed.total_bits,
        if (fixed.isSigned()) .Signed else .Unsigned,
    );
}

fn integerFitsFixedPoint(integer: Types.IntegerType, fixed: Types.FixedPointType) bool {
    var integer_minimum = integerMinValue(integer);
    defer integer_minimum.deinit();
    var integer_maximum = integerMaxValue(integer);
    defer integer_maximum.deinit();
    var fixed_minimum = fixedPointMinIntegerValue(fixed);
    defer fixed_minimum.deinit();
    var fixed_maximum = fixedPointMaxIntegerValue(fixed);
    defer fixed_maximum.deinit();
    return integer_maximum.compare(&fixed_maximum) != .gt and
        integer_minimum.compare(&fixed_minimum) != .lt;
}

fn stringLiteralImplicit(value: []const u8, target: *const Types.Type) bool {
    if (target.asFixedBytes()) |fixed| return value.len <= fixed.bytes;
    const array = target.asArray() orelse return false;
    if (array.kind == .String) {
        var invalid_position: usize = 0;
        if (!UTF8.validateUTF8(value, &invalid_position)) return false;
    }
    return array.reference.location != .CallData and
        array.isByteArrayOrString() and
        !(array.reference.location == .Storage and array.reference.isPointer());
}

fn referenceLocationConvertible(
    source: Types.ReferenceData,
    target: Types.ReferenceData,
) bool {
    if (target.location == .Storage and source.location != .Storage and target.isPointer())
        return false;
    if (target.location == .CallData and source.location != .CallData) return false;
    return true;
}

fn arrayImplicit(source: Types.ArrayType, target: Types.ArrayType) bool {
    if (source.kind != target.kind) return false;
    if (!referenceLocationConvertible(source.reference, target.reference)) return false;

    if (target.reference.location == .Storage and !target.reference.isPointer()) {
        if (!isImplicitlyConvertibleTo(source.base_type, target.base_type)) return false;
        if (target.length == null) return true;
        return source.length != null and target.length.? >= source.length.?;
    }

    if (!equalsWithReferenceLocation(
        source.base_type,
        target.base_type,
        source.reference.location,
    )) return false;
    return optionalU256Equal(source.length, target.length);
}

fn equalsWithReferenceLocation(
    left: *const Types.Type,
    right: *const Types.Type,
    location: Types.DataLocation,
) bool {
    if (left.category() != right.category()) return false;
    return switch (left.payload) {
        .Array => |array| blk: {
            const other = right.payload.Array;
            break :blk array.kind == other.kind and
                optionalU256Equal(array.length, other.length) and
                equalsWithReferenceLocation(
                    array.base_type,
                    other.base_type,
                    location,
                );
        },
        .Struct => |structure| structure.declaration == right.payload.Struct.declaration,
        else => equals(left, right),
    };
}

fn contractImplicit(source: Types.ContractType, target: *const Types.Type) bool {
    if (source.is_super) return false;
    if (target.category() != .Contract) return false;
    const other = target.payload.Contract;
    if (other.is_super) return false;
    if (source.declaration == other.declaration) return true;

    // Once inheritance analysis has populated the annotation, the upstream
    // rule is identity membership in the linearized base list.
    const annotation = ASTAnnotations.annotationConst(source.declaration) orelse return false;
    const bases = switch (annotation.*) {
        .contract_definition => |entry| entry.linearized_base_contracts,
        else => return false,
    };
    for (bases) |base| if (base == other.declaration) return true;
    return false;
}

fn tupleImplicit(source: Types.TupleType, target: *const Types.Type) bool {
    const other = target.asTuple() orelse return false;
    if (other.components.len == 0) return source.components.len == 0;
    if (source.components.len != other.components.len) return false;
    for (source.components, other.components) |from, to| {
        if (from == null and to != null) return false;
        if (from != null and to != null and !isImplicitlyConvertibleTo(from.?, to.?)) return false;
    }
    return true;
}

fn functionImplicit(source: Types.FunctionType, target: *const Types.Type) bool {
    const other = target.asFunction() orelse return false;
    if (source.options.has_bound_first_argument != other.options.has_bound_first_argument)
        return false;
    if (source.kind != other.kind) return false;
    if (source.kind == .Declaration and source.declaration != other.declaration) return false;
    if (!functionEquals(source, other.*, true)) return false;

    if (source.state_mutability != .Payable and other.state_mutability == .Payable)
        return false;
    if (source.state_mutability == .Payable and other.state_mutability == .NonPayable)
        return true;
    return @intFromEnum(source.state_mutability) <= @intFromEnum(other.state_mutability);
}

pub fn isExplicitlyConvertibleTo(
    source: *const Types.Type,
    target: *const Types.Type,
) bool {
    if (isImplicitlyConvertibleTo(source, target)) return true;
    return switch (source.payload) {
        .Address => |address| blk: {
            if (target.category() == .Address) break :blk true;
            if (target.category() == .Contract) {
                if (address.state_mutability == .Payable) break :blk true;
                break :blk !contractIsPayable(target.payload.Contract.declaration);
            }
            if (address.state_mutability != .NonPayable) break :blk false;
            if (target.asInteger()) |integer|
                break :blk !integer.isSigned() and integer.bits == 160;
            if (target.asFixedBytes()) |fixed| break :blk fixed.bytes == 20;
            break :blk false;
        },
        .RationalNumber => |rational| rationalExplicit(rational, target),
        .Integer => |integer| blk: {
            if (target.asInteger()) |other|
                break :blk integer.bits == other.bits or integer.modifier == other.modifier;
            if (target.asAddress()) |address|
                break :blk address.state_mutability != .Payable and
                    !integer.isSigned() and integer.bits == 160;
            if (target.asFixedBytes()) |fixed|
                break :blk !integer.isSigned() and
                    integer.bits == @as(u16, fixed.bytes) * 8;
            if (target.category() == .Enum) break :blk true;
            if (target.asFixedPoint()) |fixed|
                break :blk integer.isSigned() == fixed.isSigned() and
                    integer.bits == fixed.total_bits;
            break :blk false;
        },
        .FixedBytes => |fixed| blk: {
            if (target.category() == .FixedBytes) break :blk true;
            if (target.asInteger()) |integer|
                break :blk !integer.isSigned() and
                    integer.bits == @as(u16, fixed.bytes) * 8;
            if (target.asAddress()) |address|
                break :blk address.state_mutability != .Payable and fixed.bytes == 20;
            if (target.asFixedPoint()) |point|
                break :blk point.total_bits == @as(u16, fixed.bytes) * 8;
            break :blk false;
        },
        .FixedPoint => target.category() == .FixedPoint or target.category() == .Integer,
        .Array => |array| blk: {
            if (array.kind == .Bytes and target.category() == .FixedBytes) break :blk true;
            const other = target.asArray() orelse break :blk false;
            break :blk array.reference.location == other.reference.location and
                array.isByteArrayOrString() and other.isByteArrayOrString();
        },
        .ArraySlice => |slice| isImplicitlyConvertibleTo(source, target) or
            isExplicitlyConvertibleTo(slice.array_type, target),
        .Contract => |contract| blk: {
            if (contract.is_super) break :blk false;
            if (target.asAddress()) |address|
                break :blk address.state_mutability != .Payable or
                    contractIsPayable(contract.declaration);
            if (target.category() == .Contract)
                break :blk contractImplicit(contract, target);
            break :blk false;
        },
        .Enum => equals(source, target) or
            (target.asInteger() != null and !target.asInteger().?.isSigned()),
        .Function => target.category() == .Function and
            (source.payload.Function.kind == .Declaration) ==
                (target.payload.Function.kind == .Declaration),
        .TypeType => |type_type| blk: {
            const address = target.asAddress() orelse break :blk false;
            if (address.state_mutability != .NonPayable) break :blk false;
            const contract = switch (type_type.actual_type.payload) {
                .Contract => |value| value,
                else => break :blk false,
            };
            break :blk contract.declaration.nodeKind() == .contract_definition and
                contract.declaration.payload.contract_definition.contract_kind == .Library;
        },
        else => false,
    };
}

fn rationalExplicit(
    value: Types.RationalNumberType,
    target: *const Types.Type,
) bool {
    if (target.category() == .FixedBytes or target.category() == .Integer) return false;
    if (target.asAddress()) |address| {
        if (value.numerator.isZero()) return true;
        return address.state_mutability != .Payable and
            !value.numerator.isNegative() and
            value.denominator.compareUnsigned(1) == .eq and
            value.numerator.bitLength() <= 160;
    }
    if (target.category() == .Enum) {
        if (value.numerator.isNegative() or
            value.denominator.compareUnsigned(1) != .eq) return false;
        const declaration = target.payload.Enum.declaration;
        if (declaration.nodeKind() != .enum_definition) return false;
        const count = declaration.payload.enum_definition.members.len;
        return value.numerator.compareUnsigned(count) == .lt;
    }
    const fixed = target.asFixedPoint() orelse return false;
    if (value.denominator.compareUnsigned(1) != .eq)
        return rationalFixedPointShape(value) != null;
    const integer_shape = rationalIntegerShape(value) orelse return false;
    return integer_shape.modifier ==
        (if (fixed.isSigned()) Types.IntegerModifier.Signed else .Unsigned) and
        integer_shape.bits == fixed.total_bits;
}

fn contractIsPayable(declaration: *const AST.Node) bool {
    if (declaration.nodeKind() != .contract_definition) return false;
    const annotation = ASTAnnotations.annotationConst(declaration);
    const annotated_bases = if (annotation) |entry| switch (entry.*) {
        .contract_definition => |value| value.linearized_base_contracts,
        else => &.{},
    } else &.{};
    const contracts = if (annotated_bases.len == 0)
        &.{declaration}
    else
        annotated_bases;
    for (contracts) |contract| {
        if (contract.nodeKind() != .contract_definition) continue;
        for (contract.payload.contract_definition.sub_nodes) |node| {
            if (node.nodeKind() != .function_definition) continue;
            const function = node.payload.function_definition;
            if (function.kind == .Receive or
                (function.kind == .Fallback and function.state_mutability == .Payable))
                return true;
        }
    }
    return false;
}

pub fn isValueType(type_ref: *const Types.Type) bool {
    return switch (type_ref.payload) {
        .Address, .Integer, .Bool, .FixedPoint, .FixedBytes, .Function, .Enum, .UserDefinedValueType, .InaccessibleDynamic => true,
        .Contract => |value| !value.is_super,
        else => false,
    };
}

pub fn nameable(type_ref: *const Types.Type) bool {
    return switch (type_ref.payload) {
        .Address, .Integer, .Bool, .FixedPoint, .Array, .FixedBytes, .Struct, .Enum, .Mapping => true,
        .UserDefinedValueType => |value| nameable(
            value.underlying_type orelse return false,
        ),
        .Contract => |value| !value.is_super,
        .Function => |value| functionNameable(value),
        else => false,
    };
}

pub fn functionNameable(value: Types.FunctionType) bool {
    return (value.kind == .Internal or value.kind == .External) and
        !value.options.has_bound_first_argument and
        !value.options.arbitrary_parameters and
        !value.options.gas_set and
        !value.options.value_set and
        !value.options.salt_set;
}

/// Provider-aware counterpart of upstream `Type::commonType()`. Literal and
/// storage-reference mobility can allocate canonical derivative types, so the
/// compilation's provider is explicit in Zig.
pub fn commonTypeWithProvider(
    provider: *TypeProviderModule.TypeProvider,
    a: ?*const Types.Type,
    b: ?*const Types.Type,
) BehaviorError!?*const Types.Type {
    const left = a orelse return null;
    const right = b orelse return null;
    if (try mobileType(provider, left)) |left_mobile|
        if (isImplicitlyConvertibleTo(right, left_mobile)) return left_mobile;
    if (try mobileType(provider, right)) |right_mobile|
        if (isImplicitlyConvertibleTo(left, right_mobile)) return right_mobile;
    return null;
}

pub fn mobileType(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
) BehaviorError!?*const Types.Type {
    return switch (type_ref.payload) {
        .RationalNumber => |value| if (value.denominator.compareUnsigned(1) == .eq)
            rationalIntegerType(provider, value)
        else
            rationalFixedPointType(provider, value),
        .StringLiteral => provider.stringMemory(),
        .Array, .Struct => try provider.withLocation(type_ref, type_ref.asReference().?.location, true),
        .ArraySlice => |value| blk: {
            const array = value.array_type.asArray() orelse return error.InvalidType;
            if (array.reference.location == .CallData and
                array.isDynamicallySized() and
                !isDynamicallyEncoded(array.base_type))
                break :blk value.array_type;
            break :blk type_ref;
        },
        .Tuple => |value| blk: {
            const components = try provider.backing_allocator.alloc(
                ?*const Types.Type,
                value.components.len,
            );
            defer provider.backing_allocator.free(components);
            for (value.components, 0..) |component, index| {
                components[index] = if (component) |present|
                    try mobileType(provider, present)
                else
                    null;
                if (component != null and components[index] == null) break :blk null;
            }
            break :blk try provider.tuple(components);
        },
        .Function => |value| functionMobileType(provider, value),
        .TypeType, .Magic => null,
        else => type_ref,
    };
}

pub fn rationalIntegerType(
    provider: *TypeProviderModule.TypeProvider,
    value: Types.RationalNumberType,
) BehaviorError!?*const Types.Type {
    const shape = rationalIntegerShape(value) orelse return null;
    return provider.integer(shape.bits, shape.modifier);
}

const RationalIntegerShape = struct {
    bits: u16,
    modifier: Types.IntegerModifier,
};

fn rationalIntegerShape(value: Types.RationalNumberType) ?RationalIntegerShape {
    if (value.denominator.compareUnsigned(1) != .eq) return null;
    var encoded = if (value.numerator.isNegative()) blk: {
        var magnitude = value.numerator.absolute();
        defer magnitude.deinit();
        var one = Types.BigInt.initUnsigned(1);
        defer one.deinit();
        var decremented = Types.BigInt.sub(&magnitude, &one);
        defer decremented.deinit();
        break :blk decremented.shiftLeft(1);
    } else value.numerator.clone();
    defer encoded.deinit();
    if (encoded.bitLength() > 256) return null;
    const bytes = @max(@as(usize, 1), (encoded.bitLength() + 7) / 8);
    return .{
        .bits = @intCast(bytes * 8),
        .modifier = if (value.numerator.isNegative()) .Signed else .Unsigned,
    };
}

pub fn rationalFixedPointType(
    provider: *TypeProviderModule.TypeProvider,
    value: Types.RationalNumberType,
) BehaviorError!?*const Types.Type {
    const shape = rationalFixedPointShape(value) orelse return null;
    return provider.fixedPoint(shape.bits, shape.fractional_digits, shape.modifier);
}

const RationalFixedPointShape = struct {
    bits: u16,
    fractional_digits: u8,
    modifier: Types.FixedPointModifier,
};

fn rationalFixedPointShape(
    value: Types.RationalNumberType,
) ?RationalFixedPointShape {
    const negative = value.numerator.isNegative();
    var numerator = value.numerator.absolute();
    defer numerator.deinit();
    var denominator = value.denominator.absolute();
    defer denominator.deinit();
    var one = Types.BigInt.initUnsigned(1);
    defer one.deinit();
    var maximum = one.shiftLeft(if (negative) 255 else 256);
    if (!negative) {
        var reduced = Types.BigInt.sub(&maximum, &one);
        maximum.deinit();
        maximum = reduced.take();
    }
    defer maximum.deinit();

    var fractional_digits: u8 = 0;
    var ten = Types.BigInt.initUnsigned(10);
    defer ten.deinit();
    while (fractional_digits < 80) {
        var remainder = Types.BigInt.remainder(&numerator, &denominator) catch unreachable; // zlinter-disable-current-line no_swallow_error - type construction guarantees a nonzero divisor
        defer remainder.deinit();
        if (remainder.isZero()) break;
        var next_numerator = Types.BigInt.mul(&numerator, &ten);
        defer next_numerator.deinit();
        var maximum_scaled = Types.BigInt.mul(&maximum, &denominator);
        defer maximum_scaled.deinit();
        if (next_numerator.compare(&maximum_scaled) == .gt) break;
        numerator.deinit();
        numerator = next_numerator.take();
        fractional_digits += 1;
    }
    var maximum_scaled = Types.BigInt.mul(&maximum, &denominator);
    defer maximum_scaled.deinit();
    if (numerator.compare(&maximum_scaled) == .gt) return null;

    var integral = Types.BigInt.quotient(&numerator, &denominator) catch unreachable; // zlinter-disable-current-line no_swallow_error - type construction guarantees a nonzero divisor
    defer integral.deinit();
    if (negative and !integral.isZero()) {
        var decremented = Types.BigInt.sub(&integral, &one);
        defer decremented.deinit();
        var shifted = decremented.shiftLeft(1);
        integral.deinit();
        integral = shifted.take();
    }
    if (integral.bitLength() > 256) return null;
    const bytes = @max(@as(usize, 1), (integral.bitLength() + 7) / 8);
    return .{
        .bits = @intCast(bytes * 8),
        .fractional_digits = fractional_digits,
        .modifier = if (negative) .Signed else .Unsigned,
    };
}

pub fn unaryOperatorResult(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    operand: *const Types.Type,
) BehaviorError!?*const Types.Type {
    return switch (operand.payload) {
        .Address, .Enum, .Function => if (operator == .Delete)
            provider.emptyTuple()
        else
            null,
        .Contract => |value| if (!value.is_super and operator == .Delete)
            provider.emptyTuple()
        else
            null,
        .Integer => |value| switch (operator) {
            .Delete => provider.emptyTuple(),
            .Sub => if (value.isSigned()) operand else null,
            .Inc, .Dec, .BitNot => operand,
            else => null,
        },
        .FixedPoint => switch (operator) {
            .Delete => provider.emptyTuple(),
            .Sub, .Inc, .Dec => operand,
            else => null,
        },
        .RationalNumber => |value| rationalUnaryOperatorResult(provider, operator, value),
        .FixedBytes => switch (operator) {
            .Delete => provider.emptyTuple(),
            .BitNot => operand,
            else => null,
        },
        .Bool => switch (operator) {
            .Delete => provider.emptyTuple(),
            .Not => operand,
            else => null,
        },
        .Array, .ArraySlice, .Struct => blk: {
            if (operator != .Delete) break :blk null;
            const reference = operand.asReference().?;
            break :blk switch (reference.location) {
                .CallData, .Transient => null,
                .Memory => provider.emptyTuple(),
                .Storage => if (reference.isPointer()) null else provider.emptyTuple(),
            };
        },
        else => null,
    };
}

pub fn binaryOperatorResult(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    left: *const Types.Type,
    right: *const Types.Type,
) BehaviorError!?*const Types.Type {
    return switch (left.payload) {
        .Address => if (TokenModule.isCompareOp(operator))
            try commonTypeWithProvider(provider, left, right)
        else
            null,
        .Integer => |value| integerBinaryOperatorResult(
            provider,
            operator,
            left,
            value,
            right,
        ),
        .FixedPoint => fixedPointBinaryOperatorResult(provider, operator, left, right),
        .RationalNumber => |value| rationalBinaryOperatorResult(
            provider,
            operator,
            left,
            value,
            right,
        ),
        .FixedBytes => fixedBytesBinaryOperatorResult(provider, operator, left, right),
        .Bool => if (right.category() == .Bool and
            (operator == .Equal or operator == .NotEqual or
                operator == .And or operator == .Or)) right else null,
        .Function => |value| functionBinaryOperatorResult(
            provider,
            operator,
            left,
            value,
            right,
        ),
        .Contract, .Enum => if (TokenModule.isCompareOp(operator))
            try commonTypeWithProvider(provider, left, right)
        else
            null,
        else => null,
    };
}

/// Preserves the explanatory payload carried by upstream's `TypeResult` when
/// an operator has no result type. Call this only after `binaryOperatorResult`
/// returned `null`; a `null` reason means the failure has no richer message.
pub fn binaryOperatorFailureReason(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    left_type: *const Types.Type,
    right_type: *const Types.Type,
) BehaviorError!?[]const u8 {
    if (left_type.category() == .Address and !TokenModule.isCompareOp(operator))
        return "Arithmetic operations on addresses are not supported. Convert to integer first before using them.";

    if (left_type.category() == .Integer and operator == .Exp) {
        if (right_type.asInteger()) |integer|
            if (integer.isSigned())
                return "Exponentiation power is not allowed to be a signed integer type.";
        if (right_type.category() == .RationalNumber) {
            const rational = right_type.payload.RationalNumber;
            if (rational.denominator.compareUnsigned(1) != .eq)
                return "Exponent is fractional.";
            if ((try rationalIntegerType(provider, rational)) == null)
                return "Exponent too large.";
            if (rational.numerator.isNegative())
                return "Exponentiation power is not allowed to be a negative integer literal.";
        }
    }

    if (left_type.category() == .RationalNumber and
        (right_type.category() == .Integer or right_type.category() == .FixedPoint))
    {
        const left = left_type.payload.RationalNumber;
        if (left.denominator.compareUnsigned(1) != .eq)
            return "Fractional literals not supported.";
        if ((try rationalIntegerType(provider, left)) == null)
            return "Literal too large.";
        if (operator == .Exp) {
            if (right_type.asInteger()) |integer|
                if (integer.isSigned())
                    return "Exponentiation power is not allowed to be a signed integer type.";
            if (right_type.category() == .FixedPoint)
                return "Exponent is fractional.";
        }
    }

    if (left_type.category() == .RationalNumber and
        right_type.category() == .RationalNumber)
    {
        if (try rationalBinaryComputation(
            operator,
            left_type.payload.RationalNumber,
            right_type.payload.RationalNumber,
        )) |computed_value| {
            var computed = computed_value;
            defer computed.deinit();
            if ((!computed.numerator.isZero() and computed.numerator.bitLength() > 4097) or
                computed.denominator.bitLength() > 4097)
                return "Precision of rational constants is limited to 4096 bits.";
        }
    }
    return null;
}

/// Owned arbitrary-precision rational used by compile-time evaluation.
///
/// This is public so the translated `ConstantEvaluator` and the type system
/// share one implementation of Solidity's precision limits and arithmetic
/// edge cases.  Callers must deinitialize every returned value.
pub const RationalComputation = struct {
    numerator: Types.BigInt,
    denominator: Types.BigInt,

    pub fn deinit(self: *RationalComputation) void {
        self.numerator.deinit();
        self.denominator.deinit();
        self.* = undefined;
    }

    pub fn clone(self: *const RationalComputation) RationalComputation {
        return .{
            .numerator = self.numerator.clone(),
            .denominator = self.denominator.clone(),
        };
    }
};

fn rationalUnaryOperatorResult(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    operand: Types.RationalNumberType,
) BehaviorError!?*const Types.Type {
    var value: RationalComputation = switch (operator) {
        .Add => return provider.rationalNumber(
            operand.numerator,
            operand.denominator,
            operand.compatible_bytes_type,
        ),
        .Sub => .{
            .numerator = operand.numerator.negate(),
            .denominator = operand.denominator.clone(),
        },
        .BitNot => blk: {
            if (operand.denominator.compareUnsigned(1) != .eq) return null;
            break :blk .{
                .numerator = operand.numerator.bitNot(),
                .denominator = Types.BigInt.initUnsigned(1),
            };
        },
        else => return null,
    };
    defer value.deinit();
    return provider.rationalNumber(&value.numerator, &value.denominator, null);
}

fn rationalBinaryOperatorResult(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    left_type: *const Types.Type,
    left: Types.RationalNumberType,
    right_type: *const Types.Type,
) BehaviorError!?*const Types.Type {
    if (right_type.category() == .Integer or right_type.category() == .FixedPoint) {
        if (left.denominator.compareUnsigned(1) != .eq or
            (try rationalIntegerType(provider, left)) == null) return null;
        if (TokenModule.isShiftOp(operator)) {
            if (!(try isValidShiftAndAmountType(provider, operator, right_type))) return null;
            return if (left.numerator.isNegative()) provider.int256() else provider.uint256();
        }
        if (operator == .Exp) {
            if (right_type.asInteger()) |integer|
                if (integer.isSigned()) return null;
            if (right_type.category() == .FixedPoint) return null;
            return if (left.numerator.isNegative()) provider.int256() else provider.uint256();
        }
        const common = try commonTypeWithProvider(provider, left_type, right_type) orelse
            return null;
        return binaryOperatorResult(provider, operator, common, right_type);
    }
    if (right_type.category() != .RationalNumber) return null;
    const right = right_type.payload.RationalNumber;
    if (TokenModule.isCompareOp(operator)) {
        const left_mobile = try mobileType(provider, left_type) orelse return null;
        const right_mobile = try mobileType(provider, right_type) orelse return null;
        return binaryOperatorResult(provider, operator, left_mobile, right_mobile);
    }
    var value = (try rationalBinaryComputation(operator, left, right)) orelse return null;
    defer value.deinit();
    if ((!value.numerator.isZero() and value.numerator.bitLength() > 4097) or
        value.denominator.bitLength() > 4097) return null;
    return provider.rationalNumber(&value.numerator, &value.denominator, null);
}

/// Performs the raw arbitrary-precision operation used by both rational type
/// inference and constant evaluation.  `null` denotes an operation which
/// cannot be represented under upstream's 4096-bit precision policy.
pub fn rationalBinaryComputation(
    operator: Types.Token,
    left: Types.RationalNumberType,
    right: Types.RationalNumberType,
) BehaviorError!?RationalComputation {
    return switch (operator) {
        .Add, .Sub => blk: {
            var left_scaled = Types.BigInt.mul(left.numerator, right.denominator);
            defer left_scaled.deinit();
            var right_scaled = Types.BigInt.mul(right.numerator, left.denominator);
            defer right_scaled.deinit();
            break :blk .{
                .numerator = if (operator == .Add)
                    Types.BigInt.add(&left_scaled, &right_scaled)
                else
                    Types.BigInt.sub(&left_scaled, &right_scaled),
                .denominator = Types.BigInt.mul(left.denominator, right.denominator),
            };
        },
        .Mul => .{
            .numerator = Types.BigInt.mul(left.numerator, right.numerator),
            .denominator = Types.BigInt.mul(left.denominator, right.denominator),
        },
        .Div => blk: {
            if (right.numerator.isZero()) return null;
            break :blk .{
                .numerator = Types.BigInt.mul(left.numerator, right.denominator),
                .denominator = Types.BigInt.mul(left.denominator, right.numerator),
            };
        },
        .Mod => blk: {
            if (right.numerator.isZero()) return null;
            var quotient_numerator = Types.BigInt.mul(
                left.numerator,
                right.denominator,
            );
            defer quotient_numerator.deinit();
            var quotient_denominator = Types.BigInt.mul(
                left.denominator,
                right.numerator,
            );
            defer quotient_denominator.deinit();
            var quotient = Types.BigInt.quotient(
                &quotient_numerator,
                &quotient_denominator,
            ) catch return null;
            defer quotient.deinit();
            var quotient_times_right_numerator = Types.BigInt.mul(
                &quotient,
                right.numerator,
            );
            defer quotient_times_right_numerator.deinit();
            var quotient_times_right_scaled = Types.BigInt.mul(
                &quotient_times_right_numerator,
                left.denominator,
            );
            defer quotient_times_right_scaled.deinit();
            var left_scaled = Types.BigInt.mul(left.numerator, right.denominator);
            defer left_scaled.deinit();
            break :blk .{
                .numerator = Types.BigInt.sub(
                    &left_scaled,
                    &quotient_times_right_scaled,
                ),
                .denominator = Types.BigInt.mul(
                    left.denominator,
                    right.denominator,
                ),
            };
        },
        .BitOr, .BitXor, .BitAnd => blk: {
            if (left.denominator.compareUnsigned(1) != .eq or
                right.denominator.compareUnsigned(1) != .eq) return null;
            break :blk .{
                .numerator = switch (operator) {
                    .BitOr => Types.BigInt.bitOr(left.numerator, right.numerator),
                    .BitXor => Types.BigInt.bitXor(left.numerator, right.numerator),
                    .BitAnd => Types.BigInt.bitAnd(left.numerator, right.numerator),
                    else => unreachable,
                },
                .denominator = Types.BigInt.initUnsigned(1),
            };
        },
        .SHL, .SAR => blk: {
            if (left.denominator.compareUnsigned(1) != .eq or
                right.denominator.compareUnsigned(1) != .eq or
                right.numerator.isNegative() or
                right.numerator.bitLength() > 32) return null;
            const shift: usize = @intCast(right.numerator.toU256Wrapping());
            if (operator == .SHL and !fitsShiftPrecision(left.numerator, shift)) return null;
            break :blk .{
                .numerator = if (operator == .SHL)
                    left.numerator.shiftLeft(shift)
                else
                    left.numerator.shiftRight(shift),
                .denominator = Types.BigInt.initUnsigned(1),
            };
        },
        .Exp => blk: {
            if (right.denominator.compareUnsigned(1) != .eq) return null;
            if (right.numerator.isZero()) break :blk .{
                .numerator = Types.BigInt.initUnsigned(1),
                .denominator = Types.BigInt.initUnsigned(1),
            };
            if (left.numerator.isZero() or
                left.numerator.compare(left.denominator) == .eq) break :blk .{
                .numerator = left.numerator.clone(),
                .denominator = left.denominator.clone(),
            };
            var absolute_exponent = right.numerator.absolute();
            defer absolute_exponent.deinit();
            var negative_denominator = left.denominator.negate();
            defer negative_denominator.deinit();
            if (left.numerator.compare(&negative_denominator) == .eq) {
                const odd = absolute_exponent.testBit(0);
                break :blk .{
                    .numerator = Types.BigInt.initSigned(if (odd) -1 else 1),
                    .denominator = Types.BigInt.initUnsigned(1),
                };
            }
            if (absolute_exponent.bitLength() > 32) return null;
            const exponent: u32 = @intCast(absolute_exponent.toU256Wrapping());
            if (!fitsExponentPrecision(left.numerator, exponent) or
                !fitsExponentPrecision(left.denominator, exponent)) return null;
            break :blk if (right.numerator.isNegative()) .{
                .numerator = left.denominator.pow(exponent),
                .denominator = left.numerator.pow(exponent),
            } else .{
                .numerator = left.numerator.pow(exponent),
                .denominator = left.denominator.pow(exponent),
            };
        },
        else => null,
    };
}

fn fitsShiftPrecision(value: *const Types.BigInt, shift: usize) bool {
    if (value.isZero()) return true;
    return shift <= 4096 and value.bitLength() <= 4096 - shift;
}

fn fitsExponentPrecision(value: *const Types.BigInt, exponent: u64) bool {
    if (value.isZero() or exponent == 0) return true;
    var magnitude = value.absolute();
    defer magnitude.deinit();
    const bits = magnitude.bitLength();
    if (bits == 1) return true;
    if (bits > 4097) return false;
    return exponent <= 4096 / @as(u64, @intCast(bits));
}

fn isValidShiftAndAmountType(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    amount: *const Types.Type,
) BehaviorError!bool {
    if (operator == .SHR) return false;
    if (amount.asInteger()) |integer| return !integer.isSigned();
    if (amount.category() != .RationalNumber) return false;
    const rational = amount.payload.RationalNumber;
    if (rational.denominator.compareUnsigned(1) != .eq) return false;
    const integer = (try rationalIntegerType(provider, rational)) orelse return false;
    return !integer.asInteger().?.isSigned();
}

fn integerBinaryOperatorResult(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    left_type: *const Types.Type,
    left: Types.IntegerType,
    right: *const Types.Type,
) BehaviorError!?*const Types.Type {
    if (right.category() != .RationalNumber and
        right.category() != .FixedPoint and
        right.category() != .Integer) return null;
    if (TokenModule.isShiftOp(operator))
        return if (try isValidShiftAndAmountType(provider, operator, right)) left_type else null;
    if (operator == .Exp) {
        if (right.asInteger()) |integer| if (integer.isSigned()) return null;
        if (right.category() == .FixedPoint) return null;
        if (right.category() == .RationalNumber) {
            const rational = right.payload.RationalNumber;
            if (rational.denominator.compareUnsigned(1) != .eq or
                rational.numerator.isNegative() or
                (try rationalIntegerType(provider, rational)) == null) return null;
        }
        return left_type;
    }
    const common = try commonTypeWithProvider(provider, left_type, right) orelse return null;
    if (TokenModule.isCompareOp(operator)) return common;
    if (TokenModule.isBooleanOp(operator)) return null;
    _ = left;
    return common;
}

fn fixedPointBinaryOperatorResult(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    left: *const Types.Type,
    right: *const Types.Type,
) BehaviorError!?*const Types.Type {
    const common = try commonTypeWithProvider(provider, left, right) orelse return null;
    if (TokenModule.isCompareOp(operator)) return common;
    if (TokenModule.isBitOp(operator) or TokenModule.isBooleanOp(operator) or
        operator == .Exp) return null;
    return common;
}

fn fixedBytesBinaryOperatorResult(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    left: *const Types.Type,
    right: *const Types.Type,
) BehaviorError!?*const Types.Type {
    if (TokenModule.isShiftOp(operator))
        return if (try isValidShiftAndAmountType(provider, operator, right)) left else null;
    const common = try commonTypeWithProvider(provider, left, right) orelse return null;
    if (common.category() != .FixedBytes) return null;
    return if (TokenModule.isCompareOp(operator) or TokenModule.isBitOp(operator))
        common
    else
        null;
}

fn functionBinaryOperatorResult(
    provider: *TypeProviderModule.TypeProvider,
    operator: Types.Token,
    left_type: *const Types.Type,
    left: Types.FunctionType,
    right_type: *const Types.Type,
) BehaviorError!?*const Types.Type {
    if (right_type.category() != .Function or
        (operator != .Equal and operator != .NotEqual)) return null;
    const right = right_type.payload.Function;
    const comparable = (left.kind == .Internal and try sizeOnStack(left_type) == 1 and
        right.kind == .Internal and try sizeOnStack(right_type) == 1) or
        (left.kind == .External and try sizeOnStack(left_type) == 2 and
            !left.options.has_bound_first_argument and
            right.kind == .External and try sizeOnStack(right_type) == 2 and
            !right.options.has_bound_first_argument);
    return if (comparable)
        try commonTypeWithProvider(provider, left_type, right_type)
    else
        null;
}

fn functionMobileType(
    provider: *TypeProviderModule.TypeProvider,
    value: Types.FunctionType,
) BehaviorError!?*const Types.Type {
    if (value.options.value_set or value.options.gas_set or value.options.salt_set or
        value.options.has_bound_first_argument) return null;
    switch (value.kind) {
        .Internal, .External, .DelegateCall => {},
        else => return null,
    }
    const parameter_names = try provider.backing_allocator.alloc(
        []const u8,
        value.parameter_types.len,
    );
    defer provider.backing_allocator.free(parameter_names);
    @memset(parameter_names, "");
    const return_names = try provider.backing_allocator.alloc(
        []const u8,
        value.return_parameter_types.len,
    );
    defer provider.backing_allocator.free(return_names);
    @memset(return_names, "");
    return provider.function(
        value.parameter_types,
        value.return_parameter_types,
        parameter_names,
        return_names,
        value.kind,
        value.state_mutability,
        null,
        value.options,
    );
}

pub fn literalValue(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
    literal: ?AST.Literal,
) BehaviorError!u256 {
    return switch (type_ref.payload) {
        .Address => blk: {
            const value = literal orelse return error.InvalidType;
            const clean = try removeUnderscoresAlloc(provider.backing_allocator, value.value);
            defer provider.backing_allocator.free(clean);
            if (!std.mem.startsWith(u8, clean, "0x")) return error.InvalidType;
            var parsed = Types.BigInt.parse(provider.backing_allocator, clean, 0) catch
                return error.InvalidType;
            defer parsed.deinit();
            if (parsed.isNegative() or parsed.bitLength() > 256) return error.Overflow;
            break :blk parsed.toU256Wrapping();
        },
        .Bool => switch ((literal orelse return error.InvalidType).token) {
            .TrueLiteral => 1,
            .FalseLiteral => 0,
            else => error.InvalidType,
        },
        .RationalNumber => |value| blk: {
            var shifted = if (value.denominator.compareUnsigned(1) == .eq)
                value.numerator.clone()
            else inner: {
                const fixed = (try rationalFixedPointType(provider, value)) orelse
                    return error.InvalidType;
                var ten = Types.BigInt.initUnsigned(10);
                defer ten.deinit();
                var scale = ten.pow(fixed.payload.FixedPoint.fractional_digits);
                defer scale.deinit();
                var scaled = Types.BigInt.mul(value.numerator, &scale);
                defer scaled.deinit();
                break :inner Types.BigInt.quotient(&scaled, value.denominator) catch
                    return error.InvalidType;
            };
            defer shifted.deinit();
            if (!shifted.isNegative()) {
                if (shifted.bitLength() > 256) return error.Overflow;
            } else {
                var minimum_magnitude = Types.BigInt.initUnsigned(1);
                defer minimum_magnitude.deinit();
                var minimum = minimum_magnitude.shiftLeft(255);
                defer minimum.deinit();
                var negative_minimum = minimum.negate();
                defer negative_minimum.deinit();
                if (shifted.compare(&negative_minimum) == .lt) return error.Overflow;
            }
            break :blk shifted.toU256Wrapping();
        },
        else => error.InvalidType,
    };
}

fn removeUnderscoresAlloc(
    allocator: std.mem.Allocator,
    value: []const u8,
) std.mem.Allocator.Error![]u8 {
    const output = try allocator.alloc(u8, value.len);
    var length: usize = 0;
    for (value) |byte| {
        if (byte == '_') continue;
        output[length] = byte;
        length += 1;
    }
    return allocator.realloc(output, length);
}

pub fn encodingType(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
) BehaviorError!?*const Types.Type {
    return switch (type_ref.payload) {
        .Address, .Integer, .Bool, .FixedPoint, .FixedBytes => type_ref,
        .Array => |value| if (value.reference.location == .Storage)
            provider.uint256()
        else
            try provider.withLocation(type_ref, .Memory, true),
        .Contract => |value| if (value.is_super)
            null
        else if (contractIsPayable(value.declaration))
            provider.payableAddress()
        else
            provider.address(),
        .Struct => |value| if (value.reference.location == .Storage)
            provider.uint256()
        else
            type_ref,
        .Enum => provider.uint(8),
        .UserDefinedValueType => |value| encodingType(
            provider,
            value.underlying_type orelse return error.InvalidType,
        ),
        .Function => |value| if (!value.options.gas_set and
            !value.options.value_set and value.kind == .External) type_ref else null,
        .Mapping => provider.uint256(),
        else => null,
    };
}

pub fn decodingType(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
) BehaviorError!?*const Types.Type {
    return switch (type_ref.payload) {
        .Array => |value| if (value.reference.location == .Storage)
            provider.uint256()
        else
            type_ref,
        .InaccessibleDynamic => provider.uint256(),
        else => encodingType(provider, type_ref),
    };
}

pub fn interfaceType(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
    in_library: bool,
) BehaviorError!?*const Types.Type {
    var visited = std.AutoHashMap(*const AST.Node, void).init(provider.backing_allocator);
    defer visited.deinit();
    return interfaceTypeInner(provider, type_ref, in_library, 0, &visited);
}

fn interfaceTypeInner(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
    in_library: bool,
    depth: usize,
    visited_structs: *std.AutoHashMap(*const AST.Node, void),
) BehaviorError!?*const Types.Type {
    if (depth >= 256) return error.InvalidType;
    return switch (type_ref.payload) {
        .Address, .Integer, .Bool, .FixedPoint, .FixedBytes => type_ref,
        .Contract => |value| if (value.is_super)
            null
        else if (in_library)
            type_ref
        else
            encodingType(provider, type_ref),
        .Array => |value| blk: {
            const base = (try interfaceTypeInner(
                provider,
                value.base_type,
                in_library,
                depth + 1,
                visited_structs,
            )) orelse break :blk null;
            if (in_library and value.reference.location == .Storage) break :blk type_ref;
            if (value.isByteArrayOrString())
                break :blk try provider.withLocation(type_ref, .Memory, true);
            break :blk if (value.length) |length|
                try provider.arrayWithLength(.Memory, base, length)
            else
                try provider.array(.Memory, base);
        },
        .Struct => |value| blk: {
            const recursive = structRecursive(value.declaration);
            if (recursive and !(in_library and value.reference.location == .Storage))
                break :blk null;
            if (visited_structs.contains(value.declaration))
                break :blk if (in_library and value.reference.location == .Storage)
                    type_ref
                else
                    null;
            try visited_structs.put(value.declaration, {});
            defer _ = visited_structs.remove(value.declaration);
            if (value.declaration.nodeKind() != .struct_definition) return error.InvalidType;
            for (value.declaration.payload.struct_definition.members) |member| {
                const member_type = try variableDeclarationType(member);
                if ((try interfaceTypeInner(
                    provider,
                    member_type,
                    in_library,
                    depth + 1,
                    visited_structs,
                )) == null) break :blk null;
            }
            break :blk if (in_library and value.reference.location == .Storage)
                type_ref
            else
                try provider.withLocation(type_ref, .Memory, true);
        },
        .Enum => if (in_library) type_ref else provider.uint(8),
        .UserDefinedValueType => |value| interfaceTypeInner(
            provider,
            value.underlying_type orelse return error.InvalidType,
            in_library,
            depth + 1,
            visited_structs,
        ),
        .Function => |value| if (value.kind == .External) type_ref else null,
        .Mapping => |value| blk: {
            if (!in_library) break :blk null;
            if ((try interfaceTypeInner(
                provider,
                value.key_type,
                true,
                depth + 1,
                visited_structs,
            )) == null) return error.InvalidType;
            if ((try interfaceTypeInner(
                provider,
                value.value_type,
                true,
                depth + 1,
                visited_structs,
            )) == null) break :blk null;
            break :blk type_ref;
        },
        else => null,
    };
}

pub fn fullEncodingType(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
    in_library_call: bool,
    encoder_v2: bool,
    packed_mode: bool,
) BehaviorError!?*const Types.Type {
    _ = packed_mode;
    const mobile = (try mobileType(provider, type_ref)) orelse return null;
    const interface = (try interfaceType(provider, mobile, in_library_call)) orelse
        return null;
    const encoded = (try encodingType(provider, interface)) orelse return null;
    if (in_library_call and dataStoredIn(encoded, .Storage)) return encoded;
    var base = encoded;
    while (base.asArray()) |array_type| {
        base = array_type.base_type;
        if (!encoder_v2) {
            if (base.asArray()) |base_array|
                if (base_array.isDynamicallySized()) return null;
        }
    }
    if (!encoder_v2 and base.category() == .Struct) return null;
    return encoded;
}

pub fn finalArrayBaseType(
    type_ref: *const Types.Type,
    break_if_dynamic: bool,
) *const Types.Type {
    var result = type_ref;
    while (result.asArray()) |array_type| {
        if (break_if_dynamic and array_type.isDynamicallySized()) break;
        result = array_type.base_type;
    }
    return result;
}

pub fn validForLocation(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
    location: Types.DataLocation,
) BehaviorError!bool {
    return switch (type_ref.payload) {
        .Array => |value| blk: {
            if (value.base_type.category() == .Array and
                !(try validForLocation(provider, value.base_type, location))) break :blk false;
            if (value.isDynamicallySized()) break :blk true;
            break :blk switch (location) {
                .Memory => (arrayMemorySizeForLocationValidation(value) catch break :blk false) <
                    std.math.maxInt(u32),
                .CallData => (arrayCalldataSizeForLocationValidation(value) catch break :blk false) <
                    std.math.maxInt(u32),
                .Storage => blk_storage: {
                    _ = storageSizeUpperBound(type_ref) catch break :blk_storage false;
                    break :blk_storage true;
                },
                .Transient => false,
            };
        },
        .Struct => |value| blk: {
            if (value.declaration.nodeKind() != .struct_definition) return error.InvalidType;
            for (value.declaration.payload.struct_definition.members) |member| {
                const member_type = try variableDeclarationType(member);
                if (member_type.asReference() != null and
                    !(try validForLocation(provider, member_type, location))) break :blk false;
            }
            if (location == .Storage)
                _ = storageSizeUpperBound(type_ref) catch break :blk false;
            break :blk true;
        },
        .ArraySlice => |value| validForLocation(provider, value.array_type, location),
        else => true,
    };
}

fn arrayMemorySizeForLocationValidation(array: Types.ArrayType) QueryError!u256 {
    var size = array.length orelse return error.InvalidType;
    var final_type = array.base_type;
    while (final_type.asArray()) |nested| {
        const length = nested.length orelse break;
        size = std.math.mul(u256, size, length) catch return error.Overflow;
        final_type = nested.base_type;
    }
    const stride = if (isDynamicallySized(final_type))
        try memoryHeadSize(final_type)
    else
        try memoryDataSizeIgnoringReferenceLocation(final_type);
    return std.math.mul(u256, size, stride) catch return error.Overflow;
}

fn memoryDataSizeIgnoringReferenceLocation(type_ref: *const Types.Type) QueryError!u256 {
    return switch (type_ref.payload) {
        .Array => |array| blk: {
            const length = array.length orelse return error.InvalidType;
            break :blk std.math.mul(
                u256,
                length,
                try memoryHeadSize(array.base_type),
            ) catch return error.Overflow;
        },
        .Struct => |structure| structMemoryDataSize(structure),
        else => @as(u256, try calldataEncodedSize(type_ref, true)),
    };
}

fn arrayCalldataSizeForLocationValidation(array: Types.ArrayType) QueryError!u256 {
    const length = array.length orelse return error.InvalidType;
    const stride: u256 = if (array.isByteArrayOrString())
        1
    else
        try calldataHeadSize(array.base_type);
    const size = std.math.mul(u256, length, stride) catch return error.Overflow;
    const rounded = std.math.add(u256, size, 31) catch return error.Overflow;
    return std.math.mul(u256, rounded / 32, 32) catch return error.Overflow;
}

pub fn containsNestedMapping(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
) BehaviorError!bool {
    var visited = std.AutoHashMap(*const AST.Node, void).init(provider.backing_allocator);
    defer visited.deinit();
    return containsNestedMappingInner(type_ref, 0, &visited);
}

fn containsNestedMappingInner(
    type_ref: *const Types.Type,
    depth: usize,
    visited_structs: *std.AutoHashMap(*const AST.Node, void),
) BehaviorError!bool {
    if (depth >= 256) return error.InvalidType;
    return switch (type_ref.payload) {
        .Mapping => true,
        .Array => |value| containsNestedMappingInner(
            value.base_type,
            depth + 1,
            visited_structs,
        ),
        .Struct => |value| blk: {
            if (visited_structs.contains(value.declaration)) break :blk false;
            try visited_structs.put(value.declaration, {});
            defer _ = visited_structs.remove(value.declaration);
            if (value.declaration.nodeKind() != .struct_definition) return error.InvalidType;
            for (value.declaration.payload.struct_definition.members) |member|
                if (try containsNestedMappingInner(
                    try variableDeclarationType(member),
                    depth + 1,
                    visited_structs,
                )) break :blk true;
            break :blk false;
        },
        else => false,
    };
}

pub fn hasSimpleZeroValueInMemory(type_ref: *const Types.Type) bool {
    return switch (type_ref.payload) {
        .Array, .ArraySlice, .Struct, .Function, .Tuple => false,
        .UserDefinedValueType => |value| hasSimpleZeroValueInMemory(
            value.underlying_type orelse return false,
        ),
        .Mapping, .TypeType, .Modifier, .Magic, .Module, .InaccessibleDynamic => false,
        else => true,
    };
}

pub fn typeDefinition(type_ref: *const Types.Type) ?*const AST.Node {
    return switch (type_ref.payload) {
        .Struct => |value| value.declaration,
        .Enum => |value| value.declaration,
        .UserDefinedValueType => |value| value.declaration,
        else => null,
    };
}

pub fn fullDecompositionAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
) BehaviorError![]*const Types.Type {
    var result: std.ArrayList(*const Types.Type) = .empty;
    errdefer result.deinit(allocator);
    try result.append(allocator, type_ref);
    var index: usize = 0;
    while (index < result.items.len) : (index += 1) {
        const current = result.items[index];
        switch (current.payload) {
            .Array => |value| try appendUniqueType(allocator, &result, value.base_type),
            .ArraySlice => |value| try appendUniqueType(
                allocator,
                &result,
                value.array_type.payload.Array.base_type,
            ),
            .Struct => |value| {
                if (value.declaration.nodeKind() != .struct_definition) return error.InvalidType;
                for (value.declaration.payload.struct_definition.members) |member| {
                    const member_type = try provider.withLocationIfReference(
                        value.reference.location,
                        try variableDeclarationType(member),
                        false,
                    );
                    try appendUniqueType(allocator, &result, member_type);
                }
            },
            .Tuple => |value| for (value.components) |component|
                if (component) |present|
                    try appendUniqueType(allocator, &result, present),
            .Mapping => |value| try appendUniqueType(allocator, &result, value.value_type),
            else => {},
        }
    }
    return result.toOwnedSlice(allocator);
}

fn appendUniqueType(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(*const Types.Type),
    type_ref: *const Types.Type,
) QueryError!void {
    const candidate = try richIdentifierAlloc(allocator, type_ref);
    defer allocator.free(candidate);
    for (output.items) |existing| {
        const identifier = try richIdentifierAlloc(allocator, existing);
        defer allocator.free(identifier);
        if (std.mem.eql(u8, identifier, candidate)) return;
    }
    try output.append(allocator, type_ref);
}

fn structRecursive(declaration: *const AST.Node) bool {
    const annotation = ASTAnnotations.annotationConst(declaration) orelse return false;
    return switch (annotation.*) {
        .struct_declaration => |value| value.recursive orelse false,
        else => false,
    };
}

pub fn structIsRecursive(structure: Types.StructType) QueryError!bool {
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    const annotation = ASTAnnotations.annotationConst(structure.declaration) orelse
        return error.InvalidType;
    return switch (annotation.*) {
        .struct_declaration => |value| value.recursive orelse return error.InvalidType,
        else => error.InvalidType,
    };
}

pub fn returnParameterTypesWithoutDynamicTypesAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    function: Types.FunctionType,
) BehaviorError![]const *const Types.Type {
    const result = try allocator.dupe(*const Types.Type, function.return_parameter_types);
    errdefer allocator.free(result);
    switch (function.kind) {
        .External,
        .DelegateCall,
        .BareCall,
        .BareCallCode,
        .BareDelegateCall,
        .BareStaticCall,
        => for (result) |*parameter| {
            const decoded = (try decodingType(provider, parameter.*)) orelse
                return error.InvalidType;
            if (isDynamicallyEncoded(decoded)) parameter.* = provider.inaccessibleDynamic();
        },
        else => {},
    }
    return result;
}

pub fn interfaceFunctionType(
    provider: *TypeProviderModule.TypeProvider,
    function: Types.FunctionType,
) BehaviorError!?*const Types.Type {
    const declaration = function.declaration orelse return error.InvalidType;
    const in_library = function.kind != .Event and function.kind != .Error and
        declarationInLibrary(declaration);
    const parameters = (try transformParametersToExternalAlloc(
        provider,
        provider.backing_allocator,
        function.parameter_types,
        in_library,
    )) orelse return null;
    defer provider.backing_allocator.free(parameters);
    const returns = (try transformParametersToExternalAlloc(
        provider,
        provider.backing_allocator,
        function.return_parameter_types,
        in_library,
    )) orelse return null;
    defer provider.backing_allocator.free(returns);
    if (declaration.nodeKind() == .variable_declaration and returns.len == 0) return null;
    if (function.options.arbitrary_parameters) return error.InvalidType;
    return provider.function(
        parameters,
        returns,
        function.parameter_names,
        function.return_parameter_names,
        function.kind,
        function.state_mutability,
        declaration,
        .{},
    );
}

fn transformParametersToExternalAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    parameters: []const *const Types.Type,
    in_library: bool,
) BehaviorError!?[]*const Types.Type {
    const result = try allocator.alloc(*const Types.Type, parameters.len);
    errdefer allocator.free(result);
    for (parameters, result) |parameter, *target|
        target.* = (try interfaceType(provider, parameter, in_library)) orelse {
            allocator.free(result);
            return null;
        };
    return result;
}

pub fn functionCanTakeArguments(
    function: Types.FunctionType,
    arguments: *const Enums.FuncCallArguments,
    self_type: ?*const Types.Type,
) bool {
    if (function.options.has_bound_first_argument) {
        const actual_self = self_type orelse return false;
        const expected_self = function.selfType() orelse return false;
        if (!isImplicitlyConvertibleTo(actual_self, expected_self)) return false;
    }
    const parameter_types = function.parameterTypes();
    const parameter_names = function.parameterNames();
    if (function.options.arbitrary_parameters) return true;
    if (arguments.types.items.len != parameter_types.len) return false;
    if (!arguments.hasNamedArguments()) {
        for (arguments.types.items, parameter_types) |erased_actual, expected| {
            const actual: *const Types.Type = @ptrCast(@alignCast(erased_actual));
            if (!isImplicitlyConvertibleTo(actual, expected)) return false;
        }
        return true;
    }
    if (parameter_names.len != arguments.numNames() or
        arguments.numArguments() != arguments.numNames()) return false;
    var matched_names: usize = 0;
    for (arguments.names.items, arguments.types.items) |name, erased_actual| {
        const actual: *const Types.Type = @ptrCast(@alignCast(erased_actual));
        for (parameter_names, parameter_types) |parameter_name, expected| {
            if (!std.mem.eql(u8, name, parameter_name)) continue;
            matched_names += 1;
            if (!isImplicitlyConvertibleTo(actual, expected)) return false;
        }
    }
    return matched_names == arguments.numNames();
}

pub fn functionHasEqualParameterTypes(
    left: Types.FunctionType,
    right: Types.FunctionType,
) bool {
    return typeSlicesEqual(left.parameter_types, right.parameter_types);
}

pub fn functionHasEqualReturnTypes(
    left: Types.FunctionType,
    right: Types.FunctionType,
) bool {
    return typeSlicesEqual(left.return_parameter_types, right.return_parameter_types);
}

pub fn functionEqualExcludingStateMutability(
    left: Types.FunctionType,
    right: Types.FunctionType,
) bool {
    return functionEquals(left, right, true);
}

pub fn functionIsBareCall(function: Types.FunctionType) bool {
    return switch (function.kind) {
        .BareCall,
        .BareCallCode,
        .BareDelegateCall,
        .BareStaticCall,
        .ECRecover,
        .SHA256,
        .RIPEMD160,
        => true,
        else => false,
    };
}

pub fn functionIsPure(function: Types.FunctionType) bool {
    return switch (function.kind) {
        .KECCAK256,
        .ECRecover,
        .SHA256,
        .RIPEMD160,
        .AddMod,
        .MulMod,
        .ObjectCreation,
        .ABIEncode,
        .ABIEncodePacked,
        .ABIEncodeWithSelector,
        .ABIEncodeCall,
        .ABIEncodeWithSignature,
        .ABIDecode,
        .MetaType,
        .Wrap,
        .Unwrap,
        .BytesConcat,
        .StringConcat,
        .ERC7201,
        => true,
        else => false,
    };
}

pub fn functionDocumentation(function: Types.FunctionType) ?*const AST.Node {
    const declaration = function.declaration orelse return null;
    return switch (declaration.payload) {
        .function_definition => |value| value.documentation,
        .variable_declaration => |value| value.documentation,
        .event_definition => |value| value.documentation,
        .error_definition => |value| value.documentation,
        else => null,
    };
}

pub fn functionPadsArguments(function: Types.FunctionType) bool {
    return switch (function.kind) {
        .BareCall,
        .BareCallCode,
        .BareDelegateCall,
        .BareStaticCall,
        .SHA256,
        .RIPEMD160,
        .KECCAK256,
        .ABIEncodePacked,
        => false,
        else => true,
    };
}

pub fn functionTakesSinglePackedBytesParameter(function: Types.FunctionType) bool {
    return switch (function.kind) {
        .KECCAK256,
        .SHA256,
        .RIPEMD160,
        .BareCall,
        .BareCallCode,
        .BareDelegateCall,
        .BareStaticCall,
        => true,
        else => false,
    };
}

pub fn asExternallyCallableFunction(
    provider: *TypeProviderModule.TypeProvider,
    function: Types.FunctionType,
    in_library: bool,
) BehaviorError!*const Types.Type {
    const parameters = try externalCallableParametersAlloc(
        provider,
        provider.backing_allocator,
        function.parameter_types,
    );
    defer provider.backing_allocator.free(parameters);
    const returns = try externalCallableParametersAlloc(
        provider,
        provider.backing_allocator,
        function.return_parameter_types,
    );
    defer provider.backing_allocator.free(returns);
    if (in_library and function.declaration == null) return error.InvalidType;
    return provider.function(
        parameters,
        returns,
        function.parameter_names,
        function.return_parameter_names,
        if (in_library) .DelegateCall else function.kind,
        function.state_mutability,
        function.declaration,
        function.options,
    );
}

fn externalCallableParametersAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    parameters: []const *const Types.Type,
) BehaviorError![]*const Types.Type {
    const result = try allocator.alloc(*const Types.Type, parameters.len);
    errdefer allocator.free(result);
    for (parameters, result) |parameter, *target| {
        const reference = parameter.asReference();
        target.* = if (reference != null and reference.?.location == .CallData)
            try provider.withLocationIfReference(.Memory, parameter, true)
        else
            parameter;
    }
    return result;
}

pub fn newExpressionType(
    provider: *TypeProviderModule.TypeProvider,
    contract: *const AST.Node,
) BehaviorError!*const Types.Type {
    if (contract.nodeKind() != .contract_definition or
        contract.payload.contract_definition.contract_kind == .Interface)
        return error.InvalidType;
    const constructor = contractConstructor(contract);
    const count = if (constructor) |present|
        present.payload.function_definition.callable.parameters.payload.parameter_list.parameters.len
    else
        0;
    const parameters = try provider.backing_allocator.alloc(*const Types.Type, count);
    defer provider.backing_allocator.free(parameters);
    const names = try provider.backing_allocator.alloc([]const u8, count);
    defer provider.backing_allocator.free(names);
    var state_mutability: Types.StateMutability = .NonPayable;
    if (constructor) |present| {
        const definition = present.payload.function_definition;
        for (definition.callable.parameters.payload.parameter_list.parameters, 0..) |parameter, index| {
            parameters[index] = try variableDeclarationType(parameter);
            names[index] = parameter.payload.variable_declaration.declaration.name;
        }
        if (definition.state_mutability == .Payable) state_mutability = .Payable;
    }
    return provider.function(
        parameters,
        &.{try provider.contract(contract, false)},
        names,
        &.{""},
        .Creation,
        state_mutability,
        null,
        .{},
    );
}

fn contractConstructor(contract: *const AST.Node) ?*const AST.Node {
    if (contract.nodeKind() != .contract_definition) return null;
    for (contract.payload.contract_definition.sub_nodes) |node|
        if (node.nodeKind() == .function_definition and
            node.payload.function_definition.kind == .Constructor) return node;
    return null;
}

pub fn structConstructorType(
    provider: *TypeProviderModule.TypeProvider,
    structure_type: *const Types.Type,
) BehaviorError!*const Types.Type {
    const structure = switch (structure_type.payload) {
        .Struct => |value| value,
        else => return error.InvalidType,
    };
    if (try containsNestedMapping(provider, structure_type)) return error.InvalidType;
    if (structure.declaration.nodeKind() != .struct_definition) return error.InvalidType;
    const members = structure.declaration.payload.struct_definition.members;
    const parameters = try provider.backing_allocator.alloc(*const Types.Type, members.len);
    defer provider.backing_allocator.free(parameters);
    const names = try provider.backing_allocator.alloc([]const u8, members.len);
    defer provider.backing_allocator.free(names);
    for (members, 0..) |member, index| {
        parameters[index] = try provider.withLocationIfReference(
            .Memory,
            try variableDeclarationType(member),
            false,
        );
        names[index] = member.payload.variable_declaration.declaration.name;
    }
    return provider.function(
        parameters,
        &.{try provider.withLocation(structure_type, .Memory, false)},
        names,
        &.{""},
        .Internal,
        .NonPayable,
        null,
        .{},
    );
}

pub fn signatureInExternalFunctionAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
    structs_by_name: bool,
) BehaviorError![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try appendSignatureInExternalFunction(
        provider,
        allocator,
        &output,
        type_ref,
        structs_by_name,
        0,
    );
    return output.toOwnedSlice(allocator);
}

fn appendSignatureInExternalFunction(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    type_ref: *const Types.Type,
    structs_by_name: bool,
    depth: usize,
) BehaviorError!void {
    if (depth >= 256) return error.InvalidType;
    switch (type_ref.payload) {
        .Array => |array| {
            if (array.isByteArrayOrString()) {
                const canonical = try canonicalNameAlloc(allocator, type_ref);
                defer allocator.free(canonical);
                try output.appendSlice(allocator, canonical);
            } else {
                try appendSignatureInExternalFunction(
                    provider,
                    allocator,
                    output,
                    array.base_type,
                    structs_by_name,
                    depth + 1,
                );
                try output.append(allocator, '[');
                if (array.length) |length| try appendDecimal(allocator, output, length);
                try output.append(allocator, ']');
            }
        },
        .Struct => |structure| if (structs_by_name) {
            const canonical = try canonicalNameAlloc(allocator, type_ref);
            defer allocator.free(canonical);
            try output.appendSlice(allocator, canonical);
        } else {
            if (structure.declaration.nodeKind() != .struct_definition)
                return error.InvalidType;
            try output.append(allocator, '(');
            for (structure.declaration.payload.struct_definition.members, 0..) |member, index| {
                if (index != 0) try output.append(allocator, ',');
                const memory_type = try provider.withLocationIfReference(
                    .Memory,
                    try variableDeclarationType(member),
                    false,
                );
                const external = (try interfaceType(provider, memory_type, false)) orelse
                    return error.InvalidType;
                try appendSignatureInExternalFunction(
                    provider,
                    allocator,
                    output,
                    external,
                    false,
                    depth + 1,
                );
            }
            try output.append(allocator, ')');
        },
        .UserDefinedValueType => return error.InvalidType,
        else => {
            const canonical = try canonicalNameAlloc(allocator, type_ref);
            defer allocator.free(canonical);
            try output.appendSlice(allocator, canonical);
        },
    }
}

pub fn externalSignatureAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    function: Types.FunctionType,
) BehaviorError![]u8 {
    const declaration = function.declaration orelse return error.InvalidType;
    const declaration_data = declaration.declarationConst() orelse return error.InvalidType;
    if (declaration_data.name.len == 0) return error.InvalidType;
    switch (function.kind) {
        .Internal, .External, .DelegateCall, .Event, .Error, .Declaration => {},
        else => return error.InvalidType,
    }
    const in_library = function.kind != .Event and function.kind != .Error and
        declarationInLibrary(declaration);
    const parameters = (try transformParametersToExternalAlloc(
        provider,
        allocator,
        function.parameter_types,
        in_library,
    )) orelse return error.InvalidType;
    defer allocator.free(parameters);
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try output.appendSlice(allocator, declaration_data.name);
    try output.append(allocator, '(');
    for (parameters, 0..) |parameter, index| {
        if (index != 0) try output.append(allocator, ',');
        try appendSignatureInExternalFunction(
            provider,
            allocator,
            &output,
            parameter,
            in_library,
            0,
        );
        if (in_library and dataStoredIn(parameter, .Storage))
            try output.appendSlice(allocator, " storage");
    }
    try output.append(allocator, ')');
    return output.toOwnedSlice(allocator);
}

pub fn externalIdentifier(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    function: Types.FunctionType,
) BehaviorError!u256 {
    const signature = try externalSignatureAlloc(provider, allocator, function);
    defer allocator.free(signature);
    return FunctionSelector.selectorFromSignatureU32(signature);
}

pub fn externalIdentifierHexAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    function: Types.FunctionType,
) BehaviorError![]u8 {
    const signature = try externalSignatureAlloc(provider, allocator, function);
    defer allocator.free(signature);
    const selector = FunctionSelector.selectorFromSignatureH32(signature);
    const rendered = selector.hex();
    return allocator.dupe(u8, &rendered);
}

fn declarationInLibrary(declaration: *const AST.Node) bool {
    const annotation = ASTAnnotations.annotationConst(declaration) orelse return false;
    const scope = (ASTAnnotations.scopableConst(annotation) orelse return false).scope orelse
        return false;
    return scope.nodeKind() == .contract_definition and
        scope.payload.contract_definition.contract_kind == .Library;
}

const MemberBuilder = struct {
    allocator: std.mem.Allocator,
    items: std.ArrayList(Types.Member) = .empty,

    fn deinit(self: *MemberBuilder) void {
        self.items.deinit(self.allocator);
        self.* = undefined;
    }

    fn add(
        self: *MemberBuilder,
        name: []const u8,
        type_ref: *const Types.Type,
        declaration: ?*const AST.Node,
    ) std.mem.Allocator.Error!void {
        try self.items.append(self.allocator, .{
            .name = name,
            .type_ref = type_ref,
            .declaration = declaration,
        });
    }

    fn finish(self: *MemberBuilder) std.mem.Allocator.Error!Types.OwnedMemberList {
        const items = try self.items.toOwnedSlice(self.allocator);
        return .{ .allocator = self.allocator, .items = items };
    }
};

pub fn nativeMembersAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
    current_scope: ?*const AST.Node,
) BehaviorError!Types.OwnedMemberList {
    var builder = MemberBuilder{ .allocator = allocator };
    errdefer builder.deinit();
    switch (type_ref.payload) {
        .Address => |address| try appendAddressMembers(provider, &builder, address),
        .FixedBytes => try builder.add("length", try provider.uint(8), null),
        .Array => |array| try appendArrayMembers(provider, &builder, type_ref, array),
        .Contract => |contract| try appendContractMembers(provider, &builder, contract),
        .Struct => |structure| try appendStructMembers(provider, &builder, structure),
        .Function => |function| try appendFunctionMembers(
            provider,
            &builder,
            type_ref,
            function,
            current_scope,
        ),
        .TypeType => |type_type| try appendTypeTypeMembers(
            provider,
            &builder,
            type_type.actual_type,
            current_scope,
        ),
        .Module => |module| try appendModuleMembers(provider, &builder, module),
        .Magic => |magic| try appendMagicMembers(provider, &builder, magic),
        else => {},
    }
    return builder.finish();
}

fn plainFunction(
    provider: *TypeProviderModule.TypeProvider,
    parameter_types: []const *const Types.Type,
    return_types: []const *const Types.Type,
    kind: Types.FunctionKind,
    mutability: Types.StateMutability,
    options: Types.FunctionOptions,
) BehaviorError!*const Types.Type {
    const parameter_names = try provider.backing_allocator.alloc(
        []const u8,
        parameter_types.len,
    );
    defer provider.backing_allocator.free(parameter_names);
    @memset(parameter_names, "");
    const return_names = try provider.backing_allocator.alloc([]const u8, return_types.len);
    defer provider.backing_allocator.free(return_names);
    @memset(return_names, "");
    return provider.function(
        parameter_types,
        return_types,
        parameter_names,
        return_names,
        kind,
        mutability,
        null,
        options,
    );
}

fn appendAddressMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    address: Types.AddressType,
) BehaviorError!void {
    try builder.add("balance", provider.uint256(), null);
    try builder.add("code", provider.bytesMemory(), null);
    try builder.add("codehash", try provider.fixedBytes(32), null);
    try builder.add("call", try plainFunction(
        provider,
        &.{provider.bytesMemory()},
        &.{ provider.boolean(), provider.bytesMemory() },
        .BareCall,
        .Payable,
        .{},
    ), null);
    try builder.add("callcode", try plainFunction(
        provider,
        &.{provider.bytesMemory()},
        &.{ provider.boolean(), provider.bytesMemory() },
        .BareCallCode,
        .Payable,
        .{},
    ), null);
    try builder.add("delegatecall", try plainFunction(
        provider,
        &.{provider.bytesMemory()},
        &.{ provider.boolean(), provider.bytesMemory() },
        .BareDelegateCall,
        .NonPayable,
        .{},
    ), null);
    try builder.add("staticcall", try plainFunction(
        provider,
        &.{provider.bytesMemory()},
        &.{ provider.boolean(), provider.bytesMemory() },
        .BareStaticCall,
        .View,
        .{},
    ), null);
    if (address.state_mutability == .Payable) {
        try builder.add("send", try plainFunction(
            provider,
            &.{provider.uint256()},
            &.{provider.boolean()},
            .Send,
            .NonPayable,
            .{},
        ), null);
        try builder.add("transfer", try plainFunction(
            provider,
            &.{provider.uint256()},
            &.{},
            .Transfer,
            .NonPayable,
            .{},
        ), null);
    }
}

fn appendArrayMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    type_ref: *const Types.Type,
    array: Types.ArrayType,
) BehaviorError!void {
    if (array.isString()) return;
    try builder.add("length", provider.uint256(), null);
    if (!array.isDynamicallySized() or array.reference.location != .Storage) return;
    const self_pointer = try provider.withLocation(type_ref, .Storage, true);
    const push_empty = try provider.function(
        &.{self_pointer},
        &.{array.base_type},
        &.{""},
        &.{""},
        .ArrayPush,
        .NonPayable,
        null,
        .{},
    );
    try builder.add(
        "push",
        try provider.withBoundFirstArgument(push_empty),
        null,
    );
    const push_value = try provider.function(
        &.{ self_pointer, array.base_type },
        &.{},
        &.{ "", "" },
        &.{},
        .ArrayPush,
        .NonPayable,
        null,
        .{},
    );
    try builder.add(
        "push",
        try provider.withBoundFirstArgument(push_value),
        null,
    );
    const pop = try provider.function(
        &.{self_pointer},
        &.{},
        &.{""},
        &.{},
        .ArrayPop,
        .NonPayable,
        null,
        .{},
    );
    try builder.add("pop", try provider.withBoundFirstArgument(pop), null);
}

fn appendContractMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    contract_type: Types.ContractType,
) BehaviorError!void {
    if (contract_type.is_super or
        contract_type.declaration.nodeKind() != .contract_definition or
        contract_type.declaration.payload.contract_definition.contract_kind == .Library)
        return;
    var seen = std.AutoHashMap(u32, void).init(builder.allocator);
    defer seen.deinit();
    const annotation = ASTAnnotations.annotationConst(contract_type.declaration);
    const bases = if (annotation) |entry| switch (entry.*) {
        .contract_definition => |value| value.linearized_base_contracts,
        else => &.{contract_type.declaration},
    } else &.{contract_type.declaration};
    const contracts = if (bases.len == 0) &.{contract_type.declaration} else bases;
    for (contracts) |contract| {
        if (contract.nodeKind() != .contract_definition) return error.InvalidType;
        for (contract.payload.contract_definition.sub_nodes) |declaration| {
            const function_type: ?*const Types.Type = switch (declaration.payload) {
                .function_definition => |definition| if (definition.ordinary() and
                    declaration.isPublic())
                    try provider.functionFromDefinition(declaration, .External)
                else
                    null,
                .variable_declaration => if (declaration.isPublic())
                    try provider.functionFromVariable(declaration)
                else
                    null,
                else => null,
            };
            const candidate = function_type orelse continue;
            const callable = try asExternallyCallableFunction(
                provider,
                candidate.payload.Function,
                false,
            );
            const signature = try externalSignatureAlloc(
                provider,
                builder.allocator,
                callable.payload.Function,
            );
            defer builder.allocator.free(signature);
            const selector = FunctionSelector.selectorFromSignatureU32(signature);
            if (seen.contains(selector)) continue;
            try seen.put(selector, {});
            try builder.add(
                declaration.declarationConst().?.name,
                callable,
                declaration,
            );
        }
    }
}

fn appendStructMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    structure: Types.StructType,
) BehaviorError!void {
    if (structure.declaration.nodeKind() != .struct_definition) return error.InvalidType;
    for (structure.declaration.payload.struct_definition.members) |member| {
        const member_type = try variableDeclarationType(member);
        if (structure.reference.location != .Storage and
            try containsNestedMapping(provider, member_type)) return error.InvalidType;
        try builder.add(
            member.payload.variable_declaration.declaration.name,
            try provider.withLocationIfReference(
                structure.reference.location,
                member_type,
                false,
            ),
            member,
        );
    }
}

fn appendFunctionMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    type_ref: *const Types.Type,
    function: Types.FunctionType,
    current_scope: ?*const AST.Node,
) BehaviorError!void {
    switch (function.kind) {
        .Declaration => if (function.declaration != null and
            declarationIsPartOfExternalInterface(function.declaration.?))
            try builder.add("selector", try provider.fixedBytes(4), null),
        .Internal => if (function.declaration) |declaration| {
            const scope = current_scope orelse return;
            if (declaration.nodeKind() != .function_definition) return;
            const annotation = ASTAnnotations.annotationConst(declaration) orelse return;
            const defining_contract = (ASTAnnotations.scopableConst(annotation) orelse
                return).contract orelse return;
            if (scope != defining_contract and
                declarationIsPartOfExternalInterface(declaration) and
                scope.nodeKind() == .contract_definition and
                contractDerivesFrom(scope, defining_contract))
                try builder.add("selector", try provider.fixedBytes(4), null);
        },
        .External, .Creation, .BareCall, .BareCallCode, .BareDelegateCall, .BareStaticCall => {
            if (function.kind == .External) {
                try builder.add("selector", try provider.fixedBytes(4), null);
                try builder.add("address", provider.address(), null);
            }
            if (function.kind != .BareDelegateCall and
                function.state_mutability == .Payable)
            {
                const value_set = try provider.copyAndSetCallOptions(
                    type_ref,
                    false,
                    true,
                    false,
                );
                try builder.add("value", try provider.function(
                    &.{provider.uint256()},
                    &.{value_set},
                    &.{""},
                    &.{""},
                    .SetValue,
                    .Pure,
                    null,
                    function.options,
                ), null);
            }
            if (function.kind != .Creation) {
                const gas_set = try provider.copyAndSetCallOptions(
                    type_ref,
                    true,
                    false,
                    false,
                );
                try builder.add("gas", try provider.function(
                    &.{provider.uint256()},
                    &.{gas_set},
                    &.{""},
                    &.{""},
                    .SetGas,
                    .Pure,
                    null,
                    function.options,
                ), null);
            }
        },
        .DelegateCall => if (function.declaration) |declaration| {
            if (declaration.nodeKind() != .function_definition) return;
            if (!declaration.isPublic()) return error.InvalidType;
            const scope = nodeScope(declaration) orelse
                return error.InvalidType;
            if (scope.nodeKind() != .contract_definition or
                scope.payload.contract_definition.contract_kind != .Library)
                return error.InvalidType;
            try builder.add("selector", try provider.fixedBytes(4), null);
        },
        .Error => try builder.add("selector", try provider.fixedBytes(4), null),
        .Event => if (function.declaration != null and
            function.declaration.?.nodeKind() == .event_definition and
            !function.declaration.?.payload.event_definition.anonymous)
            try builder.add("selector", try provider.fixedBytes(32), null),
        else => {},
    }
}

fn declarationIsPartOfExternalInterface(declaration: *const AST.Node) bool {
    return switch (declaration.payload) {
        .function_definition => |function| function.ordinary() and
            declaration.isPublic(),
        .variable_declaration => declaration.isPublic(),
        else => false,
    };
}

fn appendTypeTypeMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    actual_type: *const Types.Type,
    current_scope: ?*const AST.Node,
) BehaviorError!void {
    switch (actual_type.payload) {
        .Contract => |contract| try appendContractTypeMembers(
            provider,
            builder,
            contract,
            current_scope,
        ),
        .Enum => |enumeration| {
            if (enumeration.declaration.nodeKind() != .enum_definition)
                return error.InvalidType;
            for (enumeration.declaration.payload.enum_definition.members) |member|
                try builder.add(
                    member.payload.enum_value.declaration.name,
                    actual_type,
                    member,
                );
        },
        .UserDefinedValueType => |value| {
            const underlying = value.underlying_type orelse return error.InvalidType;
            try builder.add("wrap", try plainFunction(
                provider,
                &.{underlying},
                &.{actual_type},
                .Wrap,
                .Pure,
                .{},
            ), null);
            try builder.add("unwrap", try plainFunction(
                provider,
                &.{actual_type},
                &.{underlying},
                .Unwrap,
                .Pure,
                .{},
            ), null);
        },
        .Array => |array| if (array.isByteArrayOrString())
            try builder.add("concat", try plainFunction(
                provider,
                &.{},
                &.{if (array.isString()) provider.stringMemory() else provider.bytesMemory()},
                if (array.isString()) .StringConcat else .BytesConcat,
                .Pure,
                .withArbitraryParameters(),
            ), null),
        else => {},
    }
}

const ContractNameAccess = enum { local, foreign, library };

fn appendContractTypeMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    contract_type: Types.ContractType,
    current_scope: ?*const AST.Node,
) BehaviorError!void {
    const contract = contract_type.declaration;
    if (contract.nodeKind() != .contract_definition) return error.InvalidType;
    if (contract_type.is_super) {
        const annotation = ASTAnnotations.annotationConst(contract) orelse return error.InvalidType;
        const bases = switch (annotation.*) {
            .contract_definition => |value| value.linearized_base_contracts,
            else => return error.InvalidType,
        };
        if (bases.len == 0) return error.InvalidType;
        for (bases[1..]) |base| {
            if (base.nodeKind() != .contract_definition) return error.InvalidType;
            for (base.payload.contract_definition.sub_nodes) |declaration| {
                if (declaration.nodeKind() != .function_definition or
                    !declaration.isVisibleInDerivedContracts() or
                    !declaration.payload.function_definition.implemented()) continue;
                const candidate = try provider.functionFromDefinition(declaration, .Internal);
                if (memberFunctionExists(
                    builder.items.items,
                    declaration.declarationConst().?.name,
                    candidate.payload.Function,
                )) continue;
                try builder.add(
                    declaration.declarationConst().?.name,
                    candidate,
                    declaration,
                );
            }
        }
        return;
    }
    const is_library = contract.payload.contract_definition.contract_kind == .Library;
    const deriving_scope = if (current_scope) |scope|
        scope.nodeKind() == .contract_definition and contractDerivesFrom(scope, contract)
    else
        false;
    const access: ContractNameAccess = if (is_library)
        .library
    else if (deriving_scope)
        .local
    else
        .foreign;
    for (contract.payload.contract_definition.sub_nodes) |declaration| {
        if (declaration.nodeKind() == .modifier_definition) continue;
        const data = declaration.declarationConst() orelse continue;
        if (data.name.len == 0 or !visibleViaContractName(declaration, access)) continue;
        const member_type = (try declarationTypeViaContractName(
            provider,
            declaration,
            access,
        )) orelse continue;
        try builder.add(data.name, member_type, declaration);
    }
}

fn memberFunctionExists(
    members: []const Types.Member,
    name: []const u8,
    function: Types.FunctionType,
) bool {
    for (members) |member| {
        if (!std.mem.eql(u8, member.name, name)) continue;
        const existing = member.type_ref.asFunction() orelse continue;
        if (functionHasEqualParameterTypes(existing.*, function)) return true;
    }
    return false;
}

fn contractDerivesFrom(contract: *const AST.Node, base: *const AST.Node) bool {
    if (contract == base) return true;
    const annotation = ASTAnnotations.annotationConst(contract) orelse return false;
    const bases = switch (annotation.*) {
        .contract_definition => |value| value.linearized_base_contracts,
        else => return false,
    };
    for (bases) |candidate| if (candidate == base) return true;
    return false;
}

fn visibleViaContractName(
    declaration: *const AST.Node,
    access: ContractNameAccess,
) bool {
    return switch (declaration.payload) {
        .function_definition => |function| function.ordinary() and switch (access) {
            .local => declaration.effectiveVisibility() != .Private,
            .foreign => declaration.isPublic(),
            .library => declaration.effectiveVisibility() != .Private,
        },
        .variable_declaration => switch (access) {
            .local => declaration.effectiveVisibility() != .Private,
            .foreign => false,
            .library => @intFromEnum(declaration.effectiveVisibility() orelse
                return false) >= @intFromEnum(AST.Visibility.Internal),
        },
        .struct_definition,
        .enum_definition,
        .user_defined_value_type_definition,
        .event_definition,
        .error_definition,
        => true,
        else => false,
    };
}

fn declarationTypeViaContractName(
    provider: *TypeProviderModule.TypeProvider,
    declaration: *const AST.Node,
    access: ContractNameAccess,
) BehaviorError!?*const Types.Type {
    return switch (declaration.payload) {
        .function_definition => |function| switch (access) {
            .library => if (declaration.isPublic())
                asExternallyCallableFunction(
                    provider,
                    (try provider.functionFromDefinition(declaration, .External)).payload.Function,
                    true,
                )
            else
                provider.functionFromDefinition(declaration, .Internal),
            .local => if (declaration.isVisibleInContract() and
                function.implemented())
                provider.functionFromDefinition(declaration, .Internal)
            else
                provider.functionFromDefinition(declaration, .Declaration),
            .foreign => provider.functionFromDefinition(declaration, .Declaration),
        },
        .variable_declaration => variableDeclarationType(declaration),
        .event_definition => provider.functionFromEvent(declaration),
        .error_definition => provider.functionFromError(declaration),
        .contract_definition => provider.typeType(try provider.contract(declaration, false)),
        .struct_definition => provider.typeType(try provider.structType(declaration, .Storage)),
        .enum_definition => provider.typeType(try provider.enumType(declaration)),
        .user_defined_value_type_definition => provider.typeType(
            try provider.userDefinedValueType(declaration, null),
        ),
        .magic_variable_declaration => |magic| if (magic.type_ref) |erased|
            @ptrCast(@alignCast(erased))
        else
            null,
        else => null,
    };
}

fn appendModuleMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    module: Types.ModuleType,
) BehaviorError!void {
    if (module.source_unit.nodeKind() != .source_unit) return error.InvalidType;
    const annotation = ASTAnnotations.annotationConst(module.source_unit) orelse
        return error.InvalidType;
    const source = switch (annotation.*) {
        .source_unit => |value| value,
        else => return error.InvalidType,
    };
    if (!source.exported_symbols.isSet()) return;
    const symbols = (source.exported_symbols.get() catch return error.InvalidType).*;
    for (symbols) |symbol|
        for (symbol.declarations) |declaration| {
            const type_ref = (try declarationType(provider, declaration)) orelse continue;
            try builder.add(symbol.name, type_ref, declaration);
        };
}

fn declarationType(
    provider: *TypeProviderModule.TypeProvider,
    declaration: *const AST.Node,
) BehaviorError!?*const Types.Type {
    return switch (declaration.payload) {
        .function_definition => provider.functionFromDefinition(declaration, .Internal),
        .variable_declaration => variableDeclarationType(declaration),
        .event_definition => provider.functionFromEvent(declaration),
        .error_definition => provider.functionFromError(declaration),
        .contract_definition => provider.typeType(try provider.contract(declaration, false)),
        .struct_definition => provider.typeType(try provider.structType(declaration, .Storage)),
        .enum_definition => provider.typeType(try provider.enumType(declaration)),
        .user_defined_value_type_definition => provider.typeType(
            try provider.userDefinedValueType(declaration, null),
        ),
        .import_directive => blk: {
            const annotation = ASTAnnotations.annotationConst(declaration) orelse
                break :blk null;
            const source_unit = switch (annotation.*) {
                .import => |value| value.source_unit,
                else => null,
            } orelse break :blk null;
            break :blk provider.module(source_unit);
        },
        .magic_variable_declaration => |magic| if (magic.type_ref) |erased|
            @ptrCast(@alignCast(erased))
        else
            null,
        else => null,
    };
}

fn appendMagicMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    magic: Types.MagicType,
) BehaviorError!void {
    switch (magic.kind) {
        .Block => {
            try builder.add("coinbase", provider.payableAddress(), null);
            try builder.add("timestamp", provider.uint256(), null);
            try builder.add("blockhash", try plainFunction(
                provider,
                &.{provider.uint256()},
                &.{try provider.fixedBytes(32)},
                .BlockHash,
                .View,
                .{},
            ), null);
            for (&[_][]const u8{
                "difficulty",
                "prevrandao",
                "number",
                "gaslimit",
                "chainid",
                "basefee",
                "blobbasefee",
            }) |name| try builder.add(name, provider.uint256(), null);
        },
        .Message => {
            try builder.add("sender", provider.address(), null);
            try builder.add("gas", provider.uint256(), null);
            try builder.add("value", provider.uint256(), null);
            try builder.add("data", provider.bytesCalldata(), null);
            try builder.add("sig", try provider.fixedBytes(4), null);
        },
        .Transaction => {
            try builder.add("origin", provider.address(), null);
            try builder.add("gasprice", provider.uint256(), null);
        },
        .ABI => try appendAbiMagicMembers(provider, builder),
        .Error => {},
        .MetaType => {
            const argument = magic.type_argument orelse return error.InvalidType;
            switch (argument.payload) {
                .Contract => |contract| {
                    if (contract.declaration.nodeKind() != .contract_definition)
                        return error.InvalidType;
                    const definition = contract.declaration.payload.contract_definition;
                    if (definition.contract_kind == .Contract and !definition.abstract) {
                        try builder.add("creationCode", provider.bytesMemory(), null);
                        try builder.add("runtimeCode", provider.bytesMemory(), null);
                    } else {
                        try builder.add("interfaceId", try provider.fixedBytes(4), null);
                    }
                    try builder.add("name", provider.stringMemory(), null);
                },
                .Integer, .Enum => {
                    try builder.add("min", argument, null);
                    try builder.add("max", argument, null);
                },
                else => return error.InvalidType,
            }
        },
    }
}

fn appendAbiMagicMembers(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
) BehaviorError!void {
    const arbitrary = Types.FunctionOptions.withArbitraryParameters();
    try builder.add("encode", try plainFunction(
        provider,
        &.{},
        &.{provider.bytesMemory()},
        .ABIEncode,
        .Pure,
        arbitrary,
    ), null);
    try builder.add("encodePacked", try plainFunction(
        provider,
        &.{},
        &.{provider.bytesMemory()},
        .ABIEncodePacked,
        .Pure,
        arbitrary,
    ), null);
    try builder.add("encodeWithSelector", try plainFunction(
        provider,
        &.{try provider.fixedBytes(4)},
        &.{provider.bytesMemory()},
        .ABIEncodeWithSelector,
        .Pure,
        arbitrary,
    ), null);
    try builder.add("encodeCall", try plainFunction(
        provider,
        &.{},
        &.{provider.bytesMemory()},
        .ABIEncodeCall,
        .Pure,
        arbitrary,
    ), null);
    try builder.add("encodeWithSignature", try plainFunction(
        provider,
        &.{provider.stringMemory()},
        &.{provider.bytesMemory()},
        .ABIEncodeWithSignature,
        .Pure,
        arbitrary,
    ), null);
    try builder.add("decode", try plainFunction(
        provider,
        &.{},
        &.{},
        .ABIDecode,
        .Pure,
        arbitrary,
    ), null);
}

pub fn membersAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
    current_scope: ?*const AST.Node,
) BehaviorError!Types.OwnedMemberList {
    var native = try nativeMembersAlloc(provider, allocator, type_ref, current_scope);
    errdefer native.deinit();
    const scope = current_scope orelse return native;
    var attached = try attachedFunctionsAlloc(provider, allocator, type_ref, scope);
    defer attached.deinit();
    if (attached.items.len == 0) return native;
    const combined = try allocator.alloc(
        Types.Member,
        native.items.len + attached.items.len,
    );
    @memcpy(combined[0..native.items.len], native.items);
    @memcpy(combined[native.items.len..], attached.items);
    native.deinit();
    return .{ .allocator = allocator, .items = combined };
}

pub fn attachedFunctionsAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
    scope: *const AST.Node,
) BehaviorError!Types.OwnedMemberList {
    var builder = MemberBuilder{ .allocator = allocator };
    errdefer builder.deinit();
    const directives = try usingForDirectivesForTypeAlloc(
        provider,
        allocator,
        type_ref,
        scope,
    );
    defer allocator.free(directives);
    var seen = std.AutoHashMap(AttachedFunctionKey, void).init(allocator);
    defer seen.deinit();
    for (directives) |directive| {
        for (directive.payload.using_for_directive.functions_and_operators) |entry| {
            if (entry.operator != null) continue;
            const declaration = referencedDeclaration(entry.function_or_library) orelse
                return error.InvalidType;
            if (declaration.nodeKind() == .contract_definition) {
                if (declaration.payload.contract_definition.contract_kind != .Library)
                    return error.InvalidType;
                for (declaration.payload.contract_definition.sub_nodes) |function| {
                    if (function.nodeKind() != .function_definition or
                        !function.payload.function_definition.ordinary() or
                        @intFromEnum(function.effectiveVisibility() orelse
                            continue) < @intFromEnum(AST.Visibility.Internal) or
                        function.payload.function_definition.callable.parameters.payload.parameter_list.parameters.len == 0)
                        continue;
                    try appendAttachedFunction(
                        provider,
                        &builder,
                        &seen,
                        type_ref,
                        function,
                        function.declarationConst().?.name,
                    );
                }
            } else {
                if (declaration.nodeKind() != .function_definition) return error.InvalidType;
                try appendAttachedFunction(
                    provider,
                    &builder,
                    &seen,
                    type_ref,
                    declaration,
                    identifierPathLastName(entry.function_or_library) orelse
                        declaration.declarationConst().?.name,
                );
            }
        }
    }
    return builder.finish();
}

const AttachedFunctionKey = struct {
    name_hash: u64,
    declaration: *const AST.Node,
};

fn appendAttachedFunction(
    provider: *TypeProviderModule.TypeProvider,
    builder: *MemberBuilder,
    seen: *std.AutoHashMap(AttachedFunctionKey, void),
    receiver: *const Types.Type,
    declaration: *const AST.Node,
    name: []const u8,
) BehaviorError!void {
    const function_type = try functionTypeWhenAttached(provider, declaration);
    const bound = try provider.withBoundFirstArgument(function_type);
    const expected_self = bound.asFunction().?.selfType() orelse return error.InvalidType;
    if (!isImplicitlyConvertibleTo(receiver, expected_self)) return;
    const key = AttachedFunctionKey{
        .name_hash = std.hash.Wyhash.hash(0, name),
        .declaration = declaration,
    };
    if (seen.contains(key)) return;
    try seen.put(key, {});
    try builder.add(name, bound, declaration);
}

fn functionTypeWhenAttached(
    provider: *TypeProviderModule.TypeProvider,
    declaration: *const AST.Node,
) BehaviorError!*const Types.Type {
    if (declaration.nodeKind() != .function_definition) return error.InvalidType;
    const enclosing = nodeScope(declaration);
    if (enclosing != null and enclosing.?.nodeKind() == .contract_definition and
        enclosing.?.payload.contract_definition.contract_kind == .Library)
    {
        if (declaration.isPublic())
            return asExternallyCallableFunction(
                provider,
                (try provider.functionFromDefinition(declaration, .External)).payload.Function,
                true,
            );
    }
    return provider.functionFromDefinition(declaration, .Internal);
}

pub fn operatorDefinitionsAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
    operator: Types.Token,
    scope: *const AST.Node,
    unary: bool,
) BehaviorError![]const *const AST.Node {
    return operatorDefinitionsWithCompatibilityIdsAlloc(
        provider,
        allocator,
        CompatibilityIdResolver.legacyNodeIds(),
        type_ref,
        operator,
        scope,
        unary,
    );
}

pub fn operatorDefinitionsWithCompatibilityIdsAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    type_ref: *const Types.Type,
    operator: Types.Token,
    scope: *const AST.Node,
    unary: bool,
) BehaviorError![]const *const AST.Node {
    if (typeDefinition(type_ref) == null)
        return allocator.alloc(*const AST.Node, 0);
    const directives = try usingForDirectivesForTypeAlloc(
        provider,
        allocator,
        type_ref,
        scope,
    );
    defer allocator.free(directives);
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    for (directives) |directive|
        for (directive.payload.using_for_directive.functions_and_operators) |entry| {
            if (entry.operator == null or entry.operator.? != operator) continue;
            const declaration = referencedDeclaration(entry.function_or_library) orelse
                return error.InvalidType;
            if (declaration.nodeKind() != .function_definition) return error.InvalidType;
            const attached_type = try functionTypeWhenAttached(provider, declaration);
            const function = attached_type.asFunction() orelse return error.InvalidType;
            const parameters = declaration.payload.function_definition.callable.parameters.payload.parameter_list.parameters;
            const expected_parameter_count: usize = if (unary) 1 else 2;
            if (function.parameter_types.len == 0 or
                !equals(type_ref, function.parameter_types[0]) or
                parameters.len != expected_parameter_count) continue;
            var duplicate = false;
            for (result.items) |existing| if (existing == declaration) {
                duplicate = true;
                break;
            };
            if (!duplicate) try result.append(allocator, declaration);
        };
    std.mem.sort(*const AST.Node, result.items, compatibility_ids, struct {
        fn lessThan(
            resolver: CompatibilityIdResolver,
            left: *const AST.Node,
            right: *const AST.Node,
        ) bool {
            return resolver.id(left).? < resolver.id(right).?;
        }
    }.lessThan);
    return result.toOwnedSlice(allocator);
}

fn usingForDirectivesForTypeAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
    scope: *const AST.Node,
) BehaviorError![]const *const AST.Node {
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    var seen = std.AutoHashMap(*const AST.Node, void).init(allocator);
    defer seen.deinit();
    const source_unit: *const AST.Node = switch (scope.nodeKind()) {
        .source_unit => scope,
        .contract_definition => blk: {
            try appendUsingDirectivesFromNodes(
                provider,
                allocator,
                &result,
                &seen,
                type_ref,
                scope.payload.contract_definition.sub_nodes,
                false,
            );
            break :blk sourceUnitForNode(scope) orelse return error.InvalidType;
        },
        else => return error.InvalidType,
    };
    try appendUsingDirectivesFromNodes(
        provider,
        allocator,
        &result,
        &seen,
        type_ref,
        source_unit.payload.source_unit.nodes,
        false,
    );
    if (typeDefinition(type_ref)) |definition| {
        if (sourceUnitForNode(definition)) |definition_source|
            try appendUsingDirectivesFromNodes(
                provider,
                allocator,
                &result,
                &seen,
                type_ref,
                definition_source.payload.source_unit.nodes,
                true,
            );
    }
    return result.toOwnedSlice(allocator);
}

fn appendUsingDirectivesFromNodes(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    output: *std.ArrayList(*const AST.Node),
    seen: *std.AutoHashMap(*const AST.Node, void),
    type_ref: *const Types.Type,
    nodes: AST.NodeList,
    globals_only: bool,
) BehaviorError!void {
    for (nodes) |node| {
        if (node.nodeKind() != .using_for_directive) continue;
        const directive = node.payload.using_for_directive;
        if (globals_only and (!directive.global or directive.type_name == null)) continue;
        if (seen.contains(node) or
            !(try usingDirectiveMatches(provider, type_ref, directive))) continue;
        try seen.put(node, {});
        try output.append(allocator, node);
    }
}

fn usingDirectiveMatches(
    provider: *TypeProviderModule.TypeProvider,
    type_ref: *const Types.Type,
    directive: AST.UsingForDirective,
) BehaviorError!bool {
    const type_name = directive.type_name orelse return true;
    const annotation = ASTAnnotations.annotationConst(type_name) orelse return error.InvalidType;
    const declared_type = switch (annotation.*) {
        .type_name => |value| value.type_ref orelse return error.InvalidType,
        else => return error.InvalidType,
    };
    const location = if (type_ref.asReference()) |reference| reference.location else .Storage;
    const normalized_actual = try provider.withLocationIfReference(location, type_ref, true);
    const normalized_declared = try provider.withLocationIfReference(
        location,
        declared_type,
        true,
    );
    return equals(normalized_actual, normalized_declared);
}

fn sourceUnitForNode(node: *const AST.Node) ?*const AST.Node {
    var current = node;
    var depth: usize = 0;
    while (depth < 256) : (depth += 1) {
        if (current.nodeKind() == .source_unit) return current;
        current = nodeScope(current) orelse return null;
    }
    return null;
}

fn referencedDeclaration(node: *const AST.Node) ?*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .identifier_path => |value| value.referenced_declaration,
        .identifier => |value| value.referenced_declaration,
        .member_access => |value| value.referenced_declaration,
        else => null,
    };
}

fn identifierPathLastName(node: *const AST.Node) ?[]const u8 {
    return switch (node.payload) {
        .identifier_path => |path| if (path.path.len == 0) null else path.path[path.path.len - 1],
        .identifier => |identifier| identifier.name,
        else => null,
    };
}

const stack_uint256 = Types.Type{ .payload = .{ .Integer = .{
    .bits = 256,
    .modifier = .Unsigned,
} } };
const stack_uint32 = Types.Type{ .payload = .{ .Integer = .{
    .bits = 32,
    .modifier = .Unsigned,
} } };
const stack_address = Types.Type{ .payload = .{ .Address = .{
    .state_mutability = .NonPayable,
} } };
const stack_payable_address = Types.Type{ .payload = .{ .Address = .{
    .state_mutability = .Payable,
} } };
const stack_bytes32 = Types.Type{ .payload = .{ .FixedBytes = .{ .bytes = 32 } } };

/// Allocator-owned counterpart of `Type::stackItems()`. Every item name is
/// owned, including empty names, so teardown is uniform and independent of
/// whether a layout component came from a static spelling or a tuple index.
pub const OwnedStackItems = struct {
    allocator: std.mem.Allocator,
    items: []Types.StackItem,

    pub fn deinit(self: *OwnedStackItems) void {
        for (self.items) |item| self.allocator.free(item.name);
        self.allocator.free(self.items);
        self.* = undefined;
    }
};

/// Returns the recursive stack-layout components defined by upstream
/// `Type::makeStackItems()`. Primitive stack-part types use immutable
/// structural equivalents of TypeProvider's canonical elementary types;
/// user types retain their provider-owned identity.
pub fn stackItemsAlloc(
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
) QueryError!OwnedStackItems {
    var items: std.ArrayList(Types.StackItem) = .empty;
    errdefer {
        for (items.items) |item| allocator.free(item.name);
        items.deinit(allocator);
    }
    try appendStackItems(allocator, &items, type_ref);
    return .{
        .allocator = allocator,
        .items = try items.toOwnedSlice(allocator),
    };
}

fn appendStackItem(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(Types.StackItem),
    name: []const u8,
    type_ref: ?*const Types.Type,
) std.mem.Allocator.Error!void {
    const owned_name = try allocator.dupe(u8, name);
    errdefer allocator.free(owned_name);
    try items.append(allocator, .{ .name = owned_name, .type_ref = type_ref });
}

fn appendStackItems(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(Types.StackItem),
    type_ref: *const Types.Type,
) QueryError!void {
    switch (type_ref.payload) {
        .StringLiteral, .Modifier, .Magic, .Module => {},
        .Array => |array| switch (array.reference.location) {
            .CallData => {
                try appendStackItem(allocator, items, "offset", &stack_uint256);
                if (array.isDynamicallySized())
                    try appendStackItem(allocator, items, "length", &stack_uint256);
            },
            .Memory => try appendStackItem(allocator, items, "mpos", &stack_uint256),
            .Storage => try appendStackItem(allocator, items, "slot", &stack_uint256),
            .Transient => return error.UnsupportedTransientReference,
        },
        .ArraySlice => {
            try appendStackItem(allocator, items, "offset", &stack_uint256);
            try appendStackItem(allocator, items, "length", &stack_uint256);
        },
        .Contract => |contract| {
            if (!contract.is_super) try appendStackItem(
                allocator,
                items,
                "address",
                if (contractIsPayable(contract.declaration))
                    &stack_payable_address
                else
                    &stack_address,
            );
        },
        .Struct => |structure| switch (structure.reference.location) {
            .CallData => try appendStackItem(allocator, items, "offset", &stack_uint256),
            .Memory => try appendStackItem(allocator, items, "mpos", &stack_uint256),
            .Storage => try appendStackItem(allocator, items, "slot", &stack_uint256),
            .Transient => return error.UnsupportedTransientReference,
        },
        .UserDefinedValueType => |value| try appendStackItems(
            allocator,
            items,
            value.underlying_type orelse return error.InvalidType,
        ),
        .Tuple => |tuple| {
            for (tuple.components, 1..) |component, index| {
                const component_type = component orelse continue;
                const name = try std.fmt.allocPrint(allocator, "component_{d}", .{index});
                defer allocator.free(name);
                try appendStackItem(allocator, items, name, component_type);
            }
        },
        .Function => |function| try appendFunctionStackItems(allocator, items, function),
        .Mapping => try appendStackItem(allocator, items, "slot", &stack_uint256),
        .TypeType => |type_type| switch (type_type.actual_type.payload) {
            .Contract => |contract| {
                if (contract.declaration.nodeKind() == .contract_definition and
                    contract.declaration.payload.contract_definition.contract_kind == .Library)
                {
                    if (contract.is_super) return error.InvalidType;
                    try appendStackItem(allocator, items, "address", &stack_address);
                }
            },
            else => {},
        },
        else => try appendStackItem(allocator, items, "", null),
    }
}

fn appendFunctionStackItems(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(Types.StackItem),
    function: Types.FunctionType,
) QueryError!void {
    var kind = function.kind;
    if (kind == .SetGas or kind == .SetValue) {
        if (function.return_parameter_types.len != 1) return error.InvalidType;
        const underlying = function.return_parameter_types[0].asFunction() orelse
            return error.InvalidType;
        kind = underlying.kind;
    }

    switch (kind) {
        .External, .DelegateCall => {
            try appendStackItem(allocator, items, "address", &stack_address);
            try appendStackItem(allocator, items, "functionSelector", &stack_uint32);
        },
        .BareCall,
        .BareCallCode,
        .BareDelegateCall,
        .BareStaticCall,
        .Transfer,
        .Send,
        => try appendStackItem(allocator, items, "address", &stack_address),
        .Internal => try appendStackItem(
            allocator,
            items,
            "functionIdentifier",
            &stack_uint256,
        ),
        .ArrayPush, .ArrayPop => if (!function.options.has_bound_first_argument)
            return error.InvalidType,
        else => {},
    }

    if (function.options.gas_set)
        try appendStackItem(allocator, items, "gas", &stack_uint256);
    if (function.options.value_set)
        try appendStackItem(allocator, items, "value", &stack_uint256);
    if (function.options.salt_set)
        try appendStackItem(allocator, items, "salt", &stack_bytes32);
    if (function.options.has_bound_first_argument) {
        if (function.parameter_types.len == 0) return error.InvalidType;
        try appendStackItem(allocator, items, "self", function.parameter_types[0]);
    }
}

/// Exact number of EVM stack words occupied by a Solidity value. The depth
/// guard turns malformed cyclic synthetic types into a query error rather
/// than recursing indefinitely.
pub fn sizeOnStack(type_ref: *const Types.Type) QueryError!usize {
    return sizeOnStackInner(type_ref, 0);
}

fn sizeOnStackInner(type_ref: *const Types.Type, depth: usize) QueryError!usize {
    if (depth >= 256) return error.InvalidType;
    return switch (type_ref.payload) {
        .StringLiteral, .Modifier, .Magic, .Module => 0,
        .Array => |array| switch (array.reference.location) {
            .CallData => if (array.isDynamicallySized()) 2 else 1,
            .Memory, .Storage => 1,
            .Transient => error.UnsupportedTransientReference,
        },
        .ArraySlice => 2,
        .Contract => |contract| if (contract.is_super) 0 else 1,
        .Struct => |structure| switch (structure.reference.location) {
            .CallData, .Memory, .Storage => 1,
            .Transient => error.UnsupportedTransientReference,
        },
        .UserDefinedValueType => |value| sizeOnStackInner(
            value.underlying_type orelse return error.InvalidType,
            depth + 1,
        ),
        .Tuple => |tuple| blk: {
            var size: usize = 0;
            for (tuple.components) |component| {
                const item_type = component orelse continue;
                size = std.math.add(
                    usize,
                    size,
                    try sizeOnStackInner(item_type, depth + 1),
                ) catch return error.Overflow;
            }
            break :blk size;
        },
        .Function => |function| functionSizeOnStack(function, depth),
        .TypeType => |type_type| switch (type_type.actual_type.payload) {
            .Contract => |contract| if (contract.declaration.nodeKind() == .contract_definition and
                contract.declaration.payload.contract_definition.contract_kind == .Library and
                !contract.is_super) 1 else 0,
            else => 0,
        },
        else => 1,
    };
}

fn functionSizeOnStack(function: Types.FunctionType, depth: usize) QueryError!usize {
    var kind = function.kind;
    if (kind == .SetGas or kind == .SetValue) {
        if (function.return_parameter_types.len != 1) return error.InvalidType;
        kind = (function.return_parameter_types[0].asFunction() orelse
            return error.InvalidType).kind;
    }
    var size: usize = switch (kind) {
        .External, .DelegateCall => 2,
        .BareCall,
        .BareCallCode,
        .BareDelegateCall,
        .BareStaticCall,
        .Transfer,
        .Send,
        .Internal,
        => 1,
        .ArrayPush, .ArrayPop => if (function.options.has_bound_first_argument)
            0
        else
            return error.InvalidType,
        else => 0,
    };
    if (function.options.gas_set) size += 1;
    if (function.options.value_set) size += 1;
    if (function.options.salt_set) size += 1;
    if (function.options.has_bound_first_argument) {
        if (function.parameter_types.len == 0) return error.InvalidType;
        size = std.math.add(
            usize,
            size,
            try sizeOnStackInner(function.parameter_types[0], depth + 1),
        ) catch return error.Overflow;
    }
    return size;
}

pub fn canBeStored(type_ref: *const Types.Type) bool {
    return switch (type_ref.payload) {
        .RationalNumber, .StringLiteral, .Tuple, .TypeType, .Modifier, .Magic, .Module, .InaccessibleDynamic => false,
        .Function => |value| value.kind == .Internal or value.kind == .External,
        .UserDefinedValueType => |value| canBeStored(
            value.underlying_type orelse return false,
        ),
        else => true,
    };
}

pub fn dataStoredIn(type_ref: *const Types.Type, location: Types.DataLocation) bool {
    if (type_ref.category() == .Mapping) return location == .Storage;
    const reference = type_ref.asReference() orelse return false;
    return reference.location == location;
}

pub fn isDynamicallySized(type_ref: *const Types.Type) bool {
    return switch (type_ref.payload) {
        .Array => |value| value.isDynamicallySized(),
        .ArraySlice => true,
        else => false,
    };
}

pub fn isDynamicallyEncoded(type_ref: *const Types.Type) bool {
    return switch (type_ref.payload) {
        .Array => |value| value.isDynamicallySized() or isDynamicallyEncoded(value.base_type),
        .ArraySlice => true,
        .Struct => |value| structHasDynamicMember(value.declaration),
        else => false,
    };
}

/// Size occupied by a value in the ABI head. Dynamically encoded values use
/// one offset word; statically encoded values occupy their full encoding.
pub fn calldataHeadSize(type_ref: *const Types.Type) QueryError!u32 {
    if (isDynamicallyEncoded(type_ref)) return 32;
    return calldataEncodedSize(type_ref, true);
}

/// Minimum number of bytes that must be present at the ABI tail for a
/// dynamically encoded value. This mirrors the virtual query used by the C++
/// decoder for its up-front bounds checks.
pub fn calldataEncodedTailSize(type_ref: *const Types.Type) QueryError!u32 {
    if (!isDynamicallyEncoded(type_ref)) return error.NotDynamicallyEncoded;
    return switch (type_ref.payload) {
        .Array => |array| if (array.isDynamicallySized())
            32
        else blk: {
            const raw = std.math.mul(
                u256,
                array.length.?,
                try calldataStride(array),
            ) catch return error.Overflow;
            if (raw > std.math.maxInt(u32)) return error.Overflow;
            break :blk @intCast(raw);
        },
        .ArraySlice => 32,
        .Struct => |structure| structCalldataTailSize(structure),
        else => error.InvalidType,
    };
}

/// One array element's stride in ABI calldata.
pub fn calldataStride(array: Types.ArrayType) QueryError!u32 {
    if (array.isByteArrayOrString()) return 1;
    return calldataHeadSize(array.base_type);
}

/// Reference values occupy one pointer word in memory; value types retain
/// their ordinary padded ABI width.
pub fn memoryHeadSize(type_ref: *const Types.Type) QueryError!u256 {
    return switch (type_ref.payload) {
        .Array, .ArraySlice, .Struct => 32,
        else => try calldataEncodedSize(type_ref, true),
    };
}

/// One array element's stride in Solidity's in-memory representation.
pub fn memoryStride(array: Types.ArrayType) QueryError!u256 {
    if (array.isByteArrayOrString()) return 1;
    return memoryHeadSize(array.base_type);
}

/// One array element's stride in Solidity storage.
pub fn storageStride(array: Types.ArrayType) QueryError!u8 {
    if (array.isByteArrayOrString()) return 1;
    return storageBytes(array.base_type);
}

/// Payload size of a statically sized value in memory. Dynamic reference
/// values are represented by a pointer and therefore have no fixed payload
/// size query at this level.
pub fn memoryDataSize(type_ref: *const Types.Type) QueryError!u256 {
    return switch (type_ref.payload) {
        .Array => |array| blk: {
            const length = array.length orelse return error.InvalidType;
            if (array.reference.location != .Memory or array.isByteArrayOrString())
                return error.InvalidType;
            break :blk std.math.mul(
                u256,
                length,
                try memoryHeadSize(array.base_type),
            ) catch return error.Overflow;
        },
        .Struct => |structure| structMemoryDataSize(structure),
        else => try calldataEncodedSize(type_ref, true),
    };
}

pub fn structMemberType(
    structure: Types.StructType,
    member_name: []const u8,
) QueryError!*const Types.Type {
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    for (structure.declaration.payload.struct_definition.members) |member| {
        if (member.nodeKind() != .variable_declaration) return error.InvalidType;
        if (!std.mem.eql(
            u8,
            member.payload.variable_declaration.declaration.name,
            member_name,
        )) continue;
        return variableDeclarationType(member);
    }
    return error.InvalidType;
}

pub fn structMemoryOffsetOfMember(
    structure: Types.StructType,
    member_name: []const u8,
) QueryError!u256 {
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    var offset: u256 = 0;
    for (structure.declaration.payload.struct_definition.members) |member| {
        if (member.nodeKind() != .variable_declaration) return error.InvalidType;
        if (std.mem.eql(
            u8,
            member.payload.variable_declaration.declaration.name,
            member_name,
        )) return offset;
        offset = std.math.add(
            u256,
            offset,
            try memoryHeadSize(try variableDeclarationType(member)),
        ) catch return error.Overflow;
    }
    return error.InvalidType;
}

pub fn structCalldataOffsetOfMember(
    structure: Types.StructType,
    member_name: []const u8,
) QueryError!u32 {
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    var offset: u32 = 0;
    for (structure.declaration.payload.struct_definition.members) |member| {
        if (member.nodeKind() != .variable_declaration) return error.InvalidType;
        if (std.mem.eql(
            u8,
            member.payload.variable_declaration.declaration.name,
            member_name,
        )) return offset;
        offset = std.math.add(
            u32,
            offset,
            try calldataHeadSize(try variableDeclarationType(member)),
        ) catch return error.Overflow;
    }
    return error.InvalidType;
}

pub fn structMemberTypesAlloc(
    allocator: std.mem.Allocator,
    structure: Types.StructType,
) QueryError![]const *const Types.Type {
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    const members = structure.declaration.payload.struct_definition.members;
    const result = try allocator.alloc(*const Types.Type, members.len);
    errdefer allocator.free(result);
    for (members, result) |member, *target|
        target.* = try variableDeclarationType(member);
    return result;
}

pub fn variableDeclarationType(node: *const AST.Node) QueryError!*const Types.Type {
    if (node.nodeKind() != .variable_declaration) return error.InvalidType;
    const annotation = ASTAnnotations.annotationConst(node) orelse
        return error.InvalidType;
    return switch (annotation.*) {
        .variable_declaration => |entry| entry.type_ref,
        else => null,
    } orelse error.InvalidType;
}

fn structCalldataTailSize(structure: Types.StructType) QueryError!u32 {
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    var size: u32 = 0;
    for (structure.declaration.payload.struct_definition.members) |member| {
        size = std.math.add(
            u32,
            size,
            try calldataHeadSize(try variableDeclarationType(member)),
        ) catch return error.Overflow;
    }
    return size;
}

fn structMemoryDataSize(structure: Types.StructType) QueryError!u256 {
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    var size: u256 = 0;
    for (structure.declaration.payload.struct_definition.members) |member| {
        size = std.math.add(
            u256,
            size,
            try memoryHeadSize(try variableDeclarationType(member)),
        ) catch return error.Overflow;
    }
    return size;
}

fn structHasDynamicMember(declaration: *const AST.Node) bool {
    if (declaration.nodeKind() != .struct_definition) return false;
    if (structRecursive(declaration)) return true;
    for (declaration.payload.struct_definition.members) |member| {
        const annotation = ASTAnnotations.annotationConst(member) orelse continue;
        const type_ref = switch (annotation.*) {
            .variable_declaration => |entry| entry.type_ref,
            else => null,
        } orelse continue;
        if (isDynamicallyEncoded(type_ref)) return true;
    }
    return false;
}

pub fn storageBytes(type_ref: *const Types.Type) QueryError!u8 {
    return switch (type_ref.payload) {
        .Address => 20,
        .Integer => |value| @intCast(value.bits / 8),
        .Bool => 1,
        .FixedPoint => |value| @intCast(value.total_bits / 8),
        .FixedBytes => |value| value.bytes,
        .Contract => |value| if (!value.is_super) 20 else error.NotStorable,
        .Enum => 1,
        .UserDefinedValueType => |value| if (value.underlying_type) |underlying|
            storageBytes(underlying)
        else
            error.InvalidType,
        .Function => |value| switch (value.kind) {
            .External => 24,
            .Internal => 8,
            else => error.NotStorable,
        },
        else => 32,
    };
}

pub fn storageSize(type_ref: *const Types.Type) QueryError!u256 {
    return storageSizeInner(type_ref, 0);
}

fn storageSizeInner(type_ref: *const Types.Type, depth: usize) QueryError!u256 {
    if (depth >= 256) return error.InvalidType;
    return switch (type_ref.payload) {
        .Array => |value| arrayStorageSize(value, depth + 1),
        .Struct => |value| structStorageSize(value, depth + 1),
        .Tuple, .TypeType, .Modifier => error.NotStorable,
        .Function => |value| if (value.kind == .Internal or value.kind == .External)
            1
        else
            error.NotStorable,
        else => 1,
    };
}

/// Conservative slot upper bound used by contract- and variable-level
/// validation. `error.Overflow` represents an exact mathematical result of
/// at least 2^256, which cannot be represented by the return type.
pub fn storageSizeUpperBound(type_ref: *const Types.Type) QueryError!u256 {
    return storageSizeUpperBoundInner(type_ref, 0);
}

fn storageSizeUpperBoundInner(
    type_ref: *const Types.Type,
    depth: usize,
) QueryError!u256 {
    if (depth >= 256) return error.InvalidType;
    return switch (type_ref.payload) {
        .Array => |value| blk: {
            const length = value.length orelse break :blk 1;
            const base = try storageSizeUpperBoundInner(value.base_type, depth + 1);
            break :blk std.math.mul(u256, length, base) catch return error.Overflow;
        },
        .Struct => |value| blk: {
            if (value.declaration.nodeKind() != .struct_definition) return error.InvalidType;
            // Upstream deliberately starts at one to retain an upper bound
            // even when every member later packs into an existing slot.
            var total: u256 = 1;
            for (value.declaration.payload.struct_definition.members) |member| {
                const annotation = ASTAnnotations.annotationConst(member) orelse
                    return error.InvalidType;
                const member_type = switch (annotation.*) {
                    .variable_declaration => |entry| entry.type_ref,
                    else => null,
                } orelse return error.InvalidType;
                const bound = try storageSizeUpperBoundInner(member_type, depth + 1);
                total = std.math.add(u256, total, bound) catch return error.Overflow;
            }
            break :blk total;
        },
        .UserDefinedValueType => |value| storageSizeUpperBoundInner(
            value.underlying_type orelse return error.InvalidType,
            depth + 1,
        ),
        .Tuple, .TypeType, .Modifier => error.NotStorable,
        else => 1,
    };
}

fn arrayStorageSize(array: Types.ArrayType, depth: usize) QueryError!u256 {
    const length = array.length orelse return 1;
    const base_bytes = try storageBytes(array.base_type);
    const size = if (base_bytes == 0)
        @as(u256, 1)
    else if (base_bytes < 32) blk: {
        const items_per_slot: u256 = 32 / base_bytes;
        const quotient = length / items_per_slot;
        break :blk std.math.add(
            u256,
            quotient,
            @intFromBool(length % items_per_slot != 0),
        ) catch return error.Overflow;
    } else std.math.mul(u256, length, try storageSizeInner(array.base_type, depth)) catch
        return error.Overflow;
    return @max(@as(u256, 1), size);
}

fn structStorageSize(structure: Types.StructType, depth: usize) QueryError!u256 {
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    var slot: u256 = 0;
    var byte_offset: u8 = 0;
    for (structure.declaration.payload.struct_definition.members) |member| {
        const member_type = try variableDeclarationType(member);
        if (!canBeStored(member_type)) return error.NotStorable;
        const bytes = try storageBytes(member_type);
        if (bytes > 32) return error.InvalidType;
        if (@as(u16, byte_offset) + bytes > 32) {
            slot = std.math.add(u256, slot, 1) catch return error.Overflow;
            byte_offset = 0;
        }
        const size = try storageSizeInner(member_type, depth);
        if (size == 1 and @as(u16, byte_offset) + bytes <= 32) {
            byte_offset += bytes;
        } else {
            slot = std.math.add(u256, slot, size) catch return error.Overflow;
            byte_offset = 0;
        }
    }
    if (byte_offset != 0)
        slot = std.math.add(u256, slot, 1) catch return error.Overflow;
    return @max(@as(u256, 1), slot);
}

pub fn calldataEncodedSize(type_ref: *const Types.Type, padded: bool) QueryError!u32 {
    return switch (type_ref.payload) {
        .Address => if (padded) 32 else 20,
        .Integer => |value| if (padded) 32 else @intCast(value.bits / 8),
        .Bool => if (padded) 32 else 1,
        .FixedPoint => |value| if (padded) 32 else @intCast(value.total_bits / 8),
        .FixedBytes => |value| if (padded) 32 else value.bytes,
        .Contract => |value| if (value.is_super)
            error.InvalidType
        else if (padded)
            32
        else
            20,
        .Enum => if (padded) 32 else 1,
        .UserDefinedValueType => |value| calldataEncodedSize(
            value.underlying_type orelse return error.InvalidType,
            padded,
        ),
        .Function => |value| blk: {
            const bytes: u32 = switch (value.kind) {
                .External => 24,
                .Internal => 8,
                else => return error.InvalidType,
            };
            break :blk if (padded) ((bytes + 31) / 32) * 32 else bytes;
        },
        .Array => |value| arrayCalldataSize(value, padded),
        .Struct => |value| structCalldataSize(value),
        .InaccessibleDynamic => 32,
        else => error.InvalidType,
    };
}

fn structCalldataSize(structure: Types.StructType) QueryError!u32 {
    if (isDynamicallyEncoded(&.{ .payload = .{ .Struct = structure } }))
        return error.DynamicEncoding;
    if (structure.declaration.nodeKind() != .struct_definition)
        return error.InvalidType;
    var size: u32 = 0;
    for (structure.declaration.payload.struct_definition.members) |member| {
        const annotation = ASTAnnotations.annotationConst(member) orelse
            return error.InvalidType;
        const member_type = switch (annotation.*) {
            .variable_declaration => |entry| entry.type_ref,
            else => null,
        } orelse return error.InvalidType;
        size = std.math.add(
            u32,
            size,
            try calldataEncodedSize(member_type, true),
        ) catch return error.Overflow;
    }
    return size;
}

fn arrayCalldataSize(array: Types.ArrayType, padded: bool) QueryError!u32 {
    if (array.length == null or isDynamicallyEncoded(array.base_type))
        return error.DynamicEncoding;
    const stride: u32 = if (array.isByteArrayOrString())
        1
    else if (isDynamicallyEncoded(array.base_type))
        32
    else
        try calldataEncodedSize(array.base_type, true);
    const raw = std.math.mul(u256, array.length.?, stride) catch return error.Overflow;
    if (raw > std.math.maxInt(u32)) return error.Overflow;
    const sized = if (padded) blk: {
        const rounded = std.math.add(u256, raw, 31) catch return error.Overflow;
        break :blk std.math.mul(u256, rounded / 32, 32) catch return error.Overflow;
    } else raw;
    if (sized > std.math.maxInt(u32)) return error.Overflow;
    return @intCast(sized);
}

pub fn leftAligned(type_ref: *const Types.Type) QueryError!bool {
    return switch (type_ref.payload) {
        .FixedBytes => true,
        .Address, .Integer, .Bool, .FixedPoint, .Enum => false,
        .UserDefinedValueType => |value| leftAligned(
            value.underlying_type orelse return error.InvalidType,
        ),
        .Contract => |value| if (value.is_super) error.InvalidType else false,
        .Function => |value| if (value.kind == .External)
            true
        else if (value.kind == .Internal)
            false
        else
            error.InvalidType,
        else => error.InvalidType,
    };
}

pub fn escapeIdentifierAlloc(
    allocator: std.mem.Allocator,
    identifier_value: []const u8,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (identifier_value) |byte| switch (byte) {
        '$' => try output.appendSlice(allocator, "$$$"),
        ',' => try output.appendSlice(allocator, "_$_"),
        '(' => try output.appendSlice(allocator, "$_"),
        ')' => try output.appendSlice(allocator, "_$"),
        else => try output.append(allocator, byte),
    };
    return output.toOwnedSlice(allocator);
}

pub fn identifierAlloc(
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
) QueryError![]u8 {
    return identifierAllocWithNodeIds(allocator, .stable, type_ref);
}

pub fn compatibilityIdentifierAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    type_ref: *const Types.Type,
) QueryError![]u8 {
    return identifierAllocWithNodeIds(
        allocator,
        .{ .compatibility = compatibility_ids },
        type_ref,
    );
}

fn identifierAllocWithNodeIds(
    allocator: std.mem.Allocator,
    node_ids: IdentifierNodeIds,
    type_ref: *const Types.Type,
) QueryError![]u8 {
    const rich = try richIdentifierAllocWithNodeIds(allocator, node_ids, type_ref);
    defer allocator.free(rich);
    const escaped = try escapeIdentifierAlloc(allocator, rich);
    errdefer allocator.free(escaped);
    if (escaped.len == 0 or std.ascii.isDigit(escaped[0])) return error.InvalidIdentifier;
    for (escaped) |byte| {
        if (std.ascii.isAlphanumeric(byte) or byte == '_' or byte == '$') continue;
        return error.InvalidIdentifier;
    }
    return escaped;
}

pub fn richIdentifierAlloc(
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
) QueryError![]u8 {
    return richIdentifierAllocWithNodeIds(allocator, .stable, type_ref);
}

pub fn compatibilityRichIdentifierAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    type_ref: *const Types.Type,
) QueryError![]u8 {
    return richIdentifierAllocWithNodeIds(
        allocator,
        .{ .compatibility = compatibility_ids },
        type_ref,
    );
}

const IdentifierNodeIds = union(enum) {
    stable,
    compatibility: CompatibilityIdResolver,

    fn append(
        self: IdentifierNodeIds,
        allocator: std.mem.Allocator,
        output: *std.ArrayList(u8),
        node: *const AST.Node,
    ) QueryError!void {
        switch (self) {
            .stable => {
                try output.append(allocator, 's');
                try appendDecimal(allocator, output, node.node_ref.source.index());
                try output.append(allocator, 'n');
                try appendDecimal(allocator, output, node.node_ref.local_node.index());
            },
            .compatibility => |resolver| try appendDecimal(
                allocator,
                output,
                resolver.id(node) orelse return error.InvalidType,
            ),
        }
    }
};

fn richIdentifierAllocWithNodeIds(
    allocator: std.mem.Allocator,
    node_ids: IdentifierNodeIds,
    type_ref: *const Types.Type,
) QueryError![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try appendRichIdentifier(allocator, &output, node_ids, type_ref);
    return output.toOwnedSlice(allocator);
}

fn appendRichIdentifier(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    node_ids: IdentifierNodeIds,
    type_ref: *const Types.Type,
) QueryError!void {
    switch (type_ref.payload) {
        .Address => |value| try output.appendSlice(
            allocator,
            if (value.state_mutability == .Payable) "t_address_payable" else "t_address",
        ),
        .Integer => |value| {
            try output.appendSlice(allocator, if (value.isSigned()) "t_int" else "t_uint");
            try appendDecimal(allocator, output, value.bits);
        },
        .RationalNumber => |value| {
            try output.appendSlice(allocator, "t_rational_");
            const negative = !value.numerator.isZero() and
                value.numerator.isNegative() != value.denominator.isNegative();
            if (negative) try output.appendSlice(allocator, "minus_");
            var absolute_numerator = value.numerator.absolute();
            defer absolute_numerator.deinit();
            var absolute_denominator = value.denominator.absolute();
            defer absolute_denominator.deinit();
            const numerator = absolute_numerator.toStringAlloc(allocator, 10) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidBase => unreachable,
            };
            defer allocator.free(numerator);
            const denominator = absolute_denominator.toStringAlloc(allocator, 10) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidBase => unreachable,
            };
            defer allocator.free(denominator);
            try output.appendSlice(allocator, numerator);
            try output.appendSlice(allocator, "_by_");
            try output.appendSlice(allocator, denominator);
        },
        .StringLiteral => |value| {
            const digest = Keccak256.keccak256(value.value);
            try output.appendSlice(allocator, "t_stringliteral_");
            try appendHex(allocator, output, digest.array());
        },
        .Bool => try output.appendSlice(allocator, "t_bool"),
        .FixedPoint => |value| {
            try output.appendSlice(allocator, if (value.isSigned()) "t_fixed" else "t_ufixed");
            try appendDecimal(allocator, output, value.total_bits);
            try output.append(allocator, 'x');
            try appendDecimal(allocator, output, value.fractional_digits);
        },
        .Array => |value| {
            switch (value.kind) {
                .String => try output.appendSlice(allocator, "t_string"),
                .Bytes => try output.appendSlice(allocator, "t_bytes"),
                .Ordinary => {
                    try output.appendSlice(allocator, "t_array(");
                    try appendRichIdentifier(allocator, output, node_ids, value.base_type);
                    try output.append(allocator, ')');
                    if (value.length) |length| try appendDecimal(allocator, output, length) else try output.appendSlice(allocator, "dyn");
                },
            }
            try appendIdentifierLocationSuffix(allocator, output, value.reference);
        },
        .ArraySlice => |value| {
            try appendRichIdentifier(allocator, output, node_ids, value.array_type);
            try output.appendSlice(allocator, "_slice");
        },
        .FixedBytes => |value| {
            try output.appendSlice(allocator, "t_bytes");
            try appendDecimal(allocator, output, value.bytes);
        },
        .Contract => |value| {
            try output.appendSlice(allocator, if (value.is_super) "t_super(" else "t_contract(");
            try appendDeclarationName(allocator, output, value.declaration);
            try output.append(allocator, ')');
            try node_ids.append(allocator, output, value.declaration);
        },
        .Struct => |value| {
            try output.appendSlice(allocator, "t_struct(");
            try appendDeclarationName(allocator, output, value.declaration);
            try output.append(allocator, ')');
            try node_ids.append(allocator, output, value.declaration);
            try appendIdentifierLocationSuffix(allocator, output, value.reference);
        },
        .Function => |value| try appendFunctionRichIdentifier(
            allocator,
            output,
            node_ids,
            value,
        ),
        .Enum => |value| {
            try output.appendSlice(allocator, "t_enum(");
            try appendDeclarationName(allocator, output, value.declaration);
            try output.append(allocator, ')');
            try node_ids.append(allocator, output, value.declaration);
        },
        .UserDefinedValueType => |value| {
            try output.appendSlice(allocator, "t_userDefinedValueType(");
            try appendDeclarationName(allocator, output, value.declaration);
            try output.append(allocator, ')');
            try node_ids.append(allocator, output, value.declaration);
        },
        .Tuple => |value| {
            try output.appendSlice(allocator, "t_tuple");
            try appendIdentifierList(allocator, output, node_ids, value.components);
        },
        .Mapping => |value| {
            try output.appendSlice(allocator, "t_mapping(");
            try appendRichIdentifier(allocator, output, node_ids, value.key_type);
            try output.append(allocator, ',');
            try appendRichIdentifier(allocator, output, node_ids, value.value_type);
            try output.append(allocator, ')');
        },
        .TypeType => |value| {
            try output.appendSlice(allocator, "t_type(");
            try appendRichIdentifier(allocator, output, node_ids, value.actual_type);
            try output.append(allocator, ')');
        },
        .Modifier => |value| {
            try output.appendSlice(allocator, "t_modifier(");
            for (value.parameter_types, 0..) |parameter, index| {
                if (index != 0) try output.append(allocator, ',');
                try appendRichIdentifier(allocator, output, node_ids, parameter);
            }
            try output.append(allocator, ')');
        },
        .Magic => |value| switch (value.kind) {
            .Block => try output.appendSlice(allocator, "t_magic_block"),
            .Message => try output.appendSlice(allocator, "t_magic_message"),
            .Transaction => try output.appendSlice(allocator, "t_magic_transaction"),
            .ABI => try output.appendSlice(allocator, "t_magic_abi"),
            .Error => try output.appendSlice(allocator, "t_error"),
            .MetaType => {
                try output.appendSlice(allocator, "t_magic_meta_type_");
                try appendRichIdentifier(allocator, output, node_ids, value.type_argument.?);
            },
        },
        .Module => |value| {
            try output.appendSlice(allocator, "t_module_");
            try node_ids.append(allocator, output, value.source_unit);
        },
        .InaccessibleDynamic => try output.appendSlice(allocator, "t_inaccessible"),
    }
}

fn appendIdentifierList(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    node_ids: IdentifierNodeIds,
    values: []const ?*const Types.Type,
) QueryError!void {
    try output.append(allocator, '(');
    for (values, 0..) |value, index| {
        if (index != 0) try output.append(allocator, ',');
        if (value) |concrete| try appendRichIdentifier(allocator, output, node_ids, concrete);
    }
    try output.append(allocator, ')');
}

fn appendFunctionRichIdentifier(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    node_ids: IdentifierNodeIds,
    value: Types.FunctionType,
) QueryError!void {
    try output.appendSlice(allocator, "t_function_");
    try output.appendSlice(allocator, functionKindIdentifier(value.kind));
    try output.append(allocator, '_');
    try output.appendSlice(allocator, Enums.stateMutabilityToString(value.state_mutability));
    try output.append(allocator, '(');
    for (value.parameter_types, 0..) |parameter, index| {
        if (index != 0) try output.append(allocator, ',');
        try appendRichIdentifier(allocator, output, node_ids, parameter);
    }
    try output.appendSlice(allocator, ")returns(");
    for (value.return_parameter_types, 0..) |parameter, index| {
        if (index != 0) try output.append(allocator, ',');
        try appendRichIdentifier(allocator, output, node_ids, parameter);
    }
    try output.append(allocator, ')');
    if (value.options.gas_set) try output.appendSlice(allocator, "gas");
    if (value.options.value_set) try output.appendSlice(allocator, "value");
    if (value.options.salt_set) try output.appendSlice(allocator, "salt");
    if (value.options.has_bound_first_argument) {
        try output.appendSlice(allocator, "attached_to(");
        try appendRichIdentifier(allocator, output, node_ids, value.parameter_types[0]);
        try output.append(allocator, ')');
    }
}

fn functionKindIdentifier(kind: Types.FunctionKind) []const u8 {
    return switch (kind) {
        .Declaration => "declaration",
        .Internal => "internal",
        .External => "external",
        .DelegateCall => "delegatecall",
        .BareCall => "barecall",
        .BareCallCode => "barecallcode",
        .BareDelegateCall => "baredelegatecall",
        .BareStaticCall => "barestaticcall",
        .Creation => "creation",
        .Send => "send",
        .Transfer => "transfer",
        .KECCAK256 => "keccak256",
        .ERC7201 => "erc7201",
        .Selfdestruct => "selfdestruct",
        .Revert => "revert",
        .ECRecover => "ecrecover",
        .SHA256 => "sha256",
        .RIPEMD160 => "ripemd160",
        .Event => "event",
        .Error => "error",
        .Wrap => "wrap",
        .Unwrap => "unwrap",
        .SetGas => "setgas",
        .SetValue => "setvalue",
        .BlockHash => "blockhash",
        .BlobHash => "blobhash",
        .AddMod => "addmod",
        .MulMod => "mulmod",
        .ArrayPush => "arraypush",
        .ArrayPop => "arraypop",
        .BytesConcat => "bytesconcat",
        .StringConcat => "stringconcat",
        .ObjectCreation => "objectcreation",
        .Assert => "assert",
        .Require => "require",
        .ABIEncode => "abiencode",
        .ABIEncodePacked => "abiencodepacked",
        .ABIEncodeWithSelector => "abiencodewithselector",
        .ABIEncodeCall => "abiencodecall",
        .ABIEncodeWithSignature => "abiencodewithsignature",
        .ABIDecode => "abidecode",
        .GasLeft => "gasleft",
        .MetaType => "metatype",
    };
}

pub fn toStringAlloc(
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
    without_data_location: bool,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try appendTypeString(allocator, &output, type_ref, without_data_location);
    return output.toOwnedSlice(allocator);
}

fn appendTypeString(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    type_ref: *const Types.Type,
    without_data_location: bool,
) std.mem.Allocator.Error!void {
    switch (type_ref.payload) {
        .Address => |value| try output.appendSlice(
            allocator,
            if (value.state_mutability == .Payable) "address payable" else "address",
        ),
        .Integer => |value| {
            try output.appendSlice(allocator, if (value.isSigned()) "int" else "uint");
            try appendDecimal(allocator, output, value.bits);
        },
        .RationalNumber => |value| {
            if (value.denominator.compareUnsigned(1) == .eq) {
                try output.appendSlice(allocator, "int_const ");
                try appendReadableBigInt(allocator, output, value.numerator);
            } else {
                try output.appendSlice(allocator, "rational_const ");
                try appendReadableBigInt(allocator, output, value.numerator);
                try output.appendSlice(allocator, " / ");
                try appendReadableBigInt(allocator, output, value.denominator);
            }
        },
        .StringLiteral => |value| {
            var printable = true;
            for (value.value) |byte|
                if (byte <= 0x1f or byte >= 0x7f) {
                    printable = false;
                    break;
                };
            if (printable) {
                try output.appendSlice(allocator, "literal_string \"");
                try output.appendSlice(allocator, value.value);
                try output.append(allocator, '"');
            } else {
                try output.appendSlice(allocator, "literal_string hex\"");
                try appendHex(allocator, output, value.value);
                try output.append(allocator, '"');
            }
        },
        .Bool => try output.appendSlice(allocator, "bool"),
        .FixedPoint => |value| {
            try output.appendSlice(allocator, if (value.isSigned()) "fixed" else "ufixed");
            try appendDecimal(allocator, output, value.total_bits);
            try output.append(allocator, 'x');
            try appendDecimal(allocator, output, value.fractional_digits);
        },
        .Array => |value| {
            switch (value.kind) {
                .String => try output.appendSlice(allocator, "string"),
                .Bytes => try output.appendSlice(allocator, "bytes"),
                .Ordinary => {
                    try appendTypeString(allocator, output, value.base_type, without_data_location);
                    try output.append(allocator, '[');
                    if (value.length) |length| try appendDecimal(allocator, output, length);
                    try output.append(allocator, ']');
                },
            }
            if (!without_data_location) {
                try output.append(allocator, ' ');
                try appendReferenceString(allocator, output, value.reference);
            }
        },
        .ArraySlice => |value| {
            try appendTypeString(allocator, output, value.array_type, without_data_location);
            try output.appendSlice(allocator, " slice");
        },
        .FixedBytes => |value| {
            try output.appendSlice(allocator, "bytes");
            try appendDecimal(allocator, output, value.bytes);
        },
        .Contract => |value| {
            const kind: []const u8 = if (value.declaration.nodeKind() == .contract_definition and
                value.declaration.payload.contract_definition.contract_kind == .Library)
                "library "
            else
                "contract ";
            try output.appendSlice(allocator, kind);
            if (value.is_super) try output.appendSlice(allocator, "super ");
            try appendDeclarationName(allocator, output, value.declaration);
        },
        .Struct => |value| {
            try output.appendSlice(allocator, "struct ");
            try appendCanonicalDeclarationName(allocator, output, value.declaration);
            if (!without_data_location) {
                try output.append(allocator, ' ');
                try appendReferenceString(allocator, output, value.reference);
            }
        },
        .Function => |value| try appendFunctionString(
            allocator,
            output,
            value,
            without_data_location,
        ),
        .Enum => |value| {
            try output.appendSlice(allocator, "enum ");
            try appendCanonicalDeclarationName(allocator, output, value.declaration);
        },
        .UserDefinedValueType => |value| try appendCanonicalDeclarationName(allocator, output, value.declaration),
        .Tuple => |value| {
            try output.appendSlice(allocator, "tuple(");
            for (value.components, 0..) |component, index| {
                if (index != 0) try output.append(allocator, ',');
                if (component) |concrete|
                    try appendTypeString(allocator, output, concrete, without_data_location);
            }
            try output.append(allocator, ')');
        },
        .Mapping => |value| {
            try output.appendSlice(allocator, "mapping(");
            try appendTypeString(allocator, output, value.key_type, without_data_location);
            try output.appendSlice(allocator, " => ");
            try appendTypeString(allocator, output, value.value_type, without_data_location);
            try output.append(allocator, ')');
        },
        .TypeType => |value| {
            try output.appendSlice(allocator, "type(");
            try appendTypeString(allocator, output, value.actual_type, without_data_location);
            try output.append(allocator, ')');
        },
        .Modifier => |value| {
            try output.appendSlice(allocator, "modifier (");
            for (value.parameter_types, 0..) |parameter, index| {
                if (index != 0) try output.append(allocator, ',');
                try appendTypeString(allocator, output, parameter, without_data_location);
            }
            try output.append(allocator, ')');
        },
        .Magic => |value| switch (value.kind) {
            .Block => try output.appendSlice(allocator, "block"),
            .Message => try output.appendSlice(allocator, "msg"),
            .Transaction => try output.appendSlice(allocator, "tx"),
            .ABI => try output.appendSlice(allocator, "abi"),
            .Error => try output.appendSlice(allocator, "error"),
            .MetaType => {
                try output.appendSlice(allocator, "type(");
                try appendTypeString(
                    allocator,
                    output,
                    value.type_argument.?,
                    without_data_location,
                );
                try output.append(allocator, ')');
            },
        },
        .Module => |value| {
            try output.appendSlice(allocator, "module \"");
            const path = sourceUnitPath(value.source_unit);
            try output.appendSlice(allocator, path);
            try output.append(allocator, '"');
        },
        .InaccessibleDynamic => try output.appendSlice(allocator, "inaccessible dynamic type"),
    }
}

fn appendFunctionString(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    value: Types.FunctionType,
    without_data_location: bool,
) std.mem.Allocator.Error!void {
    try output.appendSlice(allocator, "function ");
    if (value.kind == .Declaration and value.declaration != null) {
        const declaration = value.declaration.?;
        if (declaration.nodeKind() == .function_definition)
            if (nodeScope(declaration)) |enclosing|
                if (enclosing.nodeKind() == .contract_definition) {
                    try appendCanonicalDeclarationName(allocator, output, enclosing);
                    try output.append(allocator, '.');
                };
        try appendDeclarationName(allocator, output, value.declaration.?);
    }
    try output.append(allocator, '(');
    for (value.parameter_types, 0..) |parameter, index| {
        if (index != 0) try output.append(allocator, ',');
        try appendTypeString(allocator, output, parameter, without_data_location);
    }
    try output.append(allocator, ')');
    if (value.state_mutability != .NonPayable) {
        try output.append(allocator, ' ');
        try output.appendSlice(allocator, Enums.stateMutabilityToString(value.state_mutability));
    }
    if (value.kind == .External) try output.appendSlice(allocator, " external");
    if (value.return_parameter_types.len != 0) {
        try output.appendSlice(allocator, " returns (");
        for (value.return_parameter_types, 0..) |parameter, index| {
            if (index != 0) try output.append(allocator, ',');
            try appendTypeString(allocator, output, parameter, without_data_location);
        }
        try output.append(allocator, ')');
    }
}

/// Allocates the diagnostic-facing name used by upstream's virtual
/// `Type::humanReadableName()` family. Most types use `toString(false)`, while
/// arrays, slices, tuples, events, and errors deliberately override it.
pub fn humanReadableNameAlloc(
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try appendHumanReadableName(allocator, &output, type_ref);
    return output.toOwnedSlice(allocator);
}

fn appendHumanReadableName(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    type_ref: *const Types.Type,
) std.mem.Allocator.Error!void {
    switch (type_ref.payload) {
        .Array => |value| {
            switch (value.kind) {
                .String => try output.appendSlice(allocator, "string"),
                .Bytes => try output.appendSlice(allocator, "bytes"),
                .Ordinary => {
                    // ArrayType uses the base type's ordinary, location-free
                    // spelling rather than recursively calling its human name.
                    try appendTypeString(allocator, output, value.base_type, true);
                    try output.append(allocator, '[');
                    if (value.length) |length| try appendDecimal(allocator, output, length);
                    try output.append(allocator, ']');
                },
            }
            try output.append(allocator, ' ');
            try appendReferenceString(allocator, output, value.reference);
        },
        .ArraySlice => |value| {
            try appendHumanReadableName(allocator, output, value.array_type);
            try output.appendSlice(allocator, " slice");
        },
        .Tuple => |value| {
            try output.appendSlice(allocator, "tuple(");
            for (value.components, 0..) |component, index| {
                if (index != 0) try output.append(allocator, ',');
                if (component) |concrete|
                    try appendHumanReadableName(allocator, output, concrete);
            }
            try output.append(allocator, ')');
        },
        .Function => |value| switch (value.kind) {
            .Error, .Event => {
                try output.appendSlice(
                    allocator,
                    if (value.kind == .Error) "error " else "event ",
                );
                const declaration = value.declaration orelse {
                    std.debug.assert(false);
                    return;
                };
                try appendDeclarationName(allocator, output, declaration);
                try output.append(allocator, '(');
                for (value.parameter_types, 0..) |parameter, index| {
                    if (index != 0) try output.append(allocator, ',');
                    try appendTypeString(allocator, output, parameter, true);
                }
                try output.append(allocator, ')');
            },
            else => try appendTypeString(allocator, output, type_ref, false),
        },
        else => try appendTypeString(allocator, output, type_ref, false),
    }
}

pub fn canonicalNameAlloc(
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try appendCanonicalName(allocator, &output, type_ref);
    return output.toOwnedSlice(allocator);
}

fn appendCanonicalName(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    type_ref: *const Types.Type,
) std.mem.Allocator.Error!void {
    switch (type_ref.payload) {
        .Address => try output.appendSlice(allocator, "address"),
        .Array => |value| {
            switch (value.kind) {
                .String => try output.appendSlice(allocator, "string"),
                .Bytes => try output.appendSlice(allocator, "bytes"),
                .Ordinary => {
                    try appendCanonicalName(allocator, output, value.base_type);
                    try output.append(allocator, '[');
                    if (value.length) |length| try appendDecimal(allocator, output, length);
                    try output.append(allocator, ']');
                },
            }
        },
        .Contract, .Struct, .Enum, .UserDefinedValueType => {
            const declaration = switch (type_ref.payload) {
                .Contract => |value| value.declaration,
                .Struct => |value| value.declaration,
                .Enum => |value| value.declaration,
                .UserDefinedValueType => |value| value.declaration,
                else => unreachable,
            };
            try appendCanonicalDeclarationName(allocator, output, declaration);
        },
        .Mapping => |value| {
            try output.appendSlice(allocator, "mapping(");
            try appendCanonicalName(allocator, output, value.key_type);
            try output.appendSlice(allocator, " => ");
            try appendCanonicalName(allocator, output, value.value_type);
            try output.append(allocator, ')');
        },
        .Function => try output.appendSlice(allocator, "function"),
        else => try appendTypeString(allocator, output, type_ref, true),
    }
}

fn appendReferenceString(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    reference: Types.ReferenceData,
) std.mem.Allocator.Error!void {
    switch (reference.location) {
        .Storage => {
            try output.appendSlice(allocator, "storage ");
            try output.appendSlice(allocator, if (reference.isPointer()) "pointer" else "ref");
        },
        .CallData => try output.appendSlice(allocator, "calldata"),
        .Memory => try output.appendSlice(allocator, "memory"),
        .Transient => try output.appendSlice(allocator, "transient"),
    }
}

fn appendIdentifierLocationSuffix(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    reference: Types.ReferenceData,
) std.mem.Allocator.Error!void {
    try output.appendSlice(allocator, switch (reference.location) {
        .Storage => "_storage",
        .Transient => "_transient",
        .Memory => "_memory",
        .CallData => "_calldata",
    });
    if (reference.isPointer()) try output.appendSlice(allocator, "_ptr");
}

fn appendDeclarationName(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    declaration: *const AST.Node,
) std.mem.Allocator.Error!void {
    const data = declaration.declarationConst();
    try output.appendSlice(allocator, if (data) |value| value.name else "");
}

fn appendCanonicalDeclarationName(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    declaration: *const AST.Node,
) std.mem.Allocator.Error!void {
    if (ASTAnnotations.annotationConst(declaration)) |annotation| {
        const canonical: ?[]const u8 = switch (annotation.*) {
            .type_declaration => |value| value.canonical_name.value,
            .struct_declaration => |value| value.type_declaration.canonical_name.value,
            .contract_definition => |value| value.type_declaration.canonical_name.value,
            .type_class_definition => |value| value.type_declaration.canonical_name.value,
            else => null,
        };
        if (canonical) |name| {
            try output.appendSlice(allocator, name);
            return;
        }
    }
    try appendDeclarationName(allocator, output, declaration);
}

fn sourceUnitPath(source_unit: *const AST.Node) []const u8 {
    const annotation = ASTAnnotations.annotationConst(source_unit) orelse return "";
    return switch (annotation.*) {
        .source_unit => |value| value.path.value orelse "",
        else => "",
    };
}

fn appendDecimal(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    value: anytype,
) std.mem.Allocator.Error!void {
    const rendered = try std.fmt.allocPrint(allocator, "{d}", .{value});
    defer allocator.free(rendered);
    try output.appendSlice(allocator, rendered);
}

fn appendReadableBigInt(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    value: *const Types.BigInt,
) std.mem.Allocator.Error!void {
    const rendered = value.toStringAlloc(allocator, 10) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.InvalidBase => unreachable,
    };
    defer allocator.free(rendered);
    if (rendered.len <= 32) {
        try output.appendSlice(allocator, rendered);
        return;
    }
    try output.appendSlice(allocator, rendered[0..4]);
    try output.appendSlice(allocator, "...(");
    try appendDecimal(allocator, output, rendered.len - 8);
    try output.appendSlice(allocator, " digits omitted)...");
    try output.appendSlice(allocator, rendered[rendered.len - 4 ..]);
}

fn appendHex(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    bytes: []const u8,
) std.mem.Allocator.Error!void {
    const alphabet = "0123456789abcdef";
    for (bytes) |byte| {
        try output.append(allocator, alphabet[byte >> 4]);
        try output.append(allocator, alphabet[byte & 0x0f]);
    }
}

pub fn linearizedStateVariablesAlloc(
    allocator: std.mem.Allocator,
    contract_type: Types.ContractType,
    location: Types.DataLocation,
) QueryError![]Types.StateVariableLayout {
    if (contract_type.declaration.nodeKind() != .contract_definition or
        (location != .Storage and location != .Transient))
        return error.InvalidType;
    const reference_location: AST.VariableLocation = if (location == .Storage)
        .Unspecified
    else
        .Transient;
    var variables: std.ArrayList(*const AST.Node) = .empty;
    defer variables.deinit(allocator);
    try appendLinearizedStateVariables(
        allocator,
        &variables,
        contract_type.declaration,
        reference_location,
        false,
    );
    const types = try allocator.alloc(*const Types.Type, variables.items.len);
    defer allocator.free(types);
    for (variables.items, types) |variable, *target|
        target.* = try variableDeclarationType(variable);
    const offsets = try computeStorageOffsetsAlloc(
        allocator,
        types,
        try layoutBaseForInheritanceHierarchy(contract_type.declaration, location),
    );
    defer allocator.free(offsets.offsets);
    var result: std.ArrayList(Types.StateVariableLayout) = .empty;
    errdefer result.deinit(allocator);
    for (variables.items, offsets.offsets) |variable, maybe_offset|
        if (maybe_offset) |offset|
            try result.append(allocator, .{
                .declaration = variable,
                .slot = offset.slot,
                .byte_offset = offset.byte_offset,
            });
    return result.toOwnedSlice(allocator);
}

pub fn immutableVariablesAlloc(
    allocator: std.mem.Allocator,
    contract_type: Types.ContractType,
) QueryError![]const *const AST.Node {
    if (contract_type.declaration.nodeKind() != .contract_definition)
        return error.InvalidType;
    var variables: std.ArrayList(*const AST.Node) = .empty;
    errdefer variables.deinit(allocator);
    try appendLinearizedStateVariables(
        allocator,
        &variables,
        contract_type.declaration,
        .Unspecified,
        true,
    );
    return variables.toOwnedSlice(allocator);
}

fn appendLinearizedStateVariables(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(*const AST.Node),
    contract: *const AST.Node,
    location: AST.VariableLocation,
    immutables_only: bool,
) QueryError!void {
    const annotation = ASTAnnotations.annotationConst(contract);
    const annotated_bases = if (annotation) |entry| switch (entry.*) {
        .contract_definition => |value| value.linearized_base_contracts,
        else => &.{},
    } else &.{};
    const bases = if (annotated_bases.len == 0) &.{contract} else annotated_bases;
    var index = bases.len;
    while (index != 0) {
        index -= 1;
        const base = bases[index];
        if (base.nodeKind() != .contract_definition) return error.InvalidType;
        for (base.payload.contract_definition.sub_nodes) |node| {
            if (node.nodeKind() != .variable_declaration) continue;
            const variable = node.payload.variable_declaration;
            if (immutables_only) {
                if (variable.mutability == .Immutable)
                    try output.append(allocator, node);
                continue;
            }
            if (variable.mutability == .Constant or
                variable.mutability == .Immutable or
                variable.reference_location != location) continue;
            try output.append(allocator, node);
        }
    }
}

pub fn contractStorageSizeUpperBound(
    contract: *const AST.Node,
    location: Types.DataLocation,
) QueryError!u256 {
    if (contract.nodeKind() != .contract_definition or
        (location != .Storage and location != .Transient)) return error.InvalidType;
    const reference_location: AST.VariableLocation = if (location == .Storage)
        .Unspecified
    else
        .Transient;
    const annotation = ASTAnnotations.annotationConst(contract);
    const bases = if (annotation) |entry| switch (entry.*) {
        .contract_definition => |value| value.linearized_base_contracts,
        else => &.{contract},
    } else &.{contract};
    var total: u256 = 0;
    for (bases) |base| {
        if (base.nodeKind() != .contract_definition) return error.InvalidType;
        for (base.payload.contract_definition.sub_nodes) |node| {
            if (node.nodeKind() != .variable_declaration) continue;
            const variable = node.payload.variable_declaration;
            if (variable.mutability == .Constant or
                variable.mutability == .Immutable or
                variable.reference_location != reference_location) continue;
            total = std.math.add(
                u256,
                total,
                try storageSizeUpperBound(try variableDeclarationType(node)),
            ) catch return error.Overflow;
        }
    }
    return total;
}

pub fn layoutBaseForInheritanceHierarchy(
    contract: *const AST.Node,
    location: Types.DataLocation,
) QueryError!u256 {
    if (location == .Transient) return 0;
    if (location != .Storage or contract.nodeKind() != .contract_definition)
        return error.InvalidType;
    const specifier = contract.payload.contract_definition.storage_layout_specifier orelse
        return 0;
    const annotation = ASTAnnotations.annotationConst(specifier) orelse return error.InvalidType;
    return switch (annotation.*) {
        .storage_layout_specifier => |value| if (value.base_slot.isSet())
            (value.base_slot.get() catch return error.InvalidType).*
        else
            0,
        else => error.InvalidType,
    };
}

pub fn structStorageOffsetsAlloc(
    allocator: std.mem.Allocator,
    structure: Types.StructType,
) QueryError!Types.StorageOffsets {
    const member_types = try structMemberTypesAlloc(allocator, structure);
    defer allocator.free(member_types);
    return computeStorageOffsetsAlloc(allocator, member_types, 0);
}

pub fn structStorageOffsetOfMember(
    allocator: std.mem.Allocator,
    structure: Types.StructType,
    member_name: []const u8,
) QueryError!Types.StorageOffset {
    const offsets = try structStorageOffsetsAlloc(allocator, structure);
    defer allocator.free(offsets.offsets);
    for (structure.declaration.payload.struct_definition.members, offsets.offsets) |member, offset|
        if (std.mem.eql(
            u8,
            member.payload.variable_declaration.declaration.name,
            member_name,
        )) return offset orelse error.InvalidType;
    return error.InvalidType;
}

pub fn structMemoryMemberTypesAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    structure: Types.StructType,
) BehaviorError![]const *const Types.Type {
    if (try containsNestedMapping(
        provider,
        &.{ .payload = .{ .Struct = structure } },
    )) return error.InvalidType;
    const result = try allocator.alloc(
        *const Types.Type,
        structure.declaration.payload.struct_definition.members.len,
    );
    errdefer allocator.free(result);
    for (structure.declaration.payload.struct_definition.members, result) |member, *target|
        target.* = try provider.withLocationIfReference(
            .Memory,
            try variableDeclarationType(member),
            false,
        );
    return result;
}

pub fn enumMemberValue(
    enumeration: Types.EnumType,
    member_name: []const u8,
) QueryError!u8 {
    if (enumeration.declaration.nodeKind() != .enum_definition)
        return error.InvalidType;
    for (enumeration.declaration.payload.enum_definition.members, 0..) |member, index|
        if (std.mem.eql(u8, member.payload.enum_value.declaration.name, member_name)) {
            if (index > 255) return error.Overflow;
            return @intCast(index);
        };
    return error.InvalidType;
}

pub fn enumNumberOfMembers(enumeration: Types.EnumType) QueryError!usize {
    if (enumeration.declaration.nodeKind() != .enum_definition)
        return error.InvalidType;
    return enumeration.declaration.payload.enum_definition.members.len;
}

pub fn enumMaxValue(enumeration: Types.EnumType) QueryError!u8 {
    const count = try enumNumberOfMembers(enumeration);
    if (count == 0 or count > 256) return error.InvalidType;
    return @intCast(count - 1);
}

pub fn computeStorageOffsetsAlloc(
    allocator: std.mem.Allocator,
    type_refs: []const *const Types.Type,
    base_slot: u256,
) QueryError!Types.StorageOffsets {
    const offsets = try allocator.alloc(?Types.StorageOffset, type_refs.len);
    errdefer allocator.free(offsets);
    @memset(offsets, null);
    var slot = base_slot;
    var byte_offset: u8 = 0;
    for (type_refs, 0..) |type_ref, index| {
        if (!canBeStored(type_ref)) return error.NotStorable;
        const bytes = try storageBytes(type_ref);
        if (bytes > 32) return error.InvalidType;
        if (@as(u16, byte_offset) + bytes > 32) {
            slot = std.math.add(u256, slot, 1) catch return error.Overflow;
            byte_offset = 0;
        }
        offsets[index] = .{ .slot = slot, .byte_offset = byte_offset };
        const size = try storageSize(type_ref);
        if (size == 1 and @as(u16, byte_offset) + bytes <= 32) {
            byte_offset += bytes;
        } else {
            slot = std.math.add(u256, slot, size) catch return error.Overflow;
            byte_offset = 0;
        }
    }
    if (byte_offset > 0) slot = std.math.add(u256, slot, 1) catch return error.Overflow;
    return .{
        .offsets = offsets,
        .storage_size = slot - base_slot,
    };
}

test "upstream storage layout vectors preserve packing boundaries" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const simple_types = [_]*const Types.Type{
        try provider.uint(128),
        try provider.uint(120),
        try provider.uint(16),
    };
    const simple = try computeStorageOffsetsAlloc(
        std.testing.allocator,
        &simple_types,
        0,
    );
    defer std.testing.allocator.free(simple.offsets);
    try std.testing.expectEqual(@as(u256, 2), simple.storage_size);
    try std.testing.expectEqual(
        Types.StorageOffset{ .slot = 0, .byte_offset = 0 },
        simple.offsets[0].?,
    );
    try std.testing.expectEqual(
        Types.StorageOffset{ .slot = 0, .byte_offset = 16 },
        simple.offsets[1].?,
    );
    try std.testing.expectEqual(
        Types.StorageOffset{ .slot = 1, .byte_offset = 0 },
        simple.offsets[2].?,
    );

    const mapping = try provider.mapping(
        try provider.uint(8),
        "",
        try provider.uint(8),
        "",
    );
    const mapping_types = [_]*const Types.Type{
        try provider.uint(128),
        mapping,
        try provider.uint(16),
        mapping,
    };
    const mapped = try computeStorageOffsetsAlloc(
        std.testing.allocator,
        &mapping_types,
        0,
    );
    defer std.testing.allocator.free(mapped.offsets);
    try std.testing.expectEqual(@as(u256, 4), mapped.storage_size);
    for (mapped.offsets, 0..) |offset, index| {
        try std.testing.expectEqual(@as(u256, @intCast(index)), offset.?.slot);
        try std.testing.expectEqual(@as(u8, 0), offset.?.byte_offset);
    }

    const cases = [_]struct { bytes: u8, length: u256, slots: u256 }{
        .{ .bytes = 1, .length = 32, .slots = 1 },
        .{ .bytes = 1, .length = 33, .slots = 2 },
        .{ .bytes = 2, .length = 31, .slots = 2 },
        .{ .bytes = 7, .length = 8, .slots = 2 },
        .{ .bytes = 7, .length = 9, .slots = 3 },
        .{ .bytes = 31, .length = 9, .slots = 9 },
        .{ .bytes = 32, .length = 9, .slots = 9 },
    };
    for (cases) |case| {
        const array = try provider.arrayWithLength(
            .Storage,
            try provider.fixedBytes(case.bytes),
            case.length,
        );
        try std.testing.expectEqual(case.slots, try storageSize(array));
    }

    const maximum_packed_array = try provider.arrayWithLength(
        .Storage,
        try provider.fixedBytes(1),
        std.math.maxInt(u256),
    );
    try std.testing.expectEqual(
        std.math.maxInt(u256) / 32 + 1,
        try storageSize(maximum_packed_array),
    );
}

test "upstream identifier escaping and composite identifier vectors are exact" {
    const escaping = [_]struct { input: []const u8, expected: []const u8 }{
        .{ .input = "(", .expected = "$_" },
        .{ .input = ")", .expected = "_$" },
        .{ .input = ",", .expected = "_$_" },
        .{ .input = "$", .expected = "$$$" },
        .{ .input = ")$(", .expected = "_$$$$$_" },
        .{ .input = "()", .expected = "$__$" },
        .{ .input = "(,)", .expected = "$__$__$" },
        .{ .input = "(,$,)", .expected = "$__$_$$$_$__$" },
        .{
            .input = "((__(_$_$$,__($$,,,$$),$,,,)))$$,$$",
            .expected = "$_$___$__$$$_$$$$$$_$___$_$$$$$$_$__$__$_$$$$$$_$_$_$$$_$__$__$__$_$_$$$$$$$_$_$$$$$$",
        },
    };
    for (escaping) |case| {
        const escaped = try escapeIdentifierAlloc(std.testing.allocator, case.input);
        defer std.testing.allocator.free(escaped);
        try std.testing.expectEqualStrings(case.expected, escaped);
    }

    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    const large_array = try provider.arrayWithLength(
        .Memory,
        try provider.integer(128, .Signed),
        2535301200456458802993406410752,
    );
    const large_identifier = try identifierAlloc(std.testing.allocator, large_array);
    defer std.testing.allocator.free(large_identifier);
    try std.testing.expectEqualStrings(
        "t_array$_t_int128_$2535301200456458802993406410752_memory_ptr",
        large_identifier,
    );

    const string_array = try provider.arrayWithLength(
        .Storage,
        provider.stringStorage(),
        20,
    );
    const multi_array = try provider.array(.Storage, string_array);
    const multi_identifier = try identifierAlloc(std.testing.allocator, multi_array);
    defer std.testing.allocator.free(multi_identifier);
    try std.testing.expectEqualStrings(
        "t_array$_t_array$_t_string_storage_$20_storage_$dyn_storage_ptr",
        multi_identifier,
    );

    const literal = try provider.stringLiteral("abc - def");
    const literal_identifier = try identifierAlloc(std.testing.allocator, literal);
    defer std.testing.allocator.free(literal_identifier);
    try std.testing.expectEqualStrings(
        "t_stringliteral_196a9142ee0d40e274a6482393c762b16dd8315713207365e1e13d8d85b74fc4",
        literal_identifier,
    );
}

test "upstream static calldata size vectors preserve recursive strides" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    try std.testing.expectEqual(@as(u32, 32), try calldataEncodedSize(try provider.uint(16), true));
    try std.testing.expectEqual(@as(u32, 2), try calldataEncodedSize(try provider.uint(16), false));
    try std.testing.expectEqual(@as(u32, 32), try calldataEncodedSize(try provider.fixedBytes(16), true));
    try std.testing.expectEqual(@as(u32, 16), try calldataEncodedSize(try provider.fixedBytes(16), false));
    try std.testing.expectEqual(@as(u32, 32), try calldataEncodedSize(provider.boolean(), true));
    try std.testing.expectEqual(@as(u32, 1), try calldataEncodedSize(provider.boolean(), false));

    const uint24_array = try provider.arrayWithLength(
        .Memory,
        try provider.uint(24),
        9,
    );
    try std.testing.expectEqual(@as(u32, 9 * 32), try calldataEncodedSize(uint24_array, true));
    try std.testing.expectEqual(@as(u32, 9 * 32), try calldataEncodedSize(uint24_array, false));
    const two_dimensional = try provider.arrayWithLength(.Memory, uint24_array, 3);
    try std.testing.expectEqual(@as(u32, 9 * 3 * 32), try calldataEncodedSize(two_dimensional, true));
    try std.testing.expectEqual(@as(u32, 9 * 3 * 32), try calldataEncodedSize(two_dimensional, false));
}

test "numeric bounds and invalid layout queries preserve upstream contracts" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const int8 = (try provider.integer(8, .Signed)).payload.Integer;
    const uint256 = provider.uint256().payload.Integer;
    try std.testing.expectEqual(@as(u256, 0) -% 128, integerMin(int8));
    try std.testing.expectEqual(@as(u256, 127), integerMax(int8));
    try std.testing.expectEqual(@as(u256, 0), integerMin(uint256));
    try std.testing.expectEqual(std.math.maxInt(u256), integerMax(uint256));

    var int8_min = integerMinValue(int8);
    defer int8_min.deinit();
    var expected_int8_min = Types.BigInt.initSigned(-128);
    defer expected_int8_min.deinit();
    try std.testing.expectEqual(std.math.Order.eq, int8_min.compare(&expected_int8_min));

    const fixed = (try provider.fixedPoint(16, 2, .Signed)).payload.FixedPoint;
    var fixed_min = fixedPointMinIntegerValue(fixed);
    defer fixed_min.deinit();
    var fixed_max = fixedPointMaxIntegerValue(fixed);
    defer fixed_max.deinit();
    var expected_fixed_min = Types.BigInt.initSigned(-327);
    defer expected_fixed_min.deinit();
    var expected_fixed_max = Types.BigInt.initSigned(327);
    defer expected_fixed_max.deinit();
    try std.testing.expectEqual(std.math.Order.eq, fixed_min.compare(&expected_fixed_min));
    try std.testing.expectEqual(std.math.Order.eq, fixed_max.compare(&expected_fixed_max));
    try std.testing.expect(equals(
        try fixedPointAsIntegerType(&provider, fixed),
        try provider.integer(16, .Signed),
    ));

    const mapping = try provider.mapping(provider.uint256(), "", provider.uint256(), "");
    try std.testing.expectError(error.InvalidType, calldataEncodedSize(mapping, true));
    try std.testing.expectError(error.InvalidType, memoryHeadSize(mapping));
    const tuple = try provider.tupleOfTypes(&.{ provider.uint256(), provider.boolean() });
    try std.testing.expect(!isDynamicallyEncoded(tuple));
    try std.testing.expectError(error.InvalidType, calldataEncodedSize(tuple, true));
    try std.testing.expectError(error.InvalidType, memoryHeadSize(tuple));
    try std.testing.expectError(error.NotDynamicallyEncoded, calldataEncodedTailSize(tuple));

    const inaccessible = provider.inaccessibleDynamic();
    try std.testing.expect(!isImplicitlyConvertibleTo(inaccessible, inaccessible));
    try std.testing.expect(!isExplicitlyConvertibleTo(inaccessible, inaccessible));
}

test "UDVT alignment struct transient validity and function documentation match upstream" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var tree = try AST.Tree.init(std.testing.allocator, "", "Types.sol");
    defer tree.deinit();

    const underlying_name = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try AST.ElementaryTypeNameToken.init(.BytesM, 4, 0),
    } });
    const value_definition = try tree.createNode(.{}, .{ .user_defined_value_type_definition = .{
        .declaration = .{ .name = "Word" },
        .underlying_type = underlying_name,
    } });
    const value_type = try provider.userDefinedValueType(
        value_definition,
        try provider.fixedBytes(4),
    );
    try std.testing.expect(try leftAligned(value_type));
    try std.testing.expect(nameable(value_type));
    try std.testing.expect(canBeStored(value_type));

    const scalar_member = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "value" },
    } });
    (try ASTAnnotations.ensure(&tree, scalar_member)).variable_declaration.type_ref =
        provider.uint256();
    const struct_definition = try tree.createNode(.{}, .{ .struct_definition = .{
        .declaration = .{ .name = "Scalar" },
        .members = try tree.ownSlice(*AST.Node, &.{scalar_member}),
    } });
    (try ASTAnnotations.ensure(&tree, struct_definition)).struct_declaration.recursive = false;
    const structure = try provider.structType(struct_definition, .Storage);
    try std.testing.expect(try validForLocation(&provider, structure, .Transient));
    try std.testing.expect(!(try structIsRecursive(structure.payload.Struct)));

    const documentation = try tree.createNode(.{}, .{ .structured_documentation = .{
        .text = "Returns the value.",
    } });
    const parameters = try tree.createNode(.{}, .{ .parameter_list = .{} });
    const function_definition = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "read" },
            .parameters = parameters,
        },
        .documentation = documentation,
    } });
    const function_type = try provider.function(
        &.{},
        &.{},
        &.{},
        &.{},
        .Internal,
        .NonPayable,
        function_definition,
        .{},
    );
    try std.testing.expect(functionDocumentation(function_type.payload.Function) == documentation);

    const array = try provider.arrayWithLength(.Storage, try provider.fixedBytes(4), 2);
    try std.testing.expectEqual(@as(u8, 4), try storageStride(array.payload.Array));
    try std.testing.expectEqual(@as(u8, 1), try storageStride(provider.bytesStorage().payload.Array));
}

test "elementary equality, conversion, representation, and layout" {
    const uint8_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 8,
        .modifier = .Unsigned,
    } } };
    const uint256_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const int256_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Signed,
    } } };
    try std.testing.expect(isImplicitlyConvertibleTo(&uint8_type, &uint256_type));
    try std.testing.expect(!isImplicitlyConvertibleTo(&uint8_type, &int256_type));
    try std.testing.expect(!isExplicitlyConvertibleTo(&uint8_type, &int256_type));
    try std.testing.expect(isExplicitlyConvertibleTo(&uint256_type, &int256_type));

    const bytes32_type = Types.Type{ .payload = .{ .FixedBytes = .{ .bytes = 32 } } };
    try std.testing.expect(isExplicitlyConvertibleTo(&bytes32_type, &uint256_type));
    try std.testing.expectEqual(@as(u8, 1), try storageBytes(&uint8_type));

    const rendered = try toStringAlloc(std.testing.allocator, &uint256_type, false);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("uint256", rendered);
    const rich = try richIdentifierAlloc(std.testing.allocator, &uint256_type);
    defer std.testing.allocator.free(rich);
    try std.testing.expectEqualStrings("t_uint256", rich);
}

test "internal type identifiers use stable node references" {
    const source_id = CompatibilityIds.SourceId.init(12);
    var tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        source_id,
        "struct S {}",
        "S.sol",
    );
    defer tree.deinit();
    tree.next_node_id = 100;
    const declaration = try tree.createNode(.{}, .{ .struct_definition = .{
        .declaration = .{ .name = "S" },
    } });
    const type_ref = Types.Type{ .payload = .{ .Struct = .{
        .reference = .{},
        .declaration = declaration,
    } } };
    var projection = try CompatibilityIds.CompatibilityIdProjection.initAlloc(
        std.testing.allocator,
        &.{.{ .source = source_id, .node_count = 1 }},
    );
    defer projection.deinit();

    const stable = try richIdentifierAlloc(std.testing.allocator, &type_ref);
    defer std.testing.allocator.free(stable);
    const projected = try compatibilityRichIdentifierAlloc(
        std.testing.allocator,
        .init(&projection),
        &type_ref,
    );
    defer std.testing.allocator.free(projected);
    try std.testing.expectEqualStrings("t_struct(S)s12n0_storage_ptr", stable);
    try std.testing.expectEqualStrings("t_struct(S)1_storage_ptr", projected);

    var colliding_tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        CompatibilityIds.SourceId.init(13),
        "struct S {}",
        "Other.sol",
    );
    defer colliding_tree.deinit();
    colliding_tree.next_node_id = 100;
    const colliding_declaration = try colliding_tree.createNode(.{}, .{
        .struct_definition = .{ .declaration = .{ .name = "S" } },
    });
    const colliding_type = Types.Type{ .payload = .{ .Struct = .{
        .reference = .{},
        .declaration = colliding_declaration,
    } } };
    const colliding = try richIdentifierAlloc(std.testing.allocator, &colliding_type);
    defer std.testing.allocator.free(colliding);
    try std.testing.expectEqual(declaration.id, colliding_declaration.id);
    try std.testing.expect(!std.mem.eql(u8, stable, colliding));

    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    const first_struct = try provider.structType(declaration, .Storage);
    const second_struct = try provider.structType(colliding_declaration, .Storage);
    const tuple = try provider.tuple(&.{ first_struct, second_struct });
    const decomposition = try fullDecompositionAlloc(
        &provider,
        std.testing.allocator,
        tuple,
    );
    defer std.testing.allocator.free(decomposition);
    try std.testing.expectEqual(@as(usize, 3), decomposition.len);
    try std.testing.expect(decomposition[1] == first_struct);
    try std.testing.expect(decomposition[2] == second_struct);
}

test "contract conversions respect inheritance payability and the non-value super type" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Contracts.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const first = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "First" },
    } });
    const second = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Second" },
    } });
    const first_type = try provider.contract(first, false);
    const second_type = try provider.contract(second, false);
    try std.testing.expect(!isImplicitlyConvertibleTo(first_type, second_type));
    try std.testing.expect(!isExplicitlyConvertibleTo(first_type, second_type));

    const empty_parameters = try tree.createNode(.{}, .{ .parameter_list = .{} });
    const receive = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{},
            .parameters = empty_parameters,
        },
        .state_mutability = .Payable,
        .kind = .Receive,
    } });
    const base = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "PayableBase" },
        .sub_nodes = try tree.ownSlice(*AST.Node, &.{receive}),
    } });
    const derived = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Derived" },
    } });
    (try ASTAnnotations.ensure(&tree, base)).contract_definition.linearized_base_contracts =
        try tree.ownSlice(*AST.Node, &.{base});
    (try ASTAnnotations.ensure(&tree, derived)).contract_definition.linearized_base_contracts =
        try tree.ownSlice(*AST.Node, &.{ derived, base });
    const derived_type = try provider.contract(derived, false);
    try std.testing.expect((try encodingType(&provider, derived_type)).? ==
        provider.payableAddress());
    try std.testing.expect(!isExplicitlyConvertibleTo(provider.address(), derived_type));
    try std.testing.expect(isExplicitlyConvertibleTo(provider.payableAddress(), derived_type));

    const super_type = try provider.contract(derived, true);
    try std.testing.expect(!isImplicitlyConvertibleTo(super_type, super_type));
    try std.testing.expect(!isExplicitlyConvertibleTo(super_type, provider.address()));
    try std.testing.expect((try unaryOperatorResult(&provider, .Delete, super_type)) == null);
    try std.testing.expectError(error.InvalidType, calldataEncodedSize(super_type, true));
}

test "negative rational identifiers use the upstream minus component" {
    var numerator = Types.BigInt.initSigned(-2);
    defer numerator.deinit();
    var denominator = Types.BigInt.initUnsigned(1);
    defer denominator.deinit();
    const rational_type = Types.Type{ .payload = .{ .RationalNumber = .{
        .numerator = &numerator,
        .denominator = &denominator,
    } } };
    const identifier = try identifierAlloc(std.testing.allocator, &rational_type);
    defer std.testing.allocator.free(identifier);
    try std.testing.expectEqualStrings("t_rational_minus_2_by_1", identifier);
}

test "mapping data is always stored in storage" {
    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const mapping_type = Types.Type{ .payload = .{ .Mapping = .{
        .key_type = &uint_type,
        .value_type = &uint_type,
    } } };
    try std.testing.expect(dataStoredIn(&mapping_type, .Storage));
    try std.testing.expect(!dataStoredIn(&mapping_type, .Memory));
    try std.testing.expect(!dataStoredIn(&mapping_type, .CallData));
}

test "array and tuple formatting retains location and placeholders" {
    const byte_type = Types.Type{ .payload = .{ .FixedBytes = .{ .bytes = 1 } } };
    const bytes_memory = Types.Type{ .payload = .{ .Array = .{
        .reference = .{ .location = .Memory },
        .kind = .Bytes,
        .base_type = &byte_type,
    } } };
    const rendered = try toStringAlloc(std.testing.allocator, &bytes_memory, false);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("bytes memory", rendered);

    const tuple = Types.Type{ .payload = .{ .Tuple = .{
        .components = &.{ &byte_type, null, &bytes_memory },
    } } };
    const tuple_string = try toStringAlloc(std.testing.allocator, &tuple, false);
    defer std.testing.allocator.free(tuple_string);
    try std.testing.expectEqualStrings("tuple(bytes1,,bytes memory)", tuple_string);

    const nested_calldata = Types.Type{ .payload = .{ .Array = .{
        .reference = .{ .location = .CallData },
        .base_type = &bytes_memory,
    } } };
    const ordinary_name = try toStringAlloc(
        std.testing.allocator,
        &nested_calldata,
        false,
    );
    defer std.testing.allocator.free(ordinary_name);
    try std.testing.expectEqualStrings("bytes memory[] calldata", ordinary_name);
    const human_name = try humanReadableNameAlloc(
        std.testing.allocator,
        &nested_calldata,
    );
    defer std.testing.allocator.free(human_name);
    try std.testing.expectEqualStrings("bytes[] calldata", human_name);

    const human_tuple = try humanReadableNameAlloc(
        std.testing.allocator,
        &tuple,
    );
    defer std.testing.allocator.free(human_tuple);
    try std.testing.expectEqualStrings("tuple(bytes1,,bytes memory)", human_tuple);
}

test "stack layout recursively preserves named parts and tuple placeholders" {
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

    try std.testing.expectEqual(@as(usize, 3), try sizeOnStack(&tuple));
    var tuple_items = try stackItemsAlloc(std.testing.allocator, &tuple);
    defer tuple_items.deinit();
    try std.testing.expectEqual(@as(usize, 2), tuple_items.items.len);
    try std.testing.expectEqualStrings("component_1", tuple_items.items[0].name);
    try std.testing.expectEqualStrings("component_3", tuple_items.items[1].name);

    var array_items = try stackItemsAlloc(std.testing.allocator, &calldata_array);
    defer array_items.deinit();
    try std.testing.expectEqual(@as(usize, 2), array_items.items.len);
    try std.testing.expectEqualStrings("offset", array_items.items[0].name);
    try std.testing.expectEqualStrings("length", array_items.items[1].name);
}

test "external and bound function stack layouts include call options" {
    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const function = Types.Type{ .payload = .{ .Function = .{
        .parameter_types = &.{&uint_type},
        .kind = .External,
        .options = .{
            .gas_set = true,
            .value_set = true,
            .has_bound_first_argument = true,
        },
    } } };
    try std.testing.expectEqual(@as(usize, 5), try sizeOnStack(&function));
    var items = try stackItemsAlloc(std.testing.allocator, &function);
    defer items.deinit();
    try std.testing.expectEqual(@as(usize, 5), items.items.len);
    try std.testing.expectEqualStrings("address", items.items[0].name);
    try std.testing.expectEqualStrings("functionSelector", items.items[1].name);
    try std.testing.expectEqualStrings("gas", items.items[2].name);
    try std.testing.expectEqualStrings("value", items.items[3].name);
    try std.testing.expectEqualStrings("self", items.items[4].name);
}

test "provider-backed mobility operators interfaces and decomposition are analyzed" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const two = try provider.rationalInteger("2", null);
    const three = try provider.rationalInteger("3", null);
    const product = (try binaryOperatorResult(
        &provider,
        .Mul,
        two,
        three,
    )).?;
    try std.testing.expectEqual(
        std.math.Order.eq,
        product.payload.RationalNumber.numerator.compareUnsigned(6),
    );
    const negative = (try unaryOperatorResult(&provider, .Sub, two)).?;
    try std.testing.expect(negative.payload.RationalNumber.numerator.isNegative());
    try std.testing.expectEqual(@as(u256, 2), try literalValue(&provider, two, null));
    try std.testing.expect((try rationalIntegerType(
        &provider,
        product.payload.RationalNumber,
    )) != null);

    var one = Types.BigInt.initUnsigned(1);
    defer one.deinit();
    var two_denominator = Types.BigInt.initUnsigned(2);
    defer two_denominator.deinit();
    const half = try provider.rationalNumber(&one, &two_denominator, null);
    const half_fixed = (try rationalFixedPointType(
        &provider,
        half.payload.RationalNumber,
    )).?;
    try std.testing.expectEqual(@as(u8, 1), half_fixed.payload.FixedPoint.fractional_digits);

    const dynamic_calldata = try provider.array(.CallData, provider.uint256());
    const mobile_slice = try provider.arraySlice(dynamic_calldata);
    try std.testing.expect((try mobileType(&provider, mobile_slice)).? == dynamic_calldata);
    const static_calldata = try provider.arrayWithLength(
        .CallData,
        provider.uint256(),
        2,
    );
    const static_slice = try provider.arraySlice(static_calldata);
    try std.testing.expect((try mobileType(&provider, static_slice)).? == static_slice);

    const storage_array = try provider.array(.Storage, provider.uint256());
    try std.testing.expect((try encodingType(&provider, storage_array)).? == provider.uint256());
    const bytes_interface = (try interfaceType(
        &provider,
        provider.bytesStorage(),
        false,
    )).?;
    try std.testing.expectEqual(Types.DataLocation.Memory, bytes_interface.asReference().?.location);
    try std.testing.expect((try fullEncodingType(
        &provider,
        provider.bytesStorage(),
        false,
        true,
        false,
    )) != null);

    const mapping = try provider.mapping(provider.uint256(), "", provider.uint256(), "");
    const nested = try provider.array(.Storage, mapping);
    try std.testing.expect(try containsNestedMapping(&provider, nested));
    try std.testing.expect(!hasSimpleZeroValueInMemory(nested));
    try std.testing.expect(try validForLocation(&provider, nested, .Storage));
    const huge = try provider.arrayWithLength(
        .Memory,
        provider.uint256(),
        std.math.maxInt(u32),
    );
    try std.testing.expect(!(try validForLocation(&provider, huge, .Memory)));

    const decomposition = try fullDecompositionAlloc(
        &provider,
        std.testing.allocator,
        nested,
    );
    defer std.testing.allocator.free(decomposition);
    try std.testing.expectEqual(@as(usize, 3), decomposition.len);
    try std.testing.expect(decomposition[0] == nested);
    try std.testing.expect(decomposition[1] == mapping);
    try std.testing.expect(decomposition[2] == provider.uint256());

    const first_array = try provider.array(.Memory, provider.uint256());
    const second_array = try provider.array(.Memory, provider.uint256());
    const first_tuple = try provider.tuple(&.{first_array});
    const second_tuple = try provider.tuple(&.{second_array});
    const outer_tuple = try provider.tuple(&.{ first_tuple, second_tuple });
    const tuple_decomposition = try fullDecompositionAlloc(
        &provider,
        std.testing.allocator,
        outer_tuple,
    );
    defer std.testing.allocator.free(tuple_decomposition);
    // Stable rich identifiers preserve upstream structural tuple deduplication
    // without deriving declaration identity from compatibility IDs.
    try std.testing.expectEqual(@as(usize, 4), tuple_decomposition.len);
    try std.testing.expect(tuple_decomposition[0] == outer_tuple);
    try std.testing.expect(tuple_decomposition[1] == first_tuple);
    try std.testing.expect(tuple_decomposition[2] == first_array);
    try std.testing.expect(tuple_decomposition[3] == provider.uint256());
}

test "rational evaluator and conversion boundaries match upstream semantics" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    var five = Types.BigInt.initUnsigned(5);
    defer five.deinit();
    var three = Types.BigInt.initUnsigned(3);
    defer three.deinit();
    var two = Types.BigInt.initUnsigned(2);
    defer two.deinit();
    const five_halves = try provider.rationalNumber(&five, &two, null);
    const three_halves = try provider.rationalNumber(&three, &two, null);
    const remainder = (try binaryOperatorResult(
        &provider,
        .Mod,
        five_halves,
        three_halves,
    )).?;
    try std.testing.expectEqual(
        std.math.Order.eq,
        remainder.payload.RationalNumber.numerator.compareUnsigned(1),
    );
    try std.testing.expectEqual(
        std.math.Order.eq,
        remainder.payload.RationalNumber.denominator.compareUnsigned(1),
    );

    const zero = try provider.rationalInteger("0", null);
    try std.testing.expect(!isValueType(zero));
    const negative_one = try provider.rationalInteger("-1", null);
    const huge_odd = try provider.rationalInteger("4294967297", null);
    const zero_power = (try binaryOperatorResult(
        &provider,
        .Exp,
        zero,
        huge_odd,
    )).?;
    try std.testing.expect(zero_power.payload.RationalNumber.numerator.isZero());
    const negative_one_power = (try binaryOperatorResult(
        &provider,
        .Exp,
        negative_one,
        huge_odd,
    )).?;
    try std.testing.expect(negative_one_power.payload.RationalNumber.numerator.isNegative());

    const base_two = try provider.rationalInteger("2", null);
    const exponent_2048 = try provider.rationalInteger("2048", null);
    const exponent_2049 = try provider.rationalInteger("2049", null);
    try std.testing.expect((try binaryOperatorResult(
        &provider,
        .Exp,
        base_two,
        exponent_2048,
    )) != null);
    try std.testing.expect((try binaryOperatorResult(
        &provider,
        .Exp,
        base_two,
        exponent_2049,
    )) == null);

    const shift_4095 = try provider.rationalInteger("4095", null);
    const shift_4096 = try provider.rationalInteger("4096", null);
    try std.testing.expect((try binaryOperatorResult(
        &provider,
        .SHL,
        try provider.rationalInteger("1", null),
        shift_4095,
    )) != null);
    try std.testing.expect((try binaryOperatorResult(
        &provider,
        .SHL,
        try provider.rationalInteger("1", null),
        shift_4096,
    )) == null);

    try std.testing.expect(isExplicitlyConvertibleTo(zero, provider.payableAddress()));
    const literal_255 = try provider.rationalInteger("255", null);
    try std.testing.expect(isExplicitlyConvertibleTo(
        literal_255,
        try provider.fixedPoint(8, 0, .Unsigned),
    ));
    try std.testing.expect(isImplicitlyConvertibleTo(
        try provider.uint(8),
        try provider.fixedPoint(16, 0, .Signed),
    ));
    try std.testing.expect(isImplicitlyConvertibleTo(
        try provider.fixedPoint(8, 0, .Unsigned),
        try provider.fixedPoint(16, 0, .Signed),
    ));
}

test "string references slices and display forms retain exact conversion rules" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const literal = try provider.stringLiteral("hello");
    try std.testing.expect(!isValueType(literal));
    const storage_reference = try provider.withLocation(
        provider.stringStorage(),
        .Storage,
        false,
    );
    try std.testing.expect(isImplicitlyConvertibleTo(literal, storage_reference));
    try std.testing.expect(!isImplicitlyConvertibleTo(literal, provider.stringStorage()));
    try std.testing.expect(!isImplicitlyConvertibleTo(literal, provider.stringCalldata()));
    const invalid_utf8 = try provider.stringLiteral(&.{ 0xff, 0xfe });
    try std.testing.expect(!isImplicitlyConvertibleTo(invalid_utf8, provider.stringMemory()));
    const rendered = try toStringAlloc(std.testing.allocator, invalid_utf8, false);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("literal_string hex\"fffe\"", rendered);

    const calldata_array = try provider.array(.CallData, provider.uint256());
    const memory_array = try provider.array(.Memory, provider.uint256());
    const slice = try provider.arraySlice(calldata_array);
    try std.testing.expect(isImplicitlyConvertibleTo(slice, memory_array));
    const slice_string = try toStringAlloc(std.testing.allocator, slice, false);
    defer std.testing.allocator.free(slice_string);
    try std.testing.expectEqualStrings("uint256[] calldata slice", slice_string);
    const slice_rich = try richIdentifierAlloc(std.testing.allocator, slice);
    defer std.testing.allocator.free(slice_rich);
    try std.testing.expectEqualStrings("t_array(t_uint256)dyn_calldata_ptr_slice", slice_rich);
}

test "function projection signatures arguments and constructors are one behavior family" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Functions.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const amount = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "amount" },
    } });
    (try ASTAnnotations.ensure(&tree, amount)).variable_declaration.type_ref =
        provider.uint256();
    const parameters = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{amount}),
    } });
    const constructor = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "" },
            .parameters = parameters,
        },
        .state_mutability = .Payable,
        .kind = .Constructor,
    } });
    const contract = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Wallet" },
        .sub_nodes = try tree.ownSlice(*AST.Node, &.{constructor}),
    } });
    try (try ASTAnnotations.ensure(&tree, contract))
        .contract_definition.type_declaration.canonical_name.assign("pkg.Wallet");
    (ASTAnnotations.scopable(try ASTAnnotations.ensure(&tree, constructor))).?.scope = contract;

    const creation = (try newExpressionType(&provider, contract)).asFunction().?;
    try std.testing.expectEqual(Types.FunctionKind.Creation, creation.kind);
    try std.testing.expectEqual(Types.StateMutability.Payable, creation.state_mutability);
    try std.testing.expectEqual(@as(usize, 1), creation.parameter_types.len);
    try std.testing.expectEqualStrings("amount", creation.parameter_names[0]);

    const call = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "pay" },
            .parameters = parameters,
        },
    } });
    (ASTAnnotations.scopable(try ASTAnnotations.ensure(&tree, call))).?.scope = contract;
    const callable_type = try provider.function(
        &.{provider.uint256()},
        &.{provider.bytesMemory()},
        &.{"amount"},
        &.{"data"},
        .External,
        .NonPayable,
        call,
        .{},
    );
    const callable = callable_type.asFunction().?;

    const declaration_type = try provider.function(
        &.{provider.uint256()},
        &.{provider.bytesMemory()},
        &.{"amount"},
        &.{"data"},
        .Declaration,
        .NonPayable,
        call,
        .{},
    );
    const declaration_name = try toStringAlloc(
        std.testing.allocator,
        declaration_type,
        false,
    );
    defer std.testing.allocator.free(declaration_name);
    try std.testing.expectEqualStrings(
        "function pkg.Wallet.pay(uint256) returns (bytes memory)",
        declaration_name,
    );

    const event = try tree.createNode(.{}, .{ .event_definition = .{
        .callable = .{
            .declaration = .{ .name = "Paid" },
            .parameters = parameters,
        },
    } });
    const event_type = try provider.functionFromEvent(event);
    const event_name = try humanReadableNameAlloc(
        std.testing.allocator,
        event_type,
    );
    defer std.testing.allocator.free(event_name);
    try std.testing.expectEqualStrings("event Paid(uint256)", event_name);

    const signature = try externalSignatureAlloc(
        &provider,
        std.testing.allocator,
        callable.*,
    );
    defer std.testing.allocator.free(signature);
    try std.testing.expectEqualStrings("pay(uint256)", signature);
    try std.testing.expectEqual(
        @as(u256, FunctionSelector.selectorFromSignatureU32("pay(uint256)")),
        try externalIdentifier(&provider, std.testing.allocator, callable.*),
    );
    const selector_hex = try externalIdentifierHexAlloc(
        &provider,
        std.testing.allocator,
        callable.*,
    );
    defer std.testing.allocator.free(selector_hex);
    try std.testing.expectEqual(@as(usize, 8), selector_hex.len);

    const projected = (try interfaceFunctionType(&provider, callable.*)).?.asFunction().?;
    try std.testing.expectEqual(Types.DataLocation.Memory, projected.return_parameter_types[0].asReference().?.location);
    const returns = try returnParameterTypesWithoutDynamicTypesAlloc(
        &provider,
        std.testing.allocator,
        callable.*,
    );
    defer std.testing.allocator.free(returns);
    try std.testing.expectEqual(Types.Category.InaccessibleDynamic, returns[0].category());

    var arguments: Enums.FuncCallArguments = .{};
    defer arguments.deinit(std.testing.allocator);
    try arguments.types.append(std.testing.allocator, provider.uint(8) catch unreachable);
    try std.testing.expect(functionCanTakeArguments(callable.*, &arguments, null));
    try arguments.names.append(std.testing.allocator, "amount");
    try std.testing.expect(functionCanTakeArguments(callable.*, &arguments, null));
    try std.testing.expect(functionHasEqualParameterTypes(callable.*, callable.*));
    try std.testing.expect(functionHasEqualReturnTypes(callable.*, callable.*));
    try std.testing.expect(functionEqualExcludingStateMutability(callable.*, callable.*));
    try std.testing.expect(!functionIsBareCall(callable.*));
    try std.testing.expect(functionIsPure((try provider.function(
        &.{},
        &.{},
        &.{},
        &.{},
        .KECCAK256,
        .Pure,
        null,
        .{},
    )).payload.Function));
    try std.testing.expect(functionPadsArguments(callable.*));
    const hash_function = (try provider.function(
        &.{provider.bytesMemory()},
        &.{try provider.fixedBytes(32)},
        &.{""},
        &.{""},
        .KECCAK256,
        .Pure,
        null,
        .{},
    )).payload.Function;
    try std.testing.expect(!functionPadsArguments(hash_function));
    try std.testing.expect(functionTakesSinglePackedBytesParameter(hash_function));

    const calldata_callable = (try provider.function(
        &.{provider.bytesCalldata()},
        &.{provider.bytesCalldata()},
        &.{""},
        &.{""},
        .External,
        .View,
        call,
        .{},
    )).payload.Function;
    const external_callable = (try asExternallyCallableFunction(
        &provider,
        calldata_callable,
        false,
    )).payload.Function;
    try std.testing.expectEqual(Types.DataLocation.Memory, external_callable.parameter_types[0].asReference().?.location);
    try std.testing.expectEqual(Types.DataLocation.Memory, external_callable.return_parameter_types[0].asReference().?.location);

    const member = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "value" },
    } });
    (try ASTAnnotations.ensure(&tree, member)).variable_declaration.type_ref = provider.uint256();
    const definition = try tree.createNode(.{}, .{ .struct_definition = .{
        .declaration = .{ .name = "Record" },
        .members = try tree.ownSlice(*AST.Node, &.{member}),
    } });
    (try ASTAnnotations.ensure(&tree, definition)).struct_declaration.recursive = false;
    const structure = try provider.structType(definition, .Storage);
    const constructor_type = (try structConstructorType(&provider, structure)).asFunction().?;
    try std.testing.expectEqualStrings("value", constructor_type.parameter_names[0]);
    try std.testing.expectEqual(Types.DataLocation.Memory, constructor_type.return_parameter_types[0].asReference().?.location);
    const struct_signature = try signatureInExternalFunctionAlloc(
        &provider,
        std.testing.allocator,
        structure,
        false,
    );
    defer std.testing.allocator.free(struct_signature);
    try std.testing.expectEqualStrings("(uint256)", struct_signature);
}

test "native members materialize every closed type family with explicit ownership" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Members.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    var address_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        provider.payableAddress(),
        null,
    );
    defer address_members.deinit();
    try std.testing.expectEqual(@as(usize, 9), address_members.items.len);
    try std.testing.expect(address_members.borrowed().memberType("transfer") != null);

    const storage_array = try provider.array(.Storage, provider.uint256());
    var array_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        storage_array,
        null,
    );
    defer array_members.deinit();
    try std.testing.expectEqual(@as(usize, 4), array_members.items.len);
    try std.testing.expectEqual(@as(usize, 2), array_members.borrowed().countByName("push"));

    const parameter = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "value" },
    } });
    (try ASTAnnotations.ensure(&tree, parameter)).variable_declaration.type_ref =
        provider.uint256();
    const parameters = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{parameter}),
    } });
    const function = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "set", .visibility = .Public },
            .parameters = parameters,
        },
        .body = try tree.createNode(.{}, .{ .block = .{} }),
    } });
    const contract = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Store" },
        .sub_nodes = try tree.ownSlice(*AST.Node, &.{function}),
    } });
    (ASTAnnotations.scopable(try ASTAnnotations.ensure(&tree, function))).?.scope = contract;
    (try ASTAnnotations.ensure(&tree, contract)).contract_definition.linearized_base_contracts =
        try tree.ownSlice(*AST.Node, &.{contract});
    const contract_type = try provider.contract(contract, false);
    var contract_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        contract_type,
        null,
    );
    defer contract_members.deinit();
    try std.testing.expectEqual(@as(usize, 1), contract_members.items.len);
    try std.testing.expectEqualStrings("set", contract_members.items[0].name);

    const external = try provider.function(
        &.{provider.uint256()},
        &.{},
        &.{""},
        &.{},
        .External,
        .Payable,
        function,
        .{},
    );
    var function_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        external,
        contract,
    );
    defer function_members.deinit();
    try std.testing.expectEqual(@as(usize, 4), function_members.items.len);
    try std.testing.expect(function_members.borrowed().memberType("selector") != null);
    try std.testing.expect(function_members.borrowed().memberType("value") != null);
    try std.testing.expect(function_members.borrowed().memberType("gas") != null);

    const first = try tree.createNode(.{}, .{ .enum_value = .{
        .declaration = .{ .name = "First" },
    } });
    const second = try tree.createNode(.{}, .{ .enum_value = .{
        .declaration = .{ .name = "Second" },
    } });
    const enum_definition = try tree.createNode(.{}, .{ .enum_definition = .{
        .declaration = .{ .name = "Choice" },
        .members = try tree.ownSlice(*AST.Node, &.{ first, second }),
    } });
    const enum_type = try provider.enumType(enum_definition);
    var enum_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        try provider.typeType(enum_type),
        null,
    );
    defer enum_members.deinit();
    try std.testing.expectEqual(@as(usize, 2), enum_members.items.len);
    try std.testing.expect(enum_members.borrowed().memberType("Second") == enum_type);

    const underlying_name = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try AST.ElementaryTypeNameToken.init(.UIntM, 256, 0),
    } });
    const value_definition = try tree.createNode(.{}, .{ .user_defined_value_type_definition = .{
        .declaration = .{ .name = "Amount" },
        .underlying_type = underlying_name,
    } });
    const value_type = try provider.userDefinedValueType(
        value_definition,
        provider.uint256(),
    );
    var value_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        try provider.typeType(value_type),
        null,
    );
    defer value_members.deinit();
    try std.testing.expect(value_members.borrowed().memberType("wrap") != null);
    try std.testing.expect(value_members.borrowed().memberType("unwrap") != null);

    var abi_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        try provider.magic(.ABI),
        null,
    );
    defer abi_members.deinit();
    try std.testing.expectEqual(@as(usize, 6), abi_members.items.len);
    try std.testing.expect(abi_members.borrowed().memberType("encodeCall") != null);
    var integer_meta_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        try provider.meta(provider.uint256()),
        null,
    );
    defer integer_meta_members.deinit();
    try std.testing.expectEqual(@as(usize, 2), integer_meta_members.items.len);

    const private_variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "hidden", .visibility = .Private },
    } });
    const public_variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "visible", .visibility = .Public },
    } });
    (try ASTAnnotations.ensure(&tree, private_variable)).variable_declaration.type_ref =
        provider.uint256();
    (try ASTAnnotations.ensure(&tree, public_variable)).variable_declaration.type_ref =
        provider.uint256();
    const namespaced_contract = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Namespaced" },
        .sub_nodes = try tree.ownSlice(
            *AST.Node,
            &.{ private_variable, public_variable },
        ),
    } });
    const namespaced_type = try provider.typeType(
        try provider.contract(namespaced_contract, false),
    );
    var local_names = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        namespaced_type,
        namespaced_contract,
    );
    defer local_names.deinit();
    try std.testing.expect(local_names.borrowed().memberType("hidden") == null);
    try std.testing.expect(local_names.borrowed().memberType("visible") == provider.uint256());
    var foreign_names = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        namespaced_type,
        null,
    );
    defer foreign_names.deinit();
    try std.testing.expect(foreign_names.borrowed().memberType("hidden") == null);
    try std.testing.expect(foreign_names.borrowed().memberType("visible") == null);

    const empty_parameters = try tree.createNode(.{}, .{ .parameter_list = .{} });
    const free_function = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "helper" },
            .parameters = empty_parameters,
        },
        .free = true,
        .body = try tree.createNode(.{}, .{ .block = .{} }),
    } });
    const source_unit = try tree.createNode(.{}, .{ .source_unit = .{
        .nodes = try tree.ownSlice(*AST.Node, &.{free_function}),
    } });
    (ASTAnnotations.scopable(try ASTAnnotations.ensure(&tree, free_function))).?.scope =
        source_unit;
    const exported = try tree.ownSlice(ASTAnnotations.ExportedSymbol, &.{.{
        .name = "helper",
        .declarations = try tree.ownSlice(*AST.Node, &.{free_function}),
    }});
    try (try ASTAnnotations.ensure(&tree, source_unit)).source_unit.exported_symbols.assign(
        exported,
    );
    var module_members = try nativeMembersAlloc(
        &provider,
        std.testing.allocator,
        try provider.module(source_unit),
        null,
    );
    defer module_members.deinit();
    const imported_helper = module_members.borrowed().memberType("helper").?.asFunction().?;
    try std.testing.expectEqual(Types.FunctionKind.Internal, imported_helper.kind);
}

test "using-for members and user-defined operators are resolved as one directive set" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Using.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const underlying_name = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try AST.ElementaryTypeNameToken.init(.UIntM, 256, 0),
    } });
    const value_definition = try tree.createNode(.{}, .{ .user_defined_value_type_definition = .{
        .declaration = .{ .name = "Amount" },
        .underlying_type = underlying_name,
    } });
    const value_type = try provider.userDefinedValueType(
        value_definition,
        provider.uint256(),
    );
    const left = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "left" },
    } });
    const right = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "right" },
    } });
    (try ASTAnnotations.ensure(&tree, left)).variable_declaration.type_ref = value_type;
    (try ASTAnnotations.ensure(&tree, right)).variable_declaration.type_ref = value_type;
    const parameters = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{ left, right }),
    } });
    const returns = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{left}),
    } });
    const add = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "add" },
            .parameters = parameters,
            .return_parameters = returns,
        },
        .free = true,
        .state_mutability = .Pure,
        .body = try tree.createNode(.{}, .{ .block = .{} }),
    } });
    const path = try tree.createNode(.{}, .{ .identifier_path = .{
        .path = &.{"plus"},
        .path_locations = &.{.{}},
    } });
    (try ASTAnnotations.ensure(&tree, path)).identifier_path.referenced_declaration = add;
    const directive_type = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try AST.ElementaryTypeNameToken.init(.UIntM, 256, 0),
    } });
    (try ASTAnnotations.ensure(&tree, directive_type)).type_name.type_ref = value_type;
    const using = try tree.createNode(.{}, .{ .using_for_directive = .{
        .functions_and_operators = try tree.ownSlice(AST.FunctionAndOperator, &.{
            .{ .function_or_library = path },
            .{ .function_or_library = path, .operator = .Add },
        }),
        .uses_braces = true,
        .type_name = directive_type,
    } });
    const source = try tree.createNode(.{}, .{ .source_unit = .{
        .nodes = try tree.ownSlice(*AST.Node, &.{ value_definition, add, using }),
    } });
    (ASTAnnotations.scopable(try ASTAnnotations.ensure(&tree, value_definition))).?.scope = source;
    (ASTAnnotations.scopable(try ASTAnnotations.ensure(&tree, add))).?.scope = source;

    var attached = try attachedFunctionsAlloc(
        &provider,
        std.testing.allocator,
        value_type,
        source,
    );
    defer attached.deinit();
    try std.testing.expectEqual(@as(usize, 1), attached.items.len);
    try std.testing.expectEqualStrings("plus", attached.items[0].name);
    try std.testing.expect(attached.items[0].type_ref.asFunction().?.options.has_bound_first_argument);

    const definitions = try operatorDefinitionsAlloc(
        &provider,
        std.testing.allocator,
        value_type,
        .Add,
        source,
        false,
    );
    defer std.testing.allocator.free(definitions);
    try std.testing.expectEqual(@as(usize, 1), definitions.len);
    try std.testing.expect(definitions[0] == add);

    var members = try membersAlloc(
        &provider,
        std.testing.allocator,
        value_type,
        source,
    );
    defer members.deinit();
    try std.testing.expect(members.borrowed().memberType("plus") != null);
}

test "contract and struct state layout preserve inheritance packing and locations" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Layout.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const base_a = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "a" },
    } });
    const base_b = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "b" },
    } });
    const immutable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "frozen" },
        .mutability = .Immutable,
    } });
    (try ASTAnnotations.ensure(&tree, base_a)).variable_declaration.type_ref =
        try provider.uint(8);
    (try ASTAnnotations.ensure(&tree, base_b)).variable_declaration.type_ref =
        try provider.uint(16);
    (try ASTAnnotations.ensure(&tree, immutable)).variable_declaration.type_ref =
        provider.uint256();
    const base = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Base" },
        .sub_nodes = try tree.ownSlice(*AST.Node, &.{ base_a, base_b, immutable }),
    } });

    const derived_c = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "c" },
    } });
    const transient = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "scratch" },
        .reference_location = .Transient,
    } });
    (try ASTAnnotations.ensure(&tree, derived_c)).variable_declaration.type_ref =
        provider.uint256();
    (try ASTAnnotations.ensure(&tree, transient)).variable_declaration.type_ref =
        try provider.uint(8);
    const base_expression = try tree.createNode(.{}, .{ .literal = .{
        .token = .Number,
        .value = "5",
    } });
    const layout_specifier = try tree.createNode(.{}, .{ .storage_layout_specifier = .{
        .base_slot_expression = base_expression,
    } });
    try (try ASTAnnotations.ensure(&tree, layout_specifier)).storage_layout_specifier.base_slot.assign(5);
    const derived = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Derived" },
        .sub_nodes = try tree.ownSlice(*AST.Node, &.{ derived_c, transient }),
        .storage_layout_specifier = layout_specifier,
    } });
    (try ASTAnnotations.ensure(&tree, base)).contract_definition.linearized_base_contracts =
        try tree.ownSlice(*AST.Node, &.{base});
    (try ASTAnnotations.ensure(&tree, derived)).contract_definition.linearized_base_contracts =
        try tree.ownSlice(*AST.Node, &.{ derived, base });

    const contract_type = (try provider.contract(derived, false)).payload.Contract;
    const storage_layout = try linearizedStateVariablesAlloc(
        std.testing.allocator,
        contract_type,
        .Storage,
    );
    defer std.testing.allocator.free(storage_layout);
    try std.testing.expectEqual(@as(usize, 3), storage_layout.len);
    try std.testing.expect(storage_layout[0].declaration == base_a);
    try std.testing.expectEqual(@as(u256, 5), storage_layout[0].slot);
    try std.testing.expectEqual(@as(u8, 0), storage_layout[0].byte_offset);
    try std.testing.expectEqual(@as(u256, 5), storage_layout[1].slot);
    try std.testing.expectEqual(@as(u8, 1), storage_layout[1].byte_offset);
    try std.testing.expectEqual(@as(u256, 6), storage_layout[2].slot);

    const transient_layout = try linearizedStateVariablesAlloc(
        std.testing.allocator,
        contract_type,
        .Transient,
    );
    defer std.testing.allocator.free(transient_layout);
    try std.testing.expectEqual(@as(usize, 1), transient_layout.len);
    try std.testing.expectEqual(@as(u256, 0), transient_layout[0].slot);
    const immutables = try immutableVariablesAlloc(std.testing.allocator, contract_type);
    defer std.testing.allocator.free(immutables);
    try std.testing.expectEqual(@as(usize, 1), immutables.len);
    try std.testing.expect(immutables[0] == immutable);
    try std.testing.expectEqual(
        @as(u256, 3),
        try contractStorageSizeUpperBound(derived, .Storage),
    );

    const struct_definition = try tree.createNode(.{}, .{ .struct_definition = .{
        .declaration = .{ .name = "Packed" },
        .members = try tree.ownSlice(*AST.Node, &.{ base_a, base_b }),
    } });
    (try ASTAnnotations.ensure(&tree, struct_definition)).struct_declaration.recursive = false;
    const structure = (try provider.structType(struct_definition, .Storage)).payload.Struct;
    try std.testing.expectEqual(
        @as(u256, 1),
        try storageSize(&.{ .payload = .{ .Struct = structure } }),
    );
    const packed_offsets = try structStorageOffsetsAlloc(std.testing.allocator, structure);
    defer std.testing.allocator.free(packed_offsets.offsets);
    try std.testing.expectEqual(@as(u256, 1), packed_offsets.storage_size);
    try std.testing.expectEqual(@as(u8, 1), packed_offsets.offsets[1].?.byte_offset);
    const b_offset = try structStorageOffsetOfMember(
        std.testing.allocator,
        structure,
        "b",
    );
    try std.testing.expectEqual(@as(u8, 1), b_offset.byte_offset);
    const memory_members = try structMemoryMemberTypesAlloc(
        &provider,
        std.testing.allocator,
        structure,
    );
    defer std.testing.allocator.free(memory_members);
    try std.testing.expectEqual(@as(usize, 2), memory_members.len);

    const first = try tree.createNode(.{}, .{ .enum_value = .{
        .declaration = .{ .name = "First" },
    } });
    const second = try tree.createNode(.{}, .{ .enum_value = .{
        .declaration = .{ .name = "Second" },
    } });
    const enum_definition = try tree.createNode(.{}, .{ .enum_definition = .{
        .declaration = .{ .name = "Choice" },
        .members = try tree.ownSlice(*AST.Node, &.{ first, second }),
    } });
    const enumeration = (try provider.enumType(enum_definition)).payload.Enum;
    try std.testing.expectEqual(@as(u8, 1), try enumMemberValue(enumeration, "Second"));
    try std.testing.expectEqual(@as(usize, 2), try enumNumberOfMembers(enumeration));
    try std.testing.expectEqual(@as(u8, 1), try enumMaxValue(enumeration));
}

pub const Token = TokenModule.Token;

pub const StateMutability = Enums.StateMutability;

pub const BigInt = Numeric.BigInt;

pub const DataLocation = enum(c_int) {
    Storage,
    Transient,
    CallData,
    Memory,
};

pub const Category = enum(c_int) {
    Address,
    Integer,
    RationalNumber,
    StringLiteral,
    Bool,
    FixedPoint,
    Array,
    ArraySlice,
    FixedBytes,
    Contract,
    Struct,
    Function,
    Enum,
    UserDefinedValueType,
    Tuple,
    Mapping,
    TypeType,
    Modifier,
    Magic,
    Module,
    InaccessibleDynamic,
};

pub const IntegerModifier = enum(c_int) {
    Unsigned,
    Signed,
};

pub const FixedPointModifier = enum(c_int) {
    Unsigned,
    Signed,
};

pub const ArrayKind = enum(c_int) {
    Ordinary,
    Bytes,
    String,
};

/// How a function is invoked on the EVM.  The ordinal order is part of the
/// structurally translated ABI and matches `FunctionType::Kind` exactly.
pub const FunctionKind = enum(c_int) {
    Internal,
    External,
    DelegateCall,
    BareCall,
    BareCallCode,
    BareDelegateCall,
    BareStaticCall,
    Creation,
    Send,
    Transfer,
    KECCAK256,
    ERC7201,
    Selfdestruct,
    Revert,
    ECRecover,
    SHA256,
    RIPEMD160,
    Event,
    Error,
    Wrap,
    Unwrap,
    SetGas,
    SetValue,
    BlockHash,
    BlobHash,
    AddMod,
    MulMod,
    ArrayPush,
    ArrayPop,
    BytesConcat,
    StringConcat,
    ObjectCreation,
    Assert,
    Require,
    ABIEncode,
    ABIEncodePacked,
    ABIEncodeWithSelector,
    ABIEncodeCall,
    ABIEncodeWithSignature,
    ABIDecode,
    GasLeft,
    MetaType,
    Declaration,
};

pub const FunctionOptions = packed struct {
    arbitrary_parameters: bool = false,
    gas_set: bool = false,
    value_set: bool = false,
    salt_set: bool = false,
    has_bound_first_argument: bool = false,

    pub fn withArbitraryParameters() FunctionOptions {
        return .{ .arbitrary_parameters = true };
    }
};

pub const MagicKind = enum(c_int) {
    Block,
    Message,
    Transaction,
    ABI,
    Error,
    MetaType,
};

pub const ReferenceData = struct {
    location: DataLocation = .Storage,
    /// Meaningful only for storage.  Memory and calldata references always
    /// behave as pointers, matching `ReferenceType::isPointer()`.
    storage_pointer: bool = true,

    pub fn isPointer(self: ReferenceData) bool {
        return self.location != .Storage or self.storage_pointer;
    }
};

pub const AddressType = struct {
    state_mutability: StateMutability,
};

pub const IntegerType = struct {
    bits: u16,
    modifier: IntegerModifier,

    pub fn isSigned(self: IntegerType) bool {
        return self.modifier == .Signed;
    }
};

pub const FixedPointType = struct {
    total_bits: u16,
    fractional_digits: u8,
    modifier: FixedPointModifier,

    pub fn isSigned(self: FixedPointType) bool {
        return self.modifier == .Signed;
    }
};

/// Arbitrary-precision values are owned and torn down by `TypeProvider`; the type graph only
/// borrows them.  Denominators are positive and values are normalized.
pub const RationalNumberType = struct {
    numerator: *const BigInt,
    denominator: *const BigInt,
    compatible_bytes_type: ?*const Type = null,
};

pub const StringLiteralType = struct {
    value: []const u8,
};

pub const FixedBytesType = struct {
    bytes: u8,
};

pub const ArrayType = struct {
    reference: ReferenceData,
    kind: ArrayKind = .Ordinary,
    base_type: *const Type,
    /// `null` is a dynamic length; a present value is a static length.
    length: ?u256 = null,

    pub fn isDynamicallySized(self: ArrayType) bool {
        return self.length == null;
    }

    pub fn isByteArray(self: ArrayType) bool {
        return self.kind == .Bytes;
    }

    pub fn isByteArrayOrString(self: ArrayType) bool {
        return self.kind != .Ordinary;
    }

    pub fn isString(self: ArrayType) bool {
        return self.kind == .String;
    }
};

pub const ArraySliceType = struct {
    array_type: *const Type,
};

pub const ContractType = struct {
    declaration: *const AST.Node,
    is_super: bool = false,
};

pub const StructType = struct {
    reference: ReferenceData,
    declaration: *const AST.Node,
};

pub const FunctionType = struct {
    parameter_types: []const *const Type = &.{},
    return_parameter_types: []const *const Type = &.{},
    parameter_names: []const []const u8 = &.{},
    return_parameter_names: []const []const u8 = &.{},
    kind: FunctionKind = .Internal,
    state_mutability: StateMutability = .NonPayable,
    declaration: ?*const AST.Node = null,
    options: FunctionOptions = .{},

    pub fn parameterTypes(self: FunctionType) []const *const Type {
        if (!self.options.has_bound_first_argument) return self.parameter_types;
        std.debug.assert(self.parameter_types.len != 0);
        return self.parameter_types[1..];
    }

    pub fn parameterNames(self: FunctionType) []const []const u8 {
        if (!self.options.has_bound_first_argument) return self.parameter_names;
        std.debug.assert(self.parameter_names.len != 0);
        return self.parameter_names[1..];
    }

    pub fn selfType(self: FunctionType) ?*const Type {
        if (!self.options.has_bound_first_argument) return null;
        return self.parameter_types[0];
    }
};

pub const EnumType = struct {
    declaration: *const AST.Node,
};

pub const UserDefinedValueType = struct {
    declaration: *const AST.Node,
    /// Filled when declaration type checking resolves the elementary
    /// underlying type.  Keeping it here avoids a type/annotation import
    /// cycle while retaining a concrete type identity.
    underlying_type: ?*const Type = null,
};

pub const TupleType = struct {
    /// Null components represent tuple placeholders.
    components: []const ?*const Type = &.{},
};

pub const MappingType = struct {
    key_type: *const Type,
    key_name: []const u8 = "",
    value_type: *const Type,
    value_name: []const u8 = "",
};

pub const TypeType = struct {
    actual_type: *const Type,
};

pub const ModifierType = struct {
    parameter_types: []const *const Type = &.{},
};

pub const MagicType = struct {
    kind: MagicKind,
    type_argument: ?*const Type = null,
};

pub const ModuleType = struct {
    source_unit: *const AST.Node,
};

pub const Payload = union(Category) {
    Address: AddressType,
    Integer: IntegerType,
    RationalNumber: RationalNumberType,
    StringLiteral: StringLiteralType,
    Bool: void,
    FixedPoint: FixedPointType,
    Array: ArrayType,
    ArraySlice: ArraySliceType,
    FixedBytes: FixedBytesType,
    Contract: ContractType,
    Struct: StructType,
    Function: FunctionType,
    Enum: EnumType,
    UserDefinedValueType: UserDefinedValueType,
    Tuple: TupleType,
    Mapping: MappingType,
    TypeType: TypeType,
    Modifier: ModifierType,
    Magic: MagicType,
    Module: ModuleType,
    InaccessibleDynamic: void,
};

pub const Type = struct {
    payload: Payload,

    pub fn category(self: *const Type) Category {
        return std.meta.activeTag(self.payload);
    }

    pub fn asAddress(self: *const Type) ?*const AddressType {
        return switch (self.payload) {
            .Address => |*value| value,
            else => null,
        };
    }

    pub fn asInteger(self: *const Type) ?*const IntegerType {
        return switch (self.payload) {
            .Integer => |*value| value,
            else => null,
        };
    }

    pub fn asFixedPoint(self: *const Type) ?*const FixedPointType {
        return switch (self.payload) {
            .FixedPoint => |*value| value,
            else => null,
        };
    }

    pub fn asFixedBytes(self: *const Type) ?*const FixedBytesType {
        return switch (self.payload) {
            .FixedBytes => |*value| value,
            else => null,
        };
    }

    pub fn asArray(self: *const Type) ?*const ArrayType {
        return switch (self.payload) {
            .Array => |*value| value,
            else => null,
        };
    }

    pub fn asReference(self: *const Type) ?*const ReferenceData {
        return switch (self.payload) {
            .Array => |*value| &value.reference,
            .Struct => |*value| &value.reference,
            .ArraySlice => |value| switch (value.array_type.payload) {
                .Array => |*array| &array.reference,
                else => unreachable,
            },
            else => null,
        };
    }

    pub fn asFunction(self: *const Type) ?*const FunctionType {
        return switch (self.payload) {
            .Function => |*value| value,
            else => null,
        };
    }

    pub fn asTuple(self: *const Type) ?*const TupleType {
        return switch (self.payload) {
            .Tuple => |*value| value,
            else => null,
        };
    }

    pub fn asMapping(self: *const Type) ?*const MappingType {
        return switch (self.payload) {
            .Mapping => |*value| value,
            else => null,
        };
    }

    pub fn asStruct(self: *const Type) ?*const StructType {
        return switch (self.payload) {
            .Struct => |*value| value,
            else => null,
        };
    }

    pub fn asTypeType(self: *const Type) ?*const TypeType {
        return switch (self.payload) {
            .TypeType => |*value| value,
            else => null,
        };
    }

    pub fn asMagic(self: *const Type) ?*const MagicType {
        return switch (self.payload) {
            .Magic => |*value| value,
            else => null,
        };
    }
};

pub const TypePointers = []const *const Type;

pub const OptionalTypePointers = []const ?*const Type;

/// One named, recursively typed component of a Solidity value's Yul stack
/// representation. An empty name paired with a null type is the upstream
/// representation of one untyped stack word.
pub const StackItem = struct {
    name: []const u8,
    type_ref: ?*const Type,
};

pub const StorageOffset = struct {
    slot: u256,
    byte_offset: u8,
};

pub const StorageOffsets = struct {
    offsets: []const ?StorageOffset = &.{},
    storage_size: u256 = 0,
};

pub const StateVariableLayout = struct {
    declaration: *const AST.Node,
    slot: u256,
    byte_offset: u8,
};

pub const Member = struct {
    name: []const u8,
    type_ref: *const Type,
    declaration: ?*const AST.Node = null,
};

pub const MemberList = struct {
    items: []const Member = &.{},

    pub fn memberType(self: MemberList, name: []const u8) ?*const Type {
        var result: ?*const Type = null;
        for (self.items) |item| {
            if (!std.mem.eql(u8, item.name, name)) continue;
            std.debug.assert(result == null);
            result = item.type_ref;
        }
        return result;
    }

    pub fn countByName(self: MemberList, name: []const u8) usize {
        var count: usize = 0;
        for (self.items) |item|
            count += @intFromBool(std.mem.eql(u8, item.name, name));
        return count;
    }
};

/// Caller-owned materialization of the upstream lazily cached `MemberList`.
/// Member names, type identities, and declarations remain borrowed from the
/// syntax tree or compilation-scoped `TypeProvider`; only the slice is owned.
pub const OwnedMemberList = struct {
    allocator: std.mem.Allocator,
    items: []Member,

    pub fn deinit(self: *OwnedMemberList) void {
        self.allocator.free(self.items);
        self.* = undefined;
    }

    pub fn borrowed(self: *const OwnedMemberList) MemberList {
        return .{ .items = self.items };
    }
};

test "type-system enum ABI and reference invariants" {
    try std.testing.expectEqual(@as(c_int, 0), @intFromEnum(Category.Address));
    try std.testing.expectEqual(@as(c_int, 20), @intFromEnum(Category.InaccessibleDynamic));
    try std.testing.expectEqual(@as(c_int, 0), @intFromEnum(FunctionKind.Internal));
    try std.testing.expectEqual(@as(c_int, 42), @intFromEnum(FunctionKind.Declaration));
    try std.testing.expect((ReferenceData{ .location = .Memory }).isPointer());
    try std.testing.expect(!(ReferenceData{
        .location = .Storage,
        .storage_pointer = false,
    }).isPointer());
}
