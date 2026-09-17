// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Complete translation of `libsolidity/codegen/ReturnInfo.cpp`.

const std = @import("std");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;

const interface_address = Types.Type{ .payload = .{ .Address = .{
    .state_mutability = .NonPayable,
} } };
const interface_uint8 = Types.Type{ .payload = .{ .Integer = .{
    .bits = 8,
    .modifier = .Unsigned,
} } };
const interface_uint256 = Types.Type{ .payload = .{ .Integer = .{
    .bits = 256,
    .modifier = .Unsigned,
} } };
const inaccessible_dynamic = Types.Type{ .payload = .{ .InaccessibleDynamic = {} } };

pub const ReturnInfoError = TypeBehavior.QueryError;

/// Information required to decode a regular external call's return values.
/// The return-type pointer array is owned; the pointed-to types remain
/// compilation-owned, matching the rest of the translated type graph.
pub const ReturnInfo = struct {
    allocator: std.mem.Allocator,
    return_types: []*const Types.Type,
    dynamic_return_size: bool = false,
    estimated_return_size: u32 = 0,

    pub fn init(
        allocator: std.mem.Allocator,
        evm_version: EVMVersion,
        function_type: *const Types.FunctionType,
    ) ReturnInfoError!ReturnInfo {
        const bare_call = switch (function_type.kind) {
            .BareCall, .BareDelegateCall, .BareStaticCall => true,
            else => false,
        };
        const source_types = if (bare_call)
            &.{}
        else
            function_type.return_parameter_types;
        const return_types = try allocator.alloc(*const Types.Type, source_types.len);
        errdefer allocator.free(return_types);
        @memcpy(return_types, source_types);

        if (!evm_version.supportsReturndata() and
            substitutesDynamicReturns(function_type.kind))
        {
            for (return_types) |*return_type| {
                const decoding = decodingType(return_type.*);
                if (TypeBehavior.isDynamicallyEncoded(decoding))
                    return_type.* = &inaccessible_dynamic;
            }
        }

        var result: ReturnInfo = .{
            .allocator = allocator,
            .return_types = return_types,
        };
        for (return_types) |return_type| {
            const decoding = decodingType(return_type);
            if (TypeBehavior.isDynamicallyEncoded(decoding)) {
                result.dynamic_return_size = true;
                result.estimated_return_size = 0;
                break;
            }
            result.estimated_return_size = std.math.add(
                u32,
                result.estimated_return_size,
                try TypeBehavior.calldataEncodedSize(decoding, true),
            ) catch return error.Overflow;
        }
        return result;
    }

    pub fn deinit(self: *ReturnInfo) void {
        self.allocator.free(self.return_types);
        self.* = undefined;
    }
};

fn substitutesDynamicReturns(kind: Types.FunctionKind) bool {
    return switch (kind) {
        .External,
        .DelegateCall,
        .BareCall,
        .BareCallCode,
        .BareDelegateCall,
        .BareStaticCall,
        => true,
        else => false,
    };
}

fn decodingType(type_ref: *const Types.Type) *const Types.Type {
    return switch (type_ref.payload) {
        .Contract => &interface_address,
        .Enum => &interface_uint8,
        .UserDefinedValueType => |value| decodingType(
            value.underlying_type orelse type_ref,
        ),
        .Array => |value| if (value.reference.location == .Storage)
            &interface_uint256
        else
            type_ref,
        .Struct => |value| if (value.reference.location == .Storage)
            &interface_uint256
        else
            type_ref,
        .Mapping, .InaccessibleDynamic => &interface_uint256,
        else => type_ref,
    };
}

test "ReturnInfo computes static and dynamic returndata exactly" {
    const uint = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const bytes = Types.Type{ .payload = .{ .Array = .{
        .reference = .{ .location = .Memory },
        .base_type = &Types.Type{ .payload = .{ .Integer = .{
            .bits = 8,
            .modifier = .Unsigned,
        } } },
        .kind = .Bytes,
    } } };
    const function = Types.FunctionType{
        .kind = .External,
        .return_parameter_types = &.{ &uint, &bytes },
    };

    var current = try ReturnInfo.init(std.testing.allocator, .current(), &function);
    defer current.deinit();
    try std.testing.expect(current.dynamic_return_size);
    try std.testing.expectEqual(@as(u32, 0), current.estimated_return_size);
    try std.testing.expectEqual(@as(usize, 2), current.return_types.len);

    var legacy = try ReturnInfo.init(
        std.testing.allocator,
        .init(.SpuriousDragon),
        &function,
    );
    defer legacy.deinit();
    try std.testing.expect(!legacy.dynamic_return_size);
    try std.testing.expectEqual(@as(u32, 64), legacy.estimated_return_size);
    try std.testing.expectEqual(
        Types.Category.InaccessibleDynamic,
        legacy.return_types[1].category(),
    );
}

test "ReturnInfo leaves bare-call success and bytes tuple empty" {
    const uint = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const function = Types.FunctionType{
        .kind = .BareCall,
        .return_parameter_types = &.{&uint},
    };
    var info = try ReturnInfo.init(std.testing.allocator, .current(), &function);
    defer info.deinit();
    try std.testing.expectEqual(@as(usize, 0), info.return_types.len);
    try std.testing.expectEqual(@as(u32, 0), info.estimated_return_size);
}
