// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Assembly-path gas estimation translated from `GasEstimator.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const TypeBehavior = @import("../ast/types.zig");
const AssemblyItemModule = @import("../../libevmasm/assembly_item.zig");
const AssemblyItem = AssemblyItemModule.AssemblyItem;
const GasMeter = @import("../../libevmasm/gas_meter.zig");
const Instruction = @import("../../libevmasm/instruction.zig");
const KnownState = @import("../../libevmasm/known_state.zig").KnownState;
const PathGasMeter = @import("../../libevmasm/path_gas_meter.zig").PathGasMeter;
const FunctionSelector = @import("../../libsolutil/function_selector.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;

pub const GasConsumption = GasMeter.GasConsumption;

pub const GasEstimator = struct {
    allocator: std.mem.Allocator,
    evm_version: EVMVersion,

    pub fn init(
        allocator: std.mem.Allocator,
        evm_version: EVMVersion,
    ) GasEstimator {
        return .{ .allocator = allocator, .evm_version = evm_version };
    }

    /// Estimates the maximum path, optionally constraining calldata to the
    /// external selector supplied by `signature`.
    pub fn functionalEstimation(
        self: *const GasEstimator,
        items: []const AssemblyItem,
        signature: []const u8,
    ) !GasConsumption {
        var state = try KnownState.init(self.allocator);
        defer state.deinit();

        if (signature.len != 0) {
            const classes = state.expressionClasses();
            const zero = try classes.makeConstant(0, .{});
            const selector = try classes.makeConstant(
                FunctionSelector.selectorFromSignatureU32(signature),
                .{},
            );
            const calldata = try classes.makeOperation(
                .CALLDATALOAD,
                &.{zero},
                .{},
            );
            if (self.evm_version.hasBitwiseShifting()) {
                const shift = try classes.makeConstant(0xe0, .{});
                const shr = AssemblyItem.initInstruction(.SHR, .{});
                try classes.forceEqual(selector, &shr, &.{ shift, calldata }, true);
            } else {
                const divisor = try classes.makeConstant(@as(u256, 1) << 224, .{});
                const div = AssemblyItem.initInstruction(.DIV, .{});
                try classes.forceEqual(selector, &div, &.{ calldata, divisor }, true);
            }

            const calldata_size = try classes.makeOperation(.CALLDATASIZE, &.{}, .{});
            const four = try classes.makeConstant(4, .{});
            const lt = AssemblyItem.initInstruction(.LT, .{});
            try classes.forceEqual(zero, &lt, &.{ calldata_size, four }, true);
        }

        return PathGasMeter.estimate(
            self.allocator,
            items,
            self.evm_version,
            0,
            &state,
        );
    }

    /// Estimates an internal function beginning at one assembly-item index.
    /// Recursive functions retain upstream's conservative behavior.
    pub fn functionalEstimationForFunction(
        self: *const GasEstimator,
        items: []const AssemblyItem,
        offset: usize,
        function: *const AST.Node,
    ) !GasConsumption {
        const parameters_size = try functionParametersSize(function);
        if (parameters_size > self.evm_version.reachableStackDepth())
            return GasConsumption.infinite();

        var state = try KnownState.init(self.allocator);
        defer state.deinit();
        const invalid_tag = AssemblyItem.initType(
            .PushTag,
            @as(u256, 0) -% 0x10,
            .{},
        );
        _ = try state.feedItem(&invalid_tag, true);
        if (parameters_size != 0) {
            const swap = AssemblyItem.initInstruction(
                Instruction.swapInstruction(@intCast(parameters_size)),
                .{},
            );
            _ = try state.feedItem(&swap, true);
        }
        return PathGasMeter.estimate(
            self.allocator,
            items,
            self.evm_version,
            offset,
            &state,
        );
    }
};

fn functionParametersSize(function: *const AST.Node) !usize {
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    const parameters = function.payload.function_definition.callable.parameters;
    if (parameters.nodeKind() != .parameter_list) return error.InvalidAst;
    var result: usize = 0;
    for (parameters.payload.parameter_list.parameters) |parameter| {
        const annotation = ASTAnnotations.annotationConst(parameter) orelse
            return error.InvalidAst;
        const type_ref = switch (annotation.*) {
            .variable_declaration => |value| value.type_ref,
            else => null,
        } orelse return error.InvalidAst;
        result = try std.math.add(
            usize,
            result,
            try TypeBehavior.sizeOnStack(type_ref),
        );
    }
    return result;
}

test "functional estimator preserves straight-line and selector constraints" {
    const items = [_]AssemblyItem{
        AssemblyItem.initPush(1, .{}),
        AssemblyItem.initInstruction(.STOP, .{}),
    };
    const estimator = GasEstimator.init(
        std.testing.allocator,
        EVMVersion.init(.London),
    );
    const unconstrained = try estimator.functionalEstimation(&items, "");
    try std.testing.expect(!unconstrained.is_infinite);
    try std.testing.expectEqual(@as(u256, 3), unconstrained.value);
}
