// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deployment and execution gas metrics for EVM-only Yul expressions.

const std = @import("std");
const AST = @import("../../ast.zig");
const EVMDialect = @import("evm_dialect.zig").EVMDialect;
const Gas = @import("../../../libevmasm/gas_meter.zig");
const Instruction = @import("../../../libevmasm/instruction.zig").Instruction;
const Numeric = @import("../../../libsolutil/numeric.zig");

pub const BigInt = Numeric.BigInt;

pub const Costs = struct {
    run_gas: BigInt,
    data_gas: BigInt,

    pub fn deinit(self: *Costs) void {
        self.run_gas.deinit();
        self.data_gas.deinit();
        self.* = undefined;
    }
};

pub const GasMeter = struct {
    dialect: *const EVMDialect,
    is_creation: bool,
    runs: BigInt,

    pub fn init(
        dialect: *const EVMDialect,
        is_creation: bool,
        runs: *const BigInt,
    ) GasMeter {
        return .{
            .dialect = dialect,
            .is_creation = is_creation,
            .runs = if (is_creation) BigInt.initUnsigned(1) else runs.clone(),
        };
    }

    pub fn initUnsigned(
        dialect: *const EVMDialect,
        is_creation: bool,
        runs: usize,
    ) GasMeter {
        var run_count = BigInt.initUnsigned(@intCast(runs));
        defer run_count.deinit();
        return init(dialect, is_creation, &run_count);
    }

    pub fn deinit(self: *GasMeter) void {
        self.runs.deinit();
        self.* = undefined;
    }

    pub fn costs(self: *const GasMeter, expression: *const AST.Expression) anyerror!BigInt {
        var split = try GasMeterVisitor.costs(expression, self.dialect, self.is_creation);
        defer split.deinit();
        return self.combineCosts(&split);
    }

    pub fn instructionCosts(self: *const GasMeter, instruction: Instruction) anyerror!BigInt {
        var split = try GasMeterVisitor.instructionCosts(
            instruction,
            self.dialect,
            self.is_creation,
        );
        defer split.deinit();
        return self.combineCosts(&split);
    }

    fn combineCosts(self: *const GasMeter, split: *const Costs) BigInt {
        var repeated = BigInt.mul(&split.run_gas, &self.runs);
        defer repeated.deinit();
        return BigInt.add(&repeated, &split.data_gas);
    }
};

pub const GasMeterVisitor = struct {
    dialect: *const EVMDialect,
    is_creation: bool,
    run_gas: BigInt,
    data_gas: BigInt,

    pub fn init(dialect: *const EVMDialect, is_creation: bool) GasMeterVisitor {
        return .{
            .dialect = dialect,
            .is_creation = is_creation,
            .run_gas = BigInt.init(),
            .data_gas = BigInt.init(),
        };
    }

    pub fn deinit(self: *GasMeterVisitor) void {
        self.run_gas.deinit();
        self.data_gas.deinit();
        self.* = undefined;
    }

    pub fn costs(
        expression: *const AST.Expression,
        dialect: *const EVMDialect,
        is_creation: bool,
    ) anyerror!Costs {
        var visitor = init(dialect, is_creation);
        defer visitor.deinit();
        try visitor.visitExpression(expression);
        return .{
            .run_gas = visitor.run_gas.clone(),
            .data_gas = visitor.data_gas.clone(),
        };
    }

    pub fn instructionCosts(
        instruction: Instruction,
        dialect: *const EVMDialect,
        is_creation: bool,
    ) anyerror!Costs {
        var visitor = init(dialect, is_creation);
        defer visitor.deinit();
        try visitor.instructionCostsInternal(instruction);
        return .{
            .run_gas = visitor.run_gas.clone(),
            .data_gas = visitor.data_gas.clone(),
        };
    }

    fn visitExpression(self: *GasMeterVisitor, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .function_call => |*call| try self.visitFunctionCall(call),
            .literal => |*literal| try self.visitLiteral(literal),
            .identifier => try self.visitIdentifier(),
        }
    }

    fn visitFunctionCall(self: *GasMeterVisitor, call: *const AST.FunctionCall) anyerror!void {
        var index = call.arguments.items.len;
        while (index != 0) {
            index -= 1;
            try self.visitExpression(&call.arguments.items[index]);
        }
        const handle = switch (call.function_name) {
            .builtin => |builtin| builtin.handle,
            .identifier => return error.FunctionsNotImplemented,
        };
        const builtin = self.dialect.builtin(handle) orelse return error.UnknownBuiltin;
        const instruction = builtin.instruction orelse return error.FunctionsNotImplemented;
        try self.instructionCostsInternal(instruction);
    }

    fn visitLiteral(self: *GasMeterVisitor, literal: *const AST.Literal) anyerror!void {
        const value = try literal.value.value();
        try addUnsigned(&self.run_gas, try Gas.pushGas(value, self.dialect.evmVersion()));
        try addUnsigned(&self.data_gas, self.singleByteDataGas());
        if (!self.dialect.evmVersion().hasPush0() or value != 0) {
            const bytes = Numeric.toBigEndian256(value);
            const length = @max(@as(usize, 1), Numeric.numberEncodingSize(u256, value));
            try addUnsigned(
                &self.data_gas,
                Gas.dataGas(bytes[bytes.len - length ..], self.is_creation, self.dialect.evmVersion()),
            );
        }
    }

    fn visitIdentifier(self: *GasMeterVisitor) anyerror!void {
        try addUnsigned(&self.run_gas, try Gas.runGas(.DUP1, self.dialect.evmVersion()));
        try addUnsigned(&self.data_gas, self.singleByteDataGas());
    }

    fn singleByteDataGas(self: *const GasMeterVisitor) u32 {
        return if (self.is_creation)
            Gas.GasCosts.txDataNonZeroGas(self.dialect.evmVersion())
        else
            Gas.GasCosts.create_data_gas;
    }

    fn instructionCostsInternal(
        self: *GasMeterVisitor,
        instruction: Instruction,
    ) anyerror!void {
        const run_cost: u32 = if (instruction == .EXP)
            Gas.GasCosts.exp_gas + Gas.GasCosts.expByteGas(self.dialect.evmVersion())
        else if (instruction == .KECCAK256)
            Gas.GasCosts.keccak256_gas + Gas.GasCosts.keccak256_word_gas
        else
            try Gas.runGas(instruction, self.dialect.evmVersion());
        try addUnsigned(&self.run_gas, run_cost);
        try addUnsigned(&self.data_gas, self.singleByteDataGas());
    }
};

fn addUnsigned(target: *BigInt, value: anytype) !void {
    const Value = @TypeOf(value);
    const term = switch (@typeInfo(Value)) {
        .int => if (@bitSizeOf(Value) <= 64)
            BigInt.initUnsigned(@intCast(value))
        else
            BigInt.fromU256(@intCast(value)),
        else => @compileError("gas values must be unsigned integers"),
    };
    var owned_term = term;
    defer owned_term.deinit();
    const sum = BigInt.add(target, &owned_term);
    target.deinit();
    target.* = sum;
}

test "EVM Yul gas metrics combine execution and deployment costs" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(
        allocator,
        @import("../../../liblangutil/evm_version.zig").EVMVersion.current(),
        false,
    );
    defer dialect.deinit();
    var literal: AST.Expression = .{ .literal = .{
        .kind = .Number,
        .value = .{ .numeric_value = 1 },
    } };
    defer literal.deinit(allocator);
    var meter = GasMeter.initUnsigned(&dialect, false, 200);
    defer meter.deinit();
    var cost = try meter.costs(&literal);
    defer cost.deinit();
    try std.testing.expect(cost.compareUnsigned(0) == .gt);
}
