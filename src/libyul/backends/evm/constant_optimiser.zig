// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Replaces large numeric literals with cheaper EVM expressions.

const std = @import("std");
const AST = @import("../../ast.zig");
const ASTCopier = @import("../../optimiser/ast_copier.zig").ASTCopier;
const BuiltinHandle = @import("../../builtins.zig").BuiltinHandle;
const DebugData = @import("../../../liblangutil/debug_data.zig").DebugData;
const EVMDialect = @import("evm_dialect.zig").EVMDialect;
const EVMMetrics = @import("evm_metrics.zig");
const Instruction = @import("../../../libevmasm/instruction.zig").Instruction;
const Numeric = @import("../../../libsolutil/numeric.zig");

pub const Representation = struct {
    expression: AST.Expression,
    cost: Numeric.BigInt,

    pub fn deinit(self: *Representation, allocator: std.mem.Allocator) void {
        self.expression.deinit(allocator);
        self.cost.deinit();
        self.* = undefined;
    }
};

const Cache = std.AutoHashMap(u256, *Representation);

pub const ConstantOptimiser = struct {
    allocator: std.mem.Allocator,
    dialect: *const EVMDialect,
    meter: *const EVMMetrics.GasMeter,
    cache: Cache,

    pub fn init(
        allocator: std.mem.Allocator,
        dialect: *const EVMDialect,
        meter: *const EVMMetrics.GasMeter,
    ) ConstantOptimiser {
        return .{
            .allocator = allocator,
            .dialect = dialect,
            .meter = meter,
            .cache = Cache.init(allocator),
        };
    }

    pub fn deinit(self: *ConstantOptimiser) void {
        var iterator = self.cache.valueIterator();
        while (iterator.next()) |entry| {
            entry.*.deinit(self.allocator);
            self.allocator.destroy(entry.*);
        }
        self.cache.deinit();
        self.* = undefined;
    }

    pub fn run(self: *ConstantOptimiser, block: *AST.Block) anyerror!void {
        try self.visitBlock(block);
    }

    fn visitExpression(self: *ConstantOptimiser, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .literal => |*literal| {
                if (literal.kind != .Number) return;
                const value = try literal.value.value();
                var finder: RepresentationFinder = .{
                    .allocator = self.allocator,
                    .dialect = self.dialect,
                    .meter = self.meter,
                    .debug_data = if (expression.debugData()) |data| data.* else null,
                    .cache = &self.cache,
                };
                if (try finder.tryFindRepresentation(value)) |replacement| {
                    var copier = ASTCopier.init(self.allocator);
                    const translated = try copier.translateExpression(replacement);
                    expression.deinit(self.allocator);
                    expression.* = translated;
                }
            },
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
            .identifier => {},
        }
    }

    fn visitBlock(self: *ConstantOptimiser, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *ConstantOptimiser, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| {
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression| try self.visitExpression(expression);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }
};

pub const RepresentationFinder = struct {
    allocator: std.mem.Allocator,
    dialect: *const EVMDialect,
    meter: *const EVMMetrics.GasMeter,
    debug_data: ?DebugData,
    cache: *Cache,
    max_steps: usize = 10_000,

    pub fn tryFindRepresentation(
        self: *RepresentationFinder,
        value: u256,
    ) anyerror!?*const AST.Expression {
        if (value < 0x10000) return null;
        const representation = try self.findRepresentation(value);
        return if (representation.expression == .literal) null else &representation.expression;
    }

    fn findRepresentation(
        self: *RepresentationFinder,
        value: u256,
    ) anyerror!*const Representation {
        if (self.cache.get(value)) |cached| return cached;

        var routine = try self.representLiteral(value);
        errdefer routine.deinit(self.allocator);
        const handles = self.dialect.auxiliaryBuiltinHandles();
        const not_handle = handles.not_ orelse return error.MissingAuxiliaryBuiltin;
        const exp_handle = handles.exp orelse return error.MissingAuxiliaryBuiltin;
        const mul_handle = handles.mul orelse return error.MissingAuxiliaryBuiltin;
        const add_handle = handles.add orelse return error.MissingAuxiliaryBuiltin;
        const sub_handle = handles.sub orelse return error.MissingAuxiliaryBuiltin;

        if (Numeric.numberEncodingSize(u256, ~value) < Numeric.numberEncodingSize(u256, value)) {
            const negated = try self.representUnary(
                not_handle,
                try self.findRepresentation(~value),
            );
            routine = chooseMin(self.allocator, routine, negated);
        }

        var bits: usize = 255;
        while (bits > 8 and self.max_steps > 0) : (bits -= 1) {
            const gap_detector: u16 = @intCast((value >> @intCast(bits - 8)) & 0x1ff);
            if (gap_detector != 0xff and gap_detector != 0x100) continue;

            const power_of_two: u256 = @as(u256, 1) << @intCast(bits);
            var upper_part = value >> @intCast(bits);
            const unsigned_lower = value & (power_of_two - 1);
            const negative_lower = power_of_two - unsigned_lower < unsigned_lower;
            const lower_magnitude = if (negative_lower)
                power_of_two - unsigned_lower
            else
                unsigned_lower;
            if (negative_lower) upper_part +%= 1;
            if (upper_part == 0 or lower_magnitude >= power_of_two >> 8) continue;

            var new_routine = if (self.dialect.evmVersion().hasBitwiseShifting()) blk: {
                var shift = try self.representLiteral(bits);
                defer shift.deinit(self.allocator);
                break :blk try self.representBinary(
                    handles.shl orelse return error.MissingAuxiliaryBuiltin,
                    &shift,
                    try self.findRepresentation(upper_part),
                );
            } else blk: {
                var two = try self.representLiteral(2);
                defer two.deinit(self.allocator);
                var exponent = try self.representLiteral(bits);
                defer exponent.deinit(self.allocator);
                var power = try self.representBinary(exp_handle, &two, &exponent);
                if (upper_part != 1) {
                    const multiplied = try self.representBinary(
                        mul_handle,
                        try self.findRepresentation(upper_part),
                        &power,
                    );
                    power.deinit(self.allocator);
                    power = multiplied;
                }
                break :blk power;
            };

            if (new_routine.cost.compare(&routine.cost) != .lt) {
                new_routine.deinit(self.allocator);
                continue;
            }
            if (lower_magnitude != 0) {
                const adjusted = try self.representBinary(
                    if (negative_lower) sub_handle else add_handle,
                    &new_routine,
                    try self.findRepresentation(lower_magnitude),
                );
                new_routine.deinit(self.allocator);
                new_routine = adjusted;
            }
            self.max_steps -= 1;
            routine = chooseMin(self.allocator, routine, new_routine);
        }

        if (try MiniEVMInterpreter.eval(self.dialect, &routine.expression) != value)
            return error.InvalidGeneratedExpression;
        const stored = try self.allocator.create(Representation);
        errdefer self.allocator.destroy(stored);
        stored.* = routine;
        try self.cache.put(value, stored);
        return stored;
    }

    fn representLiteral(self: *RepresentationFinder, value: u256) anyerror!Representation {
        const hint = try Numeric.formatNumberU256Alloc(self.allocator, value);
        var expression: AST.Expression = .{ .literal = .{
            .debug_data = self.debug_data,
            .kind = .Number,
            .value = .{ .numeric_value = value, .string_value = hint },
        } };
        errdefer expression.deinit(self.allocator);
        return .{ .expression = expression, .cost = try self.meter.costs(&expression) };
    }

    fn representUnary(
        self: *RepresentationFinder,
        instruction: BuiltinHandle,
        argument: *const Representation,
    ) anyerror!Representation {
        var expression = try self.callExpression(instruction, &.{&argument.expression});
        errdefer expression.deinit(self.allocator);
        var instruction_cost = try self.instructionCost(instruction);
        defer instruction_cost.deinit();
        return .{
            .expression = expression,
            .cost = Numeric.BigInt.add(&argument.cost, &instruction_cost),
        };
    }

    fn representBinary(
        self: *RepresentationFinder,
        instruction: BuiltinHandle,
        first: *const Representation,
        second: *const Representation,
    ) anyerror!Representation {
        var expression = try self.callExpression(
            instruction,
            &.{ &first.expression, &second.expression },
        );
        errdefer expression.deinit(self.allocator);
        var instruction_cost = try self.instructionCost(instruction);
        defer instruction_cost.deinit();
        var partial = Numeric.BigInt.add(&instruction_cost, &first.cost);
        defer partial.deinit();
        return .{
            .expression = expression,
            .cost = Numeric.BigInt.add(&partial, &second.cost),
        };
    }

    fn callExpression(
        self: *RepresentationFinder,
        handle: BuiltinHandle,
        arguments: []const *const AST.Expression,
    ) anyerror!AST.Expression {
        var call: AST.FunctionCall = .{
            .debug_data = self.debug_data,
            .function_name = .{ .builtin = .{
                .debug_data = self.debug_data,
                .handle = handle,
            } },
        };
        errdefer call.deinit(self.allocator);
        var copier = ASTCopier.init(self.allocator);
        for (arguments) |argument| {
            var copy = try copier.translateExpression(argument);
            errdefer copy.deinit(self.allocator);
            try call.arguments.append(self.allocator, copy);
        }
        return .{ .function_call = call };
    }

    fn instructionCost(
        self: *RepresentationFinder,
        handle: BuiltinHandle,
    ) anyerror!Numeric.BigInt {
        const builtin = self.dialect.builtin(handle) orelse return error.UnknownBuiltin;
        return self.meter.instructionCosts(
            builtin.instruction orelse return error.ExpectedInstructionBuiltin,
        );
    }
};

fn chooseMin(
    allocator: std.mem.Allocator,
    first_value: Representation,
    second_value: Representation,
) Representation {
    var first = first_value;
    var second = second_value;
    if (first.cost.compare(&second.cost) != .gt) {
        second.deinit(allocator);
        return first;
    }
    first.deinit(allocator);
    return second;
}

const MiniEVMInterpreter = struct {
    fn eval(dialect: *const EVMDialect, expression: *const AST.Expression) anyerror!u256 {
        return switch (expression.*) {
            .literal => |*literal| literal.value.value(),
            .identifier => error.UnexpectedIdentifier,
            .function_call => |*call| blk: {
                const handle = switch (call.function_name) {
                    .builtin => |builtin| builtin.handle,
                    .identifier => return error.ExpectedBuiltin,
                };
                const builtin = dialect.builtin(handle) orelse return error.UnknownBuiltin;
                break :blk evaluateInstruction(
                    builtin.instruction orelse return error.ExpectedInstructionBuiltin,
                    dialect,
                    call,
                );
            },
        };
    }

    fn evaluateInstruction(
        instruction: Instruction,
        dialect: *const EVMDialect,
        call: *const AST.FunctionCall,
    ) anyerror!u256 {
        var arguments: [2]u256 = .{ 0, 0 };
        if (call.arguments.items.len > arguments.len) return error.InvalidGeneratedExpression;
        for (call.arguments.items, 0..) |*argument, index|
            arguments[index] = try eval(dialect, argument);
        return switch (instruction) {
            .ADD => arguments[0] +% arguments[1],
            .SUB => arguments[0] -% arguments[1],
            .MUL => arguments[0] *% arguments[1],
            .EXP => Numeric.exp256(arguments[0], arguments[1]),
            .SHL => if (arguments[0] > 255) 0 else arguments[1] << @intCast(arguments[0]),
            .NOT => ~arguments[0],
            else => error.InvalidGeneratedInstruction,
        };
    }
};

test "constant optimiser replaces a large mask with a cheaper expression" {
    const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000 }",
        "constant.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var meter = EVMMetrics.GasMeter.initUnsigned(&dialect, false, 200);
    defer meter.deinit();
    var optimiser = ConstantOptimiser.init(allocator, &dialect, &meter);
    defer optimiser.deinit();
    try optimiser.run(&ast.root_block);
    try std.testing.expect(ast.root().statements.items[0].variable_declaration.value.?.* == .function_call);
}
