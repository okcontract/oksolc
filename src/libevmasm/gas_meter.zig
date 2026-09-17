// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! EVM gas schedule and state-aware upper-bound estimator from `GasMeter.cpp`.

const std = @import("std");
const AssemblyItemModule = @import("assembly_item.zig");
const InstructionModule = @import("instruction.zig");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;

const AssemblyItem = AssemblyItemModule.AssemblyItem;
pub const ExpressionId = u32;

pub const GasCosts = struct {
    pub const stack_limit = 1024;
    pub const tier0_gas = 0;
    pub const tier1_gas = 2;
    pub const tier2_gas = 3;
    pub const tier3_gas = 5;
    pub const tier4_gas = 8;
    pub const tier5_gas = 10;
    pub const tier6_gas = 20;
    pub const exp_gas = 10;
    pub const keccak256_gas = 30;
    pub const keccak256_word_gas = 6;
    pub const access_list_address_cost = 2400;
    pub const access_list_storage_key_cost = 1900;
    pub const cold_sload_cost = 2100;
    pub const cold_account_access_cost = 2600;
    pub const warm_storage_read_cost = 100;
    pub const sstore_set_gas = 20_000;
    pub const sstore_reset_gas = 5000 - cold_sload_cost;
    pub const jumpdest_gas = 1;
    pub const log_gas = 375;
    pub const log_data_gas = 8;
    pub const log_topic_gas = 375;
    pub const create_gas = 32_000;
    pub const call_stipend = 2300;
    pub const call_value_transfer_gas = 9000;
    pub const call_new_account_gas = 25_000;
    pub const memory_gas = 3;
    pub const quad_coeff_div = 512;
    pub const create_data_gas = 200;
    pub const tx_gas = 21_000;
    pub const tx_create_gas = 53_000;
    pub const tx_data_zero_gas = 4;
    pub const copy_gas = 3;
    pub const rjumpi_gas = 4;

    pub fn expByteGas(version: EVMVersion) u32 {
        return if (version.atLeast(.SpuriousDragon)) 50 else 10;
    }

    pub fn sloadGas(version: EVMVersion) u32 {
        if (version.atLeast(.Berlin)) return cold_sload_cost;
        if (version.atLeast(.Istanbul)) return 800;
        if (version.atLeast(.TangerineWhistle)) return 200;
        return 50;
    }

    pub fn sstoreClearsSchedule(version: EVMVersion) u32 {
        return if (version.atLeast(.London))
            sstore_reset_gas + access_list_storage_key_cost
        else
            15_000;
    }

    pub fn totalSstoreSetGas(version: EVMVersion) u32 {
        return if (version.atLeast(.Berlin)) sstore_set_gas + cold_sload_cost else sstore_set_gas;
    }

    pub fn totalSstoreResetGas(version: EVMVersion) u32 {
        return if (version.atLeast(.Berlin)) sstore_reset_gas + cold_sload_cost else 5000;
    }

    pub fn extCodeGas(version: EVMVersion) u32 {
        if (version.atLeast(.Berlin)) return cold_account_access_cost;
        if (version.atLeast(.TangerineWhistle)) return 700;
        return 20;
    }

    pub fn balanceGas(version: EVMVersion) u32 {
        if (version.atLeast(.Berlin)) return cold_account_access_cost;
        if (version.atLeast(.Istanbul)) return 700;
        if (version.atLeast(.TangerineWhistle)) return 400;
        return 20;
    }

    pub fn callGas(version: EVMVersion) u32 {
        if (version.atLeast(.Berlin)) return cold_account_access_cost;
        if (version.atLeast(.TangerineWhistle)) return 700;
        return 40;
    }

    pub fn selfdestructGas(version: EVMVersion) u32 {
        if (version.atLeast(.Berlin)) return cold_account_access_cost;
        if (version.atLeast(.TangerineWhistle)) return 5000;
        return 0;
    }

    pub fn selfdestructRefundGas(version: EVMVersion) u32 {
        return if (version.atLeast(.London)) 0 else 24_000;
    }

    pub fn txDataNonZeroGas(version: EVMVersion) u32 {
        return if (version.atLeast(.Istanbul)) 16 else 68;
    }
};

pub const GasConsumption = struct {
    value: u256 = 0,
    is_infinite: bool = false,

    pub fn infinite() GasConsumption {
        return .{ .is_infinite = true };
    }

    pub fn add(self: *GasConsumption, other: GasConsumption) void {
        if (other.is_infinite and !self.is_infinite) self.* = infinite();
        if (self.is_infinite) return;
        const sum = @addWithOverflow(self.value, other.value);
        if (sum[1] != 0) {
            self.* = infinite();
        } else {
            self.value = sum[0];
        }
    }

    pub fn addValue(self: *GasConsumption, value: u256) void {
        self.add(.{ .value = value });
    }

    pub fn plus(self: GasConsumption, other: GasConsumption) GasConsumption {
        var result = self;
        result.add(other);
        return result;
    }

    pub fn lessThan(self: GasConsumption, other: GasConsumption) bool {
        if (self.is_infinite != other.is_infinite) return !self.is_infinite;
        return self.value < other.value;
    }
};

/// Borrowed state interface used by `GasMeter`. The concrete KnownState owner
/// supplies this view; returned constant pointers remain valid for the call.
pub const GasState = struct {
    context: *anyopaque,
    vtable: *const VTable,

    pub const VTable = struct {
        relative_stack_element: *const fn (*anyopaque, i32) anyerror!ExpressionId,
        known_constant: *const fn (*anyopaque, ExpressionId) ?*const u256,
        known_zero: *const fn (*anyopaque, ExpressionId) anyerror!bool,
        known_non_zero: *const fn (*anyopaque, ExpressionId) anyerror!bool,
        constant_expression: *const fn (*anyopaque, u256) anyerror!ExpressionId,
        find_add: *const fn (*anyopaque, ExpressionId, ExpressionId) anyerror!ExpressionId,
        storage_content: *const fn (*anyopaque, ExpressionId) ?ExpressionId,
        feed_item: *const fn (*anyopaque, *const AssemblyItem) anyerror!void,
    };

    fn relativeStackElement(self: GasState, offset: i32) !ExpressionId {
        return self.vtable.relative_stack_element(self.context, offset);
    }
    fn knownConstant(self: GasState, id: ExpressionId) ?*const u256 {
        return self.vtable.known_constant(self.context, id);
    }
    fn knownZero(self: GasState, id: ExpressionId) !bool {
        return self.vtable.known_zero(self.context, id);
    }
    fn knownNonZero(self: GasState, id: ExpressionId) !bool {
        return self.vtable.known_non_zero(self.context, id);
    }
    fn constantExpression(self: GasState, value: u256) !ExpressionId {
        return self.vtable.constant_expression(self.context, value);
    }
    fn findAdd(self: GasState, left: ExpressionId, right: ExpressionId) !ExpressionId {
        return self.vtable.find_add(self.context, left, right);
    }
    fn storageContent(self: GasState, slot: ExpressionId) ?ExpressionId {
        return self.vtable.storage_content(self.context, slot);
    }
    fn feedItem(self: GasState, item: *const AssemblyItem) !void {
        return self.vtable.feed_item(self.context, item);
    }
};

pub const GasMeter = struct {
    state: GasState,
    evm_version: EVMVersion,
    largest_memory_access: u256 = 0,

    pub fn estimateMax(
        self: *GasMeter,
        item: *const AssemblyItem,
        include_external_costs: bool,
    ) !GasConsumption {
        var gas: GasConsumption = .{};
        switch (item.item_type) {
            .Push => gas.value = try pushGas(item.data_value, self.evm_version),
            .PushTag,
            .PushData,
            .PushSub,
            .PushSubSize,
            .PushProgramSize,
            .PushLibraryAddress,
            .PushDeployTimeAddress,
            => gas.value = try runGas(.PUSH1, self.evm_version),
            .Tag => gas.value = try runGas(.JUMPDEST, self.evm_version),
            .Operation => gas = try self.estimateOperation(item.instruction_value.?, include_external_costs),
            else => gas = GasConsumption.infinite(),
        }
        try self.state.feedItem(item);
        return gas;
    }

    fn estimateOperation(
        self: *GasMeter,
        instruction: InstructionModule.Instruction,
        include_external_costs: bool,
    ) !GasConsumption {
        var gas: GasConsumption = .{};
        switch (instruction) {
            .SSTORE => {
                const slot = try self.state.relativeStackElement(0);
                const value = try self.state.relativeStackElement(-1);
                const old_value = self.state.storageContent(slot);
                gas.value = if (try self.state.knownZero(value) or
                    (old_value != null and try self.state.knownNonZero(old_value.?)))
                    GasCosts.totalSstoreResetGas(self.evm_version)
                else
                    GasCosts.totalSstoreSetGas(self.evm_version);
            },
            .SLOAD => gas.value = GasCosts.sloadGas(self.evm_version),
            .RETURN, .REVERT => {
                gas.value = try runGas(instruction, self.evm_version);
                gas.add(try self.memoryGasStack(0, -1));
            },
            .MLOAD, .MSTORE => {
                gas.value = try runGas(instruction, self.evm_version);
                gas.add(try self.memoryGas(try self.state.findAdd(
                    try self.state.relativeStackElement(0),
                    try self.constantExpression(32),
                )));
            },
            .MSTORE8 => {
                gas.value = try runGas(instruction, self.evm_version);
                gas.add(try self.memoryGas(try self.state.findAdd(
                    try self.state.relativeStackElement(0),
                    try self.constantExpression(1),
                )));
            },
            .KECCAK256 => {
                gas.value = GasCosts.keccak256_gas;
                gas.add(try self.memoryGasStack(0, -1));
                gas.add(self.wordGas(GasCosts.keccak256_word_gas, try self.state.relativeStackElement(-1)));
            },
            .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY => {
                gas.value = try runGas(instruction, self.evm_version);
                gas.add(try self.memoryGasStack(0, -2));
                gas.add(self.wordGas(GasCosts.copy_gas, try self.state.relativeStackElement(-2)));
            },
            .MCOPY => {
                const read_gas = try self.memoryGasStack(-1, -2);
                const write_gas = try self.memoryGasStack(0, -2);
                gas.value = try runGas(instruction, self.evm_version);
                gas.add(if (read_gas.lessThan(write_gas)) write_gas else read_gas);
                gas.add(self.wordGas(GasCosts.copy_gas, try self.state.relativeStackElement(-2)));
            },
            .EXTCODESIZE => gas.value = GasCosts.extCodeGas(self.evm_version),
            .EXTCODEHASH => gas.value = GasCosts.balanceGas(self.evm_version),
            .EXTCODECOPY => {
                gas.value = GasCosts.extCodeGas(self.evm_version);
                gas.add(try self.memoryGasStack(-1, -3));
                gas.add(self.wordGas(GasCosts.copy_gas, try self.state.relativeStackElement(-3)));
            },
            .LOG0, .LOG1, .LOG2, .LOG3, .LOG4 => {
                gas.value = @as(u256, GasCosts.log_gas) +
                    @as(u256, GasCosts.log_topic_gas) *
                        @as(u256, InstructionModule.getLogNumber(instruction));
                gas.add(try self.memoryGasStack(0, -1));
                if (self.state.knownConstant(try self.state.relativeStackElement(-1))) |value| {
                    gas.addValue(GasCosts.log_data_gas *% value.*);
                } else gas = GasConsumption.infinite();
            },
            .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL => {
                if (include_external_costs) return GasConsumption.infinite();
                gas.value = GasCosts.callGas(self.evm_version);
                if (self.state.knownConstant(try self.state.relativeStackElement(0))) |value| {
                    gas.addValue(value.*);
                } else gas = GasConsumption.infinite();
                if (instruction == .CALL) gas.addValue(GasCosts.call_new_account_gas);
                const value_size: i32 = if (instruction == .DELEGATECALL or instruction == .STATICCALL) 0 else 1;
                if (value_size != 0 and !try self.state.knownZero(try self.state.relativeStackElement(-1 - value_size))) {
                    gas.addValue(GasCosts.call_value_transfer_gas);
                }
                gas.add(try self.memoryGasStack(-2 - value_size, -3 - value_size));
                gas.add(try self.memoryGasStack(-4 - value_size, -5 - value_size));
            },
            .SELFDESTRUCT => {
                gas.value = GasCosts.selfdestructGas(self.evm_version);
                gas.addValue(GasCosts.call_new_account_gas);
            },
            .CREATE, .CREATE2 => {
                if (include_external_costs) return GasConsumption.infinite();
                gas.value = GasCosts.create_gas;
                gas.add(try self.memoryGasStack(-1, -2));
            },
            .EXP => {
                gas.value = GasCosts.exp_gas;
                if (self.state.knownConstant(try self.state.relativeStackElement(-1))) |value| {
                    if (value.* != 0) {
                        const byte_count = (@as(u32, std.math.log2_int(u256, value.*)) + 8) / 8;
                        gas.addValue(GasCosts.expByteGas(self.evm_version) * byte_count);
                    }
                } else gas.addValue(GasCosts.expByteGas(self.evm_version) * 32);
            },
            .BALANCE => gas.value = GasCosts.balanceGas(self.evm_version),
            .CHAINID => gas.value = try runGas(.CHAINID, self.evm_version),
            .SELFBALANCE => gas.value = try runGas(.SELFBALANCE, self.evm_version),
            else => gas.value = try runGas(instruction, self.evm_version),
        }
        return gas;
    }

    fn constantExpression(self: *GasMeter, value: u256) !ExpressionId {
        return self.state.constantExpression(value);
    }

    fn wordGas(self: *GasMeter, multiplier: u256, value_id: ExpressionId) GasConsumption {
        const value = self.state.knownConstant(value_id) orelse return GasConsumption.infinite();
        return .{ .value = multiplier *% ((value.* +% 31) / 32) };
    }

    fn memoryGas(self: *GasMeter, position_id: ExpressionId) !GasConsumption {
        const position = self.state.knownConstant(position_id) orelse return GasConsumption.infinite();
        if (position.* < self.largest_memory_access) return .{};
        const previous = self.largest_memory_access;
        self.largest_memory_access = position.*;
        return .{ .value = memoryCost(position.*) -% memoryCost(previous) };
    }

    fn memoryGasStack(self: *GasMeter, offset_position: i32, offset_size: i32) !GasConsumption {
        const size_id = try self.state.relativeStackElement(offset_size);
        if (try self.state.knownZero(size_id)) return .{};
        return self.memoryGas(try self.state.findAdd(
            try self.state.relativeStackElement(offset_position),
            size_id,
        ));
    }
};

fn memoryCost(position: u256) u256 {
    const size = (position +% 31) / 32;
    return GasCosts.memory_gas *% size +% (size *% size) / GasCosts.quad_coeff_div;
}

pub const GasError = error{
    InvalidGasTier,
    UnexpectedStackDepth,
};

pub fn runGas(instruction: InstructionModule.Instruction, evm_version: EVMVersion) GasError!u32 {
    if (instruction == .JUMPDEST) return GasCosts.jumpdest_gas;
    return switch (InstructionModule.instructionInfo(instruction, evm_version).gas_price_tier) {
        .Zero => GasCosts.tier0_gas,
        .Base => GasCosts.tier1_gas,
        .VeryLow => GasCosts.tier2_gas,
        .Low => GasCosts.tier3_gas,
        .Mid => GasCosts.tier4_gas,
        .High => GasCosts.tier5_gas,
        .BlockHash => GasCosts.tier6_gas,
        .WarmAccess => GasCosts.warm_storage_read_cost,
        .Special, .Invalid => error.InvalidGasTier,
    };
}

pub fn pushGas(value: u256, evm_version: EVMVersion) GasError!u32 {
    return runGas(if (evm_version.hasPush0() and value == 0) .PUSH0 else .PUSH1, evm_version);
}

pub fn swapGas(depth: usize, evm_version: EVMVersion) GasError!u32 {
    if (depth == 0 or depth > 16) return error.UnexpectedStackDepth;
    return runGas(InstructionModule.swapInstruction(@intCast(depth)), evm_version);
}

pub fn dupGas(depth: usize, evm_version: EVMVersion) GasError!u32 {
    if (depth == 0 or depth > 16) return error.UnexpectedStackDepth;
    return runGas(InstructionModule.dupInstruction(@intCast(depth)), evm_version);
}

pub fn dataGas(data: []const u8, in_creation: bool, evm_version: EVMVersion) u256 {
    if (!in_creation) return GasCosts.create_data_gas * @as(u256, data.len);
    var gas: u256 = 0;
    for (data) |byte| gas += if (byte == 0)
        GasCosts.tx_data_zero_gas
    else
        GasCosts.txDataNonZeroGas(evm_version);
    return gas;
}

pub fn dataGasLength(length: u64, in_creation: bool, evm_version: EVMVersion) u256 {
    return @as(u256, length) * if (in_creation)
        GasCosts.txDataNonZeroGas(evm_version)
    else
        GasCosts.create_data_gas;
}

const TestGasState = struct {
    const capacity = 64;

    constants: [capacity]u256 = [_]u256{0} ** capacity,
    is_constant: [capacity]bool = [_]bool{false} ** capacity,
    constant_count: usize = 0,
    relative_stack: [16]ExpressionId = [_]ExpressionId{0} ** 16,
    storage_slot: ?ExpressionId = null,
    storage_value: ?ExpressionId = null,
    feed_count: usize = 0,

    fn view(self: *TestGasState) GasState {
        return .{ .context = self, .vtable = &vtable };
    }

    fn intern(self: *TestGasState, value: u256) error{ExpressionCapacity}!ExpressionId {
        for (self.constants[0..self.constant_count], 0..) |existing, index| {
            if (self.is_constant[index] and existing == value) return @intCast(index);
        }
        if (self.constant_count == capacity) return error.ExpressionCapacity;
        const index = self.constant_count;
        self.constant_count += 1;
        self.constants[index] = value;
        self.is_constant[index] = true;
        return @intCast(index);
    }

    fn unknown(self: *TestGasState) error{ExpressionCapacity}!ExpressionId {
        if (self.constant_count == capacity) return error.ExpressionCapacity;
        const index = self.constant_count;
        self.constant_count += 1;
        self.is_constant[index] = false;
        return @intCast(index);
    }

    fn setRelative(self: *TestGasState, offset: i32, id: ExpressionId) void {
        std.debug.assert(offset <= 0 and -offset < self.relative_stack.len);
        self.relative_stack[@intCast(-offset)] = id;
    }

    fn cast(context: *anyopaque) *TestGasState {
        return @ptrCast(@alignCast(context));
    }

    fn relativeStackElement(context: *anyopaque, offset: i32) !ExpressionId {
        const self = cast(context);
        std.debug.assert(offset <= 0 and -offset < self.relative_stack.len);
        return self.relative_stack[@intCast(-offset)];
    }

    fn knownConstant(context: *anyopaque, id: ExpressionId) ?*const u256 {
        const self = cast(context);
        const index: usize = @intCast(id);
        if (index >= self.constant_count or !self.is_constant[index]) return null;
        return &self.constants[index];
    }

    fn knownZero(context: *anyopaque, id: ExpressionId) !bool {
        const value = knownConstant(context, id) orelse return false;
        return value.* == 0;
    }

    fn knownNonZero(context: *anyopaque, id: ExpressionId) !bool {
        const value = knownConstant(context, id) orelse return false;
        return value.* != 0;
    }

    fn constantExpression(context: *anyopaque, value: u256) !ExpressionId {
        return cast(context).intern(value);
    }

    fn findAdd(context: *anyopaque, left: ExpressionId, right: ExpressionId) !ExpressionId {
        const lhs = knownConstant(context, left) orelse return cast(context).unknown();
        const rhs = knownConstant(context, right) orelse return cast(context).unknown();
        return cast(context).intern(lhs.* +% rhs.*);
    }

    fn storageContent(context: *anyopaque, slot: ExpressionId) ?ExpressionId {
        const self = cast(context);
        if (self.storage_slot != null and self.storage_slot.? == slot) return self.storage_value;
        return null;
    }

    fn feedItem(context: *anyopaque, _: *const AssemblyItem) !void {
        cast(context).feed_count += 1;
    }

    const vtable: GasState.VTable = .{
        .relative_stack_element = relativeStackElement,
        .known_constant = knownConstant,
        .known_zero = knownZero,
        .known_non_zero = knownNonZero,
        .constant_expression = constantExpression,
        .find_add = findAdd,
        .storage_content = storageContent,
        .feed_item = feedItem,
    };
};

test "gas schedule transitions and static instruction tiers match protocol revisions" {
    try std.testing.expectEqual(@as(u32, 50), GasCosts.sloadGas(EVMVersion.init(.Homestead)));
    try std.testing.expectEqual(@as(u32, 800), GasCosts.sloadGas(EVMVersion.init(.Istanbul)));
    try std.testing.expectEqual(@as(u32, 2100), GasCosts.sloadGas(EVMVersion.init(.Berlin)));
    try std.testing.expectEqual(@as(u32, 3), try runGas(.ADD, EVMVersion.current()));
    try std.testing.expectEqual(@as(u32, 1), try runGas(.JUMPDEST, EVMVersion.current()));
    try std.testing.expectEqual(@as(u32, 2), try pushGas(0, EVMVersion.init(.Shanghai)));
    try std.testing.expectEqual(@as(u32, 3), try pushGas(0, EVMVersion.init(.London)));
    try std.testing.expectError(error.InvalidGasTier, runGas(.SSTORE, EVMVersion.current()));
}

test "data gas distinguishes transaction zeros from deployed bytecode" {
    try std.testing.expectEqual(
        @as(u256, 4 + 16 + 4),
        dataGas(&.{ 0, 1, 0 }, true, EVMVersion.init(.Istanbul)),
    );
    try std.testing.expectEqual(@as(u256, 600), dataGas(&.{ 0, 1, 0 }, false, EVMVersion.current()));
    try std.testing.expectEqual(@as(u256, 1600), dataGasLength(100, true, EVMVersion.current()));
}

test "gas consumption becomes infinite on fixed-width overflow" {
    var finite: GasConsumption = .{ .value = std.math.maxInt(u256) };
    finite.addValue(1);
    try std.testing.expect(finite.is_infinite);
    try std.testing.expect((GasConsumption{ .value = 1 }).lessThan(GasConsumption.infinite()));
}

test "state-aware gas estimation preserves memory growth and branch semantics" {
    var state: TestGasState = .{};
    const zero = try state.intern(0);
    const one = try state.intern(1);
    const thirty_three = try state.intern(33);
    const sixty_four = try state.intern(64);
    const gas_limit = try state.intern(1000);
    const exponent = try state.intern(256);
    const unknown = try state.unknown();
    var meter: GasMeter = .{
        .state = state.view(),
        .evm_version = EVMVersion.init(.Berlin),
    };

    state.setRelative(0, zero);
    var item = AssemblyItem.initInstruction(.MSTORE, .{});
    try std.testing.expectEqual(@as(u256, 6), (try meter.estimateMax(&item, false)).value);
    try std.testing.expectEqual(@as(u256, 32), meter.largest_memory_access);
    try std.testing.expectEqual(@as(u256, 3), (try meter.estimateMax(&item, false)).value);

    state.setRelative(0, sixty_four);
    state.setRelative(-1, thirty_three);
    item = AssemblyItem.initInstruction(.KECCAK256, .{});
    const keccak = try meter.estimateMax(&item, false);
    try std.testing.expect(!keccak.is_infinite);
    try std.testing.expectEqual(@as(u256, 51), keccak.value);
    try std.testing.expectEqual(@as(u256, 97), meter.largest_memory_access);

    state.setRelative(0, zero);
    state.setRelative(-1, unknown);
    item = AssemblyItem.initInstruction(.LOG1, .{});
    try std.testing.expect((try meter.estimateMax(&item, false)).is_infinite);

    state.setRelative(0, zero);
    state.setRelative(-1, zero);
    item = AssemblyItem.initInstruction(.SSTORE, .{});
    try std.testing.expectEqual(@as(u256, 5000), (try meter.estimateMax(&item, false)).value);
    state.setRelative(-1, unknown);
    state.storage_slot = zero;
    state.storage_value = one;
    try std.testing.expectEqual(@as(u256, 5000), (try meter.estimateMax(&item, false)).value);
    state.storage_slot = null;
    try std.testing.expectEqual(@as(u256, 22_100), (try meter.estimateMax(&item, false)).value);

    state.setRelative(0, gas_limit);
    state.setRelative(-2, one);
    state.setRelative(-4, zero);
    state.setRelative(-6, zero);
    item = AssemblyItem.initInstruction(.CALL, .{});
    try std.testing.expectEqual(@as(u256, 37_600), (try meter.estimateMax(&item, false)).value);
    try std.testing.expect((try meter.estimateMax(&item, true)).is_infinite);

    state.setRelative(-1, exponent);
    item = AssemblyItem.initInstruction(.EXP, .{});
    try std.testing.expectEqual(@as(u256, 110), (try meter.estimateMax(&item, false)).value);
    state.setRelative(-1, unknown);
    try std.testing.expectEqual(@as(u256, 1610), (try meter.estimateMax(&item, false)).value);

    try std.testing.expectEqual(@as(usize, 11), state.feed_count);
}
