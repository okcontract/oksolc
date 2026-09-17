// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Literal, code-copy, and computed constant representations.

const std = @import("std");
const Numeric = @import("../libsolutil/numeric.zig");
const Keccak256 = @import("../libsolutil/keccak256.zig");
const AssemblyItemModule = @import("assembly_item.zig");
const AssemblyItem = AssemblyItemModule.AssemblyItem;
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const GasMeter = @import("gas_meter.zig");

pub const Params = struct {
    is_creation: bool,
    runs: u64,
    multiplicity: usize,
    evm_version: EVMVersion,
};

/// The assembly owns the data section. This borrowed callback records the
/// 32-byte value and returns its canonical `PushData` item.
pub const DataSink = struct {
    context: *anyopaque,
    add_data: *const fn (*anyopaque, [32]u8) anyerror!AssemblyItem,

    pub fn add(self: DataSink, data: [32]u8) !AssemblyItem {
        return self.add_data(self.context, data);
    }
};

pub const OptimiseError = anyerror;

const PushCount = struct { value: u256, count: usize };
const Replacement = struct {
    value: u256,
    items: std.ArrayList(AssemblyItem) = .empty,

    fn deinit(self: *Replacement, allocator: std.mem.Allocator) void {
        deinitItems(allocator, &self.items);
        self.* = undefined;
    }
};

pub fn optimiseConstants(
    allocator: std.mem.Allocator,
    is_creation: bool,
    runs: u64,
    evm_version: EVMVersion,
    items: *std.ArrayList(AssemblyItem),
    data_sink: DataSink,
) OptimiseError!u32 {
    var pushes: std.ArrayList(PushCount) = .empty;
    defer pushes.deinit(allocator);
    for (items.items) |item| {
        if (item.item_type != .Push) continue;
        const found = searchPushes(pushes.items, item.data_value);
        if (found.found) pushes.items[found.index].count += 1 else try pushes.insert(allocator, found.index, .{ .value = item.data_value, .count = 1 });
    }

    var replacements: std.ArrayList(Replacement) = .empty;
    defer {
        for (replacements.items) |*replacement| replacement.deinit(allocator);
        replacements.deinit(allocator);
    }
    var optimisations: u32 = 0;
    for (pushes.items) |push| {
        if (push.value < 0x100) continue;
        const params: Params = .{
            .multiplicity = push.count,
            .is_creation = is_creation,
            .runs = runs,
            .evm_version = evm_version,
        };
        const literal_gas = try literalGasNeeded(params, push.value);
        const copy_gas = try codeCopyGasNeeded(allocator, params, push.value);
        var compute = try ComputeMethod.init(allocator, params, push.value);
        defer compute.deinit();
        const compute_gas = try compute.gasNeeded();

        var replacement: std.ArrayList(AssemblyItem) = .empty;
        errdefer deinitItems(allocator, &replacement);
        if (copy_gas < literal_gas and copy_gas < compute_gas) {
            replacement = try codeCopyExecute(allocator, params, push.value, data_sink);
            optimisations += 1;
        } else if (compute_gas < literal_gas and compute_gas <= copy_gas) {
            replacement = compute.takeRoutine();
            optimisations += 1;
        }
        if (replacement.items.len != 0)
            try replacements.append(allocator, .{ .value = push.value, .items = replacement });
    }
    if (replacements.items.len != 0) try replaceConstants(allocator, items, replacements.items);
    return optimisations;
}

pub fn simpleRunGas(items: []const AssemblyItem, evm_version: EVMVersion) !u512 {
    var gas: u512 = 0;
    for (items) |*item| {
        if (item.item_type == .Push) {
            gas += try GasMeter.pushGas(item.data_value, evm_version);
        } else if (item.item_type == .Operation) {
            gas += if (item.instruction_value.? == .EXP)
                GasMeter.GasCosts.exp_gas
            else
                try GasMeter.runGas(item.instruction_value.?, evm_version);
        }
    }
    return gas;
}

pub fn bytesRequired(items: []const AssemblyItem, evm_version: EVMVersion) !u64 {
    return @intCast(try AssemblyItemModule.bytesRequired(items, 3, evm_version, .Approximate));
}

fn combineGas(params: Params, run_gas: u512, repeated_data_gas: u512, unique_data_gas: u512) u512 {
    return @as(u512, params.runs) * run_gas +
        @as(u512, params.multiplicity) * repeated_data_gas + unique_data_gas;
}

fn literalGasNeeded(params: Params, value: u256) !u512 {
    const push = AssemblyItem.initInstruction(.PUSH1, .{});
    const encoded = Numeric.toBigEndian256(value);
    const encoded_size = @max(@as(usize, 1), Numeric.numberEncodingSize(u256, value));
    const byte_price = if (params.is_creation)
        GasMeter.GasCosts.txDataNonZeroGas(params.evm_version)
    else
        GasMeter.GasCosts.create_data_gas;
    return combineGas(
        params,
        try simpleRunGas(&.{push}, params.evm_version),
        byte_price + GasMeter.dataGas(encoded[32 - encoded_size ..], params.is_creation, params.evm_version),
        0,
    );
}

fn codeCopyGasNeeded(allocator: std.mem.Allocator, params: Params, value: u256) !u512 {
    var routine = try copyRoutine(allocator, params, null);
    defer deinitItems(allocator, &routine);
    const data = Numeric.toBigEndian256(value);
    const byte_price = if (params.is_creation)
        GasMeter.GasCosts.txDataNonZeroGas(params.evm_version)
    else
        GasMeter.GasCosts.create_data_gas;
    return combineGas(
        params,
        try simpleRunGas(routine.items, params.evm_version) + GasMeter.GasCosts.copy_gas,
        @as(u512, try bytesRequired(routine.items, params.evm_version)) * byte_price,
        GasMeter.dataGas(&data, params.is_creation, params.evm_version),
    );
}

fn codeCopyExecute(
    allocator: std.mem.Allocator,
    params: Params,
    value: u256,
    data_sink: DataSink,
) !std.ArrayList(AssemblyItem) {
    const data = Numeric.toBigEndian256(value);
    const push_data = try data_sink.add(data);
    if (push_data.item_type != .PushData) return error.InvalidAssemblyItem;
    return copyRoutine(allocator, params, push_data);
}

fn copyRoutine(
    allocator: std.mem.Allocator,
    params: Params,
    push_data: ?AssemblyItem,
) std.mem.Allocator.Error!std.ArrayList(AssemblyItem) {
    const data_used = push_data orelse AssemblyItem.initType(.PushData, @as(u256, 1) << 16, .{});
    var result: std.ArrayList(AssemblyItem) = .empty;
    errdefer result.deinit(allocator);
    if (params.evm_version.hasPush0()) {
        try result.appendSlice(allocator, &.{
            AssemblyItem.initPush(0, .{}),
            AssemblyItem.initInstruction(.MLOAD, .{}),
            AssemblyItem.initPush(32, .{}),
            data_used,
            AssemblyItem.initPush(0, .{}),
            AssemblyItem.initInstruction(.CODECOPY, .{}),
            AssemblyItem.initPush(0, .{}),
            AssemblyItem.initInstruction(.MLOAD, .{}),
            AssemblyItem.initInstruction(.SWAP1, .{}),
            AssemblyItem.initPush(0, .{}),
            AssemblyItem.initInstruction(.MSTORE, .{}),
        });
    } else {
        try result.appendSlice(allocator, &.{
            AssemblyItem.initPush(0, .{}),
            AssemblyItem.initInstruction(.DUP1, .{}),
            AssemblyItem.initInstruction(.MLOAD, .{}),
            AssemblyItem.initPush(32, .{}),
            data_used,
            AssemblyItem.initInstruction(.DUP4, .{}),
            AssemblyItem.initInstruction(.CODECOPY, .{}),
            AssemblyItem.initInstruction(.DUP2, .{}),
            AssemblyItem.initInstruction(.MLOAD, .{}),
            AssemblyItem.initInstruction(.SWAP2, .{}),
            AssemblyItem.initInstruction(.MSTORE, .{}),
        });
    }
    return result;
}

pub const ComputeMethod = struct {
    allocator: std.mem.Allocator,
    params: Params,
    value: u256,
    max_steps: usize = 10_000,
    routine: std.ArrayList(AssemblyItem) = .empty,

    pub fn init(allocator: std.mem.Allocator, params: Params, value: u256) !ComputeMethod {
        var result: ComputeMethod = .{ .allocator = allocator, .params = params, .value = value };
        errdefer result.deinit();
        result.routine = try result.findRepresentation(value);
        if (!try result.checkRepresentation(value, result.routine.items)) return error.InvalidConstantExpression;
        return result;
    }

    pub fn deinit(self: *ComputeMethod) void {
        deinitItems(self.allocator, &self.routine);
        self.* = undefined;
    }

    pub fn takeRoutine(self: *ComputeMethod) std.ArrayList(AssemblyItem) {
        const result = self.routine;
        self.routine = .empty;
        return result;
    }

    pub fn gasNeeded(self: *const ComputeMethod) !u512 {
        return self.gasNeededRoutine(self.routine.items);
    }

    fn findRepresentation(self: *ComputeMethod, value: u256) !std.ArrayList(AssemblyItem) {
        if (value < 0x10000) return listFromSlice(self.allocator, &.{AssemblyItem.initPush(value, .{})});
        if (Numeric.numberEncodingSize(u256, ~value) < Numeric.numberEncodingSize(u256, value)) {
            var result = try self.findRepresentation(~value);
            errdefer deinitItems(self.allocator, &result);
            try result.append(self.allocator, AssemblyItem.initInstruction(.NOT, .{}));
            return result;
        }

        var routine = try listFromSlice(self.allocator, &.{AssemblyItem.initPush(value, .{})});
        errdefer deinitItems(self.allocator, &routine);
        var best_gas = try self.gasNeededRoutine(routine.items);
        var bits: u16 = 255;
        while (bits > 8 and self.max_steps > 0) : (bits -= 1) {
            const shift: u8 = @intCast(bits - 8);
            const gap_detector: u16 = @truncate(value >> shift);
            const gap = gap_detector & 0x1ff;
            if (gap != 0xff and gap != 0x100) continue;

            const power_of_two: u256 = @as(u256, 1) << @intCast(bits);
            var upper_part = value >> @intCast(bits);
            const unsigned_lower = value & (power_of_two - 1);
            var lower_magnitude = unsigned_lower;
            var lower_negative = false;
            if (power_of_two - unsigned_lower < unsigned_lower) {
                lower_magnitude = power_of_two - unsigned_lower;
                lower_negative = true;
                upper_part +%= 1;
            }
            if (upper_part == 0 or lower_magnitude >= (power_of_two >> 8)) continue;

            var candidate: std.ArrayList(AssemblyItem) = .empty;
            errdefer deinitItems(self.allocator, &candidate);
            if (lower_magnitude != 0) {
                var lower = try self.findRepresentation(lower_magnitude);
                defer deinitItems(self.allocator, &lower);
                try candidate.appendSlice(self.allocator, lower.items);
            }
            if (self.params.evm_version.hasBitwiseShifting()) {
                var upper = try self.findRepresentation(upper_part);
                defer deinitItems(self.allocator, &upper);
                try candidate.appendSlice(self.allocator, upper.items);
                try candidate.append(self.allocator, AssemblyItem.initPush(bits, .{}));
                try candidate.append(self.allocator, AssemblyItem.initInstruction(.SHL, .{}));
            } else {
                try candidate.append(self.allocator, AssemblyItem.initPush(bits, .{}));
                try candidate.append(self.allocator, AssemblyItem.initPush(2, .{}));
                try candidate.append(self.allocator, AssemblyItem.initInstruction(.EXP, .{}));
                if (upper_part != 1) {
                    var upper = try self.findRepresentation(upper_part);
                    defer deinitItems(self.allocator, &upper);
                    try candidate.appendSlice(self.allocator, upper.items);
                    try candidate.append(self.allocator, AssemblyItem.initInstruction(.MUL, .{}));
                }
            }
            if (lower_magnitude != 0)
                try candidate.append(
                    self.allocator,
                    AssemblyItem.initInstruction(if (lower_negative) .SUB else .ADD, .{}),
                );

            self.max_steps -= 1;
            const candidate_gas = try self.gasNeededRoutine(candidate.items);
            if (candidate_gas < best_gas) {
                best_gas = candidate_gas;
                deinitItems(self.allocator, &routine);
                routine = candidate;
                candidate = .empty;
            }
            deinitItems(self.allocator, &candidate);
        }
        return routine;
    }

    pub fn checkRepresentation(self: *const ComputeMethod, value: u256, routine: []const AssemblyItem) !bool {
        var stack: std.ArrayList(u256) = .empty;
        defer stack.deinit(self.allocator);
        for (routine) |*item| {
            switch (item.item_type) {
                .Push => try stack.append(self.allocator, item.data_value),
                .Operation => {
                    const arguments = item.arguments();
                    if (stack.items.len < arguments) return false;
                    const top = stack.items.len - 1;
                    switch (item.instruction_value.?) {
                        .MUL => stack.items[top - 1] = stack.items[top] *% stack.items[top - 1],
                        .EXP => {
                            if (stack.items[top - 1] > 0xff) return false;
                            stack.items[top - 1] = wrappingPow(stack.items[top], @intCast(stack.items[top - 1]));
                        },
                        .ADD => stack.items[top - 1] = stack.items[top] +% stack.items[top - 1],
                        .SUB => stack.items[top - 1] = stack.items[top] -% stack.items[top - 1],
                        .NOT => stack.items[top] = ~stack.items[top],
                        .SHL => {
                            if (!self.params.evm_version.hasBitwiseShifting() or stack.items[top] > 255)
                                return false;
                            stack.items[top - 1] = stack.items[top - 1] << @intCast(stack.items[top]);
                        },
                        .SHR => {
                            if (!self.params.evm_version.hasBitwiseShifting() or stack.items[top] > 255)
                                return false;
                            stack.items[top - 1] >>= @intCast(stack.items[top]);
                        },
                        else => return false,
                    }
                    const new_length: isize = @as(isize, @intCast(stack.items.len)) + item.deposit();
                    stack.items.len = @intCast(new_length);
                },
                else => return false,
            }
        }
        return stack.items.len == 1 and stack.items[0] == value;
    }

    fn gasNeededRoutine(self: *const ComputeMethod, routine: []const AssemblyItem) !u512 {
        var exponent_count: usize = 0;
        for (routine) |*item| {
            if (item.eqlInstruction(.EXP)) exponent_count += 1;
        }
        const byte_price = if (self.params.is_creation)
            GasMeter.GasCosts.txDataNonZeroGas(self.params.evm_version)
        else
            GasMeter.GasCosts.create_data_gas;
        return combineGas(
            self.params,
            try simpleRunGas(routine, self.params.evm_version) +
                @as(u512, exponent_count) *
                    (GasMeter.GasCosts.exp_gas + GasMeter.GasCosts.expByteGas(self.params.evm_version)),
            @as(u512, try bytesRequired(routine, self.params.evm_version)) * byte_price,
            0,
        );
    }
};

fn replaceConstants(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(AssemblyItem),
    replacements: []const Replacement,
) std.mem.Allocator.Error!void {
    var replaced: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
    errdefer deinitItems(allocator, &replaced);
    for (items.items) |*item| {
        if (item.item_type == .Push) {
            const found = searchReplacements(replacements, item.data_value);
            if (found.found) {
                for (replacements[found.index].items.items) |*replacement|
                    try appendClone(allocator, &replaced, replacement);
                continue;
            }
        }
        try appendClone(allocator, &replaced, item);
    }
    deinitItems(allocator, items);
    items.* = replaced;
}

const SearchResult = struct { index: usize, found: bool };

fn searchPushes(pushes: []const PushCount, value: u256) SearchResult {
    var lower: usize = 0;
    var upper = pushes.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (pushes[middle].value < value) lower = middle + 1 else upper = middle;
    }
    return .{ .index = lower, .found = lower < pushes.len and pushes[lower].value == value };
}

fn searchReplacements(replacements: []const Replacement, value: u256) SearchResult {
    var lower: usize = 0;
    var upper = replacements.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (replacements[middle].value < value) lower = middle + 1 else upper = middle;
    }
    return .{ .index = lower, .found = lower < replacements.len and replacements[lower].value == value };
}

fn wrappingPow(base_value: u256, exponent_value: u8) u256 {
    var base = base_value;
    var exponent = exponent_value;
    var result: u256 = 1;
    while (exponent != 0) : (exponent >>= 1) {
        if (exponent & 1 != 0) result *%= base;
        base *%= base;
    }
    return result;
}

fn listFromSlice(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
) std.mem.Allocator.Error!std.ArrayList(AssemblyItem) {
    var result: std.ArrayList(AssemblyItem) = .empty;
    errdefer result.deinit(allocator);
    try result.appendSlice(allocator, items);
    return result;
}

fn appendClone(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(AssemblyItem),
    item: *const AssemblyItem,
) std.mem.Allocator.Error!void {
    var cloned = try item.clone(allocator);
    errdefer cloned.deinit(allocator);
    try items.append(allocator, cloned);
}

fn deinitItems(allocator: std.mem.Allocator, items: *std.ArrayList(AssemblyItem)) void {
    for (items.items) |*item| item.deinit(allocator);
    items.deinit(allocator);
    items.* = .empty;
}

const TestSink = struct {
    fn add(_: *anyopaque, data: [32]u8) !AssemblyItem {
        return AssemblyItem.initType(.PushData, Keccak256.keccak256(&data).toInteger(), .{});
    }
};

test "computed constants reproduce their input and optimizer replaces profitable literals" {
    const params: Params = .{
        .is_creation = false,
        .runs = 200,
        .multiplicity = 8,
        .evm_version = EVMVersion.init(.London),
    };
    const value: u256 = (@as(u256, 0x1234) << 192) | 7;
    var compute = try ComputeMethod.init(std.testing.allocator, params, value);
    defer compute.deinit();
    try std.testing.expect(try compute.checkRepresentation(value, compute.routine.items));

    var items: std.ArrayList(AssemblyItem) = .empty;
    defer deinitItems(std.testing.allocator, &items);
    for (0..8) |_| try items.append(std.testing.allocator, AssemblyItem.initPush(value, .{}));
    var sink_state: u8 = 0;
    const changed = try optimiseConstants(
        std.testing.allocator,
        false,
        200,
        EVMVersion.init(.London),
        &items,
        .{ .context = &sink_state, .add_data = TestSink.add },
    );
    try std.testing.expect(changed != 0);
}
