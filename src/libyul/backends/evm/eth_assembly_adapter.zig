// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Adapter from the Yul abstract assembly interface to `libevmasm.Assembly`.

const std = @import("std");
const AbstractModule = @import("abstract_assembly.zig");
const AbstractAssembly = AbstractModule.AbstractAssembly;
const AssemblyModule = @import("../../../libevmasm/assembly.zig");
const Assembly = AssemblyModule.Assembly;
const AssemblyItemModule = @import("../../../libevmasm/assembly_item.zig");
const AssemblyItem = AssemblyItemModule.AssemblyItem;
const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
const Instruction = @import("../../../libevmasm/instruction.zig").Instruction;
const SourceLocation = @import("../../../liblangutil/source_location.zig").SourceLocation;
const SubAssemblyID = @import("../../../libevmasm/sub_assembly_id.zig").SubAssemblyID;

pub const EthAssemblyAdapter = struct {
    allocator: std.mem.Allocator,
    assembly: *Assembly,
    data_hash_by_sub_id: std.AutoHashMap(u64, u256),
    next_data_counter: u64 = std.math.maxInt(u64) / 2,
    child_adapters: std.ArrayList(*EthAssemblyAdapter) = .empty,

    pub fn init(allocator: std.mem.Allocator, assembly: *Assembly) EthAssemblyAdapter {
        return .{
            .allocator = allocator,
            .assembly = assembly,
            .data_hash_by_sub_id = std.AutoHashMap(u64, u256).init(allocator),
        };
    }

    /// Releases adapter wrappers. The corresponding `Assembly` tree remains
    /// owned by the root assembly, exactly as it was before adaptation.
    pub fn deinit(self: *EthAssemblyAdapter) void {
        for (self.child_adapters.items) |child| {
            child.deinit();
            self.allocator.destroy(child);
        }
        self.child_adapters.deinit(self.allocator);
        self.data_hash_by_sub_id.deinit();
        self.* = undefined;
    }

    pub fn abstractAssembly(self: *EthAssemblyAdapter) AbstractAssembly {
        return .{ .context = self, .vtable = &vtable };
    }

    fn setSourceLocation(self: *EthAssemblyAdapter, location: SourceLocation) void {
        self.assembly.setSourceLocation(location);
    }

    fn stackHeight(self: *const EthAssemblyAdapter) i32 {
        return self.assembly.deposit();
    }

    fn setStackHeight(self: *EthAssemblyAdapter, height: i32) !void {
        try self.assembly.setDeposit(height);
    }

    fn appendInstruction(self: *EthAssemblyAdapter, instruction: Instruction) !void {
        _ = try self.assembly.append(AssemblyItem.initInstruction(instruction, .{}));
    }

    fn appendConstant(self: *EthAssemblyAdapter, constant: u256) !void {
        _ = try self.assembly.append(AssemblyItem.initPush(constant, .{}));
    }

    fn appendLabel(self: *EthAssemblyAdapter, label_id: AbstractModule.LabelID) !void {
        _ = try self.assembly.append(AssemblyItem.initType(.Tag, label_id, .{}));
    }

    fn appendLabelReference(self: *EthAssemblyAdapter, label_id: AbstractModule.LabelID) !void {
        _ = try self.assembly.append(AssemblyItem.initType(.PushTag, label_id, .{}));
    }

    fn newLabelId(self: *EthAssemblyAdapter) !AbstractModule.LabelID {
        const tag = try self.assembly.newTag();
        return assemblyTagToIdentifier(&tag);
    }

    fn namedLabel(
        self: *EthAssemblyAdapter,
        name: []const u8,
        parameters: usize,
        returns: usize,
        source_id: ?usize,
    ) !AbstractModule.LabelID {
        const tag = try self.assembly.namedTag(name, parameters, returns, source_id);
        return assemblyTagToIdentifier(&tag);
    }

    fn appendLinkerSymbol(self: *EthAssemblyAdapter, linker_symbol: []const u8) !void {
        _ = try self.assembly.append(try self.assembly.newPushLibraryAddress(linker_symbol));
    }

    fn appendVerbatim(
        self: *EthAssemblyAdapter,
        data: []const u8,
        arguments: usize,
        return_variables: usize,
    ) !void {
        try self.assembly.appendVerbatim(data, arguments, return_variables);
    }

    fn appendJump(
        self: *EthAssemblyAdapter,
        stack_diff_after: i32,
        jump_type: AbstractModule.JumpType,
    ) !void {
        try self.appendJumpInstruction(.JUMP, jump_type);
        try self.assembly.adjustDeposit(stack_diff_after);
    }

    fn appendJumpTo(
        self: *EthAssemblyAdapter,
        label_id: AbstractModule.LabelID,
        stack_diff_after: i32,
        jump_type: AbstractModule.JumpType,
    ) !void {
        try self.appendLabelReference(label_id);
        try self.appendJump(stack_diff_after, jump_type);
    }

    fn appendJumpToIf(
        self: *EthAssemblyAdapter,
        label_id: AbstractModule.LabelID,
        jump_type: AbstractModule.JumpType,
    ) !void {
        try self.appendLabelReference(label_id);
        try self.appendJumpInstruction(.JUMPI, jump_type);
    }

    fn appendAssemblySize(self: *EthAssemblyAdapter) !void {
        try self.assembly.appendProgramSize();
    }

    fn createSubAssembly(
        self: *EthAssemblyAdapter,
        creation: bool,
        name: []const u8,
    ) !AbstractModule.CreatedSubAssembly {
        try self.child_adapters.ensureUnusedCapacity(self.allocator, 1);
        const sub_assembly = try Assembly.create(
            self.allocator,
            self.assembly.evmVersion(),
            creation,
            name,
        );
        const child = self.allocator.create(EthAssemblyAdapter) catch |err| {
            sub_assembly.destroy();
            return err;
        };
        child.* = EthAssemblyAdapter.init(self.allocator, sub_assembly);
        const sub_item = self.assembly.newSub(sub_assembly) catch |err| {
            child.deinit();
            self.allocator.destroy(child);
            return err;
        };
        self.child_adapters.appendAssumeCapacity(child);
        return .{
            .assembly = child.abstractAssembly(),
            .sub_id = try SubAssemblyID.fromU256(sub_item.data_value),
        };
    }

    fn appendDataOffset(self: *EthAssemblyAdapter, sub_path: []const SubAssemblyID) !void {
        if (sub_path.len == 0) return error.EmptySubPath;
        if (self.data_hash_by_sub_id.get(sub_path[0].value)) |hash| {
            if (sub_path.len != 1) return error.DataPathHasChildren;
            _ = try self.assembly.append(AssemblyItem.initType(.PushData, hash, .{}));
            return;
        }
        const encoded = try self.assembly.encodeSubPath(sub_path);
        _ = try self.assembly.append(AssemblyItem.initType(.PushSub, encoded.value, .{}));
    }

    fn appendDataSize(self: *EthAssemblyAdapter, sub_path: []const SubAssemblyID) !void {
        if (sub_path.len == 0) return error.EmptySubPath;
        if (self.data_hash_by_sub_id.get(sub_path[0].value)) |hash| {
            if (sub_path.len != 1) return error.DataPathHasChildren;
            try self.appendConstant((try self.assembly.data(hash)).len);
            return;
        }
        const encoded = try self.assembly.encodeSubPath(sub_path);
        _ = try self.assembly.append(AssemblyItem.initType(.PushSubSize, encoded.value, .{}));
    }

    fn appendData(self: *EthAssemblyAdapter, data: []const u8) !SubAssemblyID {
        const push_data = try self.assembly.newData(data);
        if (self.next_data_counter == std.math.maxInt(u64)) return error.OutOfDataIds;
        const sub_id = SubAssemblyID.init(self.next_data_counter);
        self.next_data_counter += 1;
        try self.data_hash_by_sub_id.put(sub_id.value, push_data.data_value);
        return sub_id;
    }

    fn appendImmutable(self: *EthAssemblyAdapter, identifier: []const u8) !void {
        _ = try self.assembly.append(try self.assembly.newPushImmutable(identifier));
    }

    fn appendImmutableAssignment(self: *EthAssemblyAdapter, identifier: []const u8) !void {
        _ = try self.assembly.append(try self.assembly.newImmutableAssignment(identifier));
    }

    fn appendToAuxiliaryData(self: *EthAssemblyAdapter, data: []const u8) !void {
        try self.assembly.appendToAuxiliaryData(data);
    }

    fn markAsInvalid(self: *EthAssemblyAdapter) void {
        self.assembly.markAsInvalid();
    }

    fn evmVersion(self: *const EthAssemblyAdapter) EVMVersion {
        return self.assembly.evmVersion();
    }

    fn appendJumpInstruction(
        self: *EthAssemblyAdapter,
        instruction: Instruction,
        jump_type: AbstractModule.JumpType,
    ) !void {
        if (instruction != .JUMP and instruction != .JUMPI) return error.InvalidJumpInstruction;
        var jump = AssemblyItem.initInstruction(instruction, .{});
        jump.jump_type = switch (jump_type) {
            .ordinary => .Ordinary,
            .into_function => .IntoFunction,
            .out_of_function => .OutOfFunction,
        };
        _ = try self.assembly.append(jump);
    }
};

fn assemblyTagToIdentifier(tag: *const AssemblyItem) !AbstractModule.LabelID {
    if (tag.data_value > std.math.maxInt(AbstractModule.LabelID)) return error.TagIdTooLarge;
    return @intCast(tag.data_value);
}

fn adapter(context: *anyopaque) *EthAssemblyAdapter {
    return @ptrCast(@alignCast(context));
}

fn constAdapter(context: *const anyopaque) *const EthAssemblyAdapter {
    return @ptrCast(@alignCast(context));
}

fn vSetSourceLocation(context: *anyopaque, location: SourceLocation) !void {
    adapter(context).setSourceLocation(location);
}
fn vStackHeight(context: *const anyopaque) !i32 {
    return constAdapter(context).stackHeight();
}
fn vSetStackHeight(context: *anyopaque, height: i32) !void {
    return adapter(context).setStackHeight(height);
}
fn vAppendInstruction(context: *anyopaque, instruction: Instruction) !void {
    return adapter(context).appendInstruction(instruction);
}
fn vAppendConstant(context: *anyopaque, constant: u256) !void {
    return adapter(context).appendConstant(constant);
}
fn vAppendLabel(context: *anyopaque, label_id: AbstractModule.LabelID) !void {
    return adapter(context).appendLabel(label_id);
}
fn vAppendLabelReference(context: *anyopaque, label_id: AbstractModule.LabelID) !void {
    return adapter(context).appendLabelReference(label_id);
}
fn vNewLabelId(context: *anyopaque) !AbstractModule.LabelID {
    return adapter(context).newLabelId();
}
fn vNamedLabel(
    context: *anyopaque,
    name: []const u8,
    parameters: usize,
    returns: usize,
    source_id: ?usize,
) !AbstractModule.LabelID {
    return adapter(context).namedLabel(name, parameters, returns, source_id);
}
fn vAppendLinkerSymbol(context: *anyopaque, name: []const u8) !void {
    return adapter(context).appendLinkerSymbol(name);
}
fn vAppendVerbatim(context: *anyopaque, data: []const u8, arguments: usize, returns: usize) !void {
    return adapter(context).appendVerbatim(data, arguments, returns);
}
fn vAppendJump(context: *anyopaque, stack_diff_after: i32, jump_type: AbstractModule.JumpType) !void {
    return adapter(context).appendJump(stack_diff_after, jump_type);
}
fn vAppendJumpTo(
    context: *anyopaque,
    label_id: AbstractModule.LabelID,
    stack_diff_after: i32,
    jump_type: AbstractModule.JumpType,
) !void {
    return adapter(context).appendJumpTo(label_id, stack_diff_after, jump_type);
}
fn vAppendJumpToIf(
    context: *anyopaque,
    label_id: AbstractModule.LabelID,
    jump_type: AbstractModule.JumpType,
) !void {
    return adapter(context).appendJumpToIf(label_id, jump_type);
}
fn vAppendAssemblySize(context: *anyopaque) !void {
    return adapter(context).appendAssemblySize();
}
fn vCreateSubAssembly(context: *anyopaque, creation: bool, name: []const u8) !AbstractModule.CreatedSubAssembly {
    return adapter(context).createSubAssembly(creation, name);
}
fn vAppendDataOffset(context: *anyopaque, sub_path: []const SubAssemblyID) !void {
    return adapter(context).appendDataOffset(sub_path);
}
fn vAppendDataSize(context: *anyopaque, sub_path: []const SubAssemblyID) !void {
    return adapter(context).appendDataSize(sub_path);
}
fn vAppendData(context: *anyopaque, data: []const u8) !SubAssemblyID {
    return adapter(context).appendData(data);
}
fn vAppendImmutable(context: *anyopaque, identifier: []const u8) !void {
    return adapter(context).appendImmutable(identifier);
}
fn vAppendImmutableAssignment(context: *anyopaque, identifier: []const u8) !void {
    return adapter(context).appendImmutableAssignment(identifier);
}
fn vAppendToAuxiliaryData(context: *anyopaque, data: []const u8) !void {
    return adapter(context).appendToAuxiliaryData(data);
}
fn vMarkAsInvalid(context: *anyopaque) !void {
    adapter(context).markAsInvalid();
}
fn vEVMVersion(context: *const anyopaque) !EVMVersion {
    return constAdapter(context).evmVersion();
}

const vtable: AbstractModule.VTable = .{
    .set_source_location = vSetSourceLocation,
    .stack_height = vStackHeight,
    .set_stack_height = vSetStackHeight,
    .append_instruction = vAppendInstruction,
    .append_constant = vAppendConstant,
    .append_label = vAppendLabel,
    .append_label_reference = vAppendLabelReference,
    .new_label_id = vNewLabelId,
    .named_label = vNamedLabel,
    .append_linker_symbol = vAppendLinkerSymbol,
    .append_verbatim = vAppendVerbatim,
    .append_jump = vAppendJump,
    .append_jump_to = vAppendJumpTo,
    .append_jump_to_if = vAppendJumpToIf,
    .append_assembly_size = vAppendAssemblySize,
    .create_sub_assembly = vCreateSubAssembly,
    .append_data_offset = vAppendDataOffset,
    .append_data_size = vAppendDataSize,
    .append_data = vAppendData,
    .append_immutable = vAppendImmutable,
    .append_immutable_assignment = vAppendImmutableAssignment,
    .append_to_auxiliary_data = vAppendToAuxiliaryData,
    .mark_as_invalid = vMarkAsInvalid,
    .evm_version = vEVMVersion,
};

test "Eth assembly adapter preserves labels, jumps, data, and stack accounting" {
    const allocator = std.testing.allocator;
    var assembly = try Assembly.init(allocator, EVMVersion.current(), true, "root");
    defer assembly.deinit();
    var eth_adapter = EthAssemblyAdapter.init(allocator, &assembly);
    defer eth_adapter.deinit();
    const abstract = eth_adapter.abstractAssembly();

    try abstract.appendConstant(7);
    try abstract.appendInstruction(.POP);
    const label = try abstract.newLabelId();
    try abstract.appendLabel(label);
    try abstract.appendJumpTo(label, 0, .into_function);
    const data_id = try abstract.appendData("abc");
    try abstract.appendDataOffset(&.{data_id});
    try abstract.appendDataSize(&.{data_id});
    try abstract.appendLinkerSymbol("Library");
    try abstract.appendVerbatim(&.{ 0xaa, 0xbb }, 0, 1);
    try std.testing.expectEqual(EVMVersion.current().version, (try abstract.evmVersion()).version);
    try std.testing.expectEqual(@as(i32, 4), try abstract.stackHeight());
    try std.testing.expectEqual(@as(usize, 9), assembly.itemsConst().len);
    try std.testing.expectEqual(AssemblyItemModule.JumpType.IntoFunction, assembly.itemsConst()[4].jump_type);
    try std.testing.expectEqual(AssemblyItemModule.AssemblyItemType.PushData, assembly.itemsConst()[5].item_type);
}
