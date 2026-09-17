// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Stack-counting dry-run assembly and no-output builtin lowering.

const std = @import("std");
const InstructionModule = @import("../../../libevmasm/instruction.zig");
const SubAssemblyID = @import("../../../libevmasm/sub_assembly_id.zig").SubAssemblyID;
const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
const SourceLocation = @import("../../../liblangutil/source_location.zig").SourceLocation;
const AST = @import("../../ast.zig");
const AbstractModule = @import("abstract_assembly.zig");
const EVMBuiltinsModule = @import("evm_builtins.zig");
const EVMDialectModule = @import("evm_dialect.zig");

const AbstractAssembly = AbstractModule.AbstractAssembly;
const BuiltinContext = EVMBuiltinsModule.BuiltinContext;
const BuiltinFunctionForEVM = EVMBuiltinsModule.BuiltinFunctionForEVM;
const Instruction = InstructionModule.Instruction;

pub const NoOutputAssembly = struct {
    stack_height: i32 = 0,
    evm_version: EVMVersion,

    pub fn init(evm_version: EVMVersion) NoOutputAssembly {
        return .{ .evm_version = evm_version };
    }

    pub fn abstractAssembly(self: *NoOutputAssembly) AbstractAssembly {
        return .{ .context = self, .vtable = &vtable };
    }

    pub fn stackHeight(self: *const NoOutputAssembly) i32 {
        return self.stack_height;
    }

    pub fn setStackHeight(self: *NoOutputAssembly, height: i32) void {
        self.stack_height = height;
    }

    pub fn appendInstruction(self: *NoOutputAssembly, instruction: Instruction) !void {
        const info = InstructionModule.instructionInfo(instruction, self.evm_version);
        const difference = @as(i32, @intCast(info.ret)) - @as(i32, @intCast(info.args));
        self.stack_height = std.math.add(i32, self.stack_height, difference) catch
            return error.StackHeightOverflow;
    }

    pub fn appendConstant(self: *NoOutputAssembly, _: u256) !void {
        try self.appendInstruction(InstructionModule.pushInstruction(1));
    }

    pub fn appendLabel(self: *NoOutputAssembly, _: AbstractModule.LabelID) !void {
        try self.appendInstruction(.JUMPDEST);
    }

    pub fn appendLabelReference(self: *NoOutputAssembly, _: AbstractModule.LabelID) !void {
        try self.appendInstruction(InstructionModule.pushInstruction(1));
    }

    pub fn newLabelId(_: *NoOutputAssembly) AbstractModule.LabelID {
        return 1;
    }

    pub fn namedLabel(
        _: *NoOutputAssembly,
        _: []const u8,
        _: usize,
        _: usize,
        _: ?usize,
    ) AbstractModule.LabelID {
        return 1;
    }

    pub fn appendLinkerSymbol(_: *NoOutputAssembly, _: []const u8) !void {
        return error.UnsupportedLinkerSymbol;
    }

    pub fn appendVerbatim(
        self: *NoOutputAssembly,
        _: []const u8,
        arguments: usize,
        return_variables: usize,
    ) !void {
        const difference = @as(i64, @intCast(return_variables)) - @as(i64, @intCast(arguments));
        const next = @as(i64, self.stack_height) + difference;
        if (next < std.math.minInt(i32) or next > std.math.maxInt(i32))
            return error.StackHeightOverflow;
        self.stack_height = @intCast(next);
    }

    pub fn appendJump(
        self: *NoOutputAssembly,
        stack_diff_after: i32,
        _: AbstractModule.JumpType,
    ) !void {
        try self.appendInstruction(.JUMP);
        self.stack_height = std.math.add(i32, self.stack_height, stack_diff_after) catch
            return error.StackHeightOverflow;
    }

    pub fn appendJumpTo(
        self: *NoOutputAssembly,
        label_id: AbstractModule.LabelID,
        stack_diff_after: i32,
        jump_type: AbstractModule.JumpType,
    ) !void {
        try self.appendLabelReference(label_id);
        try self.appendJump(stack_diff_after, jump_type);
    }

    pub fn appendJumpToIf(
        self: *NoOutputAssembly,
        label_id: AbstractModule.LabelID,
        _: AbstractModule.JumpType,
    ) !void {
        try self.appendLabelReference(label_id);
        try self.appendInstruction(.JUMPI);
    }

    pub fn appendAssemblySize(self: *NoOutputAssembly) !void {
        try self.appendInstruction(.PUSH1);
    }

    pub fn createSubAssembly(_: *NoOutputAssembly, _: bool, _: []const u8) !AbstractModule.CreatedSubAssembly {
        return error.UnsupportedSubAssembly;
    }

    pub fn appendDataOffset(self: *NoOutputAssembly, _: []const SubAssemblyID) !void {
        try self.appendInstruction(.PUSH1);
    }

    pub fn appendDataSize(self: *NoOutputAssembly, _: []const SubAssemblyID) !void {
        try self.appendInstruction(.PUSH1);
    }

    pub fn appendData(_: *NoOutputAssembly, _: []const u8) SubAssemblyID {
        return .init(1);
    }

    pub fn appendImmutable(_: *NoOutputAssembly, _: []const u8) !void {
        return error.UnsupportedImmutableLoad;
    }

    pub fn appendImmutableAssignment(_: *NoOutputAssembly, _: []const u8) !void {
        return error.UnsupportedImmutableAssignment;
    }

    fn setSourceLocationErased(_: *anyopaque, _: SourceLocation) !void {}
    fn stackHeightErased(context: *const anyopaque) !i32 {
        const self: *const NoOutputAssembly = @ptrCast(@alignCast(context));
        return self.stackHeight();
    }
    fn setStackHeightErased(context: *anyopaque, height: i32) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        self.setStackHeight(height);
    }
    fn appendInstructionErased(context: *anyopaque, instruction: Instruction) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendInstruction(instruction);
    }
    fn appendConstantErased(context: *anyopaque, constant: u256) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendConstant(constant);
    }
    fn appendLabelErased(context: *anyopaque, label_id: AbstractModule.LabelID) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendLabel(label_id);
    }
    fn appendLabelReferenceErased(context: *anyopaque, label_id: AbstractModule.LabelID) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendLabelReference(label_id);
    }
    fn newLabelIdErased(context: *anyopaque) !AbstractModule.LabelID {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        return self.newLabelId();
    }
    fn namedLabelErased(
        context: *anyopaque,
        name: []const u8,
        parameters: usize,
        returns: usize,
        source_id: ?usize,
    ) !AbstractModule.LabelID {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        return self.namedLabel(name, parameters, returns, source_id);
    }
    fn appendLinkerSymbolErased(context: *anyopaque, name: []const u8) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendLinkerSymbol(name);
    }
    fn appendVerbatimErased(context: *anyopaque, data: []const u8, arguments: usize, returns: usize) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendVerbatim(data, arguments, returns);
    }
    fn appendJumpErased(context: *anyopaque, difference: i32, jump_type: AbstractModule.JumpType) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendJump(difference, jump_type);
    }
    fn appendJumpToErased(
        context: *anyopaque,
        label_id: AbstractModule.LabelID,
        difference: i32,
        jump_type: AbstractModule.JumpType,
    ) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendJumpTo(label_id, difference, jump_type);
    }
    fn appendJumpToIfErased(
        context: *anyopaque,
        label_id: AbstractModule.LabelID,
        jump_type: AbstractModule.JumpType,
    ) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendJumpToIf(label_id, jump_type);
    }
    fn appendAssemblySizeErased(context: *anyopaque) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendAssemblySize();
    }
    fn createSubAssemblyErased(context: *anyopaque, creation: bool, name: []const u8) !AbstractModule.CreatedSubAssembly {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        return self.createSubAssembly(creation, name);
    }
    fn appendDataOffsetErased(context: *anyopaque, path: []const SubAssemblyID) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendDataOffset(path);
    }
    fn appendDataSizeErased(context: *anyopaque, path: []const SubAssemblyID) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendDataSize(path);
    }
    fn appendDataErased(context: *anyopaque, data: []const u8) !SubAssemblyID {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        return self.appendData(data);
    }
    fn appendImmutableErased(context: *anyopaque, identifier: []const u8) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendImmutable(identifier);
    }
    fn appendImmutableAssignmentErased(context: *anyopaque, identifier: []const u8) !void {
        const self: *NoOutputAssembly = @ptrCast(@alignCast(context));
        try self.appendImmutableAssignment(identifier);
    }
    fn noOpBytes(_: *anyopaque, _: []const u8) !void {}
    fn noOp(_: *anyopaque) !void {}
    fn evmVersionErased(context: *const anyopaque) !EVMVersion {
        const self: *const NoOutputAssembly = @ptrCast(@alignCast(context));
        return self.evm_version;
    }

    const vtable: AbstractModule.VTable = .{
        .set_source_location = setSourceLocationErased,
        .stack_height = stackHeightErased,
        .set_stack_height = setStackHeightErased,
        .append_instruction = appendInstructionErased,
        .append_constant = appendConstantErased,
        .append_label = appendLabelErased,
        .append_label_reference = appendLabelReferenceErased,
        .new_label_id = newLabelIdErased,
        .named_label = namedLabelErased,
        .append_linker_symbol = appendLinkerSymbolErased,
        .append_verbatim = appendVerbatimErased,
        .append_jump = appendJumpErased,
        .append_jump_to = appendJumpToErased,
        .append_jump_to_if = appendJumpToIfErased,
        .append_assembly_size = appendAssemblySizeErased,
        .create_sub_assembly = createSubAssemblyErased,
        .append_data_offset = appendDataOffsetErased,
        .append_data_size = appendDataSizeErased,
        .append_data = appendDataErased,
        .append_immutable = appendImmutableErased,
        .append_immutable_assignment = appendImmutableAssignmentErased,
        .append_to_auxiliary_data = noOpBytes,
        .mark_as_invalid = noOp,
        .evm_version = evmVersionErased,
    };
};

/// Borrowing wrapper corresponding to the C++ dialect subclass. Analysis uses
/// the original dialect's descriptors; code generation calls
/// `generateBuiltinCode`, which retains only argument/return stack effects.
pub const NoOutputEVMDialect = struct {
    base: *const EVMDialectModule.EVMDialect,

    pub fn init(copy_from: *const EVMDialectModule.EVMDialect) NoOutputEVMDialect {
        return .{ .base = copy_from };
    }

    pub fn dialect(self: *const NoOutputEVMDialect) AST.Dialect {
        return self.base.dialect();
    }

    pub fn builtin(self: *const NoOutputEVMDialect, handle: @import("../../builtins.zig").BuiltinHandle) ?*const BuiltinFunctionForEVM {
        return self.base.builtin(handle);
    }

    pub fn generateBuiltinCode(
        _: *const NoOutputEVMDialect,
        builtin_function: *const BuiltinFunctionForEVM,
        call: *const AST.FunctionCall,
        assembly: AbstractAssembly,
        _: *BuiltinContext,
    ) !void {
        if (call.arguments.items.len != builtin_function.base.num_parameters)
            return error.InvalidBuiltinCall;
        for (0..call.arguments.items.len) |index|
            if (builtin_function.base.literalArgument(index) == null) try assembly.appendInstruction(.POP);
        for (0..builtin_function.base.num_returns) |_| try assembly.appendConstant(0);
    }
};

test "no-output assembly retains only stack effects" {
    var assembly = NoOutputAssembly.init(EVMVersion.current());
    const erased = assembly.abstractAssembly();
    try erased.appendConstant(7);
    try erased.appendConstant(9);
    try erased.appendInstruction(.ADD);
    try std.testing.expectEqual(@as(i32, 1), try erased.stackHeight());
    try erased.appendJumpTo(1, 3, .ordinary);
    try std.testing.expectEqual(@as(i32, 4), try erased.stackHeight());
    try erased.appendVerbatim(&.{ 1, 2 }, 2, 1);
    try std.testing.expectEqual(@as(i32, 3), try erased.stackHeight());
}
