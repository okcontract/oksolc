// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Manual-vtable form of the Yul EVM backend assembly interface.

const std = @import("std");
const AST = @import("../../ast.zig");
const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
const Instruction = @import("../../../libevmasm/instruction.zig").Instruction;
const SourceLocation = @import("../../../liblangutil/source_location.zig").SourceLocation;
const SubAssemblyID = @import("../../../libevmasm/sub_assembly_id.zig").SubAssemblyID;

pub const LabelID = usize;
pub const SubID = SubAssemblyID;
pub const ContainerID = u8;
pub const FunctionID = u16;

pub const JumpType = enum(c_int) {
    ordinary,
    into_function,
    out_of_function,
};

pub const AssemblyError = anyerror;

pub const CreatedSubAssembly = struct {
    assembly: AbstractAssembly,
    sub_id: SubID,
};

pub const VTable = struct {
    set_source_location: ?*const fn (*anyopaque, SourceLocation) AssemblyError!void = null,
    stack_height: ?*const fn (*const anyopaque) AssemblyError!i32 = null,
    set_stack_height: ?*const fn (*anyopaque, i32) AssemblyError!void = null,
    append_instruction: ?*const fn (*anyopaque, Instruction) AssemblyError!void = null,
    append_constant: ?*const fn (*anyopaque, u256) AssemblyError!void = null,
    append_label: ?*const fn (*anyopaque, LabelID) AssemblyError!void = null,
    append_label_reference: ?*const fn (*anyopaque, LabelID) AssemblyError!void = null,
    new_label_id: ?*const fn (*anyopaque) AssemblyError!LabelID = null,
    named_label: ?*const fn (*anyopaque, []const u8, usize, usize, ?usize) AssemblyError!LabelID = null,
    append_linker_symbol: ?*const fn (*anyopaque, []const u8) AssemblyError!void = null,
    append_verbatim: ?*const fn (*anyopaque, []const u8, usize, usize) AssemblyError!void = null,
    append_jump: ?*const fn (*anyopaque, i32, JumpType) AssemblyError!void = null,
    append_jump_to: ?*const fn (*anyopaque, LabelID, i32, JumpType) AssemblyError!void = null,
    append_jump_to_if: ?*const fn (*anyopaque, LabelID, JumpType) AssemblyError!void = null,
    append_assembly_size: ?*const fn (*anyopaque) AssemblyError!void = null,
    create_sub_assembly: ?*const fn (*anyopaque, bool, []const u8) AssemblyError!CreatedSubAssembly = null,
    append_data_offset: ?*const fn (*anyopaque, []const SubID) AssemblyError!void = null,
    append_data_size: ?*const fn (*anyopaque, []const SubID) AssemblyError!void = null,
    append_data: ?*const fn (*anyopaque, []const u8) AssemblyError!SubID = null,
    append_immutable: ?*const fn (*anyopaque, []const u8) AssemblyError!void = null,
    append_immutable_assignment: ?*const fn (*anyopaque, []const u8) AssemblyError!void = null,
    append_to_auxiliary_data: ?*const fn (*anyopaque, []const u8) AssemblyError!void = null,
    mark_as_invalid: ?*const fn (*anyopaque) AssemblyError!void = null,
    evm_version: ?*const fn (*const anyopaque) AssemblyError!EVMVersion = null,
};

pub const AbstractAssembly = struct {
    context: *anyopaque,
    vtable: *const VTable,

    pub fn setSourceLocation(self: AbstractAssembly, location: SourceLocation) AssemblyError!void {
        return (self.vtable.set_source_location orelse return error.UnsupportedAssemblyOperation)(self.context, location);
    }

    pub fn stackHeight(self: AbstractAssembly) AssemblyError!i32 {
        const context: *const anyopaque = self.context;
        return (self.vtable.stack_height orelse return error.UnsupportedAssemblyOperation)(context);
    }

    pub fn setStackHeight(self: AbstractAssembly, height: i32) AssemblyError!void {
        return (self.vtable.set_stack_height orelse return error.UnsupportedAssemblyOperation)(self.context, height);
    }

    pub fn appendInstruction(self: AbstractAssembly, instruction: Instruction) AssemblyError!void {
        return (self.vtable.append_instruction orelse return error.UnsupportedAssemblyOperation)(self.context, instruction);
    }

    pub fn appendConstant(self: AbstractAssembly, constant: u256) AssemblyError!void {
        return (self.vtable.append_constant orelse return error.UnsupportedAssemblyOperation)(self.context, constant);
    }

    pub fn appendLabel(self: AbstractAssembly, label_id: LabelID) AssemblyError!void {
        return (self.vtable.append_label orelse return error.UnsupportedAssemblyOperation)(self.context, label_id);
    }

    pub fn appendLabelReference(self: AbstractAssembly, label_id: LabelID) AssemblyError!void {
        return (self.vtable.append_label_reference orelse return error.UnsupportedAssemblyOperation)(self.context, label_id);
    }

    pub fn newLabelId(self: AbstractAssembly) AssemblyError!LabelID {
        return (self.vtable.new_label_id orelse return error.UnsupportedAssemblyOperation)(self.context);
    }

    pub fn namedLabel(
        self: AbstractAssembly,
        name: []const u8,
        parameters: usize,
        returns: usize,
        source_id: ?usize,
    ) AssemblyError!LabelID {
        return (self.vtable.named_label orelse return error.UnsupportedAssemblyOperation)(
            self.context,
            name,
            parameters,
            returns,
            source_id,
        );
    }

    pub fn appendLinkerSymbol(self: AbstractAssembly, name: []const u8) AssemblyError!void {
        return (self.vtable.append_linker_symbol orelse return error.UnsupportedAssemblyOperation)(self.context, name);
    }

    pub fn appendVerbatim(
        self: AbstractAssembly,
        data: []const u8,
        arguments: usize,
        return_variables: usize,
    ) AssemblyError!void {
        return (self.vtable.append_verbatim orelse return error.UnsupportedAssemblyOperation)(
            self.context,
            data,
            arguments,
            return_variables,
        );
    }

    pub fn appendJump(
        self: AbstractAssembly,
        stack_diff_after: i32,
        jump_type: JumpType,
    ) AssemblyError!void {
        return (self.vtable.append_jump orelse return error.UnsupportedAssemblyOperation)(
            self.context,
            stack_diff_after,
            jump_type,
        );
    }

    pub fn appendJumpTo(
        self: AbstractAssembly,
        label_id: LabelID,
        stack_diff_after: i32,
        jump_type: JumpType,
    ) AssemblyError!void {
        return (self.vtable.append_jump_to orelse return error.UnsupportedAssemblyOperation)(
            self.context,
            label_id,
            stack_diff_after,
            jump_type,
        );
    }

    pub fn appendJumpToIf(
        self: AbstractAssembly,
        label_id: LabelID,
        jump_type: JumpType,
    ) AssemblyError!void {
        return (self.vtable.append_jump_to_if orelse return error.UnsupportedAssemblyOperation)(
            self.context,
            label_id,
            jump_type,
        );
    }

    pub fn appendAssemblySize(self: AbstractAssembly) AssemblyError!void {
        return (self.vtable.append_assembly_size orelse return error.UnsupportedAssemblyOperation)(self.context);
    }

    pub fn createSubAssembly(
        self: AbstractAssembly,
        creation: bool,
        name: []const u8,
    ) AssemblyError!CreatedSubAssembly {
        return (self.vtable.create_sub_assembly orelse return error.UnsupportedAssemblyOperation)(
            self.context,
            creation,
            name,
        );
    }

    pub fn appendDataOffset(self: AbstractAssembly, sub_path: []const SubID) AssemblyError!void {
        return (self.vtable.append_data_offset orelse return error.UnsupportedAssemblyOperation)(self.context, sub_path);
    }

    pub fn appendDataSize(self: AbstractAssembly, sub_path: []const SubID) AssemblyError!void {
        return (self.vtable.append_data_size orelse return error.UnsupportedAssemblyOperation)(self.context, sub_path);
    }

    pub fn appendData(self: AbstractAssembly, data: []const u8) AssemblyError!SubID {
        return (self.vtable.append_data orelse return error.UnsupportedAssemblyOperation)(self.context, data);
    }

    pub fn appendImmutable(self: AbstractAssembly, identifier: []const u8) AssemblyError!void {
        return (self.vtable.append_immutable orelse return error.UnsupportedAssemblyOperation)(self.context, identifier);
    }

    pub fn appendImmutableAssignment(self: AbstractAssembly, identifier: []const u8) AssemblyError!void {
        return (self.vtable.append_immutable_assignment orelse return error.UnsupportedAssemblyOperation)(self.context, identifier);
    }

    pub fn appendToAuxiliaryData(self: AbstractAssembly, data: []const u8) AssemblyError!void {
        return (self.vtable.append_to_auxiliary_data orelse return error.UnsupportedAssemblyOperation)(self.context, data);
    }

    pub fn markAsInvalid(self: AbstractAssembly) AssemblyError!void {
        return (self.vtable.mark_as_invalid orelse return error.UnsupportedAssemblyOperation)(self.context);
    }

    pub fn evmVersion(self: AbstractAssembly) AssemblyError!EVMVersion {
        const context: *const anyopaque = self.context;
        return (self.vtable.evm_version orelse return error.UnsupportedAssemblyOperation)(context);
    }
};

pub const IdentifierContext = enum(c_int) {
    l_value,
    r_value,
    variable_declaration,
    non_external,
};

pub const ExternalIdentifierAccess = struct {
    context: ?*anyopaque = null,
    resolve_fn: ?*const fn (?*anyopaque, *const AST.Identifier, IdentifierContext, bool) bool = null,
    generate_code_fn: ?*const fn (
        ?*anyopaque,
        *const AST.Identifier,
        IdentifierContext,
        AbstractAssembly,
    ) AssemblyError!void = null,

    pub fn resolve(
        self: ExternalIdentifierAccess,
        identifier: *const AST.Identifier,
        identifier_context: IdentifierContext,
        crosses_function_boundary: bool,
    ) bool {
        const callback = self.resolve_fn orelse return false;
        return callback(self.context, identifier, identifier_context, crosses_function_boundary);
    }

    pub fn generateCode(
        self: ExternalIdentifierAccess,
        identifier: *const AST.Identifier,
        identifier_context: IdentifierContext,
        assembly: AbstractAssembly,
    ) AssemblyError!void {
        const callback = self.generate_code_fn orelse return error.MissingExternalCodeGenerator;
        return callback(self.context, identifier, identifier_context, assembly);
    }
};

test "abstract assembly dispatches mutation and query operations" {
    const Mock = struct {
        height: i32 = 0,
        last_instruction: ?Instruction = null,

        fn appendInstruction(context: *anyopaque, instruction: Instruction) AssemblyError!void {
            const self: *@This() = @ptrCast(@alignCast(context));
            self.last_instruction = instruction;
            self.height += @as(i32, @intCast(@import("../../../libevmasm/instruction.zig").instructionInfo(
                instruction,
                .current(),
            ).ret)) - @as(i32, @intCast(@import("../../../libevmasm/instruction.zig").instructionInfo(
                instruction,
                .current(),
            ).args));
        }

        fn stackHeight(context: *const anyopaque) AssemblyError!i32 {
            const self: *const @This() = @ptrCast(@alignCast(context));
            return self.height;
        }
    };
    const vtable: VTable = .{
        .append_instruction = Mock.appendInstruction,
        .stack_height = Mock.stackHeight,
    };
    var mock: Mock = .{};
    const assembly: AbstractAssembly = .{ .context = &mock, .vtable = &vtable };
    try assembly.appendInstruction(.ADD);
    try std.testing.expectEqual(Instruction.ADD, mock.last_instruction.?);
    try std.testing.expectEqual(@as(i32, -1), try assembly.stackHeight());
    try std.testing.expectError(error.UnsupportedAssemblyOperation, assembly.appendConstant(1));
}
