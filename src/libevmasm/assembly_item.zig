// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Value-oriented translation of `AssemblyItem.cpp`.

const std = @import("std");
const CommonData = @import("../libsolutil/common_data.zig");
const Numeric = @import("../libsolutil/numeric.zig");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;
const InstructionModule = @import("instruction.zig");
const SubAssemblyID = @import("sub_assembly_id.zig").SubAssemblyID;

pub const AssemblyItemType = enum(c_int) {
    UndefinedItem,
    Operation,
    Push,
    PushTag,
    PushSub,
    PushSubSize,
    PushProgramSize,
    Tag,
    PushData,
    PushLibraryAddress,
    PushDeployTimeAddress,
    PushImmutable,
    AssignImmutable,
    VerbatimBytecode,
};

pub const Precision = enum(c_int) {
    Precise,
    Approximate,
};

pub const JumpType = enum(c_int) {
    Ordinary,
    IntoFunction,
    OutOfFunction,
};

pub const VerbatimBytecode = struct {
    arguments: usize,
    return_variables: usize,
    /// Allocator-owned bytes.
    data: []u8,
};

pub const AssemblyItemError = std.mem.Allocator.Error || error{
    InvalidItem,
    InvalidInstruction,
    InvalidItemType,
    InvalidTag,
    ForeignTag,
    TagAlreadyHasSubassembly,
    MissingImmutableOccurrences,
    MissingSubPathDecoder,
    Overflow,
};

pub const SourceIndex = struct {
    source_name: []const u8,
    index: u32,
};

pub const OwnedNameAndData = struct {
    name: []u8,
    data: []u8,

    pub fn deinit(self: *OwnedNameAndData, allocator: std.mem.Allocator) void {
        allocator.free(self.data);
        allocator.free(self.name);
        self.* = undefined;
    }
};

pub const AssemblyTextContext = struct {
    evm_version: EVMVersion,
    context: ?*const anyopaque = null,
    decode_sub_path: ?*const fn (
        context: ?*const anyopaque,
        allocator: std.mem.Allocator,
        id: SubAssemblyID,
    ) AssemblyItemError![]SubAssemblyID = null,
};

pub const AssemblyItem = struct {
    item_type: AssemblyItemType,
    instruction_value: ?InstructionModule.Instruction = null,
    data_value: u256 = 0,
    verbatim: ?VerbatimBytecode = null,
    debug_data: DebugData = .{},
    jump_type: JumpType = .Ordinary,
    pushed_value: ?u256 = null,
    immutable_occurrences: ?usize = null,
    modifier_depth: usize = 0,

    pub fn initPush(value: u256, debug_data: DebugData) AssemblyItem {
        return initType(.Push, value, debug_data);
    }

    pub fn initInstruction(
        opcode: InstructionModule.Instruction,
        debug_data: DebugData,
    ) AssemblyItem {
        return .{
            .item_type = .Operation,
            .instruction_value = opcode,
            .debug_data = debug_data,
        };
    }

    pub fn initType(
        item_type: AssemblyItemType,
        value: u256,
        debug_data: DebugData,
    ) AssemblyItem {
        return if (item_type == .Operation)
            initInstruction(@enumFromInt(@as(u8, @truncate(value))), debug_data)
        else
            .{
                .item_type = item_type,
                .data_value = value,
                .debug_data = debug_data,
            };
    }

    pub fn initTypedInstruction(
        item_type: AssemblyItemType,
        opcode: InstructionModule.Instruction,
        value: u256,
        debug_data: DebugData,
    ) AssemblyItem {
        return .{
            .item_type = item_type,
            .instruction_value = opcode,
            .data_value = value,
            .debug_data = debug_data,
        };
    }

    pub fn initVerbatim(
        allocator: std.mem.Allocator,
        bytes: []const u8,
        argument_count: usize,
        return_variables: usize,
    ) std.mem.Allocator.Error!AssemblyItem {
        return .{
            .item_type = .VerbatimBytecode,
            .verbatim = .{
                .arguments = argument_count,
                .return_variables = return_variables,
                .data = try allocator.dupe(u8, bytes),
            },
        };
    }

    pub fn deinit(self: *AssemblyItem, allocator: std.mem.Allocator) void {
        if (self.verbatim) |verbatim| allocator.free(verbatim.data);
        self.* = undefined;
    }

    pub fn clone(self: *const AssemblyItem, allocator: std.mem.Allocator) std.mem.Allocator.Error!AssemblyItem {
        var result = self.*;
        if (self.verbatim) |verbatim| {
            result.verbatim = .{
                .arguments = verbatim.arguments,
                .return_variables = verbatim.return_variables,
                .data = try allocator.dupe(u8, verbatim.data),
            };
        }
        return result;
    }

    pub fn typeOf(self: *const AssemblyItem) AssemblyItemType {
        return self.item_type;
    }

    pub fn data(self: *const AssemblyItem) error{InvalidItemType}!u256 {
        if (self.item_type == .Operation or self.item_type == .VerbatimBytecode) {
            return error.InvalidItemType;
        }
        return self.data_value;
    }

    pub fn setData(self: *AssemblyItem, value: u256) error{InvalidItemType}!void {
        if (self.item_type == .Operation) return error.InvalidItemType;
        self.data_value = value;
    }

    pub fn hasInstruction(self: *const AssemblyItem) bool {
        const should_have_instruction = self.item_type == .Operation;
        std.debug.assert(should_have_instruction == (self.instruction_value != null));
        return should_have_instruction;
    }

    pub fn instruction(self: *const AssemblyItem) error{InvalidItemType}!InstructionModule.Instruction {
        if (!self.hasInstruction()) return error.InvalidItemType;
        return self.instruction_value.?;
    }

    pub fn verbatimData(self: *const AssemblyItem) error{InvalidItemType}![]const u8 {
        if (self.item_type != .VerbatimBytecode or self.verbatim == null) return error.InvalidItemType;
        return self.verbatim.?.data;
    }

    pub fn tag(self: *const AssemblyItem) error{InvalidTag}!AssemblyItem {
        if (self.item_type != .PushTag and self.item_type != .Tag) return error.InvalidTag;
        return initType(.Tag, self.data_value, .{});
    }

    pub fn pushTag(self: *const AssemblyItem) error{InvalidTag}!AssemblyItem {
        if (self.item_type != .PushTag and self.item_type != .Tag) return error.InvalidTag;
        return initType(.PushTag, self.data_value, .{});
    }

    pub fn toSubAssemblyTag(
        self: *const AssemblyItem,
        sub_id: SubAssemblyID,
    ) error{ InvalidTag, TagAlreadyHasSubassembly }!AssemblyItem {
        if (self.item_type != .PushTag and self.item_type != .Tag) return error.InvalidTag;
        if (self.data_value >= (@as(u256, 1) << 64)) return error.TagAlreadyHasSubassembly;
        var result = self.*;
        result.item_type = .PushTag;
        try result.setPushTagSubIdAndTag(sub_id, @truncate(self.data_value));
        return result;
    }

    pub fn splitForeignPushTag(
        self: *const AssemblyItem,
    ) error{InvalidTag}!struct { SubAssemblyID, usize } {
        if (self.item_type != .PushTag and self.item_type != .Tag) return error.InvalidTag;
        const shifted = self.data_value >> 64;
        const sub_id = SubAssemblyID.init(@truncate(shifted -% 1));
        const tag_id: usize = @intCast(@as(u64, @truncate(self.data_value)));
        return .{ sub_id, tag_id };
    }

    pub fn relativeJumpTagID(self: *const AssemblyItem) error{ InvalidTag, ForeignTag }!usize {
        const split = try self.splitForeignPushTag();
        if (!split[0].empty()) return error.ForeignTag;
        return split[1];
    }

    pub fn setPushTagSubIdAndTag(
        self: *AssemblyItem,
        sub_id: SubAssemblyID,
        tag_id: usize,
    ) error{InvalidTag}!void {
        if (self.item_type != .PushTag and self.item_type != .Tag) return error.InvalidTag;
        var combined: u256 = @as(u64, @truncate(tag_id));
        if (!sub_id.empty()) combined |= (@as(u256, sub_id.value) + 1) << 64;
        self.data_value = combined;
    }

    pub fn nameAndDataAlloc(
        self: *const AssemblyItem,
        allocator: std.mem.Allocator,
        evm_version: EVMVersion,
    ) AssemblyItemError!OwnedNameAndData {
        return switch (self.item_type) {
            .Operation => makeNameAndData(
                allocator,
                InstructionModule.instructionInfo(try self.instruction(), evm_version).name,
                "",
            ),
            .Push => makeOwnedNameAndData(allocator, "PUSH", try uppercaseHexAlloc(allocator, self.data_value)),
            .PushTag => if (self.data_value == 0)
                makeNameAndData(allocator, "PUSH [ErrorTag]", "")
            else
                makeOwnedNameAndData(
                    allocator,
                    "PUSH [tag]",
                    try std.fmt.allocPrint(allocator, "{d}", .{self.data_value}),
                ),
            .PushSub => makeOwnedNameAndData(allocator, "PUSH [$]", try fullHex256Alloc(allocator, self.data_value)),
            .PushSubSize => makeOwnedNameAndData(allocator, "PUSH #[$]", try fullHex256Alloc(allocator, self.data_value)),
            .PushProgramSize => makeNameAndData(allocator, "PUSHSIZE", ""),
            .PushLibraryAddress => makeOwnedNameAndData(allocator, "PUSHLIB", try fullHex256Alloc(allocator, self.data_value)),
            .PushDeployTimeAddress => makeNameAndData(allocator, "PUSHDEPLOYADDRESS", ""),
            .PushImmutable => makeOwnedNameAndData(allocator, "PUSHIMMUTABLE", try fullHex256Alloc(allocator, self.data_value)),
            .AssignImmutable => makeOwnedNameAndData(allocator, "ASSIGNIMMUTABLE", try fullHex256Alloc(allocator, self.data_value)),
            .Tag => makeOwnedNameAndData(
                allocator,
                "tag",
                try std.fmt.allocPrint(allocator, "{d}", .{self.data_value}),
            ),
            .PushData => makeOwnedNameAndData(allocator, "PUSH data", try uppercaseHexAlloc(allocator, self.data_value)),
            .VerbatimBytecode => makeOwnedNameAndData(
                allocator,
                "VERBATIM",
                try CommonData.toHexAlloc(allocator, try self.verbatimData(), .dont_add, .lower),
            ),
            .UndefinedItem => error.InvalidItem,
        };
    }

    pub fn bytesRequired(
        self: *const AssemblyItem,
        address_length: usize,
        evm_version: EVMVersion,
        precision: Precision,
    ) error{ MissingImmutableOccurrences, InvalidItem }!usize {
        return switch (self.item_type) {
            .Operation, .Tag => 1,
            .Push => 1 + @max(
                @as(usize, if (evm_version.hasPush0()) 0 else 1),
                Numeric.numberEncodingSize(u256, self.data_value),
            ),
            .PushSubSize, .PushProgramSize => 5,
            .PushTag, .PushData, .PushSub => 1 + address_length,
            .PushLibraryAddress, .PushDeployTimeAddress => 21,
            .PushImmutable => 33,
            .AssignImmutable => blk: {
                const occurrences = if (precision == .Approximate)
                    1
                else
                    self.immutable_occurrences orelse return error.MissingImmutableOccurrences;
                break :blk if (occurrences != 0)
                    (occurrences - 1) * 37 + 35
                else
                    2;
            },
            .VerbatimBytecode => if (self.verbatim) |verbatim| verbatim.data.len else error.InvalidItem,
            .UndefinedItem => error.InvalidItem,
        };
    }

    pub fn arguments(self: *const AssemblyItem) usize {
        if (self.hasInstruction()) {
            return InstructionModule.instructionInfo(self.instruction_value.?, EVMVersion.current()).args;
        }
        return switch (self.item_type) {
            .VerbatimBytecode => if (self.verbatim) |verbatim| verbatim.arguments else 0,
            .AssignImmutable => 2,
            else => 0,
        };
    }

    pub fn returnValues(self: *const AssemblyItem) usize {
        return switch (self.item_type) {
            .Operation => InstructionModule.instructionInfo(self.instruction_value.?, EVMVersion.current()).ret,
            .Push,
            .PushTag,
            .PushData,
            .PushSub,
            .PushSubSize,
            .PushProgramSize,
            .PushLibraryAddress,
            .PushImmutable,
            .PushDeployTimeAddress,
            => 1,
            .VerbatimBytecode => if (self.verbatim) |verbatim| verbatim.return_variables else 0,
            .Tag, .AssignImmutable, .UndefinedItem => 0,
        };
    }

    pub fn restoreVerbatimArity(
        self: *AssemblyItem,
        argument_count: usize,
        return_count: usize,
    ) error{InvalidItem}!void {
        const verbatim = if (self.verbatim) |*value| value else return error.InvalidItem;
        if (self.item_type != .VerbatimBytecode) return error.InvalidItem;
        verbatim.arguments = argument_count;
        verbatim.return_variables = return_count;
    }

    /// The original returns wrapped `size_t` and immediately casts it to an
    /// integer. The Zig API exposes the intended signed stack delta directly.
    pub fn deposit(self: *const AssemblyItem) isize {
        return @as(isize, @intCast(self.returnValues())) - @as(isize, @intCast(self.arguments()));
    }

    pub fn canBeFunctional(self: *const AssemblyItem) bool {
        if (self.jump_type != .Ordinary) return false;
        return switch (self.item_type) {
            .Operation => !InstructionModule.isDupInstruction(self.instruction_value.?) and
                !InstructionModule.isSwapInstruction(self.instruction_value.?),
            .Push,
            .PushTag,
            .PushData,
            .PushSub,
            .PushSubSize,
            .PushProgramSize,
            .PushLibraryAddress,
            .PushDeployTimeAddress,
            .PushImmutable,
            => true,
            .Tag, .AssignImmutable, .VerbatimBytecode, .UndefinedItem => false,
        };
    }

    pub fn setLocation(self: *AssemblyItem, source_location: SourceLocation) void {
        self.debug_data.native_location = source_location;
    }

    pub fn location(self: *const AssemblyItem) *const SourceLocation {
        return &self.debug_data.native_location;
    }

    pub fn setDebugData(self: *AssemblyItem, debug_data: DebugData) void {
        self.debug_data = debug_data;
    }

    pub fn debugData(self: *const AssemblyItem) *const DebugData {
        return &self.debug_data;
    }

    pub fn setJumpType(self: *AssemblyItem, jump_type: JumpType) void {
        self.jump_type = jump_type;
    }

    pub fn getJumpType(self: *const AssemblyItem) JumpType {
        return self.jump_type;
    }

    pub fn parseJumpType(text: []const u8) ?JumpType {
        if (std.mem.eql(u8, text, "[in]")) return .IntoFunction;
        if (std.mem.eql(u8, text, "[out]")) return .OutOfFunction;
        if (text.len == 0) return .Ordinary;
        return null;
    }

    pub fn getJumpTypeAsString(self: *const AssemblyItem) []const u8 {
        return switch (self.jump_type) {
            .IntoFunction => "[in]",
            .OutOfFunction => "[out]",
            .Ordinary => "",
        };
    }

    pub fn setPushedValue(self: *AssemblyItem, value: u256) void {
        self.pushed_value = value;
    }

    pub fn pushedValue(self: *const AssemblyItem) ?*const u256 {
        return if (self.pushed_value != null) &self.pushed_value.? else null;
    }

    pub fn setImmutableOccurrences(self: *AssemblyItem, count: usize) void {
        self.immutable_occurrences = count;
    }

    pub fn immutableOccurrences(self: *const AssemblyItem) ?usize {
        return self.immutable_occurrences;
    }

    pub fn eql(self: *const AssemblyItem, other: *const AssemblyItem) bool {
        if (self.item_type != other.item_type) return false;
        return switch (self.item_type) {
            .Operation => self.instruction_value == other.instruction_value,
            .VerbatimBytecode => if (self.verbatim) |left|
                if (other.verbatim) |right|
                    left.arguments == right.arguments and
                        left.return_variables == right.return_variables and
                        std.mem.eql(u8, left.data, right.data)
                else
                    false
            else
                other.verbatim == null,
            else => self.data_value == other.data_value,
        };
    }

    pub fn eqlInstruction(self: *const AssemblyItem, instruction_value: InstructionModule.Instruction) bool {
        return self.hasInstruction() and self.instruction_value.? == instruction_value;
    }

    pub fn lessThan(self: *const AssemblyItem, other: *const AssemblyItem) bool {
        if (self.item_type != other.item_type) return @intFromEnum(self.item_type) < @intFromEnum(other.item_type);
        return switch (self.item_type) {
            .Operation => @intFromEnum(self.instruction_value.?) < @intFromEnum(other.instruction_value.?),
            .VerbatimBytecode => compareVerbatim(self.verbatim, other.verbatim),
            else => self.data_value < other.data_value,
        };
    }

    pub fn toAssemblyTextAlloc(
        self: *const AssemblyItem,
        allocator: std.mem.Allocator,
        context: AssemblyTextContext,
    ) AssemblyItemError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(allocator);
        switch (self.item_type) {
            .Operation => {
                const opcode = try self.instruction();
                if (!InstructionModule.isValidInstruction(opcode)) return error.InvalidInstruction;
                const name = InstructionModule.instructionInfo(opcode, context.evm_version).name;
                for (name) |character| try output.append(allocator, std.ascii.toLower(character));
            },
            .Push => {
                const encoded = try Numeric.toCompactBigEndianAlloc(u256, allocator, self.data_value, 1);
                defer allocator.free(encoded);
                const text = try CommonData.toHexAlloc(allocator, encoded, .add, .lower);
                defer allocator.free(text);
                try output.appendSlice(allocator, text);
            },
            .PushTag => {
                const split = try self.splitForeignPushTag();
                if (split[0].empty()) {
                    try appendFormat(allocator, &output, "tag_{d}", .{split[1]});
                } else {
                    try appendFormat(allocator, &output, "tag_{d}_{d}", .{ split[0].value, split[1] });
                }
            },
            .Tag => {
                if (self.data_value >= 0x10000) return error.InvalidTag;
                try appendFormat(allocator, &output, "tag_{d}:", .{self.data_value});
            },
            .PushData => {
                try output.appendSlice(allocator, "data_");
                const hex = try fullHex256Alloc(allocator, self.data_value);
                defer allocator.free(hex);
                try output.appendSlice(allocator, hex);
            },
            .PushSub, .PushSubSize => {
                const decoder = context.decode_sub_path orelse return error.MissingSubPathDecoder;
                const path = try decoder(context.context, allocator, try SubAssemblyID.fromU256(self.data_value));
                defer allocator.free(path);
                try output.appendSlice(allocator, if (self.item_type == .PushSub) "dataOffset(" else "dataSize(");
                for (path, 0..) |component, index| {
                    if (index != 0) try output.append(allocator, '.');
                    try appendFormat(allocator, &output, "sub_{d}", .{component.value});
                }
                try output.append(allocator, ')');
            },
            .PushProgramSize => try output.appendSlice(allocator, "bytecodeSize"),
            .PushLibraryAddress => {
                const hex = try fullHex256Alloc(allocator, self.data_value);
                defer allocator.free(hex);
                try appendFormat(allocator, &output, "linkerSymbol(\"{s}\")", .{hex});
            },
            .PushDeployTimeAddress => try output.appendSlice(allocator, "deployTimeAddress()"),
            .PushImmutable, .AssignImmutable => {
                const encoded = try Numeric.toCompactBigEndianAlloc(u256, allocator, self.data_value, 1);
                defer allocator.free(encoded);
                const hex = try CommonData.toHexAlloc(allocator, encoded, .dont_add, .lower);
                defer allocator.free(hex);
                if (self.item_type == .PushImmutable)
                    try appendFormat(allocator, &output, "immutable(\"0x{s}\")", .{hex})
                else
                    try appendFormat(allocator, &output, "assignImmutable(\"0x{s}\")", .{hex});
            },
            .VerbatimBytecode => {
                const hex = try CommonData.toHexAlloc(allocator, try self.verbatimData(), .dont_add, .lower);
                defer allocator.free(hex);
                try appendFormat(allocator, &output, "verbatimbytecode_{s}", .{hex});
            },
            .UndefinedItem => return error.InvalidItem,
        }
        if (self.jump_type == .IntoFunction) {
            try output.appendSlice(allocator, "\t// in");
        } else if (self.jump_type == .OutOfFunction) {
            try output.appendSlice(allocator, "\t// out");
        }
        return output.toOwnedSlice(allocator);
    }

    pub fn renderAlloc(self: *const AssemblyItem, allocator: std.mem.Allocator) AssemblyItemError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(allocator);
        switch (self.item_type) {
            .Operation => {
                const name = InstructionModule.instructionInfo(try self.instruction(), EVMVersion.current()).name;
                try appendFormat(allocator, &output, " {s}", .{name});
                if (self.instruction_value.? == .JUMP or self.instruction_value.? == .JUMPI) {
                    try appendFormat(allocator, &output, "\t{s}", .{self.getJumpTypeAsString()});
                }
            },
            .Push => try appendFormat(allocator, &output, " PUSH {x}", .{self.data_value}),
            .PushTag => {
                const split = try self.splitForeignPushTag();
                if (split[0].empty()) {
                    try appendFormat(allocator, &output, " PushTag {d}", .{split[1]});
                } else {
                    try appendFormat(allocator, &output, " PushTag {d}:{d}", .{ split[0].value, split[1] });
                }
            },
            .Tag => try appendFormat(allocator, &output, " Tag {d}", .{self.data_value}),
            .PushData => try appendFormat(allocator, &output, " PushData {x}", .{@as(u32, @truncate(self.data_value))}),
            .PushSub => try appendFormat(allocator, &output, " PushSub {x}", .{@as(usize, @truncate(self.data_value))}),
            .PushSubSize => try appendFormat(allocator, &output, " PushSubSize {x}", .{@as(usize, @truncate(self.data_value))}),
            .PushProgramSize => try output.appendSlice(allocator, " PushProgramSize"),
            .PushLibraryAddress => {
                const hash = try fullHex256Alloc(allocator, self.data_value);
                defer allocator.free(hash);
                try appendFormat(allocator, &output, " PushLibraryAddress {s}...{s}", .{ hash[0..8], hash[56..64] });
            },
            .PushDeployTimeAddress => try output.appendSlice(allocator, " PushDeployTimeAddress"),
            .PushImmutable => try output.appendSlice(allocator, " PushImmutable"),
            .AssignImmutable => try output.appendSlice(allocator, " AssignImmutable"),
            .VerbatimBytecode => {
                const hex = try CommonData.toHexAlloc(allocator, try self.verbatimData(), .dont_add, .lower);
                defer allocator.free(hex);
                try appendFormat(allocator, &output, " Verbatim {s}", .{hex});
            },
            .UndefinedItem => try output.appendSlice(allocator, " ???"),
        }
        return output.toOwnedSlice(allocator);
    }

    fn opcodeCount(self: *const AssemblyItem) error{MissingImmutableOccurrences}!usize {
        if (self.item_type != .AssignImmutable) return 1;
        const occurrences = self.immutable_occurrences orelse return error.MissingImmutableOccurrences;
        return if (occurrences != 0) (occurrences - 1) * 5 + 3 else 2;
    }
};

pub fn bytesRequired(
    items: []const AssemblyItem,
    address_length: usize,
    evm_version: EVMVersion,
    precision: Precision,
) error{ MissingImmutableOccurrences, InvalidItem }!usize {
    var size: usize = 0;
    for (items) |*item| size += try item.bytesRequired(address_length, evm_version, precision);
    return size;
}

pub fn computeSourceMappingAlloc(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    source_indices: []const SourceIndex,
) (std.mem.Allocator.Error || error{MissingImmutableOccurrences})![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var previous_start: i32 = -1;
    var previous_length: i32 = -1;
    var previous_source_index: i32 = -1;
    var previous_modifier_depth: i32 = -1;
    var previous_jump: u8 = 0;

    for (items) |*item| {
        if (output.items.len != 0) try output.append(allocator, ';');
        const location = item.location().*;
        const length = if (location.start != -1 and location.end != -1)
            location.end - location.start
        else
            -1;
        const source_index = findSourceIndex(source_indices, location.source_name);
        const jump: u8 = switch (item.jump_type) {
            .IntoFunction => 'i',
            .OutOfFunction => 'o',
            .Ordinary => '-',
        };
        const modifier_depth: i32 = @intCast(item.modifier_depth);

        var components: u8 = 5;
        if (modifier_depth == previous_modifier_depth) {
            components -= 1;
            if (jump == previous_jump) {
                components -= 1;
                if (source_index == previous_source_index) {
                    components -= 1;
                    if (length == previous_length) {
                        components -= 1;
                        if (location.start == previous_start) components -= 1;
                    }
                }
            }
        }

        if (takeComponent(&components)) {
            if (location.start != previous_start) try appendFormat(allocator, &output, "{d}", .{location.start});
            if (takeComponent(&components)) {
                try output.append(allocator, ':');
                if (length != previous_length) try appendFormat(allocator, &output, "{d}", .{length});
                if (takeComponent(&components)) {
                    try output.append(allocator, ':');
                    if (source_index != previous_source_index) try appendFormat(allocator, &output, "{d}", .{source_index});
                    if (takeComponent(&components)) {
                        try output.append(allocator, ':');
                        if (jump != previous_jump) try output.append(allocator, jump);
                        if (takeComponent(&components)) {
                            try output.append(allocator, ':');
                            if (modifier_depth != previous_modifier_depth) try appendFormat(allocator, &output, "{d}", .{modifier_depth});
                        }
                    }
                }
            }
        }

        const opcode_count = try item.opcodeCount();
        if (opcode_count > 1) try output.appendNTimes(allocator, ';', opcode_count - 1);
        previous_start = location.start;
        previous_length = length;
        previous_source_index = source_index;
        previous_jump = jump;
        previous_modifier_depth = modifier_depth;
    }
    return output.toOwnedSlice(allocator);
}

fn makeNameAndData(
    allocator: std.mem.Allocator,
    name: []const u8,
    data: []const u8,
) std.mem.Allocator.Error!OwnedNameAndData {
    const owned_name = try allocator.dupe(u8, name);
    errdefer allocator.free(owned_name);
    return .{ .name = owned_name, .data = try allocator.dupe(u8, data) };
}

/// Takes ownership of `data` on entry, including on allocation failure.
fn makeOwnedNameAndData(
    allocator: std.mem.Allocator,
    name: []const u8,
    data: []u8,
) std.mem.Allocator.Error!OwnedNameAndData {
    errdefer allocator.free(data);
    return .{ .name = try allocator.dupe(u8, name), .data = data };
}

fn uppercaseHexAlloc(allocator: std.mem.Allocator, value: u256) std.mem.Allocator.Error![]u8 {
    return std.fmt.allocPrint(allocator, "{X}", .{value});
}

fn fullHex256Alloc(allocator: std.mem.Allocator, value: u256) std.mem.Allocator.Error![]u8 {
    const bytes = Numeric.toBigEndian256(value);
    return CommonData.toHexAlloc(allocator, &bytes, .dont_add, .lower);
}

fn appendFormat(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    comptime format: []const u8,
    args: anytype,
) std.mem.Allocator.Error!void {
    const formatted = try std.fmt.allocPrint(allocator, format, args);
    defer allocator.free(formatted);
    try output.appendSlice(allocator, formatted);
}

fn compareVerbatim(lhs: ?VerbatimBytecode, rhs: ?VerbatimBytecode) bool {
    if (lhs == null or rhs == null) return lhs == null and rhs != null;
    const left = lhs.?;
    const right = rhs.?;
    if (left.arguments != right.arguments) return left.arguments < right.arguments;
    if (left.return_variables != right.return_variables) return left.return_variables < right.return_variables;
    return std.mem.order(u8, left.data, right.data) == .lt;
}

fn findSourceIndex(source_indices: []const SourceIndex, source_name: ?[]const u8) i32 {
    const name = source_name orelse return -1;
    for (source_indices) |entry| {
        if (std.mem.eql(u8, entry.source_name, name)) return @intCast(entry.index);
    }
    return -1;
}

fn takeComponent(components: *u8) bool {
    if (components.* == 0) return false;
    components.* -= 1;
    return true;
}

test "tag packing preserves the root sentinel and foreign subassembly path" {
    var tag_item = AssemblyItem.initType(.Tag, 7, .{});
    const local = try tag_item.pushTag();
    const local_split = try local.splitForeignPushTag();
    try std.testing.expect(local_split[0].empty());
    try std.testing.expectEqual(@as(usize, 7), local_split[1]);

    const foreign = try tag_item.toSubAssemblyTag(SubAssemblyID.init(12));
    const foreign_split = try foreign.splitForeignPushTag();
    try std.testing.expectEqual(@as(u64, 12), foreign_split[0].value);
    try std.testing.expectEqual(@as(usize, 7), foreign_split[1]);
    try std.testing.expectError(error.ForeignTag, foreign.relativeJumpTagID());
}

test "item sizes and stack effects match EVM encoding rules" {
    const london = EVMVersion.init(.London);
    const shanghai = EVMVersion.init(.Shanghai);
    const zero = AssemblyItem.initPush(0, .{});
    try std.testing.expectEqual(@as(usize, 2), try zero.bytesRequired(2, london, .Precise));
    try std.testing.expectEqual(@as(usize, 1), try zero.bytesRequired(2, shanghai, .Precise));

    const add = AssemblyItem.initInstruction(.ADD, .{});
    try std.testing.expectEqual(@as(isize, -1), add.deposit());
    const duplicate = AssemblyItem.initInstruction(.DUP16, .{});
    try std.testing.expectEqual(@as(isize, 1), duplicate.deposit());
    try std.testing.expect(!duplicate.canBeFunctional());
}

test "verbatim bytes have explicit deep-copy ownership" {
    var original = try AssemblyItem.initVerbatim(std.testing.allocator, &.{ 1, 2, 3 }, 2, 1);
    defer original.deinit(std.testing.allocator);
    var cloned = try original.clone(std.testing.allocator);
    defer cloned.deinit(std.testing.allocator);
    cloned.verbatim.?.data[0] = 0xff;
    try std.testing.expectEqual(@as(u8, 1), original.verbatim.?.data[0]);
    try std.testing.expectEqual(@as(isize, -1), cloned.deposit());
}

test "source mappings preserve component elision and expanded immutable opcodes" {
    var items = [_]AssemblyItem{
        AssemblyItem.initInstruction(.ADD, .{
            .native_location = .{ .start = 1, .end = 3, .source_name = "a.sol" },
        }),
        AssemblyItem.initInstruction(.MUL, .{
            .native_location = .{ .start = 1, .end = 3, .source_name = "a.sol" },
        }),
        AssemblyItem.initType(.AssignImmutable, 0, .{
            .native_location = .{ .start = 4, .end = 9, .source_name = "a.sol" },
        }),
    };
    items[2].setImmutableOccurrences(2);
    const mapping = try computeSourceMappingAlloc(
        std.testing.allocator,
        &items,
        &.{.{ .source_name = "a.sol", .index = 0 }},
    );
    defer std.testing.allocator.free(mapping);
    try std.testing.expectEqualStrings("1:2:0:-:0;;4:5;;;;;;;", mapping);
}
