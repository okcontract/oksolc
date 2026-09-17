// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Version-independent inventory and code-generation behavior of EVM Yul builtins.

const std = @import("std");
const AST = @import("../../ast.zig");
const AbstractAssemblyModule = @import("abstract_assembly.zig");
const AbstractAssembly = AbstractAssemblyModule.AbstractAssembly;
const ControlFlowSideEffects = @import("../../control_flow_side_effects.zig").ControlFlowSideEffects;
const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
const InstructionModule = @import("../../../libevmasm/instruction.zig");
const Instruction = InstructionModule.Instruction;
const Object = @import("../../object.zig").Object;
const Scope = @import("../../scope.zig");
const SemanticInformation = @import("../../../libevmasm/semantic_information.zig");
const SideEffectsModule = @import("../../side_effects.zig");
const SideEffects = SideEffectsModule.SideEffects;

pub const BuiltinContext = struct {
    allocator: std.mem.Allocator,
    current_object: ?*const Object = null,
    sub_ids: std.StringHashMap(AbstractAssemblyModule.SubID),
    function_ids: std.AutoHashMap(*const Scope.Function, AbstractAssemblyModule.FunctionID),

    pub fn init(allocator: std.mem.Allocator) BuiltinContext {
        return .{
            .allocator = allocator,
            .sub_ids = std.StringHashMap(AbstractAssemblyModule.SubID).init(allocator),
            .function_ids = std.AutoHashMap(
                *const Scope.Function,
                AbstractAssemblyModule.FunctionID,
            ).init(allocator),
        };
    }

    pub fn deinit(self: *BuiltinContext) void {
        var keys = self.sub_ids.keyIterator();
        while (keys.next()) |key| self.allocator.free(key.*);
        self.sub_ids.deinit();
        self.function_ids.deinit();
        self.* = undefined;
    }

    pub fn putSubId(
        self: *BuiltinContext,
        name: []const u8,
        sub_id: AbstractAssemblyModule.SubID,
    ) std.mem.Allocator.Error!void {
        if (self.sub_ids.getPtr(name)) |value| {
            value.* = sub_id;
            return;
        }
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);
        try self.sub_ids.put(owned_name, sub_id);
    }
};

pub const CodegenKind = union(enum) {
    instruction: Instruction,
    linker_symbol,
    memory_guard,
    data_size,
    data_offset,
    data_copy,
    set_immutable,
    load_immutable,
    verbatim: struct { arguments: usize, return_variables: usize },
};

pub const BuiltinFunctionForEVM = struct {
    base: AST.BuiltinFunction,
    instruction: ?Instruction = null,
    codegen: CodegenKind,

    pub fn deinit(self: *BuiltinFunctionForEVM, allocator: std.mem.Allocator) void {
        allocator.free(self.base.name);
        allocator.free(self.base.literal_arguments);
        self.* = undefined;
    }

    pub fn generateCode(
        self: *const BuiltinFunctionForEVM,
        call: *const AST.FunctionCall,
        assembly: AbstractAssembly,
        context: *BuiltinContext,
    ) AbstractAssemblyModule.AssemblyError!void {
        if (call.arguments.items.len != self.base.num_parameters)
            return error.InvalidBuiltinCall;
        switch (self.codegen) {
            .instruction => |instruction| try assembly.appendInstruction(instruction),
            .linker_symbol => {
                const value = try literalTextAlloc(context.allocator, try literalArgument(call, 0));
                defer context.allocator.free(value);
                try assembly.appendLinkerSymbol(value);
            },
            .memory_guard => {
                const literal = try literalArgument(call, 0);
                try assembly.appendConstant(literal.value.value() catch return error.InvalidBuiltinCall);
            },
            .data_size => {
                const object = context.current_object orelse return error.MissingCurrentObject;
                const name = try literalTextAlloc(context.allocator, try literalArgument(call, 0));
                defer context.allocator.free(name);
                if (std.mem.eql(u8, object.name, name)) {
                    try assembly.appendAssemblySize();
                } else if (context.sub_ids.get(name)) |sub_id| {
                    try assembly.appendDataSize(&.{sub_id});
                } else {
                    const path = try object.pathToSubObject(name);
                    defer object.allocator.free(path);
                    if (path.len == 0) return error.MissingSubObject;
                    try assembly.appendDataSize(path);
                }
            },
            .data_offset => {
                const object = context.current_object orelse return error.MissingCurrentObject;
                const name = try literalTextAlloc(context.allocator, try literalArgument(call, 0));
                defer context.allocator.free(name);
                if (std.mem.eql(u8, object.name, name)) {
                    try assembly.appendConstant(0);
                } else if (context.sub_ids.get(name)) |sub_id| {
                    try assembly.appendDataOffset(&.{sub_id});
                } else {
                    const path = try object.pathToSubObject(name);
                    defer object.allocator.free(path);
                    if (path.len == 0) return error.MissingSubObject;
                    try assembly.appendDataOffset(path);
                }
            },
            .data_copy => try assembly.appendInstruction(.CODECOPY),
            .set_immutable => {
                const identifier = try literalTextAlloc(context.allocator, try literalArgument(call, 1));
                defer context.allocator.free(identifier);
                try assembly.appendImmutableAssignment(identifier);
            },
            .load_immutable => {
                const identifier = try literalTextAlloc(context.allocator, try literalArgument(call, 0));
                defer context.allocator.free(identifier);
                try assembly.appendImmutable(identifier);
            },
            .verbatim => |shape| {
                const bytecode = try literalTextAlloc(context.allocator, try literalArgument(call, 0));
                defer context.allocator.free(bytecode);
                try assembly.appendVerbatim(bytecode, shape.arguments, shape.return_variables);
            },
        }
    }
};

pub const Scopes = struct {
    const instruction_bit: u3 = 1 << 0;
    const replaced_bit: u3 = 1 << 1;
    const object_access_bit: u3 = 1 << 2;

    value: u3 = 0,

    pub fn instruction(self: Scopes) bool {
        return self.value & instruction_bit != 0;
    }

    pub fn replaced(self: Scopes) bool {
        return self.value & replaced_bit != 0;
    }

    pub fn requiresObjectAccess(self: Scopes) bool {
        return self.value & object_access_bit != 0;
    }

    pub fn combine(self: Scopes, other: Scopes) Scopes {
        return .{ .value = self.value | other.value };
    }

    pub fn instructionScope() Scopes {
        return .{ .value = instruction_bit };
    }

    pub fn replacedScope() Scopes {
        return .{ .value = replaced_bit };
    }

    pub fn objectAccessScope() Scopes {
        return .{ .value = object_access_bit };
    }
};

pub const Entry = struct {
    scopes: Scopes,
    builtin: BuiltinFunctionForEVM,
};

pub const EVMBuiltins = struct {
    allocator: std.mem.Allocator,
    entries: std.ArrayList(Entry) = .empty,

    pub fn init(allocator: std.mem.Allocator) !EVMBuiltins {
        var result: EVMBuiltins = .{ .allocator = allocator };
        errdefer result.deinit();

        const Candidate = struct { name: []const u8, instruction: Instruction };
        var candidates: std.ArrayList(Candidate) = .empty;
        defer candidates.deinit(allocator);
        inline for (std.meta.fields(Instruction)) |field| {
            try candidates.append(allocator, .{
                .name = field.name,
                .instruction = @enumFromInt(field.value),
            });
        }
        try candidates.append(allocator, .{ .name = "DIFFICULTY", .instruction = .PREVRANDAO });
        std.sort.insertion(Candidate, candidates.items, {}, struct {
            fn lessThan(_: void, left: Candidate, right: Candidate) bool {
                return std.mem.order(u8, left.name, right.name) == .lt;
            }
        }.lessThan);

        for (candidates.items) |candidate| {
            if (InstructionModule.isSwapInstruction(candidate.instruction) or
                InstructionModule.isDupInstruction(candidate.instruction)) continue;
            const version = if (candidate.instruction == .PREVRANDAO and
                std.mem.eql(u8, candidate.name, "DIFFICULTY"))
                EVMVersion.init(.London)
            else
                EVMVersion.current();
            try result.entries.append(allocator, .{
                .scopes = Scopes.instructionScope(),
                .builtin = try instructionBuiltin(
                    allocator,
                    candidate.name,
                    candidate.instruction,
                    version,
                ),
            });
        }

        try result.appendCustom("linkersymbol", 1, 1, .{}, .{}, &.{.String}, .linker_symbol);
        try result.appendCustom("memoryguard", 1, 1, .{}, .{}, &.{.Number}, .memory_guard);
        try result.appendCustom("datasize", 1, 1, .{}, .{}, &.{.String}, .data_size);
        try result.appendCustom("dataoffset", 1, 1, .{}, .{}, &.{.String}, .data_offset);
        try result.appendCustom(
            "datacopy",
            3,
            0,
            try computeSideEffectsOfInstruction(.CODECOPY),
            ControlFlowSideEffects.fromInstruction(.CODECOPY),
            &.{},
            .data_copy,
        );
        try result.appendCustom(
            "setimmutable",
            3,
            0,
            .{
                .movable = false,
                .movable_apart_from_effects = false,
                .can_be_removed = false,
                .can_be_removed_if_no_msize = false,
                .memory = .write,
            },
            .{},
            &.{ null, .String, null },
            .set_immutable,
        );
        try result.appendCustom("loadimmutable", 1, 1, .{}, .{}, &.{.String}, .load_immutable);

        for (result.entries.items) |entry| {
            if (std.mem.startsWith(u8, entry.builtin.base.name, "verbatim_"))
                return error.ReservedVerbatimPrefix;
        }
        return result;
    }

    pub fn deinit(self: *EVMBuiltins) void {
        for (self.entries.items) |*entry| entry.builtin.deinit(self.allocator);
        self.entries.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn functions(self: *const EVMBuiltins) []const Entry {
        return self.entries.items;
    }

    pub fn createVerbatimFunction(
        allocator: std.mem.Allocator,
        arguments: usize,
        return_variables: usize,
    ) !BuiltinFunctionForEVM {
        const name = try std.fmt.allocPrint(
            allocator,
            "verbatim_{d}i_{d}o",
            .{ arguments, return_variables },
        );
        errdefer allocator.free(name);
        const literal_arguments = try allocator.alloc(?AST.LiteralKind, 1 + arguments);
        errdefer allocator.free(literal_arguments);
        @memset(literal_arguments, null);
        literal_arguments[0] = .String;
        return .{
            .base = .{
                .name = name,
                .num_parameters = 1 + arguments,
                .num_returns = return_variables,
                .side_effects = SideEffects.worst(),
                .control_flow_side_effects = ControlFlowSideEffects.worst(),
                .is_msize = true,
                .literal_arguments = literal_arguments,
            },
            .codegen = .{ .verbatim = .{
                .arguments = arguments,
                .return_variables = return_variables,
            } },
        };
    }

    pub fn sideEffectsOfInstruction(instruction: Instruction) !SideEffects {
        return computeSideEffectsOfInstruction(instruction);
    }

    fn appendCustom(
        self: *EVMBuiltins,
        name: []const u8,
        parameters: usize,
        returns: usize,
        side_effects: SideEffects,
        control_flow_side_effects: ControlFlowSideEffects,
        literal_arguments: []const ?AST.LiteralKind,
        codegen: CodegenKind,
    ) !void {
        try self.entries.append(self.allocator, .{
            .scopes = Scopes.objectAccessScope(),
            .builtin = try createFunction(
                self.allocator,
                name,
                parameters,
                returns,
                side_effects,
                control_flow_side_effects,
                literal_arguments,
                codegen,
            ),
        });
    }
};

fn createFunction(
    allocator: std.mem.Allocator,
    name: []const u8,
    parameters: usize,
    returns: usize,
    side_effects: SideEffects,
    control_flow_side_effects: ControlFlowSideEffects,
    literal_arguments: []const ?AST.LiteralKind,
    codegen: CodegenKind,
) !BuiltinFunctionForEVM {
    if (literal_arguments.len != 0 and literal_arguments.len != parameters)
        return error.InvalidLiteralArgumentShape;
    const owned_name = try lowerDuplicate(allocator, name);
    errdefer allocator.free(owned_name);
    return .{
        .base = .{
            .name = owned_name,
            .num_parameters = parameters,
            .num_returns = returns,
            .side_effects = side_effects,
            .control_flow_side_effects = control_flow_side_effects,
            .literal_arguments = try allocator.dupe(?AST.LiteralKind, literal_arguments),
        },
        .codegen = codegen,
    };
}

fn instructionBuiltin(
    allocator: std.mem.Allocator,
    name: []const u8,
    instruction: Instruction,
    evm_version: EVMVersion,
) !BuiltinFunctionForEVM {
    const info = InstructionModule.instructionInfo(instruction, evm_version);
    var result = try createFunction(
        allocator,
        name,
        info.args,
        info.ret,
        try computeSideEffectsOfInstruction(instruction),
        ControlFlowSideEffects.fromInstruction(instruction),
        &.{},
        .{ .instruction = instruction },
    );
    result.base.is_msize = instruction == .MSIZE;
    result.instruction = instruction;
    return result;
}

fn computeSideEffectsOfInstruction(instruction: Instruction) !SideEffects {
    return .{
        .movable = SemanticInformation.movable(instruction),
        .movable_apart_from_effects = SemanticInformation.movableApartFromEffects(instruction),
        .can_be_removed = try SemanticInformation.canBeRemoved(instruction),
        .can_be_removed_if_no_msize = try SemanticInformation.canBeRemovedIfNoMSize(instruction),
        .cannot_loop = true,
        .other_state = @enumFromInt(@intFromEnum(SemanticInformation.otherState(instruction))),
        .storage = @enumFromInt(@intFromEnum(SemanticInformation.storage(instruction))),
        .memory = @enumFromInt(@intFromEnum(SemanticInformation.memory(instruction))),
        .transient_storage = @enumFromInt(@intFromEnum(SemanticInformation.transientStorage(instruction))),
    };
}

fn literalArgument(call: *const AST.FunctionCall, index: usize) !*const AST.Literal {
    if (index >= call.arguments.items.len) return error.InvalidBuiltinCall;
    return switch (call.arguments.items[index]) {
        .literal => |*literal| literal,
        else => error.InvalidBuiltinCall,
    };
}

fn literalTextAlloc(
    allocator: std.mem.Allocator,
    literal: *const AST.Literal,
) ![]u8 {
    if (literal.value.unlimited()) {
        return allocator.dupe(
            u8,
            literal.value.builtinStringLiteralValue() catch return error.InvalidBuiltinCall,
        );
    }
    if (literal.value.hint() catch return error.InvalidBuiltinCall) |hint|
        return allocator.dupe(u8, hint);
    if (literal.kind == .Boolean)
        return allocator.dupe(u8, if (literal.value.numeric_value.? == 0) "false" else "true");
    return std.fmt.allocPrint(allocator, "{d}", .{literal.value.numeric_value.?});
}

fn lowerDuplicate(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    const result = try allocator.dupe(u8, input);
    for (result) |*character| character.* = std.ascii.toLower(character.*);
    return result;
}

test "EVM builtins include stable instruction slots, object helpers, and verbatim shapes" {
    const allocator = std.testing.allocator;
    var builtins = try EVMBuiltins.init(allocator);
    defer builtins.deinit();
    var found_add = false;
    var found_difficulty = false;
    var found_prevrandao = false;
    var found_datasize = false;
    for (builtins.functions()) |entry| {
        if (std.mem.eql(u8, entry.builtin.base.name, "add")) found_add = true;
        if (std.mem.eql(u8, entry.builtin.base.name, "difficulty")) found_difficulty = true;
        if (std.mem.eql(u8, entry.builtin.base.name, "prevrandao")) found_prevrandao = true;
        if (std.mem.eql(u8, entry.builtin.base.name, "datasize")) found_datasize = true;
    }
    try std.testing.expect(found_add and found_difficulty and found_prevrandao and found_datasize);
    var verbatim = try EVMBuiltins.createVerbatimFunction(allocator, 2, 3);
    defer verbatim.deinit(allocator);
    try std.testing.expectEqualStrings("verbatim_2i_3o", verbatim.base.name);
    try std.testing.expectEqual(@as(usize, 3), verbatim.base.num_parameters);
    try std.testing.expectEqual(@as(usize, 3), verbatim.base.num_returns);
    try std.testing.expect(verbatim.base.is_msize);
}

test "EVM builtin code generators target the abstract assembly contract" {
    const allocator = std.testing.allocator;
    const Assembly = @import("../../../libevmasm/assembly.zig").Assembly;
    const EthAssemblyAdapter = @import("eth_assembly_adapter.zig").EthAssemblyAdapter;
    const ObjectNode = @import("../../object.zig").ObjectNode;
    const CallBuilder = struct {
        allocator: std.mem.Allocator,
        call: AST.FunctionCall = .{ .function_name = .{ .identifier = .{} } },

        fn deinit(self: *@This()) void {
            self.call.deinit(self.allocator);
        }

        fn number(self: *@This(), value: u256) !void {
            try self.call.arguments.append(self.allocator, .{ .literal = .{
                .kind = .Number,
                .value = try AST.LiteralValue.initNumeric(self.allocator, value, null),
            } });
        }

        fn string(self: *@This(), value: []const u8) !void {
            try self.call.arguments.append(self.allocator, .{ .literal = .{
                .kind = .String,
                .value = try AST.LiteralValue.initBuiltinString(self.allocator, value),
            } });
        }
    };
    const Lookup = struct {
        fn find(builtins: *const EVMBuiltins, name: []const u8) !*const BuiltinFunctionForEVM {
            for (builtins.functions()) |*entry|
                if (std.mem.eql(u8, entry.builtin.base.name, name)) return &entry.builtin;
            return error.MissingBuiltin;
        }
    };

    var builtins = try EVMBuiltins.init(allocator);
    defer builtins.deinit();
    var assembly = try Assembly.init(allocator, EVMVersion.current(), true, "builtins");
    defer assembly.deinit();
    var adapter = EthAssemblyAdapter.init(allocator, &assembly);
    defer adapter.deinit();
    const abstract = adapter.abstractAssembly();
    try abstract.setStackHeight(50);

    const root = try Object.create(allocator, "root");
    defer root.destroy();
    const child = try Object.create(allocator, "child");
    const child_assembly = try abstract.createSubAssembly(false, "child");
    child.sub_id = child_assembly.sub_id;
    try root.addSubObject(ObjectNode{ .object = child });
    var context = BuiltinContext.init(allocator);
    defer context.deinit();
    context.current_object = root;

    var instruction_call: CallBuilder = .{ .allocator = allocator };
    defer instruction_call.deinit();
    try instruction_call.number(1);
    try instruction_call.number(2);
    try (try Lookup.find(&builtins, "add")).generateCode(&instruction_call.call, abstract, &context);

    var memory_call: CallBuilder = .{ .allocator = allocator };
    defer memory_call.deinit();
    try memory_call.number(0x80);
    try (try Lookup.find(&builtins, "memoryguard")).generateCode(&memory_call.call, abstract, &context);

    var linker_call: CallBuilder = .{ .allocator = allocator };
    defer linker_call.deinit();
    try linker_call.string("source.sol:Library");
    try (try Lookup.find(&builtins, "linkersymbol")).generateCode(&linker_call.call, abstract, &context);

    var size_call: CallBuilder = .{ .allocator = allocator };
    defer size_call.deinit();
    try size_call.string("root");
    try (try Lookup.find(&builtins, "datasize")).generateCode(&size_call.call, abstract, &context);

    var offset_call: CallBuilder = .{ .allocator = allocator };
    defer offset_call.deinit();
    try offset_call.string("child");
    try (try Lookup.find(&builtins, "dataoffset")).generateCode(&offset_call.call, abstract, &context);

    var copy_call: CallBuilder = .{ .allocator = allocator };
    defer copy_call.deinit();
    try copy_call.number(0);
    try copy_call.number(1);
    try copy_call.number(2);
    try (try Lookup.find(&builtins, "datacopy")).generateCode(&copy_call.call, abstract, &context);

    var set_call: CallBuilder = .{ .allocator = allocator };
    defer set_call.deinit();
    try set_call.number(0);
    try set_call.string("slot");
    try set_call.number(1);
    try (try Lookup.find(&builtins, "setimmutable")).generateCode(&set_call.call, abstract, &context);

    var load_call: CallBuilder = .{ .allocator = allocator };
    defer load_call.deinit();
    try load_call.string("slot");
    try (try Lookup.find(&builtins, "loadimmutable")).generateCode(&load_call.call, abstract, &context);

    var verbatim = try EVMBuiltins.createVerbatimFunction(allocator, 1, 2);
    defer verbatim.deinit(allocator);
    var verbatim_call: CallBuilder = .{ .allocator = allocator };
    defer verbatim_call.deinit();
    try verbatim_call.string("\xaa\xbb");
    try verbatim_call.number(7);
    try verbatim.generateCode(&verbatim_call.call, abstract, &context);

    const items = assembly.itemsConst();
    try std.testing.expect(items.len >= 9);
    try std.testing.expect(items[0].hasInstruction());
    try std.testing.expectEqual(Instruction.ADD, try items[0].instruction());
    try std.testing.expectEqual(@as(u256, 0x80), items[1].data_value);
    try std.testing.expectEqual(@import("../../../libevmasm/assembly_item.zig").AssemblyItemType.VerbatimBytecode, items[items.len - 1].item_type);
    try std.testing.expectEqualSlices(u8, &.{ 0xaa, 0xbb }, try items[items.len - 1].verbatimData());
}
