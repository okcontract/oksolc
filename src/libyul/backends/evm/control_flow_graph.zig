// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Control-flow graph and symbolic EVM stack slots used by optimized Yul code
//! generation. Graph nodes and synthetic AST objects are individually
//! allocated so pointer identity remains stable, matching the owning C++ lists.

const std = @import("std");
const AST = @import("../../ast.zig");
const DebugData = @import("../../../liblangutil/debug_data.zig").DebugData;
const ScopeModule = @import("../../scope.zig");
const YulName = @import("../../yul_name.zig").YulName;

pub const FunctionCallReturnLabelSlot = struct {
    call: *const AST.FunctionCall,
};

pub const FunctionReturnLabelSlot = struct {
    function: *const ScopeModule.Function,
};

pub const VariableSlot = struct {
    variable: *const ScopeModule.Variable,
    debug_data: ?DebugData = null,
};

pub const LiteralSlot = struct {
    value: u256,
    debug_data: ?DebugData = null,
};

pub const TemporarySlot = struct {
    call: *const AST.FunctionCall,
    index: usize = 0,
};

pub const JunkSlot = struct {};

pub const StackSlot = union(enum) {
    function_call_return_label: FunctionCallReturnLabelSlot,
    function_return_label: FunctionReturnLabelSlot,
    variable: VariableSlot,
    literal: LiteralSlot,
    temporary: TemporarySlot,
    junk: JunkSlot,

    pub fn eql(left: StackSlot, right: StackSlot) bool {
        if (@intFromEnum(left) != @intFromEnum(right)) return false;
        return switch (left) {
            .function_call_return_label => |slot| slot.call == right.function_call_return_label.call,
            .function_return_label => |slot| slot.function == right.function_return_label.function,
            .variable => |slot| slot.variable == right.variable.variable,
            .literal => |slot| slot.value == right.literal.value,
            .temporary => |slot| slot.call == right.temporary.call and slot.index == right.temporary.index,
            .junk => true,
        };
    }

    pub fn lessThan(left: StackSlot, right: StackSlot) bool {
        const left_tag = @intFromEnum(left);
        const right_tag = @intFromEnum(right);
        if (left_tag != right_tag) return left_tag < right_tag;
        return switch (left) {
            .function_call_return_label => |slot| @intFromPtr(slot.call) < @intFromPtr(right.function_call_return_label.call),
            .function_return_label => |slot| @intFromPtr(slot.function) < @intFromPtr(right.function_return_label.function),
            .variable => |slot| @intFromPtr(slot.variable) < @intFromPtr(right.variable.variable),
            .literal => |slot| slot.value < right.literal.value,
            .temporary => |slot| blk: {
                const right_slot = right.temporary;
                if (slot.call != right_slot.call)
                    break :blk @intFromPtr(slot.call) < @intFromPtr(right_slot.call);
                break :blk slot.index < right_slot.index;
            },
            .junk => false,
        };
    }

    pub fn canBeFreelyGenerated(self: StackSlot) bool {
        return switch (self) {
            .function_call_return_label, .literal, .junk => true,
            .function_return_label, .variable, .temporary => false,
        };
    }

    pub fn debugData(self: StackSlot) ?DebugData {
        return switch (self) {
            .variable => |slot| slot.debug_data,
            .literal => |slot| slot.debug_data,
            else => null,
        };
    }
};

pub const Stack = std.ArrayList(StackSlot);

pub const BuiltinCall = struct {
    debug_data: ?DebugData,
    builtin: *const AST.BuiltinFunction,
    function_call: *const AST.FunctionCall,
    arguments: usize = 0,
};

pub const FunctionCall = struct {
    debug_data: ?DebugData,
    function: *const ScopeModule.Function,
    function_call: *const AST.FunctionCall,
    recursive: bool = false,
    can_continue: bool = true,
};

pub const Assignment = struct {
    debug_data: ?DebugData,
    variables: std.ArrayList(VariableSlot) = .empty,

    fn deinit(self: *Assignment, allocator: std.mem.Allocator) void {
        self.variables.deinit(allocator);
    }
};

pub const OperationKind = union(enum) {
    function_call: FunctionCall,
    builtin_call: BuiltinCall,
    assignment: Assignment,

    fn deinit(self: *OperationKind, allocator: std.mem.Allocator) void {
        switch (self.*) {
            .assignment => |*assignment| assignment.deinit(allocator),
            else => {},
        }
    }
};

pub const Operation = struct {
    input: Stack = .empty,
    output: Stack = .empty,
    operation: OperationKind,

    pub fn deinit(self: *Operation, allocator: std.mem.Allocator) void {
        self.input.deinit(allocator);
        self.output.deinit(allocator);
        self.operation.deinit(allocator);
        self.* = undefined;
    }
};

pub const MainExit = struct {};
pub const ConditionalJump = struct {
    debug_data: ?DebugData,
    condition: StackSlot,
    non_zero: *BasicBlock,
    zero: *BasicBlock,
};
pub const Jump = struct {
    debug_data: ?DebugData,
    target: *BasicBlock,
    backwards: bool = false,
};
pub const FunctionReturn = struct {
    debug_data: ?DebugData,
    info: *FunctionInfo,
};
pub const Terminated = struct {};

pub const Exit = union(enum) {
    main_exit: MainExit,
    jump: Jump,
    conditional_jump: ConditionalJump,
    function_return: FunctionReturn,
    terminated: Terminated,
};

pub const BasicBlock = struct {
    debug_data: ?DebugData,
    entries: std.ArrayList(*BasicBlock) = .empty,
    operations: std.ArrayList(Operation) = .empty,
    is_start_of_sub_graph: bool = false,
    needs_clean_stack: bool = false,
    exit: Exit = .{ .main_exit = .{} },

    pub fn allowsJunk(self: *const BasicBlock) bool {
        return self.is_start_of_sub_graph and !self.needs_clean_stack;
    }

    fn deinit(self: *BasicBlock, allocator: std.mem.Allocator) void {
        self.entries.deinit(allocator);
        for (self.operations.items) |*operation| operation.deinit(allocator);
        self.operations.deinit(allocator);
        self.* = undefined;
    }
};

pub const FunctionInfo = struct {
    debug_data: ?DebugData,
    function: *const ScopeModule.Function,
    function_definition: *const AST.FunctionDefinition,
    entry: *BasicBlock,
    parameters: std.ArrayList(VariableSlot) = .empty,
    return_variables: std.ArrayList(VariableSlot) = .empty,
    exits: std.ArrayList(*BasicBlock) = .empty,
    can_continue: bool = true,

    pub fn deinit(self: *FunctionInfo, allocator: std.mem.Allocator) void {
        self.parameters.deinit(allocator);
        self.return_variables.deinit(allocator);
        self.exits.deinit(allocator);
        self.* = undefined;
    }
};

pub const CFG = struct {
    allocator: std.mem.Allocator,
    entry: ?*BasicBlock = null,
    function_info: std.AutoHashMap(*const ScopeModule.Function, *FunctionInfo),
    functions: std.ArrayList(*const ScopeModule.Function) = .empty,
    blocks: std.ArrayList(*BasicBlock) = .empty,
    ghost_variables: std.ArrayList(*ScopeModule.Variable) = .empty,
    ghost_calls: std.ArrayList(*AST.FunctionCall) = .empty,

    pub fn init(allocator: std.mem.Allocator) CFG {
        return .{
            .allocator = allocator,
            .function_info = std.AutoHashMap(*const ScopeModule.Function, *FunctionInfo).init(allocator),
        };
    }

    pub fn deinit(self: *CFG) void {
        var infos = self.function_info.valueIterator();
        while (infos.next()) |info| {
            info.*.deinit(self.allocator);
            self.allocator.destroy(info.*);
        }
        self.function_info.deinit();
        self.functions.deinit(self.allocator);
        for (self.blocks.items) |block| {
            block.deinit(self.allocator);
            self.allocator.destroy(block);
        }
        self.blocks.deinit(self.allocator);
        for (self.ghost_variables.items) |variable| self.allocator.destroy(variable);
        self.ghost_variables.deinit(self.allocator);
        for (self.ghost_calls.items) |call| {
            call.deinit(self.allocator);
            self.allocator.destroy(call);
        }
        self.ghost_calls.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn makeBlock(self: *CFG, debug_data: ?DebugData) !*BasicBlock {
        const block = try self.allocator.create(BasicBlock);
        errdefer self.allocator.destroy(block);
        block.* = .{ .debug_data = debug_data };
        errdefer block.deinit(self.allocator);
        try self.blocks.append(self.allocator, block);
        return block;
    }

    pub fn makeGhostVariable(self: *CFG, name: YulName) !*ScopeModule.Variable {
        const variable = try self.allocator.create(ScopeModule.Variable);
        errdefer self.allocator.destroy(variable);
        variable.* = .{ .name = name };
        try self.ghost_variables.append(self.allocator, variable);
        return variable;
    }

    pub fn ownGhostCall(self: *CFG, call_value: AST.FunctionCall) !*AST.FunctionCall {
        const call = try self.allocator.create(AST.FunctionCall);
        errdefer self.allocator.destroy(call);
        call.* = call_value;
        errdefer call.deinit(self.allocator);
        try self.ghost_calls.append(self.allocator, call);
        return call;
    }

    pub fn createFunctionInfo(
        self: *CFG,
        function: *const ScopeModule.Function,
        definition: *const AST.FunctionDefinition,
        entry_block: *BasicBlock,
        debug_data: ?DebugData,
        can_continue: bool,
    ) !*FunctionInfo {
        if (self.function_info.contains(function)) return error.DuplicateFunctionInfo;
        const info = try self.allocator.create(FunctionInfo);
        errdefer self.allocator.destroy(info);
        info.* = .{
            .debug_data = debug_data,
            .function = function,
            .function_definition = definition,
            .entry = entry_block,
            .can_continue = can_continue,
        };
        errdefer info.deinit(self.allocator);
        try self.function_info.put(function, info);
        return info;
    }
};

test "symbolic stack-slot identity ignores debug metadata" {
    var first_call: AST.FunctionCall = .{ .function_name = .{ .identifier = .{} } };
    defer first_call.deinit(std.testing.allocator);
    const a: StackSlot = .{ .temporary = .{ .call = &first_call, .index = 1 } };
    const b: StackSlot = .{ .temporary = .{ .call = &first_call, .index = 1 } };
    try std.testing.expect(a.eql(b));
    try std.testing.expect(!a.canBeFreelyGenerated());
    try std.testing.expect((StackSlot{ .literal = .{ .value = 7 } }).canBeFreelyGenerated());
}
