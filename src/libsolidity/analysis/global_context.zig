// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Implicit global declarations translated from `GlobalContext.cpp`.
//!
//! Global pseudo-AST nodes live in their own stable arena. Their concrete type
//! identities are borrowed from the compilation's `TypeProvider`, which must
//! outlive this context.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const Types = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;

pub const GlobalContextError = TypeProviderModule.ProviderError;

const ContractPointer = struct {
    contract: ?*const AST.Node,
    declaration: *const AST.Node,
};

pub const GlobalContext = struct {
    backing_allocator: std.mem.Allocator,
    arena_state: *std.heap.ArenaAllocator,
    type_provider: *TypeProviderModule.TypeProvider,
    magic_variables: []const *const AST.Node,
    current_contract: ?*const AST.Node = null,
    this_pointers: std.ArrayList(ContractPointer) = .empty,
    super_pointers: std.ArrayList(ContractPointer) = .empty,

    pub fn init(
        backing_allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        evm_version: EVMVersion,
    ) GlobalContextError!GlobalContext {
        const arena_state = try backing_allocator.create(std.heap.ArenaAllocator);
        arena_state.* = std.heap.ArenaAllocator.init(backing_allocator);

        // Transfer ownership before the next fallible operation. The context
        // alone cleans up both the arena contents and its backing object.
        var self: GlobalContext = .{
            .backing_allocator = backing_allocator,
            .arena_state = arena_state,
            .type_provider = type_provider,
            .magic_variables = &.{},
        };
        errdefer self.deinit();
        self.magic_variables = try self.constructMagicVariables(evm_version);
        return self;
    }

    pub fn deinit(self: *GlobalContext) void {
        const backing_allocator = self.backing_allocator;
        const arena_state = self.arena_state;
        self.this_pointers.deinit(backing_allocator);
        self.super_pointers.deinit(backing_allocator);
        arena_state.deinit();
        backing_allocator.destroy(arena_state);
        self.* = undefined;
    }

    fn allocator(self: *GlobalContext) std.mem.Allocator {
        return self.arena_state.allocator();
    }

    pub fn setCurrentContract(self: *GlobalContext, contract: *const AST.Node) void {
        std.debug.assert(contract.nodeKind() == .contract_definition);
        self.current_contract = contract;
    }

    pub fn resetCurrentContract(self: *GlobalContext) void {
        self.current_contract = null;
    }

    pub fn declarations(self: *const GlobalContext) []const *const AST.Node {
        return self.magic_variables;
    }

    pub fn currentThis(self: *GlobalContext) GlobalContextError!*const AST.Node {
        if (findContractPointer(self.this_pointers.items, self.current_contract)) |existing|
            return existing;
        const type_ref = if (self.current_contract) |contract|
            try self.type_provider.contract(contract, false)
        else
            self.type_provider.emptyTuple();
        const declaration = try self.createMagicVariable("this", type_ref);
        try self.this_pointers.append(self.backing_allocator, .{
            .contract = self.current_contract,
            .declaration = declaration,
        });
        return declaration;
    }

    pub fn currentSuper(self: *GlobalContext) GlobalContextError!*const AST.Node {
        if (findContractPointer(self.super_pointers.items, self.current_contract)) |existing|
            return existing;
        const type_ref = if (self.current_contract) |contract|
            try self.type_provider.typeType(try self.type_provider.contract(contract, true))
        else
            self.type_provider.emptyTuple();
        const declaration = try self.createMagicVariable("super", type_ref);
        try self.super_pointers.append(self.backing_allocator, .{
            .contract = self.current_contract,
            .declaration = declaration,
        });
        return declaration;
    }

    fn constructMagicVariables(
        self: *GlobalContext,
        evm_version: EVMVersion,
    ) GlobalContextError![]const *const AST.Node {
        const count: usize = 24 + @as(usize, @intFromBool(evm_version.hasBlobHash()));
        const result = try self.allocator().alloc(*const AST.Node, count);
        var index: usize = 0;

        result[index] = try self.createMagicVariable(
            "abi",
            try self.type_provider.magic(.ABI),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "addmod",
            try self.function(&.{ "uint256", "uint256", "uint256" }, &.{"uint256"}, .AddMod, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "assert",
            try self.function(&.{"bool"}, &.{}, .Assert, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "block",
            try self.type_provider.magic(.Block),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "blockhash",
            try self.function(&.{"uint256"}, &.{"bytes32"}, .BlockHash, .View, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "ecrecover",
            try self.function(
                &.{ "bytes32", "uint8", "bytes32", "bytes32" },
                &.{"address"},
                .ECRecover,
                .Pure,
                .{},
            ),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "erc7201",
            try self.function(&.{"string memory"}, &.{"uint256"}, .ERC7201, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "gasleft",
            try self.function(&.{}, &.{"uint256"}, .GasLeft, .View, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "keccak256",
            try self.function(&.{"bytes memory"}, &.{"bytes32"}, .KECCAK256, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "msg",
            try self.type_provider.magic(.Message),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "mulmod",
            try self.function(&.{ "uint256", "uint256", "uint256" }, &.{"uint256"}, .MulMod, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable("now", self.type_provider.uint256());
        index += 1;
        result[index] = try self.createMagicVariable(
            "require",
            try self.function(&.{"bool"}, &.{}, .Require, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "require",
            try self.function(&.{ "bool", "string memory" }, &.{}, .Require, .Pure, .{}),
        );
        index += 1;
        const require_error = try self.type_provider.function(
            &.{ self.type_provider.boolean(), try self.type_provider.magic(.Error) },
            &.{},
            &.{ "", "" },
            &.{},
            .Require,
            .Pure,
            null,
            .{},
        );
        result[index] = try self.createMagicVariable("require", require_error);
        index += 1;
        result[index] = try self.createMagicVariable(
            "revert",
            try self.function(&.{}, &.{}, .Revert, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "revert",
            try self.function(&.{"string memory"}, &.{}, .Revert, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "ripemd160",
            try self.function(&.{"bytes memory"}, &.{"bytes20"}, .RIPEMD160, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "selfdestruct",
            try self.function(&.{"address payable"}, &.{}, .Selfdestruct, .NonPayable, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "sha256",
            try self.function(&.{"bytes memory"}, &.{"bytes32"}, .SHA256, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "sha3",
            try self.function(&.{"bytes memory"}, &.{"bytes32"}, .KECCAK256, .Pure, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "suicide",
            try self.function(&.{"address payable"}, &.{}, .Selfdestruct, .NonPayable, .{}),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "tx",
            try self.type_provider.magic(.Transaction),
        );
        index += 1;
        result[index] = try self.createMagicVariable(
            "type",
            try self.function(
                &.{},
                &.{},
                .MetaType,
                .Pure,
                Types.FunctionOptions.withArbitraryParameters(),
            ),
        );
        index += 1;
        if (evm_version.hasBlobHash()) {
            result[index] = try self.createMagicVariable(
                "blobhash",
                try self.function(&.{"uint256"}, &.{"bytes32"}, .BlobHash, .View, .{}),
            );
            index += 1;
        }
        std.debug.assert(index == result.len);
        return result;
    }

    fn function(
        self: *GlobalContext,
        parameters: []const []const u8,
        returns: []const []const u8,
        kind: Types.FunctionKind,
        state_mutability: Types.StateMutability,
        options: Types.FunctionOptions,
    ) GlobalContextError!*const Types.Type {
        return self.type_provider.functionFromTypeNames(
            parameters,
            returns,
            kind,
            state_mutability,
            options,
        );
    }

    fn createMagicVariable(
        self: *GlobalContext,
        name: []const u8,
        type_ref: *const Types.Type,
    ) std.mem.Allocator.Error!*const AST.Node {
        const node = try self.allocator().create(AST.Node);
        node.* = .{
            .id = magicVariableToId(name),
            .location = .{},
            .payload = .{ .magic_variable_declaration = .{
                .declaration = .{ .name = try self.allocator().dupe(u8, name) },
                .type_ref = @ptrCast(type_ref),
            } },
        };
        return node;
    }
};

fn findContractPointer(
    pointers: []const ContractPointer,
    contract: ?*const AST.Node,
) ?*const AST.Node {
    for (pointers) |entry| if (entry.contract == contract) return entry.declaration;
    return null;
}

pub fn declarationType(declaration: *const AST.Node) ?*const Types.Type {
    if (declaration.nodeKind() != .magic_variable_declaration) return null;
    const erased = declaration.payload.magic_variable_declaration.type_ref orelse return null;
    return @ptrCast(@alignCast(erased));
}

pub fn magicVariableToId(name: []const u8) i64 {
    const entries = [_]struct { []const u8, i64 }{
        .{ "abi", -1 },
        .{ "addmod", -2 },
        .{ "assert", -3 },
        .{ "block", -4 },
        .{ "blockhash", -5 },
        .{ "ecrecover", -6 },
        .{ "gasleft", -7 },
        .{ "keccak256", -8 },
        .{ "msg", -15 },
        .{ "mulmod", -16 },
        .{ "now", -17 },
        .{ "require", -18 },
        .{ "revert", -19 },
        .{ "ripemd160", -20 },
        .{ "selfdestruct", -21 },
        .{ "sha256", -22 },
        .{ "sha3", -23 },
        .{ "suicide", -24 },
        .{ "super", -25 },
        .{ "tx", -26 },
        .{ "type", -27 },
        .{ "this", -28 },
        .{ "blobhash", -29 },
        .{ "erc7201", -30 },
    };
    for (entries) |entry| if (std.mem.eql(u8, name, entry[0])) return entry[1];
    unreachable;
}

test "global declarations retain upstream order, overloads, ids, and EVM gates" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var context = try GlobalContext.init(
        std.testing.allocator,
        &provider,
        EVMVersion.init(.Cancun),
    );
    defer context.deinit();

    try std.testing.expectEqual(@as(usize, 25), context.declarations().len);
    try std.testing.expectEqualStrings(
        "abi",
        context.declarations()[0].payload.magic_variable_declaration.declaration.name,
    );
    try std.testing.expectEqualStrings(
        "blobhash",
        context.declarations()[24].payload.magic_variable_declaration.declaration.name,
    );
    try std.testing.expectEqual(@as(i64, -18), magicVariableToId("require"));
    var require_count: usize = 0;
    for (context.declarations()) |declaration|
        require_count += @intFromBool(std.mem.eql(
            u8,
            declaration.payload.magic_variable_declaration.declaration.name,
            "require",
        ));
    try std.testing.expectEqual(@as(usize, 3), require_count);

    const this_without_contract = try context.currentThis();
    try std.testing.expect(declarationType(this_without_contract) == provider.emptyTuple());
    try std.testing.expect((try context.currentThis()) == this_without_contract);
}

fn exerciseGlobalContextInitialization(allocator: std.mem.Allocator) !void {
    var provider = try TypeProviderModule.TypeProvider.init(allocator);
    defer provider.deinit();
    var context = try GlobalContext.init(allocator, &provider, EVMVersion.init(.Cancun));
    defer context.deinit();
    try std.testing.expectEqual(@as(usize, 25), context.declarations().len);
}

test "global context initialization has one cleanup owner at every allocation failure" {
    try exerciseGlobalContextInitialization(std.testing.allocator);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseGlobalContextInitialization, .{});
}
