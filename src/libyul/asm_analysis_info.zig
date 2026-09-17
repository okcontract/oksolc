// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned scope topology produced by Yul scope filling and semantic analysis.

const std = @import("std");
const AST = @import("ast.zig");
const Scope = @import("scope.zig").Scope;

pub const Scopes = std.AutoHashMap(?*const AST.Block, *Scope);
pub const VirtualBlocks = std.AutoHashMap(*const AST.FunctionDefinition, *AST.Block);

pub const AsmAnalysisInfo = struct {
    allocator: std.mem.Allocator,
    scopes: Scopes,
    virtual_blocks: VirtualBlocks,

    pub fn init(allocator: std.mem.Allocator) AsmAnalysisInfo {
        return .{
            .allocator = allocator,
            .scopes = Scopes.init(allocator),
            .virtual_blocks = VirtualBlocks.init(allocator),
        };
    }

    pub fn deinit(self: *AsmAnalysisInfo) void {
        var scope_iterator = self.scopes.valueIterator();
        while (scope_iterator.next()) |scope_pointer| {
            scope_pointer.*.deinit();
            self.allocator.destroy(scope_pointer.*);
        }
        self.scopes.deinit();
        var block_iterator = self.virtual_blocks.valueIterator();
        while (block_iterator.next()) |block_pointer| {
            block_pointer.*.deinit(self.allocator);
            self.allocator.destroy(block_pointer.*);
        }
        self.virtual_blocks.deinit();
        self.* = undefined;
    }

    pub fn getOrCreateScope(
        self: *AsmAnalysisInfo,
        block: ?*const AST.Block,
    ) std.mem.Allocator.Error!*Scope {
        if (self.scopes.get(block)) |scope| return scope;
        const scope = try self.allocator.create(Scope);
        errdefer self.allocator.destroy(scope);
        scope.* = Scope.init(self.allocator);
        errdefer scope.deinit();
        try self.scopes.put(block, scope);
        return scope;
    }

    pub fn getScope(self: *const AsmAnalysisInfo, block: ?*const AST.Block) ?*Scope {
        return self.scopes.get(block);
    }

    pub fn createVirtualBlock(
        self: *AsmAnalysisInfo,
        definition: *const AST.FunctionDefinition,
    ) std.mem.Allocator.Error!*AST.Block {
        if (self.virtual_blocks.get(definition)) |block| return block;
        const block = try self.allocator.create(AST.Block);
        errdefer self.allocator.destroy(block);
        block.* = .{};
        try self.virtual_blocks.put(definition, block);
        return block;
    }

    pub fn getVirtualBlock(
        self: *const AsmAnalysisInfo,
        definition: *const AST.FunctionDefinition,
    ) ?*AST.Block {
        return self.virtual_blocks.get(definition);
    }
};
