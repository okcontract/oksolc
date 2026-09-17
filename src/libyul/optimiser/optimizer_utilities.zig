// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared optimizer utilities, including ownership-safe statement filtering
//! and checked recovery of concrete EVM dialect behavior.

const std = @import("std");
const AST = @import("../ast.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
const Instruction = @import("../../libevmasm/instruction.zig").Instruction;
const Token = @import("../../liblangutil/token.zig");

pub fn removeEmptyBlocks(allocator: std.mem.Allocator, block: *AST.Block) void {
    var write_index: usize = 0;
    const original_len = block.statements.items.len;
    for (0..original_len) |read_index| {
        const statement = &block.statements.items[read_index];
        if (statement.* == .block and statement.block.statements.items.len == 0) {
            statement.deinit(allocator);
            statement.* = emptyStatement();
            continue;
        }
        if (write_index != read_index) {
            block.statements.items[write_index] = statement.*;
            statement.* = emptyStatement();
        }
        write_index += 1;
    }
    block.statements.shrinkRetainingCapacity(write_index);
}

pub fn isRestrictedIdentifier(dialect: AST.Dialect, identifier: []const u8) bool {
    return identifier.len == 0 or
        identifier[0] == '.' or
        identifier[identifier.len - 1] == '.' or
        Token.isYulKeyword(identifier) or
        Token.isFutureYulKeyword(identifier) or
        dialect.reservedIdentifier(identifier);
}

pub fn toEVMInstruction(dialect: AST.Dialect, function_name: *const AST.FunctionName) ?Instruction {
    const evm_dialect = EVMDialectModule.fromDialect(dialect) orelse return null;
    const handle = switch (function_name.*) {
        .builtin => |builtin_name| builtin_name.handle,
        .identifier => return null,
    };
    return (evm_dialect.builtin(handle) orelse return null).instruction;
}

pub fn evmVersionFromDialect(dialect: AST.Dialect) EVMVersion {
    return if (EVMDialectModule.fromDialect(dialect)) |evm_dialect|
        evm_dialect.evmVersion()
    else
        EVMVersion.current();
}

pub const StatementSet = std.AutoHashMap(*const AST.Statement, void);

pub const StatementRemover = struct {
    allocator: std.mem.Allocator,
    to_remove: *const StatementSet,

    pub fn run(
        allocator: std.mem.Allocator,
        block: *AST.Block,
        to_remove: *const StatementSet,
    ) !void {
        var remover: StatementRemover = .{ .allocator = allocator, .to_remove = to_remove };
        try remover.visitBlock(block);
    }

    fn visitBlock(self: *StatementRemover, block: *AST.Block) anyerror!void {
        var replacement: std.ArrayList(AST.Statement) = .empty;
        errdefer {
            for (replacement.items) |*statement| statement.deinit(self.allocator);
            replacement.deinit(self.allocator);
        }
        try replacement.ensureTotalCapacity(self.allocator, block.statements.items.len);
        for (block.statements.items) |*statement| {
            if (self.to_remove.contains(statement)) {
                statement.deinit(self.allocator);
                statement.* = emptyStatement();
            } else {
                replacement.appendAssumeCapacity(statement.*);
                statement.* = emptyStatement();
            }
        }
        block.statements.deinit(self.allocator);
        block.statements = replacement;
        replacement = .empty;
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *StatementRemover, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            else => {},
        }
    }
};

fn emptyStatement() AST.Statement {
    return .{ .block = .{} };
}

test "optimizer utilities identify restricted names and remove selected statements" {
    const allocator = std.testing.allocator;
    const EVMDialect = EVMDialectModule.EVMDialect;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    try std.testing.expect(isRestrictedIdentifier(dialect.dialect(), "let"));
    try std.testing.expect(isRestrictedIdentifier(dialect.dialect(), "add"));
    try std.testing.expect(isRestrictedIdentifier(dialect.dialect(), ".bad"));
    try std.testing.expect(!isRestrictedIdentifier(dialect.dialect(), "ordinary_name"));
    try std.testing.expectEqual(EVMVersion.current().version, evmVersionFromDialect(dialect.dialect()).version);

    var block: AST.Block = .{};
    defer block.deinit(allocator);
    try block.statements.append(allocator, emptyStatement());
    try block.statements.append(allocator, .{ .break_statement = .{} });
    removeEmptyBlocks(allocator, &block);
    try std.testing.expectEqual(@as(usize, 1), block.statements.items.len);
}
