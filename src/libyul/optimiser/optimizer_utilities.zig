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
    removeStatementsIf(allocator, block, {}, struct {
        fn isEmpty(_: void, statement: *const AST.Statement) bool {
            return statement.* == .block and statement.block.statements.items.len == 0;
        }
    }.isEmpty);
}

fn removeStatementsIf(
    allocator: std.mem.Allocator,
    block: *AST.Block,
    context: anytype,
    comptime predicate: fn (@TypeOf(context), *const AST.Statement) bool,
) void {
    var write_index: usize = 0;
    const original_len = block.statements.items.len;
    for (0..original_len) |read_index| {
        const statement = &block.statements.items[read_index];
        // Address-based predicates must see the original slot before it moves.
        if (predicate(context, statement)) {
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
        if (to_remove.count() == 0) return;
        var remover: StatementRemover = .{ .allocator = allocator, .to_remove = to_remove };
        try remover.visitBlock(block);
    }

    fn visitBlock(self: *StatementRemover, block: *AST.Block) anyerror!void {
        removeStatementsIf(self.allocator, block, self.to_remove, struct {
            fn isSelected(selected: *const StatementSet, statement: *const AST.Statement) bool {
                return selected.contains(statement);
            }
        }.isSelected);
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

test "statement remover preserves buffers and original address selection without allocations" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ pop(0) if 1 { pop(1) pop(2) } pop(3) { pop(4) pop(5) } for {} 0 {} { pop(6) } }",
        "remove.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var selected = StatementSet.init(allocator);
    defer selected.deinit();
    var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
    const original = ast.root_block.statements.items;
    try StatementRemover.run(rejecting.allocator(), &ast.root_block, &selected);
    try std.testing.expect(original.ptr == ast.root_block.statements.items.ptr);
    try std.testing.expectEqual(original.len, ast.root_block.statements.items.len);

    const if_body = original[1].if_statement.body.statements.items.ptr;
    try selected.put(&original[0], {});
    try selected.put(&original[1].if_statement.body.statements.items[0], {});
    try selected.put(&original[2], {});
    // Deleting an ancestor must not revisit a selected, already freed child.
    try selected.put(&original[3], {});
    try selected.put(&original[3].block.statements.items[0], {});
    try selected.put(&original[4].for_loop.body.statements.items[0], {});
    try StatementRemover.run(rejecting.allocator(), &ast.root_block, &selected);
    try std.testing.expect(!rejecting.has_induced_failure);
    try std.testing.expect(original.ptr == ast.root_block.statements.items.ptr);
    try std.testing.expectEqual(@as(usize, 2), ast.root_block.statements.items.len);
    try std.testing.expect(if_body == ast.root_block.statements.items[0].if_statement.body.statements.items.ptr);
    var expected = (try Parser.parseSource(allocator, "{ if 1 { pop(2) } for {} 0 {} {} }", "remove.yul", &reporter, .{}, .{})).?;
    defer expected.deinit();
    const actual_text = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(actual_text);
    const expected_text = try Printer.formatDefault(allocator, &expected);
    defer allocator.free(expected_text);
    try std.testing.expectEqualStrings(expected_text, actual_text);
}
