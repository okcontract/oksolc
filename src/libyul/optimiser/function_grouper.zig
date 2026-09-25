// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Canonical grouping of executable statements before top-level functions.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const FunctionGrouper = struct {
    pub const name = "FunctionGrouper";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) !void {
        try apply(context.dispenser.allocator, ast);
    }

    pub fn apply(allocator: std.mem.Allocator, block: *AST.Block) !void {
        if (alreadyGrouped(block)) return;

        var function_count: usize = 0;
        for (block.statements.items) |statement|
            if (statement == .function_definition) {
                function_count += 1;
            };
        const code_count = block.statements.items.len - function_count;
        const grouped_len = std.math.add(usize, function_count, 1) catch return error.OutOfMemory;
        const retain_code = function_count < code_count;

        // Keep the larger partition in the existing buffer. Reserve all storage
        // before moving owners; no fallible operation follows the reservations.
        // Both final lengths are known, so new storage needs no spare capacity.
        var separated: std.ArrayList(AST.Statement) = .empty;
        errdefer separated.deinit(allocator);
        try separated.ensureTotalCapacityPrecise(allocator, if (retain_code) grouped_len else code_count);
        if (!retain_code) try block.statements.ensureTotalCapacityPrecise(allocator, grouped_len);
        if (retain_code) separated.appendAssumeCapacity(.{ .block = .{} });

        var retained_len: usize = 0;
        for (block.statements.items) |statement| {
            if ((statement == .function_definition) == retain_code) {
                separated.appendAssumeCapacity(statement);
            } else {
                // Forward compaction writes only to already-read slots.
                block.statements.items[retained_len] = statement;
                retained_len += 1;
            }
        }
        if (retain_code) {
            block.statements.items.len = retained_len;
            separated.items[0] = .{ .block = .{
                .debug_data = block.debug_data,
                .statements = block.statements,
            } };
            block.statements = separated;
        } else {
            block.statements.items.len = grouped_len;
            @memmove(block.statements.items[1..], block.statements.items[0..retained_len]);
            block.statements.items[0] = .{ .block = .{
                .debug_data = block.debug_data,
                .statements = separated,
            } };
        }
    }

    pub fn alreadyGrouped(block: *const AST.Block) bool {
        if (block.statements.items.len == 0 or block.statements.items[0] != .block) return false;
        for (block.statements.items[1..]) |statement|
            if (statement != .function_definition) return false;
        return true;
    }
};

test "function grouper preserves order in one code block followed by functions" {
    const allocator = std.testing.allocator;
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    try root.statements.append(allocator, .{ .break_statement = .{} });
    try root.statements.append(allocator, .{ .function_definition = .{} });
    try root.statements.append(allocator, .{ .leave_statement = .{} });
    try FunctionGrouper.apply(allocator, &root);
    try std.testing.expect(FunctionGrouper.alreadyGrouped(&root));
    try std.testing.expectEqual(@as(usize, 2), root.statements.items[0].block.statements.items.len);
}

test "function grouper preserves partition order and annotations" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Converter = @import("../asm_json_converter.zig").AsmJsonConverter;
    const Encoding = @import("../ast_encoding.zig");
    const JSON = @import("../../libsolutil/json.zig");
    const cases = .{
        .{ "empty", "{}", "1657afb42b935c9d0d8c22e3d1dd8c564f0fe8d470aa65c702389fd02c4bd236", "56cd0acb7f0b7f4dba6fc6fc53868901b45ff76ab8031bbb004821832b871b5c" },
        .{ "code", "{ let x := \"code\" pop(x) { pop(2) } }", "8e7f17713f21faea02c01ba08c8e617f345bcfc236056e5bb42e2b297519ce43", "8c4031923d8fe91541d1b1fd9dfaf609d53bc721f41fc14eaefe2a02e22d7aab" },
        .{ "functions", "{ function f(a) -> r { r := add(a, 1) } function g(b) { pop(b) } }", "c94e40638d45a6fcc154e42528af19af4eb7422959bb033f75a95f01fe7ff5e2", "b379194b695697d17b9f13868417ad39bad97e2060e96ffc304fb5609b375d67" },
        .{ "function-heavy", "{ function f() { pop(\"f\") } pop(1) function g() { pop(\"g\") } function h() {} }", "57b9e44492a8c29c75f0896f04d3754d2cf4a7f6a52076feff238fda1f0e85a6", "f05584e706230de9ded2aafb4fc2e0a4ffb8a47ed4b62578daf20ef72992e4cb" },
        .{ "code-heavy", "{ pop(1) function f() { pop(\"f\") } let x := 2 pop(x) { pop(3) } }", "c19b8a74c510a18d7cce372a705d601f87d9ef3e56564a99f0364ffddaf5ae13", "96f524929fa97003aba686de708d763895be933b5c0e394c0230d2a847b550e5" },
        .{ "alternating", "{ function f() { pop(\"f\") } pop(1) function g() { pop(\"g\") } pop(2) }", "d0674203c6ae4f2b99106ae7b1122ee4b5277c13e847cd23a2139498fa6b2582", "d1c20d0d4703ed0b8bd804e70538ec897a455b74b86b7b517ff148105c418d54" },
        .{ "grouped", "{ { pop(1) } function f() { pop(\"f\") } }", "d76b9b8c4a640636478ba8c51a2159aa7c3a53be494fe77d80281608e4cf0c49", "e8fcc4e1eb7cc10adb6b4bf91614a12441212f8b539c59dd81000a796ac5c803" },
    };
    inline for (cases) |case| {
        const allocator = std.testing.allocator;
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, case[1], "grouping.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        ast.root_block.debug_data.?.ast_id = 41;
        for (ast.root_block.statements.items, 0..) |*statement, index| {
            if (index % 2 == 0) {
                switch (statement.*) {
                    inline else => |*value| value.debug_data = null,
                }
            } else {
                switch (statement.*) {
                    inline else => |*value| value.debug_data.?.ast_id = @intCast(53 + index),
                }
            }
        }
        try FunctionGrouper.apply(allocator, &ast.root_block);
        var json = try Converter.convertAlloc(allocator, &ast, 7);
        defer json.deinit();
        const bytes = try JSON.jsonCompactPrintAlloc(allocator, &json.value);
        defer allocator.free(bytes);
        var digest: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(bytes, &digest, .{});
        const encoded = std.fmt.bytesToHex(digest, .lower);
        const canonical = (try Encoding.hashBlock(ast.root())).hex();
        try std.testing.expectEqualStrings(case[2], &encoded);
        try std.testing.expectEqualStrings(case[3], &canonical);
    }
}

test "function grouper retains buffers and skips allocation with sufficient storage" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const cases = .{
        .{ "{}", false, false },
        .{ "{ pop(1) pop(2) }", true, true },
        .{ "{ function f() {} function g() {} }", false, false },
        .{ "{ function f() {} pop(1) function g() {} }", false, true },
        .{ "{ pop(1) function f() {} pop(2) pop(3) }", true, true },
        .{ "{ function f() {} pop(1) function g() {} pop(2) }", false, true },
        .{ "{ { pop(1) } function f() {} }", false, false },
    };
    inline for (cases) |case| {
        const allocator = std.testing.allocator;
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, case[0], "grouping-storage.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        try ast.root_block.statements.ensureUnusedCapacity(allocator, 1);
        const storage = ast.root_block.statements.items.ptr;
        var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
        try FunctionGrouper.apply(if (case[2]) allocator else rejecting.allocator(), &ast.root_block);
        try std.testing.expect(!rejecting.has_induced_failure);
        try std.testing.expect(FunctionGrouper.alreadyGrouped(&ast.root_block));
        const retained = if (case[1]) ast.root_block.statements.items[0].block.statements else ast.root_block.statements;
        try std.testing.expectEqual(storage, retained.items.ptr);
    }
}

test "function grouper reservation failures preserve the input tree" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Encoding = @import("../ast_encoding.zig");
    const Copier = @import("ast_copier.zig").ASTCopier;
    const Check = struct {
        fn run(failing: std.mem.Allocator, source: *const AST.Block) !void {
            const allocator = std.testing.allocator;
            var copier = Copier.init(allocator);
            var block = try copier.translateBlock(source);
            defer block.deinit(allocator);
            // Force functions-only input to reserve its additional code slot.
            const items = try block.statements.toOwnedSlice(allocator);
            block.statements = .fromOwnedSlice(items);
            const storage = block.statements.items.ptr;
            const before = try Encoding.hashBlock(&block);
            FunctionGrouper.apply(failing, &block) catch |err| {
                try std.testing.expectEqual(error.OutOfMemory, err);
                try std.testing.expectEqual(storage, block.statements.items.ptr);
                try std.testing.expectEqualDeep(before, try Encoding.hashBlock(&block));
                return err;
            };
            try std.testing.expect(FunctionGrouper.alreadyGrouped(&block));
        }
    };
    inline for (.{
        "{}",
        "{ pop(1) pop(2) }",
        "{ function f() { pop(\"f\") } function g() {} }",
        "{ function f() { pop(\"f\") } pop(1) function g() {} }",
        "{ pop(1) function f() { pop(\"f\") } pop(2) pop(3) }",
        "{ function f() { pop(\"f\") } pop(1) function g() {} pop(2) }",
    }) |source| {
        const allocator = std.testing.allocator;
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, source, "grouping-failure.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ast.root()});
    }
}
