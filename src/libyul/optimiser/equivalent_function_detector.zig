// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Detects alpha-equivalent Yul functions using structural block hashes and
//! collision-safe syntactic equality.

const std = @import("std");
const AST = @import("../ast.zig");
const BlockHasher = @import("block_hasher.zig");
const SyntacticalEquality = @import("syntactical_equality.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const DuplicateMap = std.AutoHashMap(YulName, *const AST.FunctionDefinition);
const CandidateMap = std.AutoHashMap(u64, std.ArrayList(*const AST.FunctionDefinition));

pub const EquivalentFunctionDetector = struct {
    allocator: std.mem.Allocator,
    block_hashes: BlockHasher.BlockHashMap,
    candidates: CandidateMap,
    duplicates: DuplicateMap,

    pub fn run(allocator: std.mem.Allocator, block: *const AST.Block) anyerror!DuplicateMap {
        var detector: EquivalentFunctionDetector = .{
            .allocator = allocator,
            .block_hashes = try BlockHasher.BlockHasher.run(allocator, block),
            .candidates = CandidateMap.init(allocator),
            .duplicates = DuplicateMap.init(allocator),
        };
        defer detector.deinit();
        try detector.visitBlock(block);
        const result = detector.duplicates;
        detector.duplicates = DuplicateMap.init(allocator);
        return result;
    }

    fn deinit(self: *EquivalentFunctionDetector) void {
        var candidate_iterator = self.candidates.valueIterator();
        while (candidate_iterator.next()) |candidate_list|
            candidate_list.deinit(self.allocator);
        self.candidates.deinit();
        self.block_hashes.deinit();
        self.duplicates.deinit();
        self.* = undefined;
    }

    fn visitBlock(self: *EquivalentFunctionDetector, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(
        self: *EquivalentFunctionDetector,
        statement: *const AST.Statement,
    ) anyerror!void {
        switch (statement.*) {
            .function_definition => |*function| try self.visitFunction(function),
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitBlock(&value.body);
                try self.visitBlock(&value.post);
            },
            .block => |*value| try self.visitBlock(value),
            else => {},
        }
    }

    fn visitFunction(
        self: *EquivalentFunctionDetector,
        function: *const AST.FunctionDefinition,
    ) anyerror!void {
        const body_hash = self.block_hashes.get(&function.body) orelse 0;
        const entry = try self.candidates.getOrPut(body_hash);
        if (!entry.found_existing) entry.value_ptr.* = .empty;
        for (entry.value_ptr.items) |candidate| {
            var equality = SyntacticalEquality.SyntacticallyEqual.init(self.allocator);
            defer equality.deinit();
            const left: AST.Statement = .{ .function_definition = function.* };
            const right: AST.Statement = .{ .function_definition = candidate.* };
            if (try equality.statement(&left, &right)) {
                try self.duplicates.put(function.name, candidate);
                return;
            }
        }
        try entry.value_ptr.append(self.allocator, function);
    }
};

test "equivalent function detector ignores local names" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a) -> r { r := add(a, 1) } function g(x) -> y { y := add(x, 1) } }",
        "equivalent.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var duplicates = try EquivalentFunctionDetector.run(allocator, ast.root());
    defer duplicates.deinit();
    try std.testing.expectEqual(@as(usize, 1), duplicates.count());
}
