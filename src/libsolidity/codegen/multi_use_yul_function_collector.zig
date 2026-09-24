// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Generate-once Yul function collector translated from
//! `MultiUseYulFunctionCollector.cpp`.

const std = @import("std");
const YulAST = @import("../../libyul/ast.zig");
const Template = @import("../../libyul/ast_template.zig");
const Printer = @import("../../libyul/asm_printer.zig");
const Builder = @import("../../libyul/ast_builder.zig").Builder;
const EVMDialect = @import("../../libyul/backends/evm/evm_dialect.zig").EVMDialect;
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;

pub const CollectorError = Template.Error || Printer.PrintError || error{
    InvalidDialect,
    EmptyFunctionName,
    ImproperFunctionName,
};

pub const MultiUseYulFunctionCollector = struct {
    allocator: std.mem.Allocator,
    requested_functions: std.array_hash_map.String(void) = .empty,
    arena: std.heap.ArenaAllocator,
    /// Optional enclosing object owner. Never reset or free this borrowed arena.
    output_arena: ?*std.heap.ArenaAllocator = null,
    dialect: ?EVMDialect = null,
    generated: std.ArrayList(YulAST.FunctionDefinition) = .empty,
    /// Source origin inherited by the next completed helper. Source-written
    /// function producers advance this explicitly at their semantic boundary.
    function_origin: SourceLocation = .{},

    pub fn init(allocator: std.mem.Allocator) MultiUseYulFunctionCollector {
        return .{ .allocator = allocator, .arena = std.heap.ArenaAllocator.init(allocator) };
    }

    pub fn deinit(self: *MultiUseYulFunctionCollector) void {
        self.clearRequestedNames();
        self.requested_functions.deinit(self.allocator);
        self.generated.deinit(self.allocator);
        self.arena.deinit();
        if (self.dialect) |*dialect| dialect.deinit();
        self.* = undefined;
    }

    fn constructionArena(self: *MultiUseYulFunctionCollector) *std.heap.ArenaAllocator {
        return self.output_arena orelse &self.arena;
    }

    pub fn generator(self: *MultiUseYulFunctionCollector, version: EVMVersion) CollectorError!Builder {
        if (self.dialect == null) self.dialect = EVMDialect.init(self.allocator, version, true) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.InvalidDialect,
        };
        std.debug.assert(self.dialect.?.evm_version.version == version.version);
        return Builder.init(self.constructionArena(), self.dialect.?.dialect());
    }

    pub fn finishGeneratedFunction(self: *MultiUseYulFunctionCollector, name: []const u8, definition: YulAST.FunctionDefinition) CollectorError!void {
        if (!self.contains(name)) return error.ImproperFunctionName;
        if (!std.mem.eql(u8, definition.name.str() catch return error.ImproperFunctionName, name))
            return error.ImproperFunctionName;
        var owned = definition;
        if (owned.debug_data == null and self.function_origin.isValid())
            owned.debug_data = .{ .origin_location = self.function_origin };
        try self.generated.append(self.allocator, owned);
    }

    /// Move the completed definitions into a code block. The collector arena
    /// remains alive until its enclosing code object has been consumed.
    pub fn takeGeneratedFunctions(self: *MultiUseYulFunctionCollector) CollectorError!YulAST.Block {
        var result: YulAST.Block = .{};
        try result.statements.ensureTotalCapacityPrecise(self.constructionArena().allocator(), self.generated.items.len);
        for (self.generated.items) |entry|
            result.statements.appendAssumeCapacity(.{ .function_definition = entry });
        self.clearRequestedNames();
        self.requested_functions.clearRetainingCapacity();
        self.generated.clearRetainingCapacity();
        return result;
    }

    pub fn contains(self: *const MultiUseYulFunctionCollector, name: []const u8) bool {
        return self.requested_functions.contains(name);
    }

    /// Register before requesting nested helpers. A true result transfers
    /// responsibility to call either `finishGeneratedFunction` or
    /// `abortFunction`.
    pub fn beginFunction(
        self: *MultiUseYulFunctionCollector,
        name: []const u8,
    ) (std.mem.Allocator.Error || error{EmptyFunctionName})!bool {
        if (name.len == 0) return error.EmptyFunctionName;
        return self.register(name);
    }

    pub fn abortFunction(self: *MultiUseYulFunctionCollector, name: []const u8) void {
        self.unregister(name);
    }

    pub fn copyFunctionName(
        self: *const MultiUseYulFunctionCollector,
        name: []const u8,
    ) std.mem.Allocator.Error![]u8 {
        return self.allocator.dupe(u8, name);
    }

    /// Test projection only. Production callers move the definitions directly.
    pub fn testFunctionsAlloc(self: *MultiUseYulFunctionCollector) CollectorError![]u8 {
        if (!@import("builtin").is_test) @compileError("function text is a test-only projection");
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        var printer = Printer.AsmPrinter.init(self.allocator, self.dialect.?.dialect(), &.{}, .noneValue(), null);
        for (self.generated.items) |definition| {
            const text = try printer.renderFunctionDefinition(&definition);
            defer self.allocator.free(text);
            try output.append(self.allocator, '\n');
            try output.appendSlice(self.allocator, text);
            try output.append(self.allocator, '\n');
        }
        const result = try output.toOwnedSlice(self.allocator);
        self.clearRequestedNames();
        self.requested_functions.clearRetainingCapacity();
        self.generated.clearRetainingCapacity();
        std.debug.assert(self.output_arena == null);
        _ = self.arena.reset(.free_all);
        return result;
    }

    fn register(self: *MultiUseYulFunctionCollector, name: []const u8) !bool {
        if (self.contains(name)) return false;
        const owned_name = try self.allocator.dupe(u8, name);
        errdefer self.allocator.free(owned_name);
        try self.requested_functions.put(self.allocator, owned_name, {});
        return true;
    }

    fn unregister(self: *MultiUseYulFunctionCollector, name: []const u8) void {
        if (self.requested_functions.fetchOrderedRemove(name)) |removed|
            self.allocator.free(removed.key);
    }

    fn clearRequestedNames(self: *MultiUseYulFunctionCollector) void {
        for (self.requested_functions.keys()) |name| self.allocator.free(name);
    }
};

test "Yul AST collector transfers definitions without copying or resetting their arena" {
    var collector = MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    const generator_value = try collector.generator(.current());
    const origin: SourceLocation = .{ .start = 1, .end = 20, .source_name = "C.sol" };
    collector.function_origin = origin;
    try std.testing.expect(try collector.beginFunction("outer"));
    try std.testing.expect(try collector.beginFunction("inner"));
    const inner = try generator_value.functionDefinition("function inner(x) -> y { y := add(x, 1) }", .{});
    try collector.finishGeneratedFunction("inner", inner);
    try collector.finishGeneratedFunction("outer", try generator_value.functionDefinition("function outer() { pop(inner(2)) }", .{}));
    try std.testing.expect(!(try collector.beginFunction("outer")));
    try std.testing.expectError(error.ImproperFunctionName, collector.finishGeneratedFunction("outer", inner));
    const capacity = collector.arena.queryCapacity();
    const result = try collector.takeGeneratedFunctions();
    try std.testing.expectEqual(@as(usize, 2), result.statements.items.len);
    const transferred = result.statements.items[0].function_definition;
    try std.testing.expect(transferred.body.statements.items.ptr == inner.body.statements.items.ptr);
    try std.testing.expect(transferred.debug_data.?.origin_location.eql(origin));
    try std.testing.expect(collector.arena.queryCapacity() >= capacity);
    try std.testing.expect(!collector.contains("outer"));
    try std.testing.expectEqual(@as(usize, 0), collector.generated.items.len);
    try std.testing.expect(try collector.beginFunction("outer"));
    collector.abortFunction("outer");
}

test "Yul AST collector releases partial construction on allocation failure" {
    var dialect = try EVMDialect.init(std.testing.allocator, .current(), true);
    defer dialect.deinit();
    const Check = struct {
        fn run(allocator: std.mem.Allocator, dialect_value: *const EVMDialect) !void {
            var collector = MultiUseYulFunctionCollector.init(allocator);
            defer collector.deinit();
            if (try collector.beginFunction("f")) {
                errdefer collector.abortFunction("f");
                const builder = Builder.init(&collector.arena, dialect_value.dialect());
                try collector.finishGeneratedFunction("f", try builder.functionDefinition("function @0(x) -> y { y := add(x, 1) }", .{"f"}));
            }
            try std.testing.expect(collector.contains("f"));
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{&dialect});
}
