// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Immutable optimized Yul, independent of the producing request and
//! global string repository. Native generated-text positions are not retained.
//! Materialization re-interns identifiers and borrows the receiving object's
//! source names; no reference to this snapshot escapes into the returned AST.

const std = @import("std");
const AST = @import("ast.zig");
const Object = @import("object.zig");
const ASTCopier = @import("optimiser/ast_copier.zig").ASTCopier;
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const YulString = @import("yul_string.zig");
const YulName = @import("yul_name.zig").YulName;
const Normalizer = @import("solidity_debug_normalizer.zig");

pub const Snapshot = struct {
    arena: std.heap.ArenaAllocator,
    names: YulString.Repository,
    root: AST.Block,

    /// The stable allocation owns the arena allocator context used by all
    /// nodes and private interned names. Publish only after construction.
    pub fn create(allocator: std.mem.Allocator, root: *const AST.Block, normalize: bool) !*Snapshot {
        const self = try init(allocator);
        errdefer self.destroy(allocator);
        var copier = ASTCopier.initWithHooks(self.arena.allocator(), self, .{
            .translate_identifier = captureName,
            .translate_debug_data = captureDebugData,
        });
        self.root = try copier.translateBlock(root);
        if (normalize) Normalizer.normalizeBlock(&self.root);
        return self;
    }

    fn init(allocator: std.mem.Allocator) !*Snapshot {
        const self = try allocator.create(Snapshot);
        errdefer allocator.destroy(self);
        self.arena = .init(allocator);
        errdefer self.arena.deinit();
        self.names = try YulString.Repository.init(self.arena.allocator());
        self.root = .{};
        return self;
    }

    pub fn decode(allocator: std.mem.Allocator, encoded: []const u8, dialect: AST.Dialect) !*Snapshot {
        const self = try init(allocator);
        errdefer self.destroy(allocator);
        self.root = try @import("ast_encoding.zig").decodeStoredBlock(&self.arena, &self.names, encoded, dialect);
        return self;
    }

    pub fn destroy(self: *Snapshot, allocator: std.mem.Allocator) void {
        self.arena.deinit();
        allocator.destroy(self);
    }

    pub fn residentBytes(self: *const Snapshot) usize {
        return @sizeOf(Snapshot) + self.arena.queryCapacity();
    }

    pub fn materialize(self: *const Snapshot, object: *const Object.Object, dialect: AST.Dialect) !AST.AST {
        const debug = if (object.debug_data) |*value| value else return error.MissingObjectDebugData;
        var context: Materialization = .{ .source_names = if (debug.source_names) |*names| names else null };
        var copier = ASTCopier.initWithHooks(object.allocator, &context, .{
            .translate_identifier = Materialization.translateName,
            .translate_debug_data = Materialization.translateDebugData,
        });
        // Do not retain a dialect pointer in the snapshot: EVM dialects can be
        // reset along with the global name repository between compilations.
        return AST.AST.init(object.allocator, dialect, try copier.translateBlock(&self.root));
    }

    fn captureName(context: ?*anyopaque, name: YulName) !YulName {
        const self: *Snapshot = @ptrCast(@alignCast(context.?));
        return .{ .handle = try self.names.stringToHandle(try name.str()) };
    }

    fn captureDebugData(context: ?*anyopaque, data: ?DebugData) !?DebugData {
        var result = data orelse return null;
        const self: *Snapshot = @ptrCast(@alignCast(context.?));
        result.native_location = .{};
        if (result.origin_location.source_name) |name| {
            const owned: YulName = .{ .handle = try self.names.stringToHandle(name) };
            result.origin_location.source_name = try owned.str();
        }
        return result;
    }

    const Materialization = struct {
        source_names: ?*const Object.SourceNameMap,

        fn translateName(_: ?*anyopaque, name: YulName) !YulName {
            return YulName.init(try name.str());
        }

        fn translateDebugData(context: ?*anyopaque, data: ?DebugData) !?DebugData {
            var result = data orelse return null;
            const self: *const Materialization = @ptrCast(@alignCast(context.?));
            const names = self.source_names orelse {
                // Native Yul has no origin table. Its canonical native/origin
                // offsets are projected by YulStack after optimization.
                result.origin_location = .{};
                return result;
            };
            if (result.origin_location.source_name) |name| {
                for (names.entries.items) |entry| {
                    if (std.mem.eql(u8, name, entry.name)) {
                        result.origin_location.source_name = entry.name;
                        return result;
                    }
                }
                return error.UnknownStructuredYulSource;
            }
            return result;
        }
    };
};

test "structured Yul snapshot owns names across repository reset and eviction" {
    const Parser = @import("object_parser.zig").ObjectParser;
    const Dialect = @import("backends/evm/evm_dialect.zig");
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const Printer = @import("asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const source =
        \\/// @use-src 0:"input.sol"
        \\object "Root" { code { /// @src 0:1:20
        \\ let x := "hello" mstore(0, x)
        \\} }
    ;
    const producer = (try Parser.parseSource(allocator, source, "generated.yul", &reporter, (try Dialect.strictAssemblyForEVMObjects(.current())).dialect())).?;
    var producer_owned = true;
    defer if (producer_owned) producer.destroy();
    const expected = try Printer.formatDefault(allocator, producer.code().?);
    defer allocator.free(expected);
    const snapshot = try Snapshot.create(allocator, producer.code().?.root(), true);
    var snapshot_owned = true;
    defer if (snapshot_owned) snapshot.destroy(allocator);
    const original_name = producer.code().?.root().statements.items[0].variable_declaration.variables.items[0].name;
    const stored_name = snapshot.root.statements.items[0].variable_declaration.variables.items[0].name;
    try std.testing.expect(original_name.handle.entry != stored_name.handle.entry);
    try std.testing.expect(snapshot.residentBytes() > @sizeOf(Snapshot));
    producer.destroy();
    producer_owned = false;
    try YulString.reset();

    const consumer = try Object.Object.create(allocator, "Consumer");
    defer consumer.destroy();
    consumer.debug_data = .{ .source_names = .{} };
    const dialect = (try Dialect.strictAssemblyForEVMObjects(.current())).dialect();
    try std.testing.expectError(error.UnknownStructuredYulSource, snapshot.materialize(consumer, dialect));
    try consumer.debug_data.?.source_names.?.put(allocator, 0, "input.sol");
    var materialized = try snapshot.materialize(consumer, dialect);
    defer materialized.deinit();
    snapshot.destroy(allocator);
    snapshot_owned = false;
    const actual = try Printer.formatDefault(allocator, &materialized);
    defer allocator.free(actual);
    try std.testing.expectEqualStrings(expected, actual);
    try std.testing.expect(materialized.root().debug_data.?.native_location.source_name == null);
}

test "structured Yul snapshot capture and materialization clean up every allocation failure" {
    const Parser = @import("asm_parser.zig").Parser;
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator, "{ let x := \"hello\" function f(a) -> r { r := a } }", "input.sol", &reporter, .{}, .{})).?;
    defer ast.deinit();
    const Helper = struct {
        fn check(failing: std.mem.Allocator, root: *const AST.Block) !void {
            const snapshot = try Snapshot.create(failing, root, true);
            defer snapshot.destroy(failing);
            const consumer = try Object.Object.create(failing, "Consumer");
            defer consumer.destroy();
            consumer.debug_data = .{ .source_names = .{} };
            try consumer.debug_data.?.source_names.?.put(failing, 0, "input.sol");
            var result = try snapshot.materialize(consumer, .{});
            defer result.deinit();
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Helper.check, .{ast.root()});
}
