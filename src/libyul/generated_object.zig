// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Request-local, immutable generated Yul object graphs. Each owner has one
//! stable arena for its own creation/deployed objects. Dependency objects are
//! borrowed from earlier owners in the same request, without cloning their ASTs.
//! The request keeps every owner and its Solidity sources alive until all users
//! finish. Do not destroy nodes individually or mutate a published graph.
//!
//! A backend materializes an independent mutable Object tree with ASTCopier.
//! That tree owns its source names and can outlive this graph (within the same
//! Yul name-repository epoch). This replaces the former parser traversal.

const std = @import("std");
const AST = @import("ast.zig");
const Objects = @import("object.zig");
const ASTCopier = @import("optimiser/ast_copier.zig").ASTCopier;
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const CharStreamProvider = @import("../liblangutil/char_stream_provider.zig").CharStreamProvider;

pub const GeneratedObject = struct {
    arena: std.heap.ArenaAllocator,
    root: ?*const Objects.Object = null,

    pub fn create(allocator: std.mem.Allocator) !*GeneratedObject {
        const result = try allocator.create(GeneratedObject);
        result.* = .{ .arena = .init(allocator) };
        return result;
    }

    pub fn destroy(self: *GeneratedObject, allocator: std.mem.Allocator) void {
        // Borrowed dependency edges must not be followed during destruction.
        self.arena.deinit();
        allocator.destroy(self);
    }

    pub fn render(self: *const GeneratedObject, output_allocator: std.mem.Allocator, selection: DebugInfoSelection, source_provider: ?CharStreamProvider) ![]u8 {
        return self.root.?.formatIRAlloc(output_allocator, selection, source_provider);
    }

    pub fn materialize(self: *const GeneratedObject, allocator: std.mem.Allocator) !*Objects.Object {
        return copyObject(allocator, self.root.?);
    }

    fn copyObject(allocator: std.mem.Allocator, source: *const Objects.Object) anyerror!*Objects.Object {
        const result = try Objects.Object.create(allocator, source.name);
        errdefer result.destroy();
        result.debug_data = .{ .source_names = .{} };
        if (source.debug_data) |debug| if (debug.source_names) |names| {
            for (names.entries.items) |entry|
                try result.debug_data.?.source_names.?.put(allocator, entry.index, entry.name);
        };
        var copier = ASTCopier.initWithHooks(allocator, &result.debug_data.?.source_names.?, .{
            .translate_debug_data = rebindDebugData,
        });
        result.setCode(try copier.translateAst(source.code() orelse return error.MissingCode), null);
        try result.sub_objects.ensureTotalCapacityPrecise(allocator, source.sub_objects.items.len);
        for (source.sub_objects.items) |node| {
            var owned: Objects.ObjectNode = switch (node) {
                .object => |child| .{ .object = try copyObject(allocator, child) },
                .data => |data| .{ .data = try Objects.Data.init(allocator, data.name, data.data) },
            };
            errdefer owned.deinit(allocator);
            try result.addSubObject(owned);
        }
        return result;
    }

    fn rebindDebugData(context: ?*anyopaque, data: ?DebugData) !?DebugData {
        var result = data orelse return null;
        const names: *const Objects.SourceNameMap = @ptrCast(@alignCast(context.?));
        result.native_location = .{};
        if (result.origin_location.source_name) |name| {
            for (names.entries.items) |entry| if (std.mem.eql(u8, entry.name, name)) {
                result.origin_location.source_name = entry.name;
                return result;
            };
            return error.UnknownGeneratedYulSource;
        }
        return result;
    }
};

test "Yul AST generated objects share dependencies and isolate mutable consumers" {
    const Builder = @import("ast_builder.zig").Builder;
    const Dialect = @import("backends/evm/evm_dialect.zig");
    const allocator = std.testing.allocator;
    const dialect = (try Dialect.strictAssemblyForEVMObjects(.current())).dialect();
    const dependency = try GeneratedObject.create(allocator);
    defer dependency.destroy(allocator);
    const child = try Objects.Object.create(dependency.arena.allocator(), "Child");
    child.debug_data = .{ .source_names = .{} };
    child.setCode(AST.AST.init(dependency.arena.allocator(), dialect, try Builder.init(&dependency.arena, dialect).statements("stop()", .{})), null);
    dependency.root = child;
    const parent = try GeneratedObject.create(allocator);
    var parent_owned = true;
    defer if (parent_owned) parent.destroy(allocator);
    const object = try Objects.Object.create(parent.arena.allocator(), "Parent");
    object.debug_data = .{ .source_names = .{} };
    try object.debug_data.?.source_names.?.put(parent.arena.allocator(), 0, "C.sol");
    const generator = Builder.init(&parent.arena, dialect).withDebug(.{ .origin_location = .{ .start = 1, .end = 5, .source_name = object.debug_data.?.source_names.?.entries.items[0].name } });
    object.setCode(AST.AST.init(parent.arena.allocator(), dialect, try generator.statements("stop()", .{})), null);
    try object.addSubObject(.{ .object = child });
    parent.root = object;
    const consumer = try parent.materialize(allocator);
    defer consumer.destroy();
    try std.testing.expect(object.sub_objects.items[0].object == child);
    try std.testing.expect(consumer.sub_objects.items[0].object != child);
    try std.testing.expect(consumer.code().?.root().statements.items.ptr != object.code().?.root().statements.items.ptr);
    const allocated_before = parent.arena.queryCapacity();
    const text = try parent.render(allocator, .defaultValue(), null);
    defer allocator.free(text);
    try std.testing.expectEqual(allocated_before, parent.arena.queryCapacity());
    parent.destroy(allocator);
    parent_owned = false;
    try std.testing.expectEqualStrings("C.sol", consumer.code().?.root().debug_data.?.origin_location.source_name.?);
    consumer.sub_objects.items[0].object.sub_id = .{ .value = 7 };
    try std.testing.expect(child.sub_id.value != 7);
}

test "Yul AST generated object construction and materialization release allocation failures" {
    const Builder = @import("ast_builder.zig").Builder;
    const Dialect = @import("backends/evm/evm_dialect.zig");
    const dialect = (try Dialect.strictAssemblyForEVMObjects(.current())).dialect();
    const Check = struct {
        fn run(allocator: std.mem.Allocator, dialect_value: AST.Dialect) !void {
            const owner = try GeneratedObject.create(allocator);
            defer owner.destroy(allocator);
            const arena = owner.arena.allocator();
            const object = try Objects.Object.create(arena, "Root");
            object.debug_data = .{ .source_names = .{} };
            try object.debug_data.?.source_names.?.put(arena, 0, "C.sol");
            const generator = Builder.init(&owner.arena, dialect_value).withDebug(.{ .origin_location = .{ .start = 0, .end = 1, .source_name = "C.sol" } });
            object.setCode(AST.AST.init(arena, dialect_value, try generator.statements("let x := 1 pop(x)", .{})), null);
            try object.addSubObject(.{ .data = try Objects.Data.init(arena, ".metadata", "data") });
            owner.root = object;
            const consumer = try owner.materialize(allocator);
            defer consumer.destroy();
            const rendered = try owner.render(allocator, .defaultValue(), null);
            defer allocator.free(rendered);
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{dialect});
}

test "Yul AST generated object rendering retains bytes beyond input owners" {
    const Builder = @import("ast_builder.zig").Builder;
    const Dialect = @import("backends/evm/evm_dialect.zig");
    const CharStream = @import("../liblangutil/char_stream.zig").CharStream;
    const Provider = @import("../liblangutil/char_stream_provider.zig").SingletonCharStreamProvider;
    const allocator = std.testing.allocator;
    const dialect = (try Dialect.strictAssemblyForEVMObjects(.current())).dialect();
    const Fixture = struct {
        const source = "/* marker */ let x = 1;";

        fn create(backing: std.mem.Allocator, selected_dialect: AST.Dialect) !*GeneratedObject {
            const owner = try GeneratedObject.create(backing);
            errdefer owner.destroy(backing);
            const arena = owner.arena.allocator();
            const object = try Objects.Object.create(arena, "Root");
            object.debug_data = .{ .source_names = .{} };
            try object.debug_data.?.source_names.?.put(arena, 0, "C.sol");
            const generator = Builder.init(&owner.arena, selected_dialect).withDebug(.{ .origin_location = .{
                .start = 0,
                .end = source.len,
                .source_name = object.debug_data.?.source_names.?.entries.items[0].name,
            } });
            object.setCode(AST.AST.init(arena, selected_dialect, try generator.statements("let x := 1 pop(x)", .{})), null);
            try object.addSubObject(.{ .data = try Objects.Data.init(arena, ".metadata", &([_]u8{0xaa} ** 256)) });
            owner.root = object;
            return owner;
        }

        fn check(failing: std.mem.Allocator, selected_dialect: AST.Dialect, selection: DebugInfoSelection, expected: []const u8, fail_output: bool) !void {
            const scratch = if (fail_output) std.testing.allocator else failing;
            const output = if (fail_output) failing else std.testing.allocator;
            const rendered = blk: {
                const owner = try create(scratch, selected_dialect);
                defer owner.destroy(scratch);
                var stream = try CharStream.initOwned(scratch, source, "C.sol", false);
                defer stream.deinit();
                const provider = Provider.init(&stream);
                break :blk try owner.render(output, selection, provider.provider());
            };
            defer output.free(rendered);
            // The object, source text and provider have all been destroyed.
            try std.testing.expectEqualStrings(expected, rendered);
        }
    };
    const reference = try Fixture.create(allocator, dialect);
    defer reference.destroy(allocator);
    const stream = CharStream.initBorrowed(Fixture.source, "C.sol");
    const provider = Provider.init(&stream);
    for ([_]DebugInfoSelection{ .noneValue(), .defaultValue(), .allValue(true) }) |selection| {
        const body = try reference.root.?.formatAlloc(allocator, selection, provider.provider());
        defer allocator.free(body);
        const expected = try std.fmt.allocPrint(allocator, "{s}{s}\n", .{ if (selection.ethdebug) "/// ethdebug: enabled\n" else "", body });
        defer allocator.free(expected);
        for ([_]bool{ false, true }) |fail_output|
            try std.testing.checkAllAllocationFailures(allocator, Fixture.check, .{ dialect, selection, expected, fail_output });
        const rendered = try reference.render(allocator, selection, provider.provider());
        defer allocator.free(rendered);
        try std.testing.expectEqualStrings(expected, rendered);
    }
}
