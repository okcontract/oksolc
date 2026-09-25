// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Append generated statements in place, transferring child storage within one
//! arena. No presentation data, cloning or AST traversal is required.
const std = @import("std");
const AST = @import("ast.zig");
const Builder = @import("ast_builder.zig").Builder;
const Template = @import("ast_template.zig");

pub const Buffer = struct {
    generator: Builder,
    block: AST.Block = .{},

    pub fn append(self: *Buffer, fragment: AST.Block) std.mem.Allocator.Error!void {
        if (self.block.statements.items.len == 0) {
            self.block.statements.deinit(self.generator.allocator());
            self.block.statements = fragment.statements;
        } else {
            try self.block.statements.appendSlice(self.generator.allocator(), fragment.statements.items);
            // Release the consumed fragment's container, never its child nodes.
            var container = fragment.statements;
            container.deinit(self.generator.allocator());
        }
    }

    pub fn add(self: *Buffer, comptime source: []const u8, arguments: anytype) Template.Error!void {
        try self.append(try self.generator.statements(source, arguments));
    }

    pub fn take(self: *Buffer) AST.Block {
        const result = self.block;
        self.block = .{};
        return result;
    }
};

test "Yul AST statement buffer transfers child storage" {
    const Dialect = @import("backends/evm/evm_dialect.zig").EVMDialect;
    var dialect = try Dialect.init(std.testing.allocator, .current(), true);
    defer dialect.deinit();
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const builder = Builder.init(&arena, dialect.dialect());
    var body: Buffer = .{ .generator = builder };
    const call = try builder.expression("add(@0, 1)", .{@as(u32, 65536)});
    try body.add("ret := @0", .{call});
    try body.add("leave", .{});
    const fragment = try builder.statements("function f() -> ret { @0 }", .{body.take()});
    const value = fragment.statements.items[0].function_definition.body.statements.items[0].assignment.value.?.function_call;
    try std.testing.expect(value.arguments.items.ptr == call.function_call.arguments.items.ptr);
    try std.testing.expectEqualStrings("65536", value.arguments.items[0].literal.value.string_value.?);
    try std.testing.expectEqual(@as(usize, 0), body.block.statements.items.len);
}
