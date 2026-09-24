// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Exact textual rendering of owned Yul ASTs.

const std = @import("std");
const common_data = @import("../libsolutil/common_data.zig");
const ASTModule = @import("ast.zig");
const Utilities = @import("utilities.zig");
const CharStreams = @import("../liblangutil/char_stream.zig");
const CharStreamProvider = @import("../liblangutil/char_stream_provider.zig").CharStreamProvider;
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;

const Stream = @import("asm_stream.zig");
pub const SourceIndexName = Stream.SourceIndexName;
pub const PrintError = Stream.PrintError;

pub const AsmPrinter = struct {
    allocator: std.mem.Allocator,
    dialect: ASTModule.Dialect,
    source_index_to_name: []const SourceIndexName = &.{},
    debug_info_selection: DebugInfoSelection = DebugInfoSelection.defaultValue(),
    solidity_source_provider: ?CharStreamProvider = null,
    last_location: SourceLocation = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        dialect: ASTModule.Dialect,
        source_index_to_name: []const SourceIndexName,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
    ) AsmPrinter {
        return .{
            .allocator = allocator,
            .dialect = dialect,
            .source_index_to_name = source_index_to_name,
            .debug_info_selection = debug_info_selection,
            .solidity_source_provider = solidity_source_provider,
        };
    }

    pub fn format(
        allocator: std.mem.Allocator,
        ast: *const ASTModule.AST,
        source_index_to_name: []const SourceIndexName,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
    ) PrintError![]u8 {
        var printer = AsmPrinter.init(
            allocator,
            ast.dialect().*,
            source_index_to_name,
            debug_info_selection,
            solidity_source_provider,
        );
        return printer.renderBlock(ast.root());
    }

    pub fn formatDefault(
        allocator: std.mem.Allocator,
        ast: *const ASTModule.AST,
    ) PrintError![]u8 {
        return format(allocator, ast, &.{}, DebugInfoSelection.defaultValue(), null);
    }

    pub fn renderExpression(self: *AsmPrinter, value: *const ASTModule.Expression) PrintError![]u8 {
        return self.render("expression", value);
    }

    pub fn renderStatement(self: *AsmPrinter, value: *const ASTModule.Statement) PrintError![]u8 {
        return self.render("statement", value);
    }

    pub fn renderLiteral(self: *AsmPrinter, value: *const ASTModule.Literal) PrintError![]u8 {
        return self.render("literal", value);
    }

    pub fn renderIdentifier(self: *AsmPrinter, value: *const ASTModule.Identifier) PrintError![]u8 {
        return self.render("identifier", value);
    }

    pub fn renderBuiltinName(self: *AsmPrinter, value: *const ASTModule.BuiltinName) PrintError![]u8 {
        return self.render("builtin", value);
    }

    pub fn renderExpressionStatement(self: *AsmPrinter, value: *const ASTModule.ExpressionStatement) PrintError![]u8 {
        return self.render("expressionStatement", value);
    }

    pub fn renderAssignment(self: *AsmPrinter, value: *const ASTModule.Assignment) PrintError![]u8 {
        return self.render("assignment", value);
    }

    pub fn renderVariableDeclaration(self: *AsmPrinter, value: *const ASTModule.VariableDeclaration) PrintError![]u8 {
        return self.render("variable", value);
    }

    pub fn renderFunctionDefinition(self: *AsmPrinter, value: *const ASTModule.FunctionDefinition) PrintError![]u8 {
        return self.render("function", value);
    }

    pub fn renderFunctionCall(self: *AsmPrinter, value: *const ASTModule.FunctionCall) PrintError![]u8 {
        return self.render("functionCall", value);
    }

    pub fn renderIf(self: *AsmPrinter, value: *const ASTModule.If) PrintError![]u8 {
        return self.render("branch", value);
    }

    pub fn renderSwitch(self: *AsmPrinter, value: *const ASTModule.Switch) PrintError![]u8 {
        return self.render("selectionStatement", value);
    }

    pub fn renderForLoop(self: *AsmPrinter, value: *const ASTModule.ForLoop) PrintError![]u8 {
        return self.render("loop", value);
    }

    pub fn renderBlock(self: *AsmPrinter, value: *const ASTModule.Block) PrintError![]u8 {
        return self.render("block", value);
    }

    fn render(self: *AsmPrinter, comptime method: []const u8, value: anytype) PrintError![]u8 {
        var bytes = std.Io.Writer.Allocating.init(self.allocator);
        defer bytes.deinit();
        var output: Stream.Output = .{ .writer = &bytes.writer };
        var renderer: Stream.Renderer = .{
            .output = &output,
            .dialect = self.dialect,
            .sources = self.source_index_to_name,
            .selection = self.debug_info_selection,
            .provider = self.solidity_source_provider,
            .last_location = self.last_location,
        };
        defer self.last_location = renderer.last_location;
        @call(.auto, @field(Stream.Renderer, method), .{ &renderer, value }) catch |err| switch (err) {
            error.WriteFailed => return error.OutOfMemory,
            error.LayoutLimit => unreachable, // Only private probes have a limit.
            error.MissingCode, error.MissingDebugData => return error.InvalidAST,
            else => |remaining| return remaining,
        };
        return bytes.toOwnedSlice();
    }
};

pub fn formatSourceLocation(
    allocator: std.mem.Allocator,
    location: SourceLocation,
    source_index_to_name: []const SourceIndexName,
    debug_info_selection: DebugInfoSelection,
    solidity_source_provider: ?CharStreamProvider,
) PrintError![]u8 {
    var output = std.Io.Writer.Allocating.init(allocator);
    defer output.deinit();
    writeSourceLocation(&output.writer, location, source_index_to_name, debug_info_selection, solidity_source_provider) catch |err| switch (err) {
        error.WriteFailed => return error.OutOfMemory,
        else => |remaining| return remaining,
    };
    return output.toOwnedSlice();
}

/// Stream annotation text into either an output buffer or the layout counter.
/// Source bytes are borrowed only during this call. Only the writer can allocate.
pub fn writeSourceLocation(
    writer: anytype,
    location: SourceLocation,
    source_index_to_name: []const SourceIndexName,
    debug_info_selection: DebugInfoSelection,
    solidity_source_provider: ?CharStreamProvider,
) !void {
    if (source_index_to_name.len == 0) return error.UnknownSourceName;
    if (debug_info_selection.snippet and !debug_info_selection.location) return error.InvalidAST;
    if (debug_info_selection.none()) return;

    var source_index: ?u32 = null;
    var snippet: ?CharStreams.SingleLineSnippet = null;
    if (location.source_name) |source_name| {
        for (source_index_to_name) |entry| {
            if (std.mem.eql(u8, source_name, entry.name)) {
                source_index = entry.index;
                break;
            }
        }
        if (source_index == null) return error.UnknownSourceName;
        if (debug_info_selection.snippet) {
            if (solidity_source_provider) |provider| {
                const stream = provider.charStream(source_name) catch return error.SourceNameMismatch;
                if (!stream.isImportedFromAST()) snippet = stream.singleLineSnippet(location);
            }
        }
    }

    var buffer: [64]u8 = undefined;
    const prefix = if (source_index) |index|
        std.fmt.bufPrint(&buffer, "@src {d}:{d}:{d}", .{ index, location.start, location.end }) catch unreachable // zlinter-disable-current-line no_swallow_error - 64 bytes fit the source index and both signed 32-bit offsets
    else
        std.fmt.bufPrint(&buffer, "@src -1:{d}:{d}", .{ location.start, location.end }) catch unreachable; // zlinter-disable-current-line no_swallow_error - 64 bytes fit the source index and both signed 32-bit offsets
    try writer.writeAll(prefix);
    if (snippet) |view| {
        try writer.writeAll("  \"");
        var comment: CommentWriter(@TypeOf(writer)) = .{ .writer = writer };
        try common_data.writeEscapedStringContent(&comment, view.prefix);
        if (view.truncated) try comment.writeAll("...");
        try comment.writeByte('"');
    }
}

/// Escapes comment terminators across both byte and slice writes. The adapter
/// borrows its writer synchronously and is discarded if a write fails.
fn CommentWriter(comptime Writer: type) type {
    return struct {
        const Self = @This();
        writer: Writer,
        previous_star: bool = false,

        pub fn writeByte(self: *Self, byte: u8) !void {
            if (byte == '/' and self.previous_star) try self.writer.writeByte('\\');
            try self.writer.writeByte(byte);
            self.previous_star = byte == '*';
        }

        pub fn writeAll(self: *Self, bytes: []const u8) !void {
            var start: usize = 0;
            for (bytes, 0..) |byte, index| {
                if (byte == '/' and self.previous_star) {
                    try self.writer.writeAll(bytes[start..index]);
                    try self.writer.writeAll("\\/");
                    start = index + 1;
                }
                self.previous_star = byte == '*';
            }
            try self.writer.writeAll(bytes[start..]);
        }
    };
}

test "source locations include escaped snippets and stable source indices" {
    const CharStream = @import("../liblangutil/char_stream.zig").CharStream;
    const Provider = @import("../liblangutil/char_stream_provider.zig").SingletonCharStreamProvider;
    const stream = CharStream.initBorrowed("alpha */ omega", "source.sol");
    const singleton = Provider.init(&stream);
    const provider = singleton.provider();
    const rendered = try formatSourceLocation(
        std.testing.allocator,
        .{ .start = 0, .end = 14, .source_name = "source.sol" },
        &.{.{ .index = 7, .name = "source.sol" }},
        .{ .location = true, .snippet = true },
        provider,
    );
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("@src 7:0:14  \"alpha *\\/ omega\"", rendered);
}

test "source locations preserve snippet bounds and byte escaping" {
    const CharStream = @import("../liblangutil/char_stream.zig").CharStream;
    const Provider = @import("../liblangutil/char_stream_provider.zig").SingletonCharStreamProvider;
    const allocator = std.testing.allocator;
    const Case = struct { source: []const u8 = "alpha */ omega\r\nnext", start: i32, end: i32, expected: []const u8 };
    const cases = [_]Case{
        .{ .start = 0, .end = 100, .expected = "\"alpha *\\/ omega...\"" },
        .{ .start = 0, .end = 14, .expected = "\"alpha *\\/ omega\"" },
        .{ .start = 6, .end = 8, .expected = "\"*\\/\"" },
        .{ .start = 7, .end = 9, .expected = "\"/ \"" },
        .{ .start = 5, .end = 5, .expected = "\"\"" },
        .{ .start = 14, .end = 16, .expected = "\"...\"" },
        .{ .start = 16, .end = 100, .expected = "\"next\"" },
        .{ .start = 20, .end = 25, .expected = "\"\"" },
        .{ .start = 3, .end = 2, .expected = "\"\"" },
        .{ .start = -1, .end = 4, .expected = "\"\"" },
        .{ .start = 0, .end = -1, .expected = "\"\"" },
        .{ .source = "x\\\"\t\x01\x7f\xc3\xa9 */ \nnext", .start = 0, .end = 100, .expected = "\"x\\\\\\\"\\t\\x01\\x7f\\xc3\\xa9 *\\/ ...\"" },
        .{ .source = "a" ** 63 ++ "*/ tail", .start = 0, .end = 100, .expected = "\"" ++ "a" ** 63 ++ "*\\/ tail\"" },
        .{ .source = "", .start = 0, .end = 1, .expected = "\"\"" },
    };
    for (cases) |case| {
        const stream = CharStream.initBorrowed(case.source, "source.sol");
        const singleton = Provider.init(&stream);
        const location: SourceLocation = .{ .start = case.start, .end = case.end, .source_name = "source.sol" };
        const rendered = try formatSourceLocation(allocator, location, &.{.{ .index = 7, .name = "source.sol" }}, .{ .location = true, .snippet = true }, singleton.provider());
        defer allocator.free(rendered);
        var expected_buffer: [256]u8 = undefined;
        const expected = try std.fmt.bufPrint(&expected_buffer, "@src 7:{d}:{d}  {s}", .{ case.start, case.end, case.expected });
        try std.testing.expectEqualStrings(expected, rendered);
    }
}

test "source locations validate providers before output and omit unavailable snippets" {
    const CharStream = @import("../liblangutil/char_stream.zig").CharStream;
    const Provider = @import("../liblangutil/char_stream_provider.zig").SingletonCharStreamProvider;
    var stream = CharStream.initBorrowed("source", "source.sol");
    const singleton = Provider.init(&stream);
    const names = &[_]SourceIndexName{.{ .index = 7, .name = "source.sol" }};
    const location: SourceLocation = .{ .start = 0, .end = 6, .source_name = "source.sol" };
    const selection: DebugInfoSelection = .{ .location = true, .snippet = true };
    var buffer: [128]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buffer);
    try writeSourceLocation(&writer, location, names, selection, null);
    try std.testing.expectEqualStrings("@src 7:0:6", writer.buffered());
    writer.end = 0;
    stream.imported_from_ast = true;
    try writeSourceLocation(&writer, location, names, selection, singleton.provider());
    try std.testing.expectEqualStrings("@src 7:0:6", writer.buffered());
    writer.end = 0;
    try writeSourceLocation(&writer, .{}, names, selection, singleton.provider());
    try std.testing.expectEqualStrings("@src -1:-1:-1", writer.buffered());
    writer.end = 0;
    try std.testing.expectError(error.UnknownSourceName, writeSourceLocation(&writer, location, &.{}, selection, singleton.provider()));
    try std.testing.expectError(error.UnknownSourceName, writeSourceLocation(&writer, .{ .source_name = "other.sol" }, names, selection, singleton.provider()));
    try std.testing.expectError(error.InvalidAST, writeSourceLocation(&writer, location, names, .{ .snippet = true }, singleton.provider()));
    stream.name_bytes = "other.sol";
    try std.testing.expectError(error.SourceNameMismatch, writeSourceLocation(&writer, location, names, selection, singleton.provider()));
    try std.testing.expectEqual(@as(usize, 0), writer.buffered().len);
    try writeSourceLocation(&writer, location, names, .{}, singleton.provider());
    try std.testing.expectEqual(@as(usize, 0), writer.buffered().len);
}

test "source locations stream snippets into bounded writers and layout counters" {
    const Provider = @import("../liblangutil/char_stream_provider.zig").SingletonCharStreamProvider;
    const stream = CharStreams.CharStream.initBorrowed("ab */ \\\"\t\xff\r\nmore", "source.sol");
    const singleton = Provider.init(&stream);
    const names = &[_]SourceIndexName{.{ .index = 7, .name = "source.sol" }};
    const location: SourceLocation = .{ .start = 0, .end = 100, .source_name = "source.sol" };
    const selection: DebugInfoSelection = .{ .location = true, .snippet = true };
    const expected = "@src 7:0:100  \"ab *\\/ \\\\\\\"\\t\\xff...\"";
    var buffer: [128]u8 = undefined;
    for (0..expected.len + 1) |capacity| {
        var writer = std.Io.Writer.fixed(buffer[0..capacity]);
        if (capacity < expected.len) {
            try std.testing.expectError(error.WriteFailed, writeSourceLocation(&writer, location, names, selection, singleton.provider()));
            try std.testing.expect(std.mem.startsWith(u8, expected, writer.buffered()));
        } else {
            try writeSourceLocation(&writer, location, names, selection, singleton.provider());
            try std.testing.expectEqualStrings(expected, writer.buffered());
        }
    }
    var counter: Stream.Output = .{};
    try writeSourceLocation(&counter, location, names, selection, singleton.provider());
    try std.testing.expectEqual(expected.len, counter.count);
    for (0..expected.len + 2) |limit| {
        counter = .{ .limit = limit };
        if (limit <= expected.len) {
            try std.testing.expectError(error.LayoutLimit, writeSourceLocation(&counter, location, names, selection, singleton.provider()));
        } else {
            try writeSourceLocation(&counter, location, names, selection, singleton.provider());
            try std.testing.expectEqual(expected.len, counter.count);
        }
    }

    var writer = std.Io.Writer.fixed(&buffer);
    var comment: CommentWriter(*std.Io.Writer) = .{ .writer = &writer };
    try comment.writeAll("**");
    try comment.writeByte('/');
    try comment.writeByte('*');
    try comment.writeAll("/");
    try comment.writeAll("**/ / */");
    try std.testing.expectEqualStrings("**\\/*\\/**\\/ / *\\/", writer.buffered());
}

test "printer renders compact and multiline blocks with recursive ownership" {
    const allocator = std.testing.allocator;
    const x = try @import("yul_name.zig").YulName.init("x");
    var root: ASTModule.Block = .{};
    const value = try ASTModule.createExpression(allocator, .{
        .literal = .{ .kind = .Number, .value = try Utilities.valueOfNumberLiteral(allocator, "1") },
    });
    try root.statements.append(allocator, .{
        .variable_declaration = .{
            .variables = blk: {
                var variables: ASTModule.NameWithDebugDataList = .empty;
                try variables.append(allocator, .{ .name = x });
                break :blk variables;
            },
            .value = value,
        },
    });
    var ast = ASTModule.AST.init(allocator, .{}, root);
    defer ast.deinit();
    const rendered = try AsmPrinter.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expectEqualStrings("{ let x := 1 }", rendered);
}
