// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! One streaming layout for Yul output and bounded layout probes. Probes keep
//! only a byte counter and copied annotation state, never a presentation tree.

const std = @import("std");
const AST = @import("ast.zig");
const Objects = @import("object.zig");
const CommonData = @import("../libsolutil/common_data.zig");
const Utilities = @import("utilities.zig");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;
const CharStreamProvider = @import("../liblangutil/char_stream_provider.zig").CharStreamProvider;

pub const SourceIndexName = Objects.SourceNameEntry;
pub const PrintError = std.mem.Allocator.Error || error{ InvalidAST, InvalidYulStringHandle, UnknownBuiltin, UnknownSourceName, SourceNameMismatch };
pub const Error = PrintError || std.Io.Writer.Error || error{ LayoutLimit, MissingCode, MissingDebugData };

/// A null writer counts without retaining bytes. Layout probes stop at their
/// first newline or length limit, before visiting the remainder of a subtree.
pub const Output = struct {
    writer: ?*std.Io.Writer = null,
    indent: usize = 0,
    line_start: bool = false,
    count: usize = 0,
    limit: ?usize = null,
    stop_at_newline: bool = false,

    pub fn writeAll(self: *Output, text: []const u8) Error!void {
        var remaining = text;
        while (std.mem.findScalar(u8, remaining, '\n')) |index| {
            try self.flat(remaining[0..index]);
            try self.newline();
            remaining = remaining[index + 1 ..];
        }
        try self.flat(remaining);
    }

    pub fn writeByte(self: *Output, byte: u8) Error!void {
        return self.writeAll(&.{byte});
    }

    fn advance(self: *Output, len: usize) Error!void {
        const next = std.math.add(usize, self.count, len) catch return error.OutOfMemory;
        if (self.limit) |limit| if (next >= limit) return error.LayoutLimit;
        self.count = next;
    }

    fn flat(self: *Output, text: []const u8) Error!void {
        if (text.len == 0) return;
        try self.indentation();
        try self.advance(text.len);
        if (self.writer) |writer| try writer.writeAll(text);
    }

    pub fn indentation(self: *Output) Error!void {
        if (!self.line_start) return;
        self.line_start = false;
        try self.advance(self.indent);
        if (self.writer) |writer| try writer.splatByteAll(' ', self.indent);
    }

    pub fn newline(self: *Output) Error!void {
        if (self.stop_at_newline) return error.LayoutLimit;
        try self.advance(1);
        if (self.writer) |writer| try writer.writeByte('\n');
        self.line_start = true;
    }

    pub fn integer(self: *Output, value: anytype) Error!void {
        var buffer: [80]u8 = undefined; // All signed source IDs and u256 literals fit.
        const rendered = std.fmt.bufPrint(&buffer, "{d}", .{value}) catch unreachable; // zlinter-disable-current-line no_swallow_error - 80 bytes fit every supported integer up to u256
        try self.writeAll(rendered);
    }
};

pub const Renderer = Render(false);

/// Reconstruct canonical native offsets on the existing owned tree. Source
/// names remain borrowed from the stack's input stream. No program text or
/// second AST is allocated. Failure leaves the stack unanalysed.
pub fn projectObject(
    value: *Objects.Object,
    source_name: []const u8,
    selection: DebugInfoSelection,
    provider: ?CharStreamProvider,
) Error!usize {
    var output: Output = .{};
    if (selection.ethdebug) try output.writeAll("/// ethdebug: enabled\n");
    var renderer: Render(true) = .{
        .output = &output,
        .dialect = .{},
        .selection = selection,
        .provider = provider,
        .projection = .{ .source_name = source_name },
    };
    try renderer.object(value);
    try output.newline();
    return output.count;
}

const Projection = struct {
    source_name: []const u8,
    mapped: bool = false,
    parsed_location: SourceLocation = .{},
    pending_location: ?SourceLocation = null,
    pending_ast_id: ?i64 = null,
};

fn Render(comptime project: bool) type {
    return struct {
        const Self = @This();
        fn Pointer(comptime T: type) type {
            return if (project) *T else *const T;
        }
        fn Slice(comptime T: type) type {
            return if (project) []T else []const T;
        }
        projection: if (project) Projection else void = if (project) .{ .source_name = "" } else {}, // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value when projection is disabled
        output: *Output,
        dialect: AST.Dialect,
        sources: []const SourceIndexName = &.{},
        selection: DebugInfoSelection = .defaultValue(),
        provider: ?CharStreamProvider = null,
        last_location: SourceLocation = .{},

        pub fn object(self: *Self, value: Pointer(Objects.Object)) Error!void {
            const code = if (value.code_value) |*owned_code| owned_code else return error.MissingCode;
            const data = value.debug_data orelse return error.MissingDebugData;
            var child: Self = .{
                .output = self.output,
                .dialect = code.dialect().*,
                .sources = if (data.source_names) |source_names| source_names.entries.items else &.{},
                .selection = self.selection,
                .provider = self.provider,
                .projection = if (project) .{ .source_name = self.projection.source_name, .mapped = data.source_names != null } else {}, // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value when projection is disabled
            };
            try data.writeUseSrcComment(self.output);
            try self.output.writeAll("object ");
            try CommonData.writeEscapedQuoted(self.output, value.name);
            try self.output.writeAll(" {\n");
            const parent_indent = self.output.indent;
            defer self.output.indent = parent_indent;
            self.output.indent += 4;
            try self.output.writeAll("code ");
            try child.block(&code.root_block);
            for (value.sub_objects.items) |*node| {
                try self.output.newline();
                switch (node.*) {
                    .object => |nested| try child.object(nested),
                    .data => |*literal_data| try literal_data.writeTo(self.output),
                }
            }
            self.output.indent = parent_indent;
            try self.output.writeAll("\n}");
        }

        pub fn expression(self: *Self, value: Pointer(AST.Expression)) Error!void {
            switch (value.*) {
                .literal => |*item| try self.literal(item),
                .identifier => |*item| try self.identifier(item),
                .function_call => |*item| try self.functionCall(item),
            }
        }

        pub fn statement(self: *Self, value: Pointer(AST.Statement)) Error!void {
            switch (value.*) {
                .expression_statement => |*item| try self.expressionStatement(item),
                .assignment => |*item| try self.assignment(item),
                .variable_declaration => |*item| try self.variable(item),
                .function_definition => |*item| try self.function(item),
                .if_statement => |*item| try self.branch(item),
                .switch_statement => |*item| try self.selectionStatement(item),
                .for_loop => |*item| try self.loop(item),
                .break_statement => |*item| try self.keyword(&item.debug_data, "break"),
                .continue_statement => |*item| try self.keyword(&item.debug_data, "continue"),
                .leave_statement => |*item| try self.keyword(&item.debug_data, "leave"),
                .block => |*item| try self.block(item),
            }
        }

        pub fn literal(self: *Self, value: Pointer(AST.Literal)) Error!void {
            if (!Utilities.validLiteral(value)) return error.InvalidAST;
            try self.comment(value.debug_data, false);
            const mark = try self.start();
            var buffer: [80]u8 = undefined;
            const text = if (value.value.string_value) |hint| hint else blk: {
                const numeric = value.value.numeric_value orelse return error.InvalidAST;
                if (value.kind == .Boolean) break :blk if (numeric == 0) "false" else "true";
                break :blk std.fmt.bufPrint(&buffer, "{d}", .{numeric}) catch unreachable; // zlinter-disable-current-line no_swallow_error - 80 bytes fit the decimal representation of a u256 literal
            };
            if (value.kind == .String) try CommonData.writeEscapedQuoted(self.output, text) else try self.output.writeAll(text);
            try self.finish(&value.debug_data, mark);
        }

        pub fn identifier(self: *Self, value: Pointer(AST.Identifier)) Error!void {
            if (value.name.empty()) return error.InvalidAST;
            try self.comment(value.debug_data, false);
            const mark = try self.start();
            try self.output.writeAll(value.name.str() catch return error.InvalidYulStringHandle);
            try self.finish(&value.debug_data, mark);
        }

        pub fn builtin(self: *Self, value: Pointer(AST.BuiltinName)) Error!void {
            try self.comment(value.debug_data, false);
            const mark = try self.start();
            const definition = self.dialect.builtin(value.handle) catch return error.UnknownBuiltin;
            try self.output.writeAll(definition.name);
            try self.finish(&value.debug_data, mark);
        }

        pub fn functionCall(self: *Self, value: Pointer(AST.FunctionCall)) Error!void {
            try self.comment(value.debug_data, false);
            switch (value.function_name) {
                .identifier => |*name| try self.identifier(name),
                .builtin => |*name| try self.builtin(name),
            }
            const mark = if (project) switch (value.function_name) { // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value when projection is disabled
                inline else => |name| name.debug_data.?,
            } else {};
            try self.output.writeByte('(');
            for (value.arguments.items, 0..) |*argument, index| {
                if (index != 0) try self.output.writeAll(", ");
                try self.expression(argument);
            }
            try self.output.writeByte(')');
            try self.finish(&value.debug_data, mark);
        }

        pub fn expressionStatement(self: *Self, value: Pointer(AST.ExpressionStatement)) Error!void {
            try self.comment(value.debug_data, true);
            try self.expression(&value.expression);
            if (project) value.debug_data = value.expression.debugData().?.*;
        }

        pub fn assignment(self: *Self, value: Pointer(AST.Assignment)) Error!void {
            if (value.variable_names.items.len == 0 or value.value == null) return error.InvalidAST;
            try self.comment(value.debug_data, true);
            for (value.variable_names.items, 0..) |*name, index| {
                if (index != 0) try self.output.writeAll(", ");
                try self.identifier(name);
            }
            try self.output.writeAll(" := ");
            try self.expression(value.value.?);
            try self.finish(&value.debug_data, if (project) value.variable_names.items[0].debug_data.? else {}); // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value when projection is disabled
        }

        pub fn variable(self: *Self, value: Pointer(AST.VariableDeclaration)) Error!void {
            try self.comment(value.debug_data, true);
            const mark = try self.start();
            try self.output.writeAll("let ");
            try self.names(value.variables.items);
            if (value.value) |expression_value| {
                try self.output.writeAll(" := ");
                try self.expression(expression_value);
            }
            try self.finish(&value.debug_data, mark);
        }

        pub fn function(self: *Self, value: Pointer(AST.FunctionDefinition)) Error!void {
            if (self.output.stop_at_newline) return error.LayoutLimit;
            if (value.name.empty()) return error.InvalidAST;
            try self.comment(value.debug_data, true);
            const mark = try self.start();
            try self.output.writeAll("function ");
            try self.output.writeAll(value.name.str() catch return error.InvalidYulStringHandle);
            try self.output.writeByte('(');
            try self.names(value.parameters.items);
            try self.output.writeByte(')');
            if (value.return_variables.items.len != 0) {
                try self.output.writeAll(" -> ");
                try self.names(value.return_variables.items);
            }
            try self.output.newline();
            try self.block(&value.body);
            try self.finish(&value.debug_data, mark);
        }

        pub fn branch(self: *Self, value: Pointer(AST.If)) Error!void {
            const condition = value.condition orelse return error.InvalidAST;
            try self.comment(value.debug_data, true);
            const mark = try self.start();
            try self.output.writeAll("if ");
            try self.expression(condition);
            if (self.output.stop_at_newline) {
                try self.output.writeByte(' ');
                return self.block(&value.body);
            }
            // A block without newlines has at most 33 bytes: { + body<30 + }.
            const compact = try self.probe("block", &value.body, 34);
            try self.output.writeByte(if (compact) ' ' else '\n');
            try self.block(&value.body);
            try self.finish(&value.debug_data, mark);
        }

        pub fn selectionStatement(self: *Self, value: Pointer(AST.Switch)) Error!void {
            if (self.output.stop_at_newline and value.cases.items.len != 0) return error.LayoutLimit;
            const subject = value.expression orelse return error.InvalidAST;
            try self.comment(value.debug_data, true);
            const mark = try self.start();
            try self.output.writeAll("switch ");
            try self.expression(subject);
            for (value.cases.items) |*branch_value| {
                try self.output.newline();
                const case_mark = try self.start();
                if (branch_value.value) |label| {
                    try self.output.writeAll("case ");
                    try self.literal(label);
                    try self.output.writeByte(' ');
                } else try self.output.writeAll("default ");
                try self.block(&branch_value.body);
                try self.finish(&branch_value.debug_data, case_mark);
            }
            try self.finish(&value.debug_data, mark);
        }

        pub fn loop(self: *Self, value: Pointer(AST.ForLoop)) Error!void {
            if (self.output.stop_at_newline) return error.LayoutLimit;
            const condition = value.condition orelse return error.InvalidAST;
            try self.comment(value.debug_data, true);
            const mark = try self.start();
            const compact = try self.probe("loopHeader", value, 60);
            const separator: u8 = if (compact) ' ' else '\n';
            try self.output.writeAll("for ");
            try self.block(&value.pre);
            try self.output.writeByte(separator);
            try self.expression(condition);
            try self.output.writeByte(separator);
            try self.block(&value.post);
            try self.output.newline();
            try self.block(&value.body);
            try self.finish(&value.debug_data, mark);
        }

        fn loopHeader(self: *Self, value: Pointer(AST.ForLoop)) Error!void {
            try self.block(&value.pre);
            try self.expression(value.condition orelse return error.InvalidAST);
            try self.block(&value.post);
        }

        fn keyword(self: *Self, data: Pointer(?DebugData), text: []const u8) Error!void {
            try self.comment(data.*, true);
            const mark = try self.start();
            try self.output.writeAll(text);
            try self.finish(data, mark);
        }

        pub fn block(self: *Self, value: Pointer(AST.Block)) Error!void {
            try self.comment(value.debug_data, true);
            const mark = try self.start();
            if (value.statements.items.len == 0) {
                try self.output.writeAll("{ }");
                return self.finish(&value.debug_data, mark);
            }
            const compact = if (self.output.limit) |limit| compact: {
                // Reserve the enclosing { } before descending. Starting each nested
                // probe with a fresh 30-byte budget would revisit arbitrarily deep
                // block/if chains before learning that their parent cannot fit.
                if (value.statements.items.len != 1 or limit - self.output.count <= 4) return error.LayoutLimit;
                const budget = @min(30, limit - self.output.count - 4);
                if (!try self.probe("statement", &value.statements.items[0], budget)) return error.LayoutLimit;
                break :compact true;
            } else value.statements.items.len == 1 and try self.probe("statement", &value.statements.items[0], 30);
            if (compact) {
                try self.output.writeAll("{ ");
                try self.statement(&value.statements.items[0]);
                try self.output.writeAll(" }");
                return self.finish(&value.debug_data, mark);
            }
            try self.output.writeAll("{\n");
            const parent_indent = self.output.indent;
            defer self.output.indent = parent_indent;
            self.output.indent += 4;
            for (value.statements.items, 0..) |*item, index| {
                if (index != 0) try self.output.newline();
                try self.statement(item);
            }
            self.output.indent = parent_indent;
            try self.output.writeAll("\n}");
            try self.finish(&value.debug_data, mark);
        }

        fn probe(self: *const Self, comptime method: []const u8, value: anytype, limit: usize) Error!bool {
            var output: Output = .{ .limit = limit, .stop_at_newline = true };
            // Probes always borrow const nodes, including during native projection.
            var renderer: Renderer = .{
                .output = &output,
                .dialect = self.dialect,
                .sources = self.sources,
                .selection = self.selection,
                .provider = self.provider,
                .last_location = self.last_location,
            };
            @call(.auto, @field(Renderer, method), .{ &renderer, value }) catch |err| switch (err) {
                error.LayoutLimit => return false,
                else => return err,
            };
            return true;
        }

        fn names(self: *Self, values: Slice(AST.NameWithDebugData)) Error!void {
            for (values, 0..) |*value, index| {
                if (value.name.empty()) return error.InvalidAST;
                if (index != 0) try self.output.writeAll(", ");
                try self.comment(value.debug_data, true);
                const mark = try self.start();
                try self.output.writeAll(value.name.str() catch return error.InvalidYulStringHandle);
                try self.finish(&value.debug_data, mark);
            }
        }

        fn comment(self: *Self, optional_data: ?DebugData, is_statement: bool) Error!void {
            const data = optional_data orelse return;
            if (self.selection.none()) return;
            const ast_id = if (self.selection.ast_id) data.ast_id else null;
            const location_changed = self.sources.len != 0 and !self.last_location.eql(data.origin_location);
            if (ast_id == null and !location_changed) return;
            if (is_statement and self.output.stop_at_newline) return error.LayoutLimit;
            try self.output.writeAll(if (is_statement) "/// " else "/** ");
            if (ast_id) |id| {
                try self.output.writeAll("@ast-id ");
                try self.output.integer(id);
            }
            if (location_changed) {
                self.last_location = data.origin_location;
                if (ast_id != null) try self.output.writeByte(' ');
                try @import("asm_printer.zig").writeSourceLocation(self.output, data.origin_location, self.sources, self.selection, self.provider);
            }
            try self.output.writeAll(if (is_statement) "\n" else " */ ");
            if (project) {
                // The scanner retains only the last adjacent documentation comment.
                self.projection.pending_location = if (location_changed) data.origin_location else null;
                self.projection.pending_ast_id = ast_id;
            }
        }

        fn start(self: *Self) Error!(if (project) DebugData else void) {
            if (!project) return;
            try self.output.indentation();
            const offset = std.math.cast(i32, self.output.count) orelse return error.InvalidAST;
            const native: SourceLocation = .{ .start = offset, .end = offset, .source_name = self.projection.source_name };
            if (self.projection.pending_location) |location| self.projection.parsed_location = location;
            const result: DebugData = .{
                .native_location = native,
                .origin_location = if (self.projection.mapped) self.projection.parsed_location else native,
                .ast_id = if (self.projection.mapped) self.projection.pending_ast_id else null,
            };
            self.projection.pending_location = null;
            self.projection.pending_ast_id = null;
            return result;
        }

        fn finish(self: *const Self, data: Pointer(?DebugData), mark: if (project) DebugData else void) Error!void {
            if (!project) return;
            var result = mark;
            result.native_location.end = std.math.cast(i32, self.output.count) orelse return error.InvalidAST;
            if (!self.projection.mapped) result.origin_location.end = result.native_location.end;
            data.* = result;
        }
    };
}

test "Yul AST layout probes stay bounded on deep block chains without allocation" {
    const Counter = struct {
        calls: usize = 0,
        definition: AST.BuiltinFunction = .{ .name = "stop", .num_parameters = 0, .num_returns = 0, .side_effects = .{}, .control_flow_side_effects = .{} },
        fn builtin(context: ?*const anyopaque, _: @import("builtins.zig").BuiltinHandle) ?*const AST.BuiltinFunction {
            const self: *@This() = @ptrCast(@alignCast(@constCast(context.?)));
            self.calls += 1;
            return &self.definition;
        }
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const items = try arena.allocator().alloc(AST.Statement, 1);
    items[0] = .{ .expression_statement = .{ .expression = .{ .function_call = .{ .function_name = .{ .builtin = .{ .handle = .{ .id = 0 } } } } } } };
    var root: AST.Block = .{ .statements = .{ .items = items, .capacity = 1 } };
    var first_calls: usize = 0;
    for (0..200) |depth| {
        const wrapper = try arena.allocator().alloc(AST.Statement, 1);
        wrapper[0] = .{ .block = root };
        root = .{ .statements = .{ .items = wrapper, .capacity = 1 } };
        if (depth != 99 and depth != 199) continue;
        var counter: Counter = .{};
        var output: Output = .{};
        var renderer: Renderer = .{ .output = &output, .dialect = .{ .context = &counter, .vtable = &.{ .builtin = Counter.builtin } } };
        try renderer.block(&root);
        if (depth == 99) first_calls = counter.calls else try std.testing.expectEqual(first_calls, counter.calls);
        try std.testing.expect(counter.calls < 1024);
    }
}

test "Yul AST streaming output releases every allocation failure" {
    const Builder = @import("ast_builder.zig").Builder;
    const Printer = @import("asm_printer.zig").AsmPrinter;
    const EVM = @import("backends/evm/evm_dialect.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const dialect = (try EVM.strictAssemblyForEVMObjects(.current())).dialect();
    const builder = Builder.init(&arena, dialect).withDebug(.{ .origin_location = .{ .source_name = "C.sol", .start = 1, .end = 10 }, .ast_id = 3 });
    const root = try builder.statements("function f(a) -> r { if a { r := add(a, 1) } } mstore(0, f(7))", .{});
    const Helper = struct {
        fn check(failing: std.mem.Allocator, block: *const AST.Block, selected_dialect: AST.Dialect) !void {
            var printer = Printer.init(failing, selected_dialect, &.{.{ .index = 0, .name = "C.sol" }}, .defaultValue(), null);
            const text = try printer.renderBlock(block);
            defer failing.free(text);
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Helper.check, .{ &root, dialect });
}

fn expectObjectJsonEqual(allocator: std.mem.Allocator, expected: *const Objects.Object, actual: *const Objects.Object) !void {
    const JSON = @import("../libsolutil/json.zig");
    var expected_value = try expected.toJsonAlloc(allocator);
    defer expected_value.deinit();
    var actual_value = try actual.toJsonAlloc(allocator);
    defer actual_value.deinit();
    const expected_text = try JSON.jsonCompactPrintAlloc(allocator, &expected_value.value);
    defer allocator.free(expected_text);
    const actual_text = try JSON.jsonCompactPrintAlloc(allocator, &actual_value.value);
    defer allocator.free(actual_text);
    try std.testing.expectEqualStrings(expected_text, actual_text);
}

test "source locations preserve object projection with borrowed snippets" {
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const Parser = @import("object_parser.zig").ObjectParser;
    const EVM = @import("backends/evm/evm_dialect.zig");
    const CharStream = @import("../liblangutil/char_stream.zig").CharStream;
    const Provider = @import("../liblangutil/char_stream_provider.zig").SingletonCharStreamProvider;
    const allocator = std.testing.allocator;
    const dialect = (try EVM.strictAssemblyForEVMObjects(.current())).dialect();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const object = (try Parser.parseSource(allocator,
        \\/// @use-src 0:"C.sol"
        \\object "Root" { code {
        \\  /// @src 0:0:100
        \\  let a := 1
        \\  /// @src 0:4:12
        \\  pop(a)
        \\} }
    , "input.yul", &reporter, dialect)).?;
    defer object.destroy();
    const stream = CharStream.initBorrowed("ab */ \"\t\x01\r\nnext", "C.sol");
    const provider = Provider.init(&stream);
    const selection = DebugInfoSelection.defaultValue();
    const rendered = try object.formatIRAlloc(allocator, selection, provider.provider());
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "*\\/") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "\\x01...") != null);
    const reference = (try Parser.parseSource(allocator, rendered, "input.yul", &reporter, dialect)).?;
    defer reference.destroy();
    const original_items = object.code_value.?.root().statements.items.ptr;
    try std.testing.expectEqual(rendered.len, try projectObject(object, "input.yul", selection, provider.provider()));
    try std.testing.expectEqual(original_items, object.code_value.?.root().statements.items.ptr);
    try expectObjectJsonEqual(allocator, reference, object);
    var buffer: [2048]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buffer);
    try object.writeTo(&writer, selection, provider.provider());
    try std.testing.expectEqualStrings(rendered[0 .. rendered.len - 1], writer.buffered());
}

test "Yul AST native projection preserves empty and absent source mappings" {
    const Parser = @import("object_parser.zig").ObjectParser;
    const EVM = @import("backends/evm/evm_dialect.zig");
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const allocator = std.testing.allocator;
    const dialect = (try EVM.strictAssemblyForEVMObjects(.current())).dialect();
    for ([_][]const u8{ "", "/// @use-src \n" }) |header| {
        const source = try std.fmt.allocPrint(allocator, "{s}object \"Root\" {{ code {{ let a, b a, b := f() function f() -> x,y {{ x := 1 y := 2 }} }} }}", .{header});
        defer allocator.free(source);
        for ([_]DebugInfoSelection{ .defaultValue(), .noneValue(), .only(.location), .only(.ast_id) }) |selection| {
            var reporter = Diagnostics.ErrorReporter.init(allocator);
            defer reporter.deinit();
            const object = (try Parser.parseSource(allocator, source, "input.yul", &reporter, dialect)).?;
            defer object.destroy();
            const block = &object.code_value.?.root_block;
            block.debug_data.?.ast_id = 20;
            block.statements.items[0].variable_declaration.debug_data = null;
            block.statements.items[0].variable_declaration.variables.items[0].debug_data.?.ast_id = 30;
            block.statements.items[1].assignment.value.?.function_call.function_name.identifier.debug_data.?.ast_id = 40;
            const rendered = try object.formatAlloc(allocator, selection, null);
            defer allocator.free(rendered);
            const reference = (try Parser.parseSource(allocator, rendered, "input.yul", &reporter, dialect)).?;
            defer reference.destroy();
            const original_items = block.statements.items.ptr;
            _ = try projectObject(object, "input.yul", selection, null);
            try std.testing.expect(original_items == block.statements.items.ptr);
            try expectObjectJsonEqual(allocator, reference, object);
        }
    }
}
