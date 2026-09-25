// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic encoding of the existing Yul AST for cache identity and storage.
//! No pointer, native struct layout, hash iteration order or name-repository ID
//! enters the stream. Builtin IDs are dialect-local: callers must include the
//! dialect/compiler identity in their enclosing cache key.
//!
//! The alpha-equivalence BlockHasher intentionally omits names, annotations and
//! literal spelling, and uses a non-cryptographic digest. It cannot serve this
//! byte-compatible artifact cache. Here one encoder streams to a bounded hashing
//! writer or a caller-owned storage writer without constructing program text.

const std = @import("std");
const AST = @import("ast.zig");
const Objects = @import("object.zig");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;
const H256 = @import("../libsolutil/fixed_hash.zig").H256;
const YulName = @import("yul_name.zig").YulName;

const block_magic = "oksolc.yul.ast\x00";
const sources_magic = "oksolc.yul.sources\x00";
const schema_version: u32 = 1;
const HashWriter = std.Io.Writer.Hashing(std.crypto.hash.sha3.Keccak256);

pub fn hashBlock(block: *const AST.Block) !H256 {
    var buffer: [4096]u8 = undefined;
    var sink = HashWriter.init(&buffer);
    try encodeBlock(&sink.writer, block);
    try sink.writer.flush();
    var result = H256.init();
    sink.hasher.final(result.mutableArray());
    return result;
}

pub fn hashSources(data: *const Objects.ObjectDebugData) !H256 {
    var buffer: [1024]u8 = undefined;
    var sink = HashWriter.init(&buffer);
    try encodeSources(&sink.writer, data);
    try sink.writer.flush();
    var result = H256.init();
    sink.hasher.final(result.mutableArray());
    return result;
}

/// Hashes the complete assembly input graph, omitting only auxiliary metadata.
/// This is an immutable traversal with bounded scratch storage. Cache hits do
/// not allocate a serialized input; cold persistent entries use the same walk.
pub fn hashObjectWithoutMetadata(object: *const Objects.Object) !H256 {
    var buffer: [4096]u8 = undefined;
    var sink = HashWriter.init(&buffer);
    try encodeObjectWithoutMetadata(&sink.writer, object);
    try sink.writer.flush();
    var result = H256.init();
    sink.hasher.final(result.mutableArray());
    return result;
}

pub fn encodeObjectWithoutMetadataAlloc(allocator: std.mem.Allocator, object: *const Objects.Object) ![]u8 {
    var sink = std.Io.Writer.Allocating.init(allocator);
    defer sink.deinit();
    encodeObjectWithoutMetadata(&sink.writer, object) catch |err| switch (err) {
        error.WriteFailed => return error.OutOfMemory,
        else => return err,
    };
    return sink.toOwnedSlice();
}

fn encodeObjectWithoutMetadata(writer: *std.Io.Writer, object: *const Objects.Object) !void {
    try writer.writeAll("oksolc.yul.object\x00");
    try writer.writeInt(u32, schema_version, .big);
    var encoder: Encoder = .{ .writer = writer };
    try encoder.objectWithoutMetadata(object);
}

fn encodeSources(writer: *std.Io.Writer, data: *const Objects.ObjectDebugData) !void {
    var encoder: Encoder = .{ .writer = writer };
    try writer.writeAll(sources_magic);
    try writer.writeInt(u32, schema_version, .big);
    try encoder.boolean(data.source_names != null);
    if (data.source_names) |names| {
        try encoder.count(names.entries.items.len);
        for (names.entries.items) |entry| {
            try writer.writeInt(u32, entry.index, .big);
            try encoder.bytes(entry.name);
        }
    }
}

/// Native generated-text positions are omitted, as in the former cache key.
/// Origins, ast-ids, literal kind/value/spelling and all ordered AST fields are
/// encoded. Repeated adjacent annotations use a one-byte back-reference.
pub fn encodeBlock(writer: *std.Io.Writer, block: *const AST.Block) !void {
    try writer.writeAll(block_magic);
    try writer.writeInt(u32, schema_version, .big);
    var encoder: Encoder = .{ .writer = writer };
    try encoder.block(block);
}

const ExpressionTag = enum(u8) { literal = 1, identifier = 2, call = 3 };
const StatementTag = enum(u8) { expression = 1, assignment = 2, variable = 3, function = 4, branch = 5, selection = 6, loop = 7, break_loop = 8, continue_loop = 9, leave = 10, block = 11 };

const Encoder = struct {
    writer: *std.Io.Writer,
    previous_debug: ?DebugData = null,

    fn objectWithoutMetadata(self: *Encoder, value: *const Objects.Object) anyerror!void {
        try self.bytes(value.name);
        try self.boolean(value.debug_data != null);
        if (value.debug_data) |*data| try encodeSources(self.writer, data);
        try self.boolean(value.code() != null);
        if (value.code()) |code| {
            self.previous_debug = null;
            try self.block(code.root());
        }
        var child_count: usize = 0;
        for (value.sub_objects.items) |*node| {
            if (node.* == .data and std.mem.eql(u8, node.data.name, Objects.Object.metadataName())) continue;
            child_count += 1;
        }
        try self.count(child_count);
        for (value.sub_objects.items) |*node| switch (node.*) {
            .object => |child| {
                try self.writer.writeByte(0);
                try self.objectWithoutMetadata(child);
            },
            .data => |*data| {
                if (std.mem.eql(u8, data.name, Objects.Object.metadataName())) continue;
                try self.writer.writeByte(1);
                try self.bytes(data.name);
                try self.bytes(data.data);
            },
        };
    }

    fn boolean(self: *Encoder, value: bool) !void {
        try self.writer.writeByte(@intFromBool(value));
    }

    fn count(self: *Encoder, value: usize) !void {
        try self.writer.writeInt(u32, std.math.cast(u32, value) orelse return error.EncodingLimitExceeded, .big);
    }

    fn bytes(self: *Encoder, value: []const u8) !void {
        try self.count(value.len);
        try self.writer.writeAll(value);
    }

    fn optionalBytes(self: *Encoder, value: ?[]const u8) !void {
        try self.boolean(value != null);
        if (value) |text| try self.bytes(text);
    }

    fn name(self: *Encoder, value: YulName) !void {
        if (value.empty()) return error.InvalidAST;
        try self.bytes(try value.str());
    }

    fn location(self: *Encoder, value: SourceLocation) !void {
        try self.writer.writeInt(i32, value.start, .big);
        try self.writer.writeInt(i32, value.end, .big);
        try self.optionalBytes(value.source_name);
    }

    fn debug(self: *Encoder, value: ?DebugData) !void {
        var data = value orelse {
            try self.writer.writeByte(0);
            self.previous_debug = null;
            return;
        };
        data.native_location = .{};
        if (self.previous_debug) |previous| {
            if (previous.ast_id == data.ast_id and previous.origin_location.eql(data.origin_location)) {
                try self.writer.writeByte(1);
                return;
            }
        }
        try self.writer.writeByte(2);
        try self.location(data.origin_location);
        try self.boolean(data.ast_id != null);
        if (data.ast_id) |id| try self.writer.writeInt(i64, id, .big);
        self.previous_debug = data;
    }

    fn identifier(self: *Encoder, value: *const AST.Identifier) !void {
        try self.debug(value.debug_data);
        try self.name(value.name);
    }

    fn names(self: *Encoder, values: []const AST.NameWithDebugData) !void {
        try self.count(values.len);
        for (values) |value| {
            try self.debug(value.debug_data);
            try self.name(value.name);
        }
    }

    fn literal(self: *Encoder, value: *const AST.Literal) !void {
        try self.debug(value.debug_data);
        try self.writer.writeByte(switch (value.kind) {
            .Number => 0,
            .Boolean => 1,
            .String => 2,
        });
        try self.boolean(value.value.numeric_value != null);
        if (value.value.numeric_value) |numeric| try self.writer.writeInt(u256, numeric, .big);
        try self.optionalBytes(value.value.string_value);
    }

    fn expression(self: *Encoder, value: *const AST.Expression) anyerror!void {
        switch (value.*) {
            .literal => |*item| {
                try self.writer.writeByte(@intFromEnum(ExpressionTag.literal));
                try self.literal(item);
            },
            .identifier => |*item| {
                try self.writer.writeByte(@intFromEnum(ExpressionTag.identifier));
                try self.identifier(item);
            },
            .function_call => |*item| {
                try self.writer.writeByte(@intFromEnum(ExpressionTag.call));
                try self.debug(item.debug_data);
                switch (item.function_name) {
                    .builtin => |builtin| {
                        try self.writer.writeByte(0);
                        try self.debug(builtin.debug_data);
                        try self.count(builtin.handle.id);
                    },
                    .identifier => |*identifier_value| {
                        try self.writer.writeByte(1);
                        try self.identifier(identifier_value);
                    },
                }
                try self.count(item.arguments.items.len);
                for (item.arguments.items) |*argument| try self.expression(argument);
            },
        }
    }

    fn block(self: *Encoder, value: *const AST.Block) anyerror!void {
        try self.debug(value.debug_data);
        try self.count(value.statements.items.len);
        for (value.statements.items) |*item| try self.statement(item);
    }

    fn statement(self: *Encoder, value: *const AST.Statement) !void {
        const tag: StatementTag = switch (value.*) {
            .expression_statement => .expression,
            .assignment => .assignment,
            .variable_declaration => .variable,
            .function_definition => .function,
            .if_statement => .branch,
            .switch_statement => .selection,
            .for_loop => .loop,
            .break_statement => .break_loop,
            .continue_statement => .continue_loop,
            .leave_statement => .leave,
            .block => .block,
        };
        try self.writer.writeByte(@intFromEnum(tag));
        switch (value.*) {
            .expression_statement => |*item| {
                try self.debug(item.debug_data);
                try self.expression(&item.expression);
            },
            .assignment => |*item| {
                try self.debug(item.debug_data);
                try self.count(item.variable_names.items.len);
                for (item.variable_names.items) |*target| try self.identifier(target);
                try self.expression(item.value orelse return error.InvalidAST);
            },
            .variable_declaration => |*item| {
                try self.debug(item.debug_data);
                try self.names(item.variables.items);
                try self.boolean(item.value != null);
                if (item.value) |expression_value| try self.expression(expression_value);
            },
            .function_definition => |*item| {
                try self.debug(item.debug_data);
                try self.name(item.name);
                try self.names(item.parameters.items);
                try self.names(item.return_variables.items);
                try self.block(&item.body);
            },
            .if_statement => |*item| {
                try self.debug(item.debug_data);
                try self.expression(item.condition orelse return error.InvalidAST);
                try self.block(&item.body);
            },
            .switch_statement => |*item| {
                try self.debug(item.debug_data);
                try self.expression(item.expression orelse return error.InvalidAST);
                try self.count(item.cases.items.len);
                for (item.cases.items) |*branch| {
                    try self.debug(branch.debug_data);
                    try self.boolean(branch.value != null);
                    if (branch.value) |label| try self.literal(label);
                    try self.block(&branch.body);
                }
            },
            .for_loop => |*item| {
                try self.debug(item.debug_data);
                try self.block(&item.pre);
                try self.expression(item.condition orelse return error.InvalidAST);
                try self.block(&item.post);
                try self.block(&item.body);
            },
            inline .break_statement, .continue_statement, .leave_statement => |*item| try self.debug(item.debug_data),
            .block => |*item| try self.block(item),
        }
    }
};

/// Cache payloads wrap the structural encoding in an integrity checksum. The
/// caller's persistent artifact key additionally binds the compiler and dialect.
pub fn encodeStoredBlockAlloc(allocator: std.mem.Allocator, root: *const AST.Block) ![]u8 {
    var sink = std.Io.Writer.Allocating.init(allocator);
    defer sink.deinit();
    encodeBlock(&sink.writer, root) catch |err| switch (err) {
        error.WriteFailed => return error.OutOfMemory,
        else => return err,
    };
    const digest = @import("../libsolutil/keccak256.zig").keccak256(sink.written());
    sink.writer.writeAll(digest.bytes()) catch return error.OutOfMemory;
    return sink.toOwnedSlice();
}

pub const DecodeError = std.mem.Allocator.Error || error{ CorruptAST, IncompatibleASTSchema };

/// All nodes and private strings belong to the supplied arena/repository. The
/// caller discards that arena on error. No reference to encoded bytes escapes.
/// Decode validates structure and literals; the consumer must also run scope,
/// object-reference and instruction analysis before publishing the result.
pub fn decodeStoredBlock(arena: *std.heap.ArenaAllocator, names: *@import("yul_string.zig").Repository, encoded: []const u8, dialect: AST.Dialect) DecodeError!AST.Block {
    const checksum_size = H256.size;
    if (encoded.len < block_magic.len + 4 + checksum_size) return error.CorruptAST;
    const content = encoded[0 .. encoded.len - checksum_size];
    const digest = @import("../libsolutil/keccak256.zig").keccak256(content);
    if (!std.mem.eql(u8, digest.bytes(), encoded[content.len..])) return error.CorruptAST;
    var decoder: Decoder = .{ .reader = .fixed(content), .allocator = arena.allocator(), .names = names, .dialect = dialect };
    if (!std.mem.eql(u8, try decoder.take(block_magic.len), block_magic)) return error.CorruptAST;
    if (try decoder.integer(u32) != schema_version) return error.IncompatibleASTSchema;
    const root = try decoder.block();
    if (decoder.reader.bufferedLen() != 0) return error.CorruptAST;
    return root;
}

const Decoder = struct {
    reader: std.Io.Reader,
    allocator: std.mem.Allocator,
    names: *@import("yul_string.zig").Repository,
    dialect: AST.Dialect,
    previous_debug: ?DebugData = null,
    depth: usize = 0,
    inside_function: bool = false,
    loop_component: enum { none, pre, post, body } = .none,

    fn take(self: *Decoder, len: usize) DecodeError![]const u8 {
        // Check first: Reader.take's fixed-buffer precondition also requires
        // each request to fit within the complete original buffer.
        if (len > self.reader.bufferedLen()) return error.CorruptAST;
        return self.reader.take(len) catch return error.CorruptAST;
    }

    fn integer(self: *Decoder, comptime T: type) DecodeError!T {
        const data = try self.take(@sizeOf(T));
        return std.mem.readInt(T, data[0..@sizeOf(T)], .big);
    }

    fn boolean(self: *Decoder) DecodeError!bool {
        return switch (try self.integer(u8)) {
            0 => false,
            1 => true,
            else => error.CorruptAST,
        };
    }

    fn bytes(self: *Decoder) DecodeError![]const u8 {
        return self.take(try self.integer(u32));
    }

    fn intern(self: *Decoder, text: []const u8) DecodeError!YulName {
        return .{ .handle = try self.names.stringToHandle(text) };
    }

    fn name(self: *Decoder) DecodeError!YulName {
        const text = try self.bytes();
        const Lexical = @import("../liblangutil/common.zig");
        if (text.len == 0 or !Lexical.isIdentifierStart(text[0])) return error.CorruptAST;
        for (text[1..]) |c| if (!Lexical.isIdentifierPart(c) and c != '.') return error.CorruptAST;
        const keywords = [_][]const u8{ "let", "function", "if", "switch", "case", "default", "for", "break", "continue", "leave", "true", "false" };
        for (keywords) |word| if (std.mem.eql(u8, text, word)) return error.CorruptAST;
        if (self.dialect.reservedIdentifier(text)) return error.CorruptAST;
        return self.intern(text);
    }

    fn location(self: *Decoder) DecodeError!SourceLocation {
        const start = try self.integer(i32);
        const end = try self.integer(i32);
        if (start < -1 or end < -1 or (start >= 0 and end < start)) return error.CorruptAST;
        const source = if (try self.boolean()) blk: {
            const name_value = try self.intern(try self.bytes());
            break :blk name_value.str() catch return error.CorruptAST;
        } else null;
        return .{ .start = start, .end = end, .source_name = source };
    }

    fn debug(self: *Decoder) DecodeError!?DebugData {
        switch (try self.integer(u8)) {
            0 => self.previous_debug = null,
            1 => if (self.previous_debug == null) return error.CorruptAST,
            2 => self.previous_debug = .{ .origin_location = try self.location(), .ast_id = if (try self.boolean()) try self.integer(i64) else null },
            else => return error.CorruptAST,
        }
        return self.previous_debug;
    }

    /// Reject count bombs before reserving memory. Each member must occupy at
    /// least min_bytes in the remaining encoded input. Reserve exactly once.
    fn list(self: *Decoder, comptime T: type, min_bytes: usize) DecodeError!std.ArrayList(T) {
        const count = try self.integer(u32);
        if (count > self.reader.bufferedLen() / min_bytes) return error.CorruptAST;
        const items = try self.allocator.alloc(T, count);
        return .{ .items = items, .capacity = count };
    }

    fn namedValues(self: *Decoder) DecodeError!AST.NameWithDebugDataList {
        const result = try self.list(AST.NameWithDebugData, 6);
        for (result.items) |*item| item.* = .{ .debug_data = try self.debug(), .name = try self.name() };
        return result;
    }

    fn identifier(self: *Decoder) DecodeError!AST.Identifier {
        return .{ .debug_data = try self.debug(), .name = try self.name() };
    }

    fn literal(self: *Decoder, unlimited_allowed: bool) DecodeError!AST.Literal {
        const annotation = try self.debug();
        const kind: AST.LiteralKind = switch (try self.integer(u8)) {
            0 => .Number,
            1 => .Boolean,
            2 => .String,
            else => return error.CorruptAST,
        };
        const numeric = if (try self.boolean()) try self.integer(u256) else null;
        const spelling = if (try self.boolean()) try self.allocator.dupe(u8, try self.bytes()) else null;
        const result: AST.Literal = .{ .debug_data = annotation, .kind = kind, .value = .{ .numeric_value = numeric, .string_value = spelling } };
        if (numeric == null and (!unlimited_allowed or kind != .String or spelling == null)) return error.CorruptAST;
        if (!@import("utilities.zig").validLiteral(&result)) return error.CorruptAST;
        return result;
    }

    fn builtin(self: *Decoder) DecodeError!AST.BuiltinName {
        const annotation = try self.debug();
        const handle: @import("builtins.zig").BuiltinHandle = .{ .id = try self.integer(u32) };
        // Verbatim IDs encode their signature. A fresh process has not yet
        // materialized these lazy builtins; reconstruct through their owner.
        const EVM = @import("backends/evm/evm_dialect.zig");
        if (EVM.fromDialect(self.dialect)) |evm| {
            if (handle.id < EVM.verbatim_id_offset) {
                if (!evm.providesObjectAccess()) return error.CorruptAST;
                _ = @constCast(evm).verbatimFunction(handle.id % EVM.verbatim_max_input_slots, handle.id / EVM.verbatim_max_input_slots) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => return error.CorruptAST,
                };
            }
        }
        _ = self.dialect.builtin(handle) catch return error.CorruptAST;
        return .{ .debug_data = annotation, .handle = handle };
    }

    fn enter(self: *Decoder) DecodeError!void {
        if (self.depth >= 1200) return error.CorruptAST;
        self.depth += 1;
    }

    fn expressionPointer(self: *Decoder) DecodeError!*AST.Expression {
        const value = try self.expression(false);
        const result = try self.allocator.create(AST.Expression);
        result.* = value;
        return result;
    }

    fn expression(self: *Decoder, unlimited_allowed: bool) DecodeError!AST.Expression {
        try self.enter();
        defer self.depth -= 1;
        const tag = std.enums.fromInt(ExpressionTag, try self.integer(u8)) orelse return error.CorruptAST;
        return switch (tag) {
            .literal => .{ .literal = try self.literal(unlimited_allowed) },
            .identifier => .{ .identifier = try self.identifier() },
            .call => blk: {
                const annotation = try self.debug();
                const function_name: AST.FunctionName = switch (try self.integer(u8)) {
                    0 => .{ .builtin = try self.builtin() },
                    1 => .{ .identifier = try self.identifier() },
                    else => return error.CorruptAST,
                };
                const function = if (function_name == .builtin) self.dialect.builtin(function_name.builtin.handle) catch return error.CorruptAST else null;
                const arguments = try self.list(AST.Expression, 7);
                if (function) |value| if (arguments.items.len != value.num_parameters) return error.CorruptAST;
                for (arguments.items, 0..) |*argument, i| argument.* = try self.expression(if (function) |value| value.literalArgument(i) == .String else false);
                break :blk .{ .function_call = .{ .debug_data = annotation, .function_name = function_name, .arguments = arguments } };
            },
        };
    }

    fn block(self: *Decoder) DecodeError!AST.Block {
        try self.enter();
        defer self.depth -= 1;
        const annotation = try self.debug();
        const statements = try self.list(AST.Statement, 2);
        for (statements.items) |*item| item.* = try self.statement();
        return .{ .debug_data = annotation, .statements = statements };
    }

    fn statement(self: *Decoder) DecodeError!AST.Statement {
        const tag = std.enums.fromInt(StatementTag, try self.integer(u8)) orelse return error.CorruptAST;
        if (tag == .block) return .{ .block = try self.block() };
        const annotation = try self.debug();
        switch (tag) {
            .expression => {
                const expr = try self.expression(false);
                if (expr != .function_call) return error.CorruptAST;
                return .{ .expression_statement = .{ .debug_data = annotation, .expression = expr } };
            },
            .assignment => {
                const targets = try self.list(AST.Identifier, 6);
                if (targets.items.len == 0) return error.CorruptAST;
                for (targets.items) |*item| item.* = try self.identifier();
                return .{ .assignment = .{ .debug_data = annotation, .variable_names = targets, .value = try self.expressionPointer() } };
            },
            .variable => {
                const variables = try self.namedValues();
                if (variables.items.len == 0) return error.CorruptAST;
                return .{ .variable_declaration = .{ .debug_data = annotation, .variables = variables, .value = if (try self.boolean()) try self.expressionPointer() else null } };
            },
            .function => {
                if (self.loop_component == .pre) return error.CorruptAST;
                const previous_loop = self.loop_component;
                const previous_function = self.inside_function;
                defer {
                    self.loop_component = previous_loop;
                    self.inside_function = previous_function;
                }
                self.loop_component = .none;
                self.inside_function = true;
                return .{ .function_definition = .{ .debug_data = annotation, .name = try self.name(), .parameters = try self.namedValues(), .return_variables = try self.namedValues(), .body = try self.block() } };
            },
            .branch => return .{ .if_statement = .{ .debug_data = annotation, .condition = try self.expressionPointer(), .body = try self.block() } },
            .selection => {
                const expr = try self.expressionPointer();
                const cases = try self.list(AST.Case, 7);
                if (cases.items.len == 0) return error.CorruptAST;
                for (cases.items, 0..) |*item, i| {
                    const data = try self.debug();
                    const label = if (try self.boolean()) blk: {
                        const literal_value = try self.literal(false);
                        const ptr = try self.allocator.create(AST.Literal);
                        ptr.* = literal_value;
                        break :blk ptr;
                    } else null;
                    if (label == null and i != cases.items.len - 1) return error.CorruptAST;
                    item.* = .{ .debug_data = data, .value = label, .body = try self.block() };
                }
                return .{ .switch_statement = .{ .debug_data = annotation, .expression = expr, .cases = cases } };
            },
            .loop => {
                const previous_loop = self.loop_component;
                defer self.loop_component = previous_loop;
                self.loop_component = .pre;
                const pre = try self.block();
                self.loop_component = .none;
                const condition = try self.expressionPointer();
                self.loop_component = .post;
                const post = try self.block();
                self.loop_component = .body;
                return .{ .for_loop = .{ .debug_data = annotation, .pre = pre, .condition = condition, .post = post, .body = try self.block() } };
            },
            .break_loop, .continue_loop => {
                if (self.loop_component != .body) return error.CorruptAST;
                return if (tag == .break_loop) .{ .break_statement = .{ .debug_data = annotation } } else .{ .continue_statement = .{ .debug_data = annotation } };
            },
            .leave => {
                if (!self.inside_function) return error.CorruptAST;
                return .{ .leave_statement = .{ .debug_data = annotation } };
            },
            .block => unreachable,
        }
    }
};

test "Yul AST encoding retains names, spelling and annotations independently of ownership" {
    const Builder = @import("ast_builder.zig").Builder;
    const Snapshot = @import("ast_snapshot.zig").Snapshot;
    const Dialect = @import("backends/evm/evm_dialect.zig");
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const dialect = (try Dialect.strictAssemblyForEVMObjects(.current())).dialect();
    const generator = Builder.init(&arena, dialect).withDebug(.{ .origin_location = .{ .start = 1, .end = 10, .source_name = "C.sol" }, .ast_id = 7 });
    var root = try generator.statements(
        \\let x := 0x01
        \\function f(a) -> r {
        \\ for { let i := 0 } lt(i, a) { i := add(i, 1) } {
        \\  if eq(i, 2) { continue }
        \\  switch i case 3 { break } default { r := add(r, i) }
        \\ }
        \\ { let untouched }
        \\ leave
        \\}
        \\pop(f(x))
    , .{});
    const original = try hashBlock(&root);
    const encoded = try encodeStoredBlockAlloc(allocator, &root);
    defer allocator.free(encoded);
    const decoded = try Snapshot.decode(allocator, encoded, dialect);
    defer decoded.destroy(allocator);
    try std.testing.expect(original.eql(&try hashBlock(&decoded.root)));
    const snapshot = try Snapshot.create(allocator, &root, false);
    defer snapshot.destroy(allocator);
    try std.testing.expect(original.eql(&try hashBlock(&snapshot.root)));
    root.debug_data.?.native_location = .{ .start = 100, .end = 200, .source_name = "generated.yul" };
    try std.testing.expect(original.eql(&try hashBlock(&root)));
    root.debug_data.?.origin_location.end += 1;
    try std.testing.expect(!original.eql(&try hashBlock(&root)));
    root.debug_data.?.origin_location.end -= 1;
    root.debug_data.?.ast_id = 8;
    try std.testing.expect(!original.eql(&try hashBlock(&root)));
    root.debug_data.?.ast_id = 7;
    const declaration = &root.statements.items[0].variable_declaration;
    const original_name = declaration.variables.items[0].name;
    declaration.variables.items[0].name = try generator.name("different_name");
    try std.testing.expect(!original.eql(&try hashBlock(&root)));
    declaration.variables.items[0].name = original_name;
    const original_hint = declaration.value.?.literal.value.string_value;
    declaration.value.?.literal.value.string_value = try arena.allocator().dupe(u8, "1");
    try std.testing.expect(!original.eql(&try hashBlock(&root)));
    declaration.value.?.literal.value.string_value = original_hint;
    try std.testing.expect(original.eql(&try hashBlock(&root)));
    std.mem.swap(AST.Statement, &root.statements.items[0], &root.statements.items[1]);
    try std.testing.expect(!original.eql(&try hashBlock(&root)));
}

test "Yul AST encoding streams large builtin strings with the same stored digest" {
    const Builder = @import("ast_builder.zig").Builder;
    const Dialect = @import("backends/evm/evm_dialect.zig");
    const Keccak = @import("../libsolutil/keccak256.zig");
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const generator = Builder.init(&arena, (try Dialect.strictAssemblyForEVMObjects(.current())).dialect());
    const label = try arena.allocator().alloc(u8, 10_000);
    @memset(label, 'x');
    const root = try generator.statements("datacopy(0, dataoffset(@0), datasize(@0))", .{label});
    var output = std.Io.Writer.Allocating.init(allocator);
    defer output.deinit();
    try encodeBlock(&output.writer, &root);
    const stored = Keccak.keccak256(output.written());
    try std.testing.expect(stored.eql(&try hashBlock(&root)));
}

test "Yul AST source encoding preserves indices, names, and absent tables" {
    const allocator = std.testing.allocator;
    var first: Objects.ObjectDebugData = .{ .source_names = .{} };
    defer first.deinit(allocator);
    var second: Objects.ObjectDebugData = .{ .source_names = .{} };
    defer second.deinit(allocator);
    try first.source_names.?.put(allocator, 3, "a.sol");
    try first.source_names.?.put(allocator, 0, "b\"\\\n.sol");
    try second.source_names.?.put(allocator, 0, "b\"\\\n.sol");
    try second.source_names.?.put(allocator, 3, "a.sol");
    const original = try hashSources(&first);
    try std.testing.expect(original.eql(&try hashSources(&second)));
    second.source_names.?.entries.items[1].index = 4;
    try std.testing.expect(!original.eql(&try hashSources(&second)));
    const empty = try hashSources(&.{ .source_names = .{} });
    try std.testing.expect(!empty.eql(&try hashSources(&.{})));
}

test "stored Yul AST validates corruption, schema, bounds and syntax" {
    const Snapshot = @import("ast_snapshot.zig").Snapshot;
    const Builder = @import("ast_builder.zig").Builder;
    const EVM = @import("backends/evm/evm_dialect.zig");
    const allocator = std.testing.allocator;
    const dialect = (try EVM.strictAssemblyForEVMObjects(.current())).dialect();
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const builder = Builder.init(&arena, dialect);
    var root = try builder.statements("let x := 0x01 mstore(0, x)", .{});
    const bytes = try encodeStoredBlockAlloc(allocator, &root);
    defer allocator.free(bytes);
    for (0..bytes.len) |length| try std.testing.expectError(error.CorruptAST, Snapshot.decode(allocator, bytes[0..length], dialect));
    bytes[bytes.len - 1] ^= 1;
    try std.testing.expectError(error.CorruptAST, Snapshot.decode(allocator, bytes, dialect));
    bytes[bytes.len - 1] ^= 1;

    const Helper = struct {
        fn updateChecksum(encoded: []u8) void {
            const split = encoded.len - H256.size;
            const digest = @import("../libsolutil/keccak256.zig").keccak256(encoded[0..split]);
            @memcpy(encoded[split..], digest.bytes());
        }
        fn reject(root_value: *const AST.Block, dialect_value: AST.Dialect) !void {
            const encoded = try encodeStoredBlockAlloc(std.testing.allocator, root_value);
            defer std.testing.allocator.free(encoded);
            try std.testing.expectError(error.CorruptAST, Snapshot.decode(std.testing.allocator, encoded, dialect_value));
        }
    };
    const schema_offset = block_magic.len + 3;
    bytes[schema_offset] = 0xff;
    Helper.updateChecksum(bytes);
    try std.testing.expectError(error.IncompatibleASTSchema, Snapshot.decode(allocator, bytes, dialect));
    bytes[schema_offset] = schema_version;
    const root_offset = block_magic.len + 4;
    bytes[root_offset] = 1; // No previous annotation exists.
    Helper.updateChecksum(bytes);
    try std.testing.expectError(error.CorruptAST, Snapshot.decode(allocator, bytes, dialect));
    bytes[root_offset] = 0;
    @memset(bytes[root_offset + 1 ..][0..4], 0xff); // Count exceeds remaining input.
    Helper.updateChecksum(bytes);
    try std.testing.expectError(error.CorruptAST, Snapshot.decode(allocator, bytes, dialect));

    // Correct checksums do not substitute for validating AST contents.
    root.statements.items[0].variable_declaration.value.?.literal.value.numeric_value = 2;
    try Helper.reject(&root, dialect); // Literal spelling disagrees with its value.
    root.statements.items[0].variable_declaration.value.?.literal.value.numeric_value = 1;
    root.statements.items[0].variable_declaration.variables.items[0].name = try YulName.init("a b");
    try Helper.reject(&root, dialect);
    root.statements.items[0].variable_declaration.variables.items[0].name = try YulName.init("x");
    root.statements.items[1].expression_statement.expression.function_call.function_name.builtin.handle.id = std.math.maxInt(u32);
    try Helper.reject(&root, dialect);
    const extra = try allocator.alloc(u8, bytes.len + 1);
    defer allocator.free(extra);
    const empty_bytes = try encodeStoredBlockAlloc(allocator, &.{});
    defer allocator.free(empty_bytes);
    const trailing = extra[0 .. empty_bytes.len + 1];
    @memcpy(trailing[0 .. empty_bytes.len - H256.size], empty_bytes[0 .. empty_bytes.len - H256.size]);
    trailing[empty_bytes.len - H256.size] = 0;
    Helper.updateChecksum(trailing);
    try std.testing.expectError(error.CorruptAST, Snapshot.decode(allocator, trailing, dialect));
    const break_statement: AST.Statement = .{ .break_statement = .{} };
    const invalid_loop: AST.Block = .{ .statements = .{ .items = @constCast(&[_]AST.Statement{break_statement}), .capacity = 1 } };
    try Helper.reject(&invalid_loop, dialect);
    const leave_statement: AST.Statement = .{ .leave_statement = .{} };
    const invalid_leave: AST.Block = .{ .statements = .{ .items = @constCast(&[_]AST.Statement{leave_statement}), .capacity = 1 } };
    try Helper.reject(&invalid_leave, dialect);

    var deep: AST.Block = .{};
    for (0..1201) |_| {
        const items = try arena.allocator().alloc(AST.Statement, 1);
        items[0] = .{ .block = deep };
        deep = .{ .statements = .{ .items = items, .capacity = 1 } };
    }
    try Helper.reject(&deep, dialect);
}

test "stored Yul AST restores lazy builtins and owns bytes through allocation failures" {
    const Snapshot = @import("ast_snapshot.zig").Snapshot;
    const Builder = @import("ast_builder.zig").Builder;
    const EVM = @import("backends/evm/evm_dialect.zig");
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    var producer_dialect = try EVM.EVMDialect.init(allocator, .current(), true);
    defer producer_dialect.deinit();
    const builder = Builder.init(&arena, producer_dialect.dialect());
    const root = try builder.statements("let x := verbatim_0i_1o(@0) mstore(0, x) pop(true) pop(@1)", .{ "\x60\x01", try builder.string("hi", .word) });
    const bytes = try encodeStoredBlockAlloc(allocator, &root);
    defer allocator.free(bytes);
    var consumer_dialect = try EVM.EVMDialect.init(allocator, .current(), true);
    defer consumer_dialect.deinit();
    const decoded = try Snapshot.decode(allocator, bytes, consumer_dialect.dialect());
    defer decoded.destroy(allocator);
    try std.testing.expect((try hashBlock(&root)).eql(&try hashBlock(&decoded.root)));
    @memset(bytes, 0);
    try std.testing.expect((try hashBlock(&root)).eql(&try hashBlock(&decoded.root)));

    const Helper = struct {
        fn check(failing: std.mem.Allocator, value: *const AST.Block, dialect: AST.Dialect) !void {
            const encoded = try encodeStoredBlockAlloc(failing, value);
            defer failing.free(encoded);
            const snapshot = try Snapshot.decode(failing, encoded, dialect);
            defer snapshot.destroy(failing);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Helper.check, .{ &root, consumer_dialect.dialect() });
}

test "Yul AST object cache identity excludes metadata and retains assembly inputs" {
    const Parser = @import("object_parser.zig").ObjectParser;
    const EVM = @import("backends/evm/evm_dialect.zig");
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const Keccak = @import("../libsolutil/keccak256.zig");
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const dialect = (try EVM.strictAssemblyForEVMObjects(.current())).dialect();
    const object = (try Parser.parseSource(allocator,
        \\/// @use-src 0:"C.sol"
        \\object "Root" { code { stop() }
        \\ object "Child" { code { stop() } data ".metadata" hex"1234" data "ordinary" hex"abcd" }
        \\}
    , "generated.yul", &reporter, dialect)).?;
    defer object.destroy();
    const original = try hashObjectWithoutMetadata(object);
    const stored = try encodeObjectWithoutMetadataAlloc(allocator, object);
    defer allocator.free(stored);
    try std.testing.expect(original.eql(&Keccak.keccak256(stored)));
    const child = object.sub_objects.items[0].object;
    // Parser data buffers are allocator-owned mutable bytes behind const views.
    @constCast(child.sub_objects.items[0].data.data)[0] ^= 1;
    try std.testing.expect(original.eql(&try hashObjectWithoutMetadata(object)));
    @constCast(child.sub_objects.items[1].data.data)[0] ^= 1;
    try std.testing.expect(!original.eql(&try hashObjectWithoutMetadata(object)));
    @constCast(child.sub_objects.items[1].data.data)[0] ^= 1;
    // Metadata presence itself has no influence on assembly input identity.
    var metadata = child.sub_objects.orderedRemove(0);
    defer metadata.deinit(allocator);
    _ = child.sub_index_by_name.remove(metadata.name());
    try child.sub_index_by_name.put(child.sub_objects.items[0].name(), 0);
    try std.testing.expect(original.eql(&try hashObjectWithoutMetadata(object)));
    child.code_value.?.root_block.debug_data.?.ast_id = 7;
    try std.testing.expect(!original.eql(&try hashObjectWithoutMetadata(object)));
    child.code_value.?.root_block.debug_data.?.ast_id = null;
    try std.testing.expect(original.eql(&try hashObjectWithoutMetadata(object)));
    object.debug_data.?.source_names.?.entries.items[0].index = 1;
    try std.testing.expect(!original.eql(&try hashObjectWithoutMetadata(object)));

    const Helper = struct {
        fn check(failing: std.mem.Allocator, value: *const Objects.Object) !void {
            const encoded = try encodeObjectWithoutMetadataAlloc(failing, value);
            defer failing.free(encoded);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Helper.check, .{object});
}
