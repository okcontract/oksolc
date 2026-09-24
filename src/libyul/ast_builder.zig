// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Typed construction of the existing Yul AST in a phase-owned arena.
//!
//! Child values passed to constructors are moved, never shared, and must use
//! this arena for any owned storage. Use the existing ASTCopier when importing
//! a foreign tree or when an expression or block must occur more than once.
//! The caller owns the arena and must keep it alive until the resulting tree
//! has been consumed or copied. Arena ownership also covers incomplete trees
//! after an allocation failure, allowing nested `try` construction safely.

const std = @import("std");
const AST = @import("ast.zig");
const Utilities = @import("utilities.zig");
const YulName = @import("yul_name.zig").YulName;
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const Lexical = @import("../liblangutil/common.zig");

pub const BuildError = std.mem.Allocator.Error || error{ InvalidIdentifier, EmptyBinding, StringTooLong };

pub const Builder = struct {
    arena: *std.heap.ArenaAllocator,
    dialect: AST.Dialect,
    debug_data: ?DebugData = null,

    pub fn init(arena: *std.heap.ArenaAllocator, dialect: AST.Dialect) Builder {
        return .{ .arena = arena, .dialect = dialect };
    }

    /// Static grammar is checked at Zig compile time; runtime work only builds
    /// the existing AST. Arguments obey this builder's arena ownership rules.
    pub fn expression(self: Builder, comptime source: []const u8, arguments: anytype) @import("ast_template.zig").Error!AST.Expression {
        return @import("ast_template.zig").expression(self, source, arguments);
    }

    pub fn statements(self: Builder, comptime source: []const u8, arguments: anytype) @import("ast_template.zig").Error!AST.Block {
        return @import("ast_template.zig").statements(self, source, arguments);
    }

    pub fn functionDefinition(self: Builder, comptime source: []const u8, arguments: anytype) @import("ast_template.zig").Error!AST.FunctionDefinition {
        return @import("ast_template.zig").functionDefinition(self, source, arguments);
    }

    pub fn withDebug(self: Builder, data: ?DebugData) Builder {
        var result = self;
        result.debug_data = data;
        return result;
    }

    pub fn allocator(self: Builder) std.mem.Allocator {
        return self.arena.allocator();
    }

    pub fn name(_: Builder, text: []const u8) BuildError!YulName {
        if (text.len == 0 or !Lexical.isIdentifierStart(text[0])) return error.InvalidIdentifier;
        for (text[1..]) |c| if (!Lexical.isIdentifierPart(c) and c != '.') return error.InvalidIdentifier;
        return YulName.init(text);
    }

    /// Intern generated local names once; immutable handles can be reused in
    /// binding and expression lists without allocating temporary expressions.
    pub fn indexedNames(self: Builder, prefix: []const u8, count: usize) BuildError![]const YulName {
        return self.indexedNameRange(prefix, 0, count);
    }

    pub fn indexedNameRange(self: Builder, prefix: []const u8, start: usize, end: usize) BuildError![]const YulName {
        std.debug.assert(start <= end);
        const names = try self.allocator().alloc(YulName, end - start);
        for (names, start..) |*entry, index| {
            const text = try std.fmt.allocPrint(self.allocator(), "{s}{d}", .{ prefix, index });
            defer self.allocator().free(text);
            entry.* = try self.name(text);
        }
        return names;
    }

    pub fn identifier(self: Builder, text: []const u8) BuildError!AST.Expression {
        return .{ .identifier = .{ .debug_data = self.debug_data, .name = try self.name(text) } };
    }

    pub fn number(self: Builder, value: u256) AST.Expression {
        return .{ .literal = .{ .debug_data = self.debug_data, .kind = .Number, .value = .{ .numeric_value = value } } };
    }

    /// A numeric token's spelling can affect published IR. Parse just that
    /// literal value, using the same rules as user input, without parsing code.
    pub fn numberToken(self: Builder, token: []const u8) Utilities.LiteralError!AST.Expression {
        return .{ .literal = .{
            .debug_data = self.debug_data,
            .kind = .Number,
            .value = try Utilities.valueOfNumberLiteral(self.allocator(), token),
        } };
    }

    pub fn boolean(self: Builder, value: bool) AST.Expression {
        return .{ .literal = .{ .debug_data = self.debug_data, .kind = .Boolean, .value = .{ .numeric_value = @intFromBool(value) } } };
    }

    pub fn string(self: Builder, bytes: []const u8, mode: enum { word, builtin }) BuildError!AST.Expression {
        if (mode == .word and bytes.len > 32) return error.StringTooLong;
        return .{ .literal = .{
            .debug_data = self.debug_data,
            .kind = .String,
            .value = if (mode == .builtin)
                try Utilities.valueOfBuiltinStringLiteralArgument(self.allocator(), bytes)
            else
                try Utilities.valueOfStringLiteral(self.allocator(), bytes),
        } };
    }

    /// Preserve the shared word-literal kind and numeric spelling directly.
    pub fn word(self: Builder, bytes: []const u8) BuildError!AST.Expression {
        if (bytes.len > 32) return error.StringTooLong;
        if (@import("../libsolutil/common_data.zig").preferStringLiteral(bytes))
            return self.string(bytes, .word);
        const value = @import("../libsolutil/fixed_hash.zig").H256.fromBytes(bytes, .align_left);
        const hex = value.hex();
        return .{ .literal = .{
            .debug_data = self.debug_data,
            .kind = .Number,
            .value = .{
                .numeric_value = std.mem.readInt(u256, &value.storage, .big),
                .string_value = try std.fmt.allocPrint(self.allocator(), "0x{s}", .{hex}),
            },
        } };
    }

    pub fn call(self: Builder, function_text: []const u8, arguments: []const AST.Expression) BuildError!AST.Expression {
        return .{ .function_call = .{
            .debug_data = self.debug_data,
            .function_name = if (self.dialect.findBuiltin(function_text)) |handle|
                .{ .builtin = .{ .debug_data = self.debug_data, .handle = handle } }
            else
                .{ .identifier = .{ .debug_data = self.debug_data, .name = try self.name(function_text) } },
            .arguments = .fromOwnedSlice(try self.allocator().dupe(AST.Expression, arguments)),
        } };
    }

    pub fn expressionStatement(self: Builder, value: AST.Expression) AST.Statement {
        return .{ .expression_statement = .{ .debug_data = self.debug_data, .expression = value } };
    }

    pub fn declare(self: Builder, names: []const []const u8, value: ?AST.Expression) BuildError!AST.Statement {
        if (names.len == 0) return error.EmptyBinding;
        return .{ .variable_declaration = .{
            .debug_data = self.debug_data,
            .variables = try self.bindingNames(names),
            .value = if (value) |initial_value| try AST.createExpression(self.allocator(), initial_value) else null,
        } };
    }

    pub fn assign(self: Builder, names: []const []const u8, value: AST.Expression) BuildError!AST.Statement {
        if (names.len == 0) return error.EmptyBinding;
        const targets = try self.allocator().alloc(AST.Identifier, names.len);
        for (targets, names) |*target, text| target.* = .{ .debug_data = self.debug_data, .name = try self.name(text) };
        return .{ .assignment = .{
            .debug_data = self.debug_data,
            .variable_names = .fromOwnedSlice(targets),
            .value = try AST.createExpression(self.allocator(), value),
        } };
    }

    pub fn block(self: Builder, children: []const AST.Statement) std.mem.Allocator.Error!AST.Block {
        return .{ .debug_data = self.debug_data, .statements = .fromOwnedSlice(try self.allocator().dupe(AST.Statement, children)) };
    }

    pub fn function(self: Builder, function_name: []const u8, parameters: []const []const u8, returns: []const []const u8, body: AST.Block) BuildError!AST.Statement {
        return .{ .function_definition = .{
            .debug_data = self.debug_data,
            .name = try self.name(function_name),
            .parameters = try self.bindingNames(parameters),
            .return_variables = try self.bindingNames(returns),
            .body = body,
        } };
    }

    pub fn ifStatement(self: Builder, condition: AST.Expression, body: AST.Block) std.mem.Allocator.Error!AST.Statement {
        return .{ .if_statement = .{
            .debug_data = self.debug_data,
            .condition = try AST.createExpression(self.allocator(), condition),
            .body = body,
        } };
    }

    pub fn case(self: Builder, value: ?AST.Literal, body: AST.Block) std.mem.Allocator.Error!AST.Case {
        return .{
            .debug_data = self.debug_data,
            .value = if (value) |literal| try AST.createLiteral(self.allocator(), literal) else null,
            .body = body,
        };
    }

    pub fn switchStatement(self: Builder, value: AST.Expression, cases: []const AST.Case) std.mem.Allocator.Error!AST.Statement {
        return .{ .switch_statement = .{
            .debug_data = self.debug_data,
            .expression = try AST.createExpression(self.allocator(), value),
            .cases = .fromOwnedSlice(try self.allocator().dupe(AST.Case, cases)),
        } };
    }

    pub fn forLoop(self: Builder, pre: AST.Block, condition: AST.Expression, post: AST.Block, body: AST.Block) std.mem.Allocator.Error!AST.Statement {
        return .{ .for_loop = .{
            .debug_data = self.debug_data,
            .pre = pre,
            .condition = try AST.createExpression(self.allocator(), condition),
            .post = post,
            .body = body,
        } };
    }

    pub fn breakStatement(self: Builder) AST.Statement {
        return .{ .break_statement = .{ .debug_data = self.debug_data } };
    }

    pub fn continueStatement(self: Builder) AST.Statement {
        return .{ .continue_statement = .{ .debug_data = self.debug_data } };
    }

    pub fn leaveStatement(self: Builder) AST.Statement {
        return .{ .leave_statement = .{ .debug_data = self.debug_data } };
    }

    fn bindingNames(self: Builder, texts: []const []const u8) BuildError!AST.NameWithDebugDataList {
        const result = try self.allocator().alloc(AST.NameWithDebugData, texts.len);
        for (result, texts) |*item, text| item.* = .{ .debug_data = self.debug_data, .name = try self.name(text) };
        return .fromOwnedSlice(result);
    }
};

fn buildTestTree(builder: Builder) !AST.Block {
    const b = builder;
    return b.block(&.{
        try b.function("sum", &.{"limit"}, &.{"result"}, try b.block(&.{
            try b.assign(&.{"result"}, b.number(0)),
            try b.forLoop(
                try b.block(&.{try b.declare(&.{"i"}, b.number(0))}),
                try b.call("lt", &.{ try b.identifier("i"), try b.identifier("limit") }),
                try b.block(&.{try b.assign(&.{"i"}, try b.call("add", &.{ try b.identifier("i"), b.number(1) }))}),
                try b.block(&.{
                    try b.ifStatement(try b.call("eq", &.{ try b.identifier("i"), b.number(2) }), try b.block(&.{b.continueStatement()})),
                    try b.ifStatement(try b.call("eq", &.{ try b.identifier("i"), b.number(7) }), try b.block(&.{b.breakStatement()})),
                    try b.assign(&.{"result"}, try b.call("add", &.{ try b.identifier("result"), try b.identifier("i") })),
                }),
            ),
            b.leaveStatement(),
        })),
        try b.declare(&.{"value"}, try b.call("sum", &.{b.number(10)})),
        try b.switchStatement(try b.identifier("value"), &.{
            try b.case(b.number(0).literal, try b.block(&.{b.expressionStatement(try b.call("stop", &.{}))})),
            try b.case(null, try b.block(&.{b.expressionStatement(try b.call("mstore", &.{ b.number(0), try b.identifier("value") }))})),
        }),
        .{ .block = try b.block(&.{
            try b.declare(&.{"text"}, try b.string("abc", .word)),
            try b.declare(&.{"yes"}, b.boolean(true)),
            try b.declare(&.{"offset"}, try b.call("dataoffset", &.{try b.string("child", .builtin)})),
            try b.declare(&.{ "a", "b" }, null),
        }) },
    });
}

test "Yul AST builder produces the parser tree and survives its construction arena" {
    const allocator = std.testing.allocator;
    const Dialect = @import("backends/evm/evm_dialect.zig");
    const Parser = @import("asm_parser.zig").Parser;
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const Copier = @import("optimiser/ast_copier.zig").ASTCopier;
    const Equality = @import("optimiser/syntactical_equality.zig").SyntacticallyEqual;
    var dialect = try Dialect.EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var arena = std.heap.ArenaAllocator.init(allocator);
    var arena_owned = true;
    defer if (arena_owned) arena.deinit();
    const builder = Builder.init(&arena, dialect.dialect()).withDebug(.{ .origin_location = .{ .start = 2, .end = 5, .source_name = "input.sol" } });
    const root = try buildTestTree(builder);
    var copier = Copier.init(allocator);
    var owned = try copier.translateBlock(&root);
    defer owned.deinit(allocator);
    arena.deinit();
    arena_owned = false;
    try std.testing.expectEqual(@as(i32, 2), owned.debug_data.?.origin_location.start);
    try std.testing.expectEqualStrings("abc", owned.statements.items[3].block.statements.items[0].variable_declaration.value.?.literal.value.string_value.?);
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var parsed = (try Parser.parseSource(allocator,
        \\{
        \\  function sum(limit) -> result {
        \\    result := 0
        \\    for { let i := 0 } lt(i, limit) { i := add(i, 1) } {
        \\      if eq(i, 2) { continue }
        \\      if eq(i, 7) { break }
        \\      result := add(result, i)
        \\    }
        \\    leave
        \\  }
        \\  let value := sum(10)
        \\  switch value case 0 { stop() } default { mstore(0, value) }
        \\  { let text := "abc" let yes := true let offset := dataoffset("child") let a, b }
        \\}
    , "input.yul", &reporter, dialect.dialect(), .{})).?;
    defer parsed.deinit();
    try std.testing.expect(!reporter.hasErrors());
    var equal = Equality.init(allocator);
    defer equal.deinit();
    try std.testing.expect(try equal.block(&owned, parsed.root()));
}

test "Yul AST builder literal boundaries and allocation failures are explicit" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const b = Builder.init(&arena, .{});
    try std.testing.expectError(error.InvalidIdentifier, b.identifier("x, y"));
    try std.testing.expectError(error.EmptyBinding, b.declare(&.{}, null));
    try std.testing.expectError(error.EmptyBinding, b.assign(&.{}, b.number(0)));
    try std.testing.expectError(error.StringTooLong, b.string("a" ** 33, .word));
    try std.testing.expect((try b.string("a" ** 33, .builtin)).literal.value.unlimited());
    try std.testing.expectEqual(@as(u256, 0), (try b.string("", .word)).literal.value.numeric_value.?);
    try std.testing.expectEqual(@as(u256, 255), (try b.numberToken("0x00ff")).literal.value.numeric_value.?);
    try std.testing.expectEqualStrings("0x00ff", (try b.numberToken("0x00ff")).literal.value.string_value.?);
    try std.testing.expectError(error.InvalidNumberLiteral, b.numberToken("1 pop(0)"));
    const Failure = struct {
        fn run(failing: std.mem.Allocator) !void {
            var local = std.heap.ArenaAllocator.init(failing);
            defer local.deinit();
            const root = try buildTestTree(Builder.init(&local, .{}));
            try std.testing.expectEqual(@as(usize, 4), root.statements.items.len);
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Failure.run, .{});
}

test "Yul AST word literals retain string or numeric representation" {
    const allocator = std.testing.allocator;
    const Dialect = @import("backends/evm/evm_dialect.zig").EVMDialect;
    var dialect = try Dialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const builder = Builder.init(&arena, dialect.dialect());
    var printer = @import("asm_printer.zig").AsmPrinter.init(allocator, dialect.dialect(), &.{}, .noneValue(), null);
    const words = [_][]const u8{ "", "hello", "a\\b", "a\"b", "a\x00b", "\xff", "01234567890123456789012345678901" };
    for (words) |bytes| {
        const expression_value = try builder.word(bytes);
        const rendered = try printer.renderExpression(&expression_value);
        defer allocator.free(rendered);
        const reference = try @import("../libsolutil/common_data.zig").formatAsStringOrNumberAlloc(allocator, bytes);
        defer allocator.free(reference);
        try std.testing.expectEqualStrings(reference, rendered);
    }
    try std.testing.expectError(error.StringTooLong, builder.word("012345678901234567890123456789012"));
}
