// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Static Yul templates compile into typed AST construction, never runtime
//! parsing. Positional holes (`@0`) accept names, values or AST fragments as
//! required by their syntactic position. AST arguments are consumed; repeated
//! occurrences are deep-copied before the final occurrence takes ownership.
//! As with Builder, owned child storage must belong to the construction arena.

const std = @import("std");
const AST = @import("ast.zig");
const YulName = @import("yul_name.zig").YulName;
const Builder = @import("ast_builder.zig").Builder;
const Copier = @import("optimiser/ast_copier.zig").ASTCopier;
const SyntaxModule = @import("ast_template/syntax.zig");
const none = SyntaxModule.none;

pub const Error = @import("ast_builder.zig").BuildError || error{InvalidTemplateArgument};

pub fn expression(b: Builder, comptime source: []const u8, arguments: anytype) Error!AST.Expression {
    const template = comptime parse(source, true);
    return Instantiate(template).buildExpression(b, template.root, arguments, false);
}

pub fn statements(b: Builder, comptime source: []const u8, arguments: anytype) Error!AST.Block {
    const template = comptime parse(source, false);
    return Instantiate(template).block(b, template.root, arguments);
}

/// Construct a function directly, avoiding a temporary one-statement block.
pub fn functionDefinition(b: Builder, comptime source: []const u8, arguments: anytype) Error!AST.FunctionDefinition {
    const template = comptime parse(source, false);
    const first = comptime template.nodes[template.root].first;
    if (comptime first == none or template.nodes[first].kind != .function or template.nodes[first].next != none)
        @compileError("Yul function template must contain exactly one function");
    return (try Instantiate(template).statement(b, first, arguments)).function_definition;
}

fn parse(comptime source: []const u8, comptime only_expression: bool) SyntaxModule.Syntax(source) {
    @setEvalBranchQuota(100_000);
    return SyntaxModule.Syntax(source).parse(only_expression) catch |err|
        @compileError("invalid Yul AST template: " ++ @errorName(err) ++ "\n" ++ source);
}

fn Instantiate(comptime tree: anytype) type {
    return struct {
        const Self = @This();

        fn lastUse(comptime id: usize) bool {
            for (tree.nodes[id + 1 .. tree.count]) |node|
                if (node.kind == .hole and node.parameter == tree.nodes[id].parameter) return false;
            return true;
        }

        inline fn argument(comptime id: usize, values: anytype) @TypeOf(values[tree.nodes[id].parameter]) {
            if (tree.nodes[id].parameter >= values.len) @compileError("Yul template parameter is missing");
            return values[tree.nodes[id].parameter];
        }

        fn name(comptime id: usize, values: anytype) []const u8 {
            if (comptime tree.nodes[id].kind == .identifier) return tree.spelling(id);
            if (comptime tree.nodes[id].kind != .hole) @compileError("expected a Yul name");
            const value = argument(id, values);
            if (comptime !isBytes(@TypeOf(value))) @compileError("Yul name holes require identifier bytes");
            return value;
        }

        fn buildExpression(b: Builder, comptime id: usize, values: anytype, unlimited: bool) Error!AST.Expression {
            const node = comptime tree.nodes[id];
            switch (node.kind) {
                .identifier => return b.identifier(tree.spelling(id)),
                .number => {
                    const value = comptime SyntaxModule.numberValue(tree.spelling(id)) catch unreachable; // zlinter-disable-current-line no_swallow_error - numeric syntax was validated during compile-time template parsing
                    return .{ .literal = .{ .debug_data = b.debug_data, .kind = .Number, .value = try AST.LiteralValue.initNumeric(b.allocator(), value, tree.spelling(id)) } };
                },
                .boolean => return b.boolean(comptime std.mem.eql(u8, tree.spelling(id), "true")),
                .string => {
                    const decoded = comptime decodeString(tree.spelling(id));
                    return b.string(decoded.bytes[0..decoded.len], if (unlimited) .builtin else .word);
                },
                .hole => {
                    const value = argument(id, values);
                    const T = @TypeOf(value);
                    if (T == AST.Expression) {
                        if (comptime lastUse(id)) return value;
                        var copier = Copier.init(b.allocator());
                        return copier.translateExpression(&value) catch |err| return copyError(err);
                    }
                    if (T == YulName) return .{ .identifier = .{ .debug_data = b.debug_data, .name = value } };
                    if (comptime isBytes(T)) return if (unlimited) b.string(value, .builtin) else b.identifier(value);
                    if (T == bool) return b.boolean(value);
                    switch (@typeInfo(T)) {
                        .int, .comptime_int => {
                            const number = std.math.cast(u256, value) orelse return error.InvalidTemplateArgument;
                            return .{ .literal = .{ .debug_data = b.debug_data, .kind = .Number, .value = .{
                                .numeric_value = number,
                                .string_value = try std.fmt.allocPrint(b.allocator(), "{d}", .{number}),
                            } } };
                        },
                        else => @compileError("Yul expression holes require expressions, identifiers, integers or booleans"),
                    }
                },
                .call => {
                    const function_name = name(node.first, values);
                    var result = try b.call(function_name, &.{});
                    const builtin = if (result.function_call.function_name == .builtin)
                        b.dialect.builtin(result.function_call.function_name.builtin.handle) catch return error.InvalidTemplateArgument
                    else
                        null;
                    // Static grammar fixes the arity except for typed list holes.
                    // Count lengths without visiting or copying any child AST.
                    var capacity: usize = 0;
                    comptime var counted = tree.nodes[node.first].next;
                    inline while (counted != none) : (counted = tree.nodes[counted].next) {
                        capacity += if (comptime tree.nodes[counted].kind == .hole and isArgumentList(@TypeOf(argument(counted, values)))) argument(counted, values).len else 1;
                    }
                    try result.function_call.arguments.ensureTotalCapacityPrecise(b.allocator(), capacity);
                    comptime var child = tree.nodes[node.first].next;
                    inline while (child != none) : (child = tree.nodes[child].next) {
                        if (comptime tree.nodes[child].kind == .hole and isArgumentList(@TypeOf(argument(child, values)))) {
                            const input = argument(child, values);
                            for (input) |value| {
                                var copier = Copier.init(b.allocator());
                                const item: AST.Expression = if (@TypeOf(value) == YulName)
                                    .{ .identifier = .{ .debug_data = b.debug_data, .name = value } }
                                else if (comptime isBytes(@TypeOf(value))) try b.identifier(value) else if (comptime lastUse(child)) value else copier.translateExpression(&value) catch |err| return copyError(err);
                                result.function_call.arguments.appendAssumeCapacity(item);
                            }
                        } else {
                            const string_argument = if (builtin) |entry| entry.literalArgument(result.function_call.arguments.items.len) == .String else false;
                            result.function_call.arguments.appendAssumeCapacity(try Self.buildExpression(b, child, values, string_argument));
                        }
                    }
                    return result;
                },
                else => @compileError("expected an expression in Yul template"),
            }
        }

        fn bindings(b: Builder, comptime id: usize, values: anytype, comptime T: type) Error!std.ArrayList(T) {
            var capacity: usize = 0;
            comptime var counted = tree.nodes[id].first;
            inline while (counted != none) : (counted = tree.nodes[counted].next) {
                capacity += if (comptime tree.nodes[counted].kind == .hole and !isBytes(@TypeOf(argument(counted, values)))) argument(counted, values).len else 1;
            }
            var result = try std.ArrayList(T).initCapacity(b.allocator(), capacity);
            comptime var child = tree.nodes[id].first;
            inline while (child != none) : (child = tree.nodes[child].next) {
                if (comptime tree.nodes[child].kind == .hole and !isBytes(@TypeOf(argument(child, values)))) {
                    for (argument(child, values)) |text|
                        result.appendAssumeCapacity(.{ .debug_data = b.debug_data, .name = if (@TypeOf(text) == YulName) text else try b.name(text) });
                } else result.appendAssumeCapacity(.{ .debug_data = b.debug_data, .name = try b.name(name(child, values)) });
            }
            return result;
        }

        fn block(b: Builder, comptime id: usize, values: anytype) Error!AST.Block {
            var capacity: usize = 0;
            comptime var counted = tree.nodes[id].first;
            inline while (counted != none) : (counted = tree.nodes[counted].next) {
                capacity += if (comptime tree.nodes[counted].kind == .hole and @TypeOf(argument(counted, values)) == AST.Block) argument(counted, values).statements.items.len else 1;
            }
            var result: AST.Block = .{ .debug_data = b.debug_data, .statements = try .initCapacity(b.allocator(), capacity) };
            comptime var child = tree.nodes[id].first;
            inline while (child != none) : (child = tree.nodes[child].next) {
                if (comptime tree.nodes[child].kind == .hole) {
                    const value = argument(child, values);
                    const T = @TypeOf(value);
                    var copier = Copier.init(b.allocator());
                    if (T == AST.Block) {
                        var fragment = if (comptime lastUse(child)) value else copier.translateBlock(&value) catch |err| return copyError(err);
                        result.statements.appendSliceAssumeCapacity(fragment.statements.items);
                        // Only the temporary container is released; its children
                        // have transferred into result and must not be destroyed.
                        fragment.statements.deinit(b.allocator());
                    } else if (T == AST.Statement) {
                        const item = if (comptime lastUse(child)) value else copier.translateStatement(&value) catch |err| return copyError(err);
                        result.statements.appendAssumeCapacity(item);
                    } else @compileError("Yul statement holes require AST statements or blocks");
                } else result.statements.appendAssumeCapacity(try statement(b, child, values));
            }
            return result;
        }

        fn statement(b: Builder, comptime id: usize, values: anytype) Error!AST.Statement {
            const node = comptime tree.nodes[id];
            switch (node.kind) {
                .block => return .{ .block = try block(b, id, values) },
                .break_statement => return b.breakStatement(),
                .continue_statement => return b.continueStatement(),
                .leave_statement => return b.leaveStatement(),
                .expression_statement => return b.expressionStatement(try Self.buildExpression(b, node.first, values, false)),
                .declaration => {
                    const targets = try bindings(b, node.first, values, AST.NameWithDebugData);
                    if (targets.items.len == 0) return error.EmptyBinding;
                    const value_id = tree.nodes[node.first].next;
                    return .{ .variable_declaration = .{
                        .debug_data = b.debug_data,
                        .variables = targets,
                        .value = if (value_id == none) null else try AST.createExpression(b.allocator(), try Self.buildExpression(b, value_id, values, false)),
                    } };
                },
                .assignment => {
                    const identifiers = try bindings(b, node.first, values, AST.Identifier);
                    if (identifiers.items.len == 0) return error.EmptyBinding;
                    return .{ .assignment = .{
                        .debug_data = b.debug_data,
                        .variable_names = identifiers,
                        .value = try AST.createExpression(b.allocator(), try Self.buildExpression(b, tree.nodes[node.first].next, values, false)),
                    } };
                },
                .function => {
                    const parameters = tree.nodes[node.first].next;
                    const returns = tree.nodes[parameters].next;
                    return .{ .function_definition = .{
                        .debug_data = b.debug_data,
                        .name = try b.name(name(node.first, values)),
                        .parameters = try bindings(b, parameters, values, AST.NameWithDebugData),
                        .return_variables = try bindings(b, returns, values, AST.NameWithDebugData),
                        .body = try block(b, tree.nodes[returns].next, values),
                    } };
                },
                .if_statement => return b.ifStatement(try Self.buildExpression(b, node.first, values, false), try block(b, tree.nodes[node.first].next, values)),
                .for_loop => {
                    const condition = tree.nodes[node.first].next;
                    const post = tree.nodes[condition].next;
                    return b.forLoop(try block(b, node.first, values), try Self.buildExpression(b, condition, values, false), try block(b, post, values), try block(b, tree.nodes[post].next, values));
                },
                .switch_statement => {
                    comptime var capacity: usize = 0;
                    comptime var counted = tree.nodes[node.first].next;
                    inline while (counted != none) : (counted = tree.nodes[counted].next) {
                        capacity += 1;
                    }
                    var cases = try std.ArrayList(AST.Case).initCapacity(b.allocator(), capacity);
                    comptime var child = tree.nodes[node.first].next;
                    inline while (child != none) : (child = tree.nodes[child].next) {
                        const branch = comptime tree.nodes[child];
                        const literal: ?AST.Literal = if (branch.kind == .case_default) null else blk: {
                            const value = try Self.buildExpression(b, branch.first, values, false);
                            if (value != .literal) return error.InvalidTemplateArgument;
                            break :blk value.literal;
                        };
                        const body_id = if (branch.kind == .case_default) branch.first else tree.nodes[branch.first].next;
                        cases.appendAssumeCapacity(try b.case(literal, try block(b, body_id, values)));
                    }
                    return .{ .switch_statement = .{ .debug_data = b.debug_data, .expression = try AST.createExpression(b.allocator(), try Self.buildExpression(b, node.first, values, false)), .cases = cases } };
                },
                else => @compileError("expected a statement in Yul template"),
            }
        }
    };
}

fn isBytes(comptime T: type) bool {
    const pointer = switch (@typeInfo(T)) {
        .pointer => |p| p,
        else => return false,
    };
    if (pointer.size == .slice) return pointer.child == u8;
    return pointer.size == .one and @typeInfo(pointer.child) == .array and @typeInfo(pointer.child).array.child == u8;
}

fn isArgumentList(comptime T: type) bool {
    const pointer = switch (@typeInfo(T)) {
        .pointer => |p| p,
        else => return false,
    };
    if (pointer.size == .slice) return pointer.child == AST.Expression or pointer.child == YulName or isBytes(pointer.child);
    return pointer.size == .one and @typeInfo(pointer.child) == .array and (@typeInfo(pointer.child).array.child == AST.Expression or @typeInfo(pointer.child).array.child == YulName or isBytes(@typeInfo(pointer.child).array.child));
}

fn copyError(err: anyerror) Error {
    return if (err == error.OutOfMemory) error.OutOfMemory else error.InvalidTemplateArgument;
}

fn DecodedString(comptime length: usize) type {
    return struct { bytes: [length]u8, len: usize };
}

fn decodeString(comptime text: []const u8) DecodedString(text.len) {
    var result: DecodedString(text.len) = .{ .bytes = undefined, .len = 0 };
    var i: usize = 1;
    while (i + 1 < text.len) : (i += 1) {
        var c = text[i];
        if (c == '\\') {
            i += 1;
            c = switch (text[i]) {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                '\\' => '\\',
                '\'' => '\'',
                '"' => '"',
                'x' => blk: {
                    if (i + 3 >= text.len) @compileError("invalid Yul template string escape");
                    const byte = std.fmt.parseInt(u8, text[i + 1 ..][0..2], 16) catch @compileError("invalid Yul template hex escape");
                    i += 2;
                    break :blk byte;
                },
                else => @compileError("unsupported Yul template string escape; use a typed string hole"),
            };
        }
        result.bytes[result.len] = c;
        result.len += 1;
    }
    return result;
}

test "Yul AST template compiles typed holes and copies repeated expressions" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const Dialect = @import("backends/evm/evm_dialect.zig");
    var dialect = try Dialect.EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    const b = Builder.init(&arena, dialect.dialect());
    const add = try expression(b, "add(@0, 1)", .{try b.identifier("value")});
    var root = try statements(b,
        \\function @0(@1) -> @2 { @3 }
        \\let x := @0(@4)
        \\let first := @5
        \\let second := @5
        \\let data := dataoffset("long label exceeding thirty two bytes")
        \\let text := "a\x62\n"
    , .{ "f", &[_][]const u8{"value"}, &[_][]const u8{"result"}, try statements(b, "result := @0", .{try b.identifier("value")}), &[_]AST.Expression{b.number(7)}, add });
    try std.testing.expectEqual(@as(usize, 6), root.statements.items.len);
    const first = root.statements.items[2].variable_declaration.value.?;
    const second = root.statements.items[3].variable_declaration.value.?;
    try std.testing.expect(first.function_call.arguments.items.ptr != second.function_call.arguments.items.ptr);
    first.function_call.arguments.items[1].literal.value.numeric_value = 2;
    try std.testing.expectEqual(@as(u256, 1), second.function_call.arguments.items[1].literal.value.numeric_value.?);
    try std.testing.expect(root.statements.items[4].variable_declaration.value.?.function_call.arguments.items[0].literal.value.unlimited());
    try std.testing.expectEqualStrings("ab\n", root.statements.items[5].variable_declaration.value.?.literal.value.string_value.?);
}

test "Yul AST templates preserve the complete statement grammar and failure ownership" {
    const source =
        \\function f(a) -> result {
        \\    let x, y
        \\    x, y := pair(a)
        \\    result := 0
        \\    for { let i := 0 } lt(i, x) { i := add(i, 1) } {
        \\        if eq(i, 1) { continue }
        \\        if eq(i, 9) { break }
        \\        switch i case 2 { result := y } default { result := add(result, i) }
        \\    }
        \\    { let temporary := 0x00ff pop(temporary) }
        \\    leave
        \\}
        \\function pair(value) -> x, y { x := value y := 2 }
        \\mstore(0, f(3))
    ;
    const allocator = std.testing.allocator;
    const Dialect = @import("backends/evm/evm_dialect.zig");
    const Parser = @import("asm_parser.zig").Parser;
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const Equality = @import("optimiser/syntactical_equality.zig").SyntacticallyEqual;
    var dialect = try Dialect.EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const built = try statements(Builder.init(&arena, dialect.dialect()), source, .{});
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var parsed = (try Parser.parseSource(allocator, "{\n" ++ source ++ "\n}", "reference.yul", &reporter, dialect.dialect(), .{})).?;
    defer parsed.deinit();
    var equal = Equality.init(allocator);
    defer equal.deinit();
    try std.testing.expect(!reporter.hasErrors());
    try std.testing.expect(try equal.block(&built, parsed.root()));
    const Failure = struct {
        fn run(failing: std.mem.Allocator) !void {
            var local = std.heap.ArenaAllocator.init(failing);
            defer local.deinit();
            const b = Builder.init(&local, .{});
            _ = try statements(b, source, .{});
            const body = try statements(b, "pop(1)", .{});
            _ = try statements(b, "function @0(@1) -> @2 { @3 @3 }", .{ "empty", &[_][]const u8{}, &[_][]const u8{}, body });
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Failure.run, .{});
}

comptime {
    _ = SyntaxModule;
}

test "Yul AST interned names expand bindings and calls, including empty lists" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const Dialect = @import("backends/evm/evm_dialect.zig").EVMDialect;
    var dialect = try Dialect.init(allocator, .current(), true);
    defer dialect.deinit();
    const b = Builder.init(&arena, dialect.dialect());
    const names = try b.indexedNames("value_", 2);
    const empty = try b.indexedNames("unused_", 0);
    const definition = try b.functionDefinition("function f(@0) -> @1 { @1 := pair(@0, @2) }", .{ names, try b.indexedNames("result_", 2), empty });
    try std.testing.expectEqual(@as(usize, 2), definition.parameters.items.len);
    const arguments = definition.body.statements.items[0].assignment.value.?.function_call.arguments.items;
    try std.testing.expectEqual(@as(usize, 2), arguments.len);
    for (arguments, definition.parameters.items) |argument, parameter| {
        try std.testing.expect(argument.identifier.name.eql(parameter.name));
    }
    const no_returns = try b.functionDefinition("function empty(@0) -> @0 { g(@0) }", .{empty});
    try std.testing.expectEqual(@as(usize, 0), no_returns.return_variables.items.len);
}

test "Yul AST runtime object labels remain string literals at builtin boundaries" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    var dialect = try @import("backends/evm/evm_dialect.zig").EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    const b = Builder.init(&arena, dialect.dialect());
    const label: []const u8 = "contract label exceeding thirty two bytes";
    const body = try b.statements("let size := datasize(@0) datacopy(0, dataoffset(@0), size)", .{label});
    const size = body.statements.items[0].variable_declaration.value.?.function_call.arguments.items[0].literal;
    const offset = body.statements.items[1].expression_statement.expression.function_call.arguments.items[1].function_call.arguments.items[0].literal;
    try std.testing.expectEqual(AST.LiteralKind.String, size.kind);
    try std.testing.expect(size.value.unlimited());
    try std.testing.expectEqualStrings(label, size.value.string_value.?);
    try std.testing.expectEqualStrings(label, offset.value.string_value.?);
    try std.testing.expect(size.value.string_value.?.ptr != offset.value.string_value.?.ptr);
    const named = try b.expression("custom(@0)", .{"argument"});
    try std.testing.expectEqualStrings("argument", try named.function_call.arguments.items[0].identifier.name.str());
}
