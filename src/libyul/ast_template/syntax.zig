// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Compile-time syntax for typed Yul construction templates. `@0`, `@1`, ...
//! denote typed substitutions, never runtime source text. This grammar is
//! deliberately independent of user-input diagnostics and source scanning.

const std = @import("std");
const Lexical = @import("../../liblangutil/common.zig");

pub const none = std.math.maxInt(usize);
pub const Kind = enum {
    identifier,
    number,
    string,
    boolean,
    hole,
    call,
    block,
    declaration,
    assignment,
    expression_statement,
    function,
    bindings,
    if_statement,
    switch_statement,
    case_value,
    case_default,
    for_loop,
    break_statement,
    continue_statement,
    leave_statement,
};
pub const Node = struct {
    kind: Kind,
    start: usize = 0,
    end: usize = 0,
    first: usize = none,
    next: usize = none,
    parameter: usize = 0,
};
pub const ParseError = error{ InvalidTemplate, InvalidNumber, InvalidString, TemplateTooDeep };

pub fn Syntax(comptime source: []const u8) type {
    return struct {
        const Self = @This();
        pub const text = source;
        nodes: [source.len + 1]Node = undefined,
        count: usize = 0,
        position: usize = 0,
        depth: usize = 0,
        root: usize = none,

        pub fn parse(comptime expression_only: bool) ParseError!Self {
            @setEvalBranchQuota(100_000);
            var parser: Self = .{};
            parser.root = if (expression_only) try parser.expression() else try parser.statements(false);
            try parser.skip();
            if (parser.position != source.len) return error.InvalidTemplate;
            return parser;
        }

        pub fn spelling(self: *const Self, id: usize) []const u8 {
            return source[self.nodes[id].start..self.nodes[id].end];
        }

        fn add(self: *Self, node: Node) usize {
            std.debug.assert(self.count < self.nodes.len);
            const id = self.count;
            self.nodes[id] = node;
            self.count += 1;
            return id;
        }

        fn append(self: *Self, parent: usize, child: usize) void {
            if (self.nodes[parent].first == none) {
                self.nodes[parent].first = child;
                return;
            }
            var last = self.nodes[parent].first;
            while (self.nodes[last].next != none) last = self.nodes[last].next;
            self.nodes[last].next = child;
        }

        fn skip(self: *Self) ParseError!void {
            while (self.position < source.len) {
                if (Lexical.isWhiteSpace(source[self.position])) {
                    self.position += 1;
                } else if (std.mem.startsWith(u8, source[self.position..], "//")) {
                    while (self.position < source.len and source[self.position] != '\n') self.position += 1;
                } else if (std.mem.startsWith(u8, source[self.position..], "/*")) {
                    const length = std.mem.find(u8, source[self.position + 2 ..], "*/") orelse return error.InvalidTemplate;
                    self.position += length + 4;
                } else break;
            }
        }

        fn take(self: *Self, token: []const u8) ParseError!bool {
            try self.skip();
            if (!std.mem.startsWith(u8, source[self.position..], token)) return false;
            if (Lexical.isIdentifierPart(token[token.len - 1]) and self.position + token.len < source.len and
                (Lexical.isIdentifierPart(source[self.position + token.len]) or source[self.position + token.len] == '.')) return false;
            self.position += token.len;
            return true;
        }

        fn expect(self: *Self, token: []const u8) ParseError!void {
            if (!try self.take(token)) return error.InvalidTemplate;
        }

        fn identifier(self: *Self) ParseError!usize {
            try self.skip();
            const start = self.position;
            if (start == source.len) return error.InvalidTemplate;
            if (source[start] == '@') {
                self.position += 1;
                const digits = self.position;
                while (self.position < source.len and std.ascii.isDigit(source[self.position])) self.position += 1;
                if (digits == self.position) return error.InvalidTemplate;
                if (self.position < source.len and (Lexical.isIdentifierPart(source[self.position]) or source[self.position] == '.')) return error.InvalidTemplate;
                return self.add(.{ .kind = .hole, .start = start, .end = self.position, .parameter = std.fmt.parseInt(usize, source[digits..self.position], 10) catch return error.InvalidTemplate });
            }
            if (!Lexical.isIdentifierStart(source[start])) return error.InvalidTemplate;
            self.position += 1;
            while (self.position < source.len and (Lexical.isIdentifierPart(source[self.position]) or source[self.position] == '.')) self.position += 1;
            return self.add(.{ .kind = .identifier, .start = start, .end = self.position });
        }

        fn expression(self: *Self) ParseError!usize {
            self.depth += 1;
            defer self.depth -= 1;
            if (self.depth > 256) return error.TemplateTooDeep;
            try self.skip();
            const start = self.position;
            if (start == source.len) return error.InvalidTemplate;
            const c = source[start];
            if (c == '"' or c == '\'') {
                self.position += 1;
                while (self.position < source.len and source[self.position] != c) {
                    if (source[self.position] == '\\') self.position += 1;
                    if (self.position == source.len) return error.InvalidString;
                    self.position += 1;
                }
                if (self.position == source.len) return error.InvalidString;
                self.position += 1;
                return self.add(.{ .kind = .string, .start = start, .end = self.position });
            }
            if (std.ascii.isDigit(c)) {
                self.position += 1;
                while (self.position < source.len and std.ascii.isAlphanumeric(source[self.position])) self.position += 1;
                _ = numberValue(source[start..self.position]) catch return error.InvalidNumber;
                return self.add(.{ .kind = .number, .start = start, .end = self.position });
            }
            const name = try self.identifier();
            if (std.mem.eql(u8, self.spelling(name), "true") or std.mem.eql(u8, self.spelling(name), "false")) {
                self.nodes[name].kind = .boolean;
                return name;
            }
            if (!try self.take("(")) return name;
            const call = self.add(.{ .kind = .call });
            self.append(call, name);
            if (!try self.take(")")) {
                while (true) {
                    self.append(call, try self.expression());
                    if (!try self.take(",")) break;
                }
                try self.expect(")");
            }
            return call;
        }

        fn bindings(self: *Self) ParseError!usize {
            const list = self.add(.{ .kind = .bindings });
            self.append(list, try self.identifier());
            while (try self.take(",")) self.append(list, try self.identifier());
            return list;
        }

        fn statements(self: *Self, braced: bool) ParseError!usize {
            self.depth += 1;
            defer self.depth -= 1;
            if (self.depth > 256) return error.TemplateTooDeep;
            if (braced) try self.expect("{");
            const result = self.add(.{ .kind = .block });
            while (true) {
                try self.skip();
                if (self.position == source.len) {
                    if (braced) return error.InvalidTemplate;
                    break;
                }
                if (braced and try self.take("}")) break;
                self.append(result, try self.statement());
            }
            return result;
        }

        fn statement(self: *Self) ParseError!usize {
            try self.skip();
            if (source[self.position] == '{') return self.statements(true);
            inline for (.{ .{ "break", Kind.break_statement }, .{ "continue", Kind.continue_statement }, .{ "leave", Kind.leave_statement } }) |entry|
                if (try self.take(entry[0])) return self.add(.{ .kind = entry[1] });
            if (try self.take("let")) {
                const result = self.add(.{ .kind = .declaration });
                self.append(result, try self.bindings());
                if (try self.take(":=")) self.append(result, try self.expression());
                return result;
            }
            if (try self.take("function")) {
                const result = self.add(.{ .kind = .function });
                self.append(result, try self.identifier());
                try self.expect("(");
                self.append(result, if (try self.take(")")) self.add(.{ .kind = .bindings }) else blk: {
                    const parameters = try self.bindings();
                    try self.expect(")");
                    break :blk parameters;
                });
                self.append(result, if (try self.take("->")) try self.bindings() else self.add(.{ .kind = .bindings }));
                self.append(result, try self.statements(true));
                return result;
            }
            if (try self.take("if")) {
                const result = self.add(.{ .kind = .if_statement });
                self.append(result, try self.expression());
                self.append(result, try self.statements(true));
                return result;
            }
            if (try self.take("for")) {
                const result = self.add(.{ .kind = .for_loop });
                self.append(result, try self.statements(true));
                self.append(result, try self.expression());
                self.append(result, try self.statements(true));
                self.append(result, try self.statements(true));
                return result;
            }
            if (try self.take("switch")) {
                const result = self.add(.{ .kind = .switch_statement });
                self.append(result, try self.expression());
                var cases: usize = 0;
                while (try self.take("case")) {
                    const branch = self.add(.{ .kind = .case_value });
                    self.append(branch, try self.expression());
                    self.append(branch, try self.statements(true));
                    self.append(result, branch);
                    cases += 1;
                }
                if (try self.take("default")) {
                    const branch = self.add(.{ .kind = .case_default });
                    self.append(branch, try self.statements(true));
                    self.append(result, branch);
                    cases += 1;
                }
                if (cases == 0) return error.InvalidTemplate;
                return result;
            }
            const first = try self.expression();
            if (self.nodes[first].kind == .call) {
                const result = self.add(.{ .kind = .expression_statement });
                self.append(result, first);
                return result;
            }
            if (self.nodes[first].kind != .identifier and self.nodes[first].kind != .hole) return error.InvalidTemplate;
            if (self.nodes[first].kind == .hole) {
                try self.skip();
                if (!std.mem.startsWith(u8, source[self.position..], ",") and !std.mem.startsWith(u8, source[self.position..], ":=")) return first;
            }
            const result = self.add(.{ .kind = .assignment });
            const variables = self.add(.{ .kind = .bindings });
            self.append(variables, first);
            while (try self.take(",")) self.append(variables, try self.identifier());
            self.append(result, variables);
            try self.expect(":=");
            self.append(result, try self.expression());
            return result;
        }
    };
}

pub fn numberValue(text: []const u8) ParseError!u256 {
    if (std.mem.startsWith(u8, text, "0x")) return std.fmt.parseInt(u256, text[2..], 16) catch error.InvalidNumber;
    return std.fmt.parseInt(u256, text, 10) catch error.InvalidNumber;
}

test "Yul AST template grammar rejects malformed static code" {
    try std.testing.expectError(error.InvalidTemplate, comptime Syntax("let x :=").parse(false));
    try std.testing.expectError(error.InvalidTemplate, comptime Syntax("function x(a) { ").parse(false));
    try std.testing.expectError(error.InvalidTemplate, comptime Syntax("switch x").parse(false));
    try std.testing.expectError(error.InvalidNumber, comptime Syntax("0xnotanumber").parse(true));
    try std.testing.expectError(error.InvalidString, comptime Syntax("\"unterminated").parse(true));
    _ = comptime try Syntax("function @0(@1) -> @2 { @3 } let x := @0(@4)").parse(false);
}
