// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Semantic-version parsing and pragma match expressions translated from
//! `SemVerHandler.h/.cpp`.

const std = @import("std");
const Token = @import("token.zig").Token;

pub const SemVerError = error{
    EmptyVersionPragma,
    IntegerTooLarge,
    InvalidRangeCombination,
    ExpectedVersionNumber,
    InvalidVersionStart,
    InvalidExpression,
    InvalidVersion,
};

pub const wildcard = std.math.maxInt(u32);

pub const SemVerVersion = struct {
    numbers: [3]u32 = .{ 0, 0, 0 },
    prerelease: []u8 = &.{},
    build: []u8 = &.{},
    owner_allocator: ?std.mem.Allocator = null,

    pub fn init(
        allocator: std.mem.Allocator,
        version_string: []const u8,
    ) (std.mem.Allocator.Error || SemVerError)!SemVerVersion {
        var result: SemVerVersion = .{ .owner_allocator = allocator };
        errdefer result.deinit();
        var index: usize = 0;
        for (0..3) |level| {
            var value: u32 = 0;
            while (index < version_string.len and isDigit(version_string[index])) : (index += 1) {
                value = value *% 10 +% (version_string[index] - '0');
            }
            result.numbers[level] = value;
            if (level < 2) {
                if (index == version_string.len or version_string[index] != '.') {
                    return error.InvalidVersion;
                }
                index += 1;
            }
        }
        if (index < version_string.len and version_string[index] == '-') {
            index += 1;
            const start = index;
            while (index < version_string.len and version_string[index] != '+') : (index += 1) {}
            result.prerelease = try allocator.dupe(u8, version_string[start..index]);
        } else {
            result.prerelease = try allocator.alloc(u8, 0);
        }
        if (index < version_string.len and version_string[index] == '+') {
            index += 1;
            result.build = try allocator.dupe(u8, version_string[index..]);
            index = version_string.len;
        } else {
            result.build = try allocator.alloc(u8, 0);
        }
        if (index != version_string.len) return error.InvalidVersion;
        return result;
    }

    pub fn clone(self: SemVerVersion, allocator: std.mem.Allocator) !SemVerVersion {
        const prerelease = try allocator.dupe(u8, self.prerelease);
        errdefer allocator.free(prerelease);
        const build = try allocator.dupe(u8, self.build);
        return .{
            .numbers = self.numbers,
            .prerelease = prerelease,
            .build = build,
            .owner_allocator = allocator,
        };
    }

    pub fn deinit(self: *SemVerVersion) void {
        if (self.owner_allocator) |allocator| {
            allocator.free(self.prerelease);
            allocator.free(self.build);
        }
        self.* = undefined;
    }

    pub fn major(self: SemVerVersion) u32 {
        return self.numbers[0];
    }
    pub fn minor(self: SemVerVersion) u32 {
        return self.numbers[1];
    }
    pub fn patch(self: SemVerVersion) u32 {
        return self.numbers[2];
    }
    pub fn isPrerelease(self: SemVerVersion) bool {
        return self.prerelease.len != 0;
    }
};

pub const MatchComponent = struct {
    prefix: Token = .Illegal,
    version: SemVerVersion = .{},
    levels_present: u32 = 1,

    pub fn matches(self: MatchComponent, candidate: SemVerVersion) bool {
        if (self.prefix == .BitNot) {
            var component = self;
            component.prefix = .GreaterThanOrEqual;
            if (!component.matches(candidate)) return false;
            component.levels_present = if (self.levels_present >= 2) 2 else 1;
            component.prefix = .LessThanOrEqual;
            return component.matches(candidate);
        }
        if (self.prefix == .BitXor) {
            var component = self;
            component.prefix = .GreaterThanOrEqual;
            if (!component.matches(candidate)) return false;
            component.levels_present = if (component.version.numbers[0] == 0 and
                component.levels_present != 1) 2 else 1;
            component.prefix = .LessThanOrEqual;
            return component.matches(candidate);
        }

        var comparison: i2 = 0;
        var did_compare = false;
        for (0..self.levels_present) |index| {
            if (comparison != 0) break;
            const expected = self.version.numbers[index];
            if (expected == wildcard) continue;
            did_compare = true;
            comparison = if (candidate.numbers[index] < expected)
                -1
            else if (candidate.numbers[index] > expected)
                1
            else
                0;
        }
        if (comparison == 0 and candidate.prerelease.len != 0 and did_compare) {
            comparison = -1;
        }
        return switch (self.prefix) {
            .Assign => comparison == 0,
            .LessThan => comparison < 0,
            .LessThanOrEqual => comparison <= 0,
            .GreaterThan => comparison > 0,
            .GreaterThanOrEqual => comparison >= 0,
            else => false,
        };
    }
};

pub const Conjunction = struct {
    components: std.ArrayList(MatchComponent) = .empty,

    fn deinit(self: *Conjunction, allocator: std.mem.Allocator) void {
        self.components.deinit(allocator);
        self.* = undefined;
    }

    pub fn matches(self: Conjunction, version: SemVerVersion) bool {
        for (self.components.items) |component| if (!component.matches(version)) return false;
        return true;
    }
};

pub const SemVerMatchExpression = struct {
    allocator: std.mem.Allocator,
    disjunction: std.ArrayList(Conjunction) = .empty,

    pub fn init(allocator: std.mem.Allocator) SemVerMatchExpression {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *SemVerMatchExpression) void {
        for (self.disjunction.items) |*conjunction| conjunction.deinit(self.allocator);
        self.disjunction.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn isValid(self: *const SemVerMatchExpression) bool {
        return self.disjunction.items.len != 0;
    }

    pub fn matches(self: *const SemVerMatchExpression, version: SemVerVersion) bool {
        if (!self.isValid()) return false;
        for (self.disjunction.items) |conjunction| {
            if (conjunction.matches(version)) return true;
        }
        return false;
    }
};

pub const SemVerMatchExpressionParser = struct {
    allocator: std.mem.Allocator,
    tokens: []const Token,
    literals: []const []const u8,
    position: usize = 0,
    position_inside: usize = 0,
    failure_character: ?u8 = null,

    pub fn init(
        allocator: std.mem.Allocator,
        tokens: []const Token,
        literals: []const []const u8,
    ) SemVerError!SemVerMatchExpressionParser {
        if (tokens.len != literals.len) return error.InvalidExpression;
        return .{ .allocator = allocator, .tokens = tokens, .literals = literals };
    }

    pub fn parse(
        self: *SemVerMatchExpressionParser,
    ) (std.mem.Allocator.Error || SemVerError)!SemVerMatchExpression {
        self.reset();
        if (self.tokens.len == 0) return error.EmptyVersionPragma;
        var expression = SemVerMatchExpression.init(self.allocator);
        errdefer expression.deinit();

        while (true) {
            try self.parseMatchExpression(&expression);
            if (self.position >= self.tokens.len) break;
            if (self.currentToken() != .Or) return error.InvalidRangeCombination;
            self.nextToken();
        }
        return expression;
    }

    fn reset(self: *SemVerMatchExpressionParser) void {
        self.position = 0;
        self.position_inside = 0;
        self.failure_character = null;
    }

    fn parseMatchExpression(
        self: *SemVerMatchExpressionParser,
        expression: *SemVerMatchExpression,
    ) (std.mem.Allocator.Error || SemVerError)!void {
        var conjunction: Conjunction = .{};
        errdefer conjunction.deinit(self.allocator);
        try conjunction.components.append(self.allocator, try self.parseMatchComponent());
        if (self.currentToken() == .Sub) {
            conjunction.components.items[0].prefix = .GreaterThanOrEqual;
            self.nextToken();
            var upper = try self.parseMatchComponent();
            upper.prefix = .LessThanOrEqual;
            try conjunction.components.append(self.allocator, upper);
        } else {
            while (self.currentToken() != .Or and self.currentToken() != .Illegal) {
                try conjunction.components.append(self.allocator, try self.parseMatchComponent());
            }
        }
        try expression.disjunction.append(self.allocator, conjunction);
    }

    fn parseMatchComponent(
        self: *SemVerMatchExpressionParser,
    ) SemVerError!MatchComponent {
        var component: MatchComponent = .{};
        switch (self.currentToken()) {
            .BitXor,
            .BitNot,
            .LessThan,
            .LessThanOrEqual,
            .GreaterThan,
            .GreaterThanOrEqual,
            .Assign,
            => {
                component.prefix = self.currentToken();
                self.nextToken();
            },
            else => component.prefix = .Assign,
        }

        component.levels_present = 0;
        while (component.levels_present < 3) {
            component.version.numbers[component.levels_present] = try self.parseVersionPart();
            component.levels_present += 1;
            if (self.currentChar()) |character| {
                if (character == '.') {
                    _ = self.nextChar();
                    continue;
                }
            }
            break;
        }
        return component;
    }

    fn parseVersionPart(self: *SemVerMatchExpressionParser) SemVerError!u32 {
        const start_position = self.position;
        const character = self.currentChar() orelse return error.ExpectedVersionNumber;
        _ = self.nextChar();
        if (character == 'x' or character == 'X' or character == '*') return wildcard;
        if (character == '0') return 0;
        if (character < '1' or character > '9') {
            self.failure_character = character;
            return error.InvalidVersionStart;
        }

        var value: u32 = character - '0';
        while (self.position == start_position) {
            const current = self.currentChar() orelse break;
            if (!isDigit(current)) break;
            const multiplied = value *% 10;
            if (multiplied < value) return error.IntegerTooLarge;
            const next_value = multiplied +% (current - '0');
            if (next_value < multiplied) return error.IntegerTooLarge;
            value = next_value;
            _ = self.nextChar();
        }
        return value;
    }

    pub fn errorMessageAlloc(
        self: *const SemVerMatchExpressionParser,
        allocator: std.mem.Allocator,
        parse_error: SemVerError,
    ) std.mem.Allocator.Error![]u8 {
        return switch (parse_error) {
            error.EmptyVersionPragma => allocator.dupe(u8, "Empty version pragma."),
            error.IntegerTooLarge => allocator.dupe(
                u8,
                "Integer too large to be used in a version number.",
            ),
            error.InvalidRangeCombination => allocator.dupe(
                u8,
                "You can only combine version ranges using the || operator.",
            ),
            error.ExpectedVersionNumber => allocator.dupe(
                u8,
                "Expected version number but reached end of pragma.",
            ),
            error.InvalidVersionStart => std.fmt.allocPrint(
                allocator,
                "Expected the start of a version number but instead found character '{c}'. Version number is invalid or the pragma is not terminated with a semicolon.",
                .{self.failure_character orelse '?'},
            ),
            error.InvalidExpression => allocator.dupe(u8, "Invalid version expression."),
            error.InvalidVersion => allocator.dupe(u8, "Invalid semantic version."),
        };
    }

    fn currentChar(self: *const SemVerMatchExpressionParser) ?u8 {
        if (self.position >= self.literals.len) return null;
        if (self.position_inside >= self.literals[self.position].len) return null;
        return self.literals[self.position][self.position_inside];
    }

    fn nextChar(self: *SemVerMatchExpressionParser) ?u8 {
        if (self.position < self.literals.len) {
            if (self.position_inside + 1 >= self.literals[self.position].len) {
                self.nextToken();
            } else {
                self.position_inside += 1;
            }
        }
        return self.currentChar();
    }

    fn currentToken(self: *const SemVerMatchExpressionParser) Token {
        if (self.position < self.tokens.len) return self.tokens[self.position];
        return .Illegal;
    }

    fn nextToken(self: *SemVerMatchExpressionParser) void {
        self.position += 1;
        self.position_inside = 0;
    }
};

fn isDigit(character: u8) bool {
    return character >= '0' and character <= '9';
}

test "semantic versions preserve prerelease/build and pragma matching" {
    var release = try SemVerVersion.init(std.testing.allocator, "1.2.3+build.7");
    defer release.deinit();
    try std.testing.expectEqual(@as(u32, 1), release.major());
    try std.testing.expectEqualStrings("build.7", release.build);

    const tokens = [_]Token{ .GreaterThanOrEqual, .Number, .LessThan, .Number };
    const literals = [_][]const u8{ ">=", "1.2.0", "<", "2.0.0" };
    var parser = try SemVerMatchExpressionParser.init(std.testing.allocator, &tokens, &literals);
    var expression = try parser.parse();
    defer expression.deinit();
    try std.testing.expect(expression.matches(release));

    var prerelease = try SemVerVersion.init(std.testing.allocator, "1.2.0-alpha");
    defer prerelease.deinit();
    try std.testing.expect(!expression.matches(prerelease));
}

test "version pragma failures retain the upstream diagnostic reason" {
    const tokens = [_]Token{.Identifier};
    const literals = [_][]const u8{"pragma"};
    var parser = try SemVerMatchExpressionParser.init(std.testing.allocator, &tokens, &literals);
    try std.testing.expectError(error.InvalidVersionStart, parser.parse());
    const message = try parser.errorMessageAlloc(std.testing.allocator, error.InvalidVersionStart);
    defer std.testing.allocator.free(message);
    try std.testing.expectEqualStrings(
        "Expected the start of a version number but instead found character 'p'. Version number is invalid or the pragma is not terminated with a semicolon.",
        message,
    );

    var empty = try SemVerMatchExpressionParser.init(std.testing.allocator, &.{}, &.{});
    try std.testing.expectError(error.EmptyVersionPragma, empty.parse());
    const empty_message = try empty.errorMessageAlloc(std.testing.allocator, error.EmptyVersionPragma);
    defer std.testing.allocator.free(empty_message);
    try std.testing.expectEqualStrings("Empty version pragma.", empty_message);
}
