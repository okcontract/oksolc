// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Coherent structural translation of `Token.h/.cpp`.

const std = @import("std");

/// The upstream enum explicitly uses `unsigned int`; retain that ABI rather
/// than shrinking the enum merely because the scanner can encode it in a byte.
pub const Token = enum(c_uint) {
    EOS,
    LParen,
    RParen,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    Colon,
    Semicolon,
    Period,
    Conditional,
    DoubleArrow,
    RightArrow,
    Assign,
    AssignBitOr,
    AssignBitXor,
    AssignBitAnd,
    AssignShl,
    AssignSar,
    AssignShr,
    AssignAdd,
    AssignSub,
    AssignMul,
    AssignDiv,
    AssignMod,
    Comma,
    Or,
    And,
    BitOr,
    BitXor,
    BitAnd,
    SHL,
    SAR,
    SHR,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Exp,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Not,
    BitNot,
    Inc,
    Dec,
    Delete,
    AssemblyAssign,
    Abstract,
    Anonymous,
    As,
    Assembly,
    Break,
    Catch,
    Constant,
    Constructor,
    Continue,
    Contract,
    Do,
    Else,
    Enum,
    Emit,
    Event,
    External,
    Fallback,
    For,
    Function,
    Hex,
    If,
    Indexed,
    Interface,
    Internal,
    Immutable,
    Import,
    Is,
    Library,
    Mapping,
    Memory,
    Modifier,
    New,
    Override,
    Payable,
    Public,
    Pragma,
    Private,
    Pure,
    Receive,
    Return,
    Returns,
    Storage,
    CallData,
    Struct,
    Throw,
    Try,
    Type,
    Unchecked,
    Unicode,
    Using,
    View,
    Virtual,
    While,
    SubWei,
    SubGwei,
    SubEther,
    SubSecond,
    SubMinute,
    SubHour,
    SubDay,
    SubWeek,
    SubYear,
    Int,
    UInt,
    Bytes,
    String,
    Address,
    Bool,
    Fixed,
    UFixed,
    IntM,
    UIntM,
    BytesM,
    FixedMxN,
    UFixedMxN,
    TypesEnd,
    TrueLiteral,
    FalseLiteral,
    Number,
    StringLiteral,
    UnicodeStringLiteral,
    HexStringLiteral,
    CommentLiteral,
    Identifier,
    After,
    Alias,
    Apply,
    Auto,
    Byte,
    Case,
    CopyOf,
    Default,
    Define,
    Final,
    Implements,
    In,
    Inline,
    Let,
    Macro,
    Match,
    Mutable,
    NullLiteral,
    Of,
    Partial,
    Promise,
    Reference,
    Relocatable,
    Sealed,
    Sizeof,
    Static,
    Supports,
    Switch,
    Typedef,
    TypeOf,
    Var,
    Leave,
    NonExperimentalEnd,
    Class,
    Instantiation,
    Integer,
    Itself,
    StaticAssert,
    Builtin,
    ForAll,
    ExperimentalEnd,
    Illegal,
    Whitespace,
    NUM_TOKENS,
};

pub const count: usize = @intFromEnum(Token.NUM_TOKENS);

comptime {
    if (count > 0x100) @compileError("scanner tokens no longer fit in one byte");
    if (@sizeOf(Token) != @sizeOf(c_uint)) {
        @compileError("Token must retain the upstream unsigned-int ABI");
    }
}

fn tokenOrdinal(token: Token) c_uint {
    return @intFromEnum(token);
}

fn inRange(token: Token, first: Token, last: Token) bool {
    return tokenOrdinal(token) >= tokenOrdinal(first) and
        tokenOrdinal(token) <= tokenOrdinal(last);
}

pub fn isElementaryTypeName(token: Token) bool {
    return tokenOrdinal(token) >= tokenOrdinal(.Int) and
        tokenOrdinal(token) < tokenOrdinal(.TypesEnd);
}

pub fn isAssignmentOp(token: Token) bool {
    return inRange(token, .Assign, .AssignMod);
}

pub fn isBinaryOp(token: Token) bool {
    return inRange(token, .Comma, .Exp);
}

pub fn isCommutativeOp(token: Token) bool {
    return token == .BitOr or token == .BitXor or token == .BitAnd or
        token == .Add or token == .Mul or token == .Equal or token == .NotEqual;
}

pub fn isArithmeticOp(token: Token) bool {
    return inRange(token, .Add, .Exp);
}

pub fn isCompareOp(token: Token) bool {
    return inRange(token, .Equal, .GreaterThanOrEqual);
}

pub fn isBitOp(token: Token) bool {
    return inRange(token, .BitOr, .BitAnd) or token == .BitNot;
}

pub fn isBooleanOp(token: Token) bool {
    return inRange(token, .Or, .And) or token == .Not;
}

pub fn isUnaryOp(token: Token) bool {
    return inRange(token, .Not, .Delete) or token == .Sub;
}

pub fn isCountOp(token: Token) bool {
    return token == .Inc or token == .Dec;
}

pub fn isShiftOp(token: Token) bool {
    return inRange(token, .SHL, .SHR);
}

pub fn isVariableVisibilitySpecifier(token: Token) bool {
    return token == .Public or token == .Private or token == .Internal;
}

pub fn isVisibilitySpecifier(token: Token) bool {
    return isVariableVisibilitySpecifier(token) or token == .External;
}

pub fn isLocationSpecifier(token: Token) bool {
    return token == .Memory or token == .Storage or token == .CallData;
}

pub fn isStateMutabilitySpecifier(token: Token) bool {
    return token == .Pure or token == .View or token == .Payable;
}

pub fn isEtherSubdenomination(token: Token) bool {
    return inRange(token, .SubWei, .SubEther);
}

pub fn isTimeSubdenomination(token: Token) bool {
    return inRange(token, .SubSecond, .SubYear);
}

pub fn isReservedKeyword(token: Token) bool {
    return inRange(token, .After, .Var);
}

pub fn isYulKeywordToken(token: Token) bool {
    return token == .Function or token == .Let or token == .If or
        token == .Switch or token == .Case or token == .Default or
        token == .For or token == .Break or token == .Continue or
        token == .Leave or token == .TrueLiteral or token == .FalseLiteral or
        token == .HexStringLiteral or token == .Hex;
}

pub fn isBuiltinTypeClassName(token: Token) bool {
    return token == .Integer or
        (isBinaryOp(token) and token != .Comma) or
        isCompareOp(token) or isUnaryOp(token) or
        (isAssignmentOp(token) and token != .Assign);
}

pub fn isExperimentalSolidityKeyword(token: Token) bool {
    return switch (token) {
        .Assembly,
        .Contract,
        .External,
        .Fallback,
        .Pragma,
        .Import,
        .As,
        .Function,
        .Let,
        .Return,
        .Type,
        .If,
        .Else,
        .Do,
        .While,
        .For,
        .Continue,
        .Break,
        => true,
        else => tokenOrdinal(token) > tokenOrdinal(.NonExperimentalEnd) and
            tokenOrdinal(token) < tokenOrdinal(.ExperimentalEnd),
    };
}

pub fn isExperimentalSolidityOnlyKeyword(token: Token) bool {
    return tokenOrdinal(token) > tokenOrdinal(.NonExperimentalEnd) and
        tokenOrdinal(token) < tokenOrdinal(.ExperimentalEnd);
}

pub const InvalidOperator = error{InvalidAssignmentOperator};

pub fn assignmentToBinaryOp(token: Token) InvalidOperator!Token {
    if (!isAssignmentOp(token) or token == .Assign) {
        return error.InvalidAssignmentOperator;
    }
    const offset = tokenOrdinal(.BitOr) - tokenOrdinal(.AssignBitOr);
    return @enumFromInt(tokenOrdinal(token) + offset);
}

pub fn precedence(token: Token) i8 {
    return switch (token) {
        .Comma => 1,
        .Assign,
        .AssignBitOr,
        .AssignBitXor,
        .AssignBitAnd,
        .AssignShl,
        .AssignSar,
        .AssignShr,
        .AssignAdd,
        .AssignSub,
        .AssignMul,
        .AssignDiv,
        .AssignMod,
        .AssemblyAssign,
        => 2,
        .Conditional => 3,
        .Or => 4,
        .And => 5,
        .Equal, .NotEqual => 6,
        .LessThan, .GreaterThan, .LessThanOrEqual, .GreaterThanOrEqual => 7,
        .BitOr => 8,
        .BitXor => 9,
        .BitAnd => 10,
        .SHL, .SAR, .SHR => 11,
        .Add, .Sub => 12,
        .Mul, .Div, .Mod => 13,
        .Exp => 14,
        else => 0,
    };
}

pub fn hasExpHighestPrecedence() bool {
    if (precedence(.Exp) != 14) return false;
    inline for (std.meta.fields(Token)) |field| {
        const token: Token = @enumFromInt(field.value);
        if (token != .Exp and token != .NUM_TOKENS and precedence(token) >= 14) {
            return false;
        }
    }
    return true;
}

fn isKeywordToken(token: Token) bool {
    return token == .Delete or
        inRange(token, .Abstract, .While) or
        inRange(token, .SubWei, .UFixed) or
        token == .TrueLiteral or token == .FalseLiteral or
        inRange(token, .After, .Var) or
        inRange(token, .Class, .ForAll);
}

fn keywordSpelling(comptime token: Token) []const u8 {
    return switch (token) {
        .SubWei => "wei",
        .SubGwei => "gwei",
        .SubEther => "ether",
        .SubSecond => "seconds",
        .SubMinute => "minutes",
        .SubHour => "hours",
        .SubDay => "days",
        .SubWeek => "weeks",
        .SubYear => "years",
        .TrueLiteral => "true",
        .FalseLiteral => "false",
        .NullLiteral => "null",
        .StaticAssert => "static_assert",
        .Builtin => "__builtin",
        .Integer => "Integer",
        else => comptime blk: {
            const spelling = @tagName(token);
            var buffer: [spelling.len:0]u8 = @splat(0);
            _ = std.ascii.lowerString(&buffer, spelling);
            const lowercase = buffer;
            break :blk &lowercase;
        },
    };
}

/// Returns the syntactic spelling or `null` for tokens without a unique one.
pub fn toString(token: Token) ?[]const u8 {
    @setEvalBranchQuota(10_000);
    return switch (token) {
        .EOS => "EOS",
        .LParen => "(",
        .RParen => ")",
        .LBrack => "[",
        .RBrack => "]",
        .LBrace => "{",
        .RBrace => "}",
        .Colon => ":",
        .Semicolon => ";",
        .Period => ".",
        .Conditional => "?",
        .DoubleArrow => "=>",
        .RightArrow => "->",
        .Assign => "=",
        .AssignBitOr => "|=",
        .AssignBitXor => "^=",
        .AssignBitAnd => "&=",
        .AssignShl => "<<=",
        .AssignSar => ">>=",
        .AssignShr => ">>>=",
        .AssignAdd => "+=",
        .AssignSub => "-=",
        .AssignMul => "*=",
        .AssignDiv => "/=",
        .AssignMod => "%=",
        .Comma => ",",
        .Or => "||",
        .And => "&&",
        .BitOr => "|",
        .BitXor => "^",
        .BitAnd => "&",
        .SHL => "<<",
        .SAR => ">>",
        .SHR => ">>>",
        .Add => "+",
        .Sub => "-",
        .Mul => "*",
        .Div => "/",
        .Mod => "%",
        .Exp => "**",
        .Equal => "==",
        .NotEqual => "!=",
        .LessThan => "<",
        .GreaterThan => ">",
        .LessThanOrEqual => "<=",
        .GreaterThanOrEqual => ">=",
        .Not => "!",
        .BitNot => "~",
        .Inc => "++",
        .Dec => "--",
        .AssemblyAssign => ":=",
        .IntM => "intM",
        .UIntM => "uintM",
        .BytesM => "bytesM",
        .FixedMxN => "fixedMxN",
        .UFixedMxN => "ufixedMxN",
        .Leave => "leave",
        .Illegal => "ILLEGAL",
        inline else => |keyword| comptime if (isKeywordToken(keyword)) keywordSpelling(keyword) else null,
    };
}

pub fn name(token: Token) []const u8 {
    if (token == .NUM_TOKENS) return "";
    return @tagName(token);
}

pub fn friendlyName(token: Token) []const u8 {
    return toString(token) orelse name(token);
}

// Build once from the authoritative token spellings. Runtime queries compare
// only equal-length keys; they do not classify every enum member again.
const keywords = blk: {
    @setEvalBranchQuota(100_000);
    var entries: []const struct { []const u8, Token } = &.{};
    for (std.enums.values(Token)) |token| {
        if (isKeywordToken(token)) entries = entries ++ .{.{ toString(token).?, token }};
    }
    const map = std.StaticStringMap(Token).initComptime(entries);
    // Duplicate spellings cannot round-trip to both of their tokens.
    for (entries) |entry|
        if (map.get(entry[0]).? != entry[1]) @compileError("duplicate token keyword spelling");
    break :blk map;
};

fn keywordByName(literal: []const u8) Token {
    return keywords.get(literal) orelse .Identifier;
}

pub fn isYulKeyword(literal: []const u8) bool {
    return isYulKeywordToken(keywordByName(literal));
}

pub fn isFutureSolidityKeyword(literal: []const u8) bool {
    return std.mem.eql(u8, literal, "transient") or
        std.mem.eql(u8, literal, "layout") or
        std.mem.eql(u8, literal, "at") or
        std.mem.eql(u8, literal, "error") or
        std.mem.eql(u8, literal, "super") or
        std.mem.eql(u8, literal, "this") or
        isFutureYulKeyword(literal);
}

pub fn isFutureYulKeyword(literal: []const u8) bool {
    return std.mem.eql(u8, literal, "leave");
}

pub fn isFutureYulReservedIdentifier(literal: []const u8) bool {
    const identifiers = [_][]const u8{
        "basefee",     "blobbasefee", "blobhash", "clz",    "mcopy",
        "memoryguard", "prevrandao",  "tload",    "tstore",
    };
    for (identifiers) |identifier| {
        if (std.mem.eql(u8, literal, identifier)) return true;
    }
    return false;
}

pub const IdentifierToken = struct {
    token: Token,
    first_number: u32 = 0,
    second_number: u32 = 0,
};

const SizedTypePrefix = struct { token: Token, digits_start: usize };

fn sizedTypePrefix(comptime token: Token, literal: []const u8) ?SizedTypePrefix {
    const prefix = comptime toString(token).?;
    if (literal.len > prefix.len and std.ascii.isDigit(literal[prefix.len]) and
        std.mem.startsWith(u8, literal, prefix))
    {
        return .{ .token = token, .digits_start = prefix.len };
    }
    return null;
}

pub fn fromIdentifierOrKeyword(literal: []const u8) IdentifierToken {
    // Only these five prefixes can introduce sized types. Ordinary identifiers
    // and keywords do not need another full scan looking for a digit.
    const sized_type = (if (literal.len == 0) null else switch (literal[0]) {
        'b' => sizedTypePrefix(.Bytes, literal),
        'i' => sizedTypePrefix(.Int, literal),
        'u' => sizedTypePrefix(.UInt, literal) orelse sizedTypePrefix(.UFixed, literal),
        'f' => sizedTypePrefix(.Fixed, literal),
        else => null,
    }) orelse
        return .{ .token = keywordByName(literal) };
    const position_m = sized_type.digits_start;
    var position_x = position_m;
    while (position_x < literal.len and std.ascii.isDigit(literal[position_x])) : (position_x += 1) {}
    const m = parseSize(literal[position_m..position_x]) orelse
        return .{ .token = .Identifier };
    const keyword = sized_type.token;

    if (keyword == .Bytes) {
        if (m > 0 and m <= 32 and position_x == literal.len) {
            return .{ .token = .BytesM, .first_number = m };
        }
    } else if (keyword == .UInt or keyword == .Int) {
        if (m > 0 and m <= 256 and m % 8 == 0 and position_x == literal.len) {
            return .{
                .token = if (keyword == .UInt) .UIntM else .IntM,
                .first_number = m,
            };
        }
    } else if (keyword == .UFixed or keyword == .Fixed) {
        if (position_m < position_x and position_x < literal.len and literal[position_x] == 'x') {
            const n = parseSize(literal[position_x + 1 ..]) orelse
                return .{ .token = .Identifier };
            if (m >= 8 and m <= 256 and m % 8 == 0 and n <= 80) {
                return .{
                    .token = if (keyword == .UFixed) .UFixedMxN else .FixedMxN,
                    .first_number = m,
                    .second_number = n,
                };
            }
        }
    }
    return .{ .token = .Identifier };
}

fn parseSize(bytes: []const u8) ?u32 {
    if (bytes.len == 0 or (bytes.len > 1 and bytes[0] == '0')) return null;
    var result: u32 = 0;
    for (bytes) |c| {
        if (!std.ascii.isDigit(c) or result >= 256) return null;
        result = result * 10 + (c - '0');
    }
    return result;
}

pub const ElementaryTypeError = error{InvalidElementaryTypeDetails};

pub const ElementaryTypeNameToken = struct {
    token_value: Token,
    first_number: u32,
    second_number: u32,

    pub fn init(
        token_value: Token,
        first_number: u32,
        second_number: u32,
    ) ElementaryTypeError!ElementaryTypeNameToken {
        if (!isElementaryTypeName(token_value)) return error.InvalidElementaryTypeDetails;
        const valid = switch (token_value) {
            .BytesM => second_number == 0 and first_number <= 32,
            .UIntM, .IntM => second_number == 0 and
                first_number <= 256 and first_number % 8 == 0,
            .UFixedMxN, .FixedMxN => first_number >= 8 and
                first_number <= 256 and first_number % 8 == 0 and
                second_number <= 80,
            else => first_number == 0 and second_number == 0,
        };
        if (!valid) return error.InvalidElementaryTypeDetails;
        return .{
            .token_value = token_value,
            .first_number = first_number,
            .second_number = second_number,
        };
    }

    pub fn renderAlloc(
        self: ElementaryTypeNameToken,
        allocator: std.mem.Allocator,
        token_value_only: bool,
    ) std.mem.Allocator.Error![]u8 {
        const base = toString(self.token_value).?;
        if (token_value_only or (self.first_number == 0 and self.second_number == 0)) {
            return allocator.dupe(u8, base);
        }
        return switch (self.token_value) {
            .FixedMxN, .UFixedMxN => std.fmt.allocPrint(
                allocator,
                "{s}{d}x{d}",
                .{ base[0 .. base.len - 3], self.first_number, self.second_number },
            ),
            else => std.fmt.allocPrint(
                allocator,
                "{s}{d}",
                .{ base[0 .. base.len - 1], self.first_number },
            ),
        };
    }
};

test "token ABI, contiguous ranges, and spellings" {
    try std.testing.expectEqual(@sizeOf(c_uint), @sizeOf(Token));
    try std.testing.expectEqual(@as(usize, 179), count);
    try std.testing.expectEqualStrings(">>>=", toString(.AssignShr).?);
    try std.testing.expectEqualStrings("calldata", toString(.CallData).?);
    try std.testing.expectEqualStrings("Identifier", friendlyName(.Identifier));
    try std.testing.expect(hasExpHighestPrecedence());
    try std.testing.expectEqual(Token.BitOr, try assignmentToBinaryOp(.AssignBitOr));
    try std.testing.expectEqual(Token.Mod, try assignmentToBinaryOp(.AssignMod));
}

test "keyword and sized elementary type recognition" {
    try std.testing.expectEqual(Token.Function, fromIdentifierOrKeyword("function").token);
    try std.testing.expectEqual(Token.Identifier, fromIdentifierOrKeyword("Function").token);
    try std.testing.expectEqualDeep(
        IdentifierToken{ .token = .UIntM, .first_number = 256 },
        fromIdentifierOrKeyword("uint256"),
    );
    try std.testing.expectEqualDeep(
        IdentifierToken{ .token = .UFixedMxN, .first_number = 128, .second_number = 18 },
        fromIdentifierOrKeyword("ufixed128x18"),
    );
    try std.testing.expectEqual(Token.Identifier, fromIdentifierOrKeyword("uint0256").token);

    const sized = try ElementaryTypeNameToken.init(.UIntM, 256, 0);
    const rendered = try sized.renderAlloc(std.testing.allocator, false);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("uint256", rendered);
}

test "sized type prefixes preserve keywords and reject malformed suffixes" {
    const cases = [_]struct { literal: []const u8, expected: IdentifierToken }{
        .{ .literal = "", .expected = .{ .token = .Identifier } },
        .{ .literal = "interface", .expected = .{ .token = .Interface } },
        .{ .literal = "internal", .expected = .{ .token = .Internal } },
        .{ .literal = "Integer", .expected = .{ .token = .Integer } },
        .{ .literal = "int", .expected = .{ .token = .Int } },
        .{ .literal = "ufixed", .expected = .{ .token = .UFixed } },
        .{ .literal = "bytes", .expected = .{ .token = .Bytes } },
        .{ .literal = "int8", .expected = .{ .token = .IntM, .first_number = 8 } },
        .{ .literal = "uint256", .expected = .{ .token = .UIntM, .first_number = 256 } },
        .{ .literal = "bytes1", .expected = .{ .token = .BytesM, .first_number = 1 } },
        .{ .literal = "bytes32", .expected = .{ .token = .BytesM, .first_number = 32 } },
        .{ .literal = "fixed8x0", .expected = .{ .token = .FixedMxN, .first_number = 8 } },
        .{ .literal = "ufixed256x80", .expected = .{ .token = .UFixedMxN, .first_number = 256, .second_number = 80 } },
    };
    for (cases) |case| try std.testing.expectEqualDeep(case.expected, fromIdentifierOrKeyword(case.literal));
    for ([_][]const u8{
        "int0",        "uint9",        "uint264",  "uint0256", "bytes0",                  "bytes33",    "bytes01", "uint8_",
        "fixed256x81", "fixed128x018", "ufixed8x", "int8x2",   "uint9999999999999999999", "account123",
    }) |literal| try std.testing.expectEqualDeep(IdentifierToken{ .token = .Identifier }, fromIdentifierOrKeyword(literal));
}

test "keyword lookup matches the former scan on spellings and near misses" {
    const Reference = struct {
        fn lookup(literal: []const u8) Token {
            for (std.enums.values(Token)) |token| {
                if (token != .NUM_TOKENS and isKeywordToken(token)) {
                    if (std.mem.eql(u8, literal, toString(token).?)) return token;
                }
            }
            return .Identifier;
        }

        fn check(literal: []const u8) !void {
            try std.testing.expectEqual(lookup(literal), keywordByName(literal));
        }
    };
    for (std.enums.values(Token)) |token| {
        try Reference.check(@tagName(token));
        if (toString(token)) |spelling| {
            for (0..spelling.len + 1) |length| try Reference.check(spelling[0..length]);
            const suffixed = try std.fmt.allocPrint(std.testing.allocator, "{s}_1", .{spelling});
            defer std.testing.allocator.free(suffixed);
            try Reference.check(suffixed);
            const upper = try std.ascii.allocUpperString(std.testing.allocator, spelling);
            defer std.testing.allocator.free(upper);
            try Reference.check(upper);
        }
    }
    for ([_][]const u8{ "", "\x00", "\xff", "function\x00", "uint256", "ufixed128x18", "static_assert", "__builtin", "Integer", "integer" }) |literal|
        try Reference.check(literal);
}
