// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Recursive-descent parser for untyped Yul assembly.

const std = @import("std");
const ASTModule = @import("ast.zig");
const Utilities = @import("utilities.zig");
const YulName = @import("yul_name.zig").YulName;
const ScannerModule = @import("../liblangutil/scanner.zig");
const TokenModule = @import("../liblangutil/token.zig");
const ParserBaseModule = @import("../liblangutil/parser_base.zig");
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;

const Token = TokenModule.Token;

pub const ForLoopComponent = enum {
    none,
    for_loop_pre,
    for_loop_post,
    for_loop_body,
};

pub const UseSourceLocationFrom = enum {
    scanner,
    location_override,
    comments,
};

pub const SourceIndexName = struct {
    index: u32,
    name: []const u8,
};

pub const Options = struct {
    location_override: ?SourceLocation = null,
    source_names: ?[]const SourceIndexName = null,
};

pub const ParseError = ScannerModule.ScanFailure ||
    Diagnostics.ReportError ||
    TokenModule.ElementaryTypeError ||
    Utilities.LiteralError ||
    error{
        InvalidYulStringHandle,
        UnknownBuiltin,
        InternalParserState,
    };

const Elementary = union(enum) {
    literal: ASTModule.Literal,
    identifier: ASTModule.Identifier,
    builtin: ASTModule.BuiltinName,

    fn deinit(self: *Elementary, allocator: std.mem.Allocator) void {
        switch (self.*) {
            .literal => |*literal| literal.deinit(allocator),
            .identifier, .builtin => {},
        }
        self.* = undefined;
    }

    fn debugData(self: *const Elementary) ?DebugData {
        return switch (self.*) {
            .literal => |literal| literal.debug_data,
            .identifier => |identifier| identifier.debug_data,
            .builtin => |builtin| builtin.debug_data,
        };
    }
};

const DebugData = @import("../liblangutil/debug_data.zig").DebugData;

pub const Parser = struct {
    allocator: std.mem.Allocator,
    base: ParserBaseModule.ParserBase,
    dialect: ASTModule.Dialect,
    source_names: ?[]const SourceIndexName = null,
    location_override: SourceLocation = .{},
    location_from_comment: SourceLocation = .{},
    ast_id_from_comment: ?i64 = null,
    use_source_location_from: UseSourceLocationFrom = .scanner,
    current_for_loop_component: ForLoopComponent = .none,
    inside_function: bool = false,
    recursion_depth: usize = 0,

    pub fn init(
        allocator: std.mem.Allocator,
        scanner: *ScannerModule.Scanner,
        error_reporter: *Diagnostics.ErrorReporter,
        dialect: ASTModule.Dialect,
        options: Options,
    ) Parser {
        const location_mode: UseSourceLocationFrom = if (options.location_override != null)
            .location_override
        else if (options.source_names != null)
            .comments
        else
            .scanner;
        return .{
            .allocator = allocator,
            .base = ParserBaseModule.ParserBase.init(allocator, scanner, error_reporter),
            .dialect = dialect,
            .source_names = options.source_names,
            .location_override = options.location_override orelse .{},
            .use_source_location_from = location_mode,
        };
    }

    pub fn parseSource(
        allocator: std.mem.Allocator,
        source: []const u8,
        source_name: []const u8,
        error_reporter: *Diagnostics.ErrorReporter,
        dialect: ASTModule.Dialect,
        options: Options,
    ) ParseError!?ASTModule.AST {
        var stream = ScannerModule.CharStream.initBorrowed(source, source_name);
        var scanner = try ScannerModule.Scanner.init(allocator, &stream, .Solidity);
        defer scanner.deinit();
        var parser = Parser.init(allocator, &scanner, error_reporter, dialect, options);
        return parser.parseComplete();
    }

    pub fn parseComplete(self: *Parser) ParseError!?ASTModule.AST {
        const maybe_root = try self.parseInline();
        if (maybe_root == null) {
            self.expectToken(.EOS) catch |err| switch (err) {
                error.FatalDiagnostic => {},
                else => return err,
            };
            return null;
        }
        var root = maybe_root.?;
        errdefer root.deinit(self.allocator);
        self.expectToken(.EOS) catch |err| switch (err) {
            error.FatalDiagnostic => return null,
            else => return err,
        };
        return ASTModule.AST.init(self.allocator, self.dialect, root);
    }

    pub fn parseInline(self: *Parser) ParseError!?ASTModule.Block {
        self.recursion_depth = 0;
        const previous_kind = self.base.scanner.scannerKind();
        try self.base.scanner.setScannerMode(.Yul);
        const parse_result: ParseError!?ASTModule.Block = parsed: {
            if (self.use_source_location_from == .comments)
                self.fetchDebugDataFromComment() catch |err| break :parsed err;
            break :parsed self.parseBlock() catch |err| switch (err) {
                error.FatalDiagnostic => null,
                else => err,
            };
        };
        const restore_result = self.base.scanner.setScannerMode(previous_kind);
        var block = try parse_result;
        errdefer if (block) |*value| value.deinit(self.allocator);
        try restore_result;
        return block;
    }

    fn currentLocation(self: *const Parser) SourceLocation {
        if (self.use_source_location_from == .location_override) return self.location_override;
        return self.base.scanner.currentLocation();
    }

    fn currentToken(self: *const Parser) Token {
        return self.base.scanner.currentToken();
    }

    fn currentLiteral(self: *const Parser) []const u8 {
        return self.base.scanner.currentLiteral();
    }

    fn advance(self: *Parser) ParseError!Token {
        const token = try self.base.scanner.next();
        if (self.use_source_location_from == .comments) try self.fetchDebugDataFromComment();
        return token;
    }

    fn expectToken(self: *Parser, expected: Token) ParseError!void {
        const actual = self.currentToken();
        if (actual != expected) {
            const expected_name = try self.base.tokenNameAlloc(expected);
            defer self.allocator.free(expected_name);
            const actual_name = try self.base.tokenNameAlloc(actual);
            defer self.allocator.free(actual_name);
            const description = try std.fmt.allocPrint(
                self.allocator,
                "Expected {s} but got {s}",
                .{ expected_name, actual_name },
            );
            defer self.allocator.free(description);
            try self.fatalParserError(2314, self.currentLocation(), description);
        }
        _ = try self.advance();
    }

    fn recursionGuard(self: *Parser) ParseError!RecursionGuard {
        self.recursion_depth += 1;
        if (self.recursion_depth >= 1200) {
            try self.fatalParserError(
                7319,
                self.currentLocation(),
                "Maximum recursion depth reached during parsing.",
            );
        }
        return .{ .parser = self };
    }

    fn fatalParserError(
        self: *Parser,
        error_id: u64,
        location: SourceLocation,
        description: []const u8,
    ) Diagnostics.ReportError!void {
        try self.base.error_reporter.fatal(
            .{ .value = error_id },
            .ParserError,
            location,
            null,
            description,
        );
    }

    fn parserError(
        self: *Parser,
        error_id: u64,
        location: SourceLocation,
        description: []const u8,
    ) Diagnostics.ReportError!void {
        try self.base.error_reporter.parserError(.{ .value = error_id }, location, description);
    }

    fn syntaxError(
        self: *Parser,
        error_id: u64,
        location: SourceLocation,
        description: []const u8,
    ) Diagnostics.ReportError!void {
        try self.base.error_reporter.syntaxError(.{ .value = error_id }, location, description);
    }

    fn createDebugData(self: *const Parser) DebugData {
        const scanner_location = self.base.scanner.currentLocation();
        return switch (self.use_source_location_from) {
            .scanner => .{
                .native_location = scanner_location,
                .origin_location = scanner_location,
            },
            .location_override => .{
                .native_location = self.location_override,
                .origin_location = self.location_override,
            },
            .comments => .{
                .native_location = scanner_location,
                .origin_location = self.location_from_comment,
                .ast_id = self.ast_id_from_comment,
            },
        };
    }

    fn updateLocationEndFrom(
        self: *const Parser,
        debug_data: *?DebugData,
        location: SourceLocation,
    ) void {
        if (debug_data.* == null) return;
        switch (self.use_source_location_from) {
            .scanner => {
                debug_data.*.?.native_location.end = location.end;
                debug_data.*.?.origin_location.end = location.end;
            },
            .location_override => {},
            .comments => debug_data.*.?.native_location.end = location.end,
        }
    }

    fn parseBlock(self: *Parser) ParseError!ASTModule.Block {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        var block: ASTModule.Block = .{ .debug_data = self.createDebugData() };
        errdefer block.deinit(self.allocator);
        try self.expectToken(.LBrace);
        while (self.currentToken() != .RBrace) {
            var statement = try self.parseStatement();
            errdefer statement.deinit(self.allocator);
            try block.statements.append(self.allocator, statement);
        }
        self.updateLocationEndFrom(&block.debug_data, self.currentLocation());
        _ = try self.advance();
        return block;
    }

    fn parseStatement(self: *Parser) ParseError!ASTModule.Statement {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        switch (self.currentToken()) {
            .Let => return .{ .variable_declaration = try self.parseVariableDeclaration() },
            .Function => return .{ .function_definition = try self.parseFunctionDefinition() },
            .LBrace => return .{ .block = try self.parseBlock() },
            .If => {
                var value: ASTModule.If = .{ .debug_data = self.createDebugData() };
                errdefer value.deinit(self.allocator);
                _ = try self.advance();
                value.condition = try self.parseExpressionPointer();
                value.body = try self.parseBlock();
                self.updateLocationEndFrom(&value.debug_data, nativeLocation(value.body.debug_data));
                return .{ .if_statement = value };
            },
            .Switch => {
                var value: ASTModule.Switch = .{ .debug_data = self.createDebugData() };
                errdefer value.deinit(self.allocator);
                _ = try self.advance();
                value.expression = try self.parseExpressionPointer();
                while (self.currentToken() == .Case) {
                    var case_value = try self.parseCase();
                    errdefer case_value.deinit(self.allocator);
                    try value.cases.append(self.allocator, case_value);
                }
                if (self.currentToken() == .Default) {
                    var case_value = try self.parseCase();
                    errdefer case_value.deinit(self.allocator);
                    try value.cases.append(self.allocator, case_value);
                }
                if (self.currentToken() == .Default)
                    try self.fatalParserError(6931, self.currentLocation(), "Only one default case allowed.")
                else if (self.currentToken() == .Case)
                    try self.fatalParserError(4904, self.currentLocation(), "Case not allowed after default case.");
                if (value.cases.items.len == 0)
                    try self.fatalParserError(2418, self.currentLocation(), "Switch statement without any cases.");
                self.updateLocationEndFrom(
                    &value.debug_data,
                    nativeLocation(value.cases.items[value.cases.items.len - 1].body.debug_data),
                );
                return .{ .switch_statement = value };
            },
            .For => return .{ .for_loop = try self.parseForLoop() },
            .Break => {
                const result: ASTModule.Statement = .{
                    .break_statement = .{ .debug_data = self.createDebugData() },
                };
                try self.checkBreakContinuePosition("break");
                _ = try self.advance();
                return result;
            },
            .Continue => {
                const result: ASTModule.Statement = .{
                    .continue_statement = .{ .debug_data = self.createDebugData() },
                };
                try self.checkBreakContinuePosition("continue");
                _ = try self.advance();
                return result;
            },
            .Leave => {
                const result: ASTModule.Statement = .{
                    .leave_statement = .{ .debug_data = self.createDebugData() },
                };
                if (!self.inside_function) try self.syntaxError(
                    8149,
                    self.currentLocation(),
                    "Keyword \"leave\" can only be used inside a function.",
                );
                _ = try self.advance();
                return result;
            },
            else => {},
        }

        var elementary = try self.parseLiteralOrIdentifier(false);
        errdefer elementary.deinit(self.allocator);
        switch (self.currentToken()) {
            .LParen => {
                const expression: ASTModule.Expression = .{
                    .function_call = try self.parseCall(&elementary),
                };
                return .{ .expression_statement = .{
                    .debug_data = expression.debugData().?.*,
                    .expression = expression,
                } };
            },
            .Comma, .AssemblyAssign => {
                var assignment: ASTModule.Assignment = .{ .debug_data = elementary.debugData() };
                errdefer assignment.deinit(self.allocator);
                while (true) {
                    switch (elementary) {
                        .literal => {
                            const token = if (self.currentToken() == .Comma) "," else ":=";
                            const description = try std.fmt.allocPrint(
                                self.allocator,
                                "Variable name must precede \"{s}\"{s}",
                                .{ token, if (self.currentToken() == .Comma) " in multiple assignment." else " in assignment." },
                            );
                            defer self.allocator.free(description);
                            try self.fatalParserError(2856, self.currentLocation(), description);
                        },
                        .builtin => |builtin| {
                            const name = (self.dialect.builtin(builtin.handle) catch return error.UnknownBuiltin).name;
                            const description = try std.fmt.allocPrint(
                                self.allocator,
                                "Cannot assign to builtin function \"{s}\".",
                                .{name},
                            );
                            defer self.allocator.free(description);
                            try self.fatalParserError(6272, self.currentLocation(), description);
                        },
                        .identifier => |identifier| {
                            try assignment.variable_names.append(self.allocator, identifier);
                            if (self.currentToken() != .Comma) break;
                            try self.expectToken(.Comma);
                            elementary = try self.parseLiteralOrIdentifier(false);
                            continue;
                        },
                    }
                    break;
                }
                try self.expectToken(.AssemblyAssign);
                assignment.value = try self.parseExpressionPointer();
                self.updateLocationEndFrom(
                    &assignment.debug_data,
                    nativeLocation(assignment.value.?.debugData()),
                );
                return .{ .assignment = assignment };
            },
            else => try self.fatalParserError(6913, self.currentLocation(), "Call or assignment expected."),
        }
        return error.InternalParserState;
    }

    fn parseCase(self: *Parser) ParseError!ASTModule.Case {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        var result: ASTModule.Case = .{ .debug_data = self.createDebugData() };
        errdefer result.deinit(self.allocator);
        if (self.currentToken() == .Default) {
            _ = try self.advance();
        } else if (self.currentToken() == .Case) {
            _ = try self.advance();
            var elementary = try self.parseLiteralOrIdentifier(false);
            var owns_elementary = true;
            defer if (owns_elementary) elementary.deinit(self.allocator);
            switch (elementary) {
                .literal => |literal| {
                    result.value = try ASTModule.createLiteral(self.allocator, literal);
                    owns_elementary = false;
                },
                else => try self.fatalParserError(4805, self.currentLocation(), "Literal expected."),
            }
        } else return error.InternalParserState;
        result.body = try self.parseBlock();
        self.updateLocationEndFrom(&result.debug_data, nativeLocation(result.body.debug_data));
        return result;
    }

    fn parseForLoop(self: *Parser) ParseError!ASTModule.ForLoop {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        const previous = self.current_for_loop_component;
        defer self.current_for_loop_component = previous;
        var result: ASTModule.ForLoop = .{ .debug_data = self.createDebugData() };
        errdefer result.deinit(self.allocator);
        try self.expectToken(.For);
        self.current_for_loop_component = .for_loop_pre;
        result.pre = try self.parseBlock();
        self.current_for_loop_component = .none;
        result.condition = try self.parseExpressionPointer();
        self.current_for_loop_component = .for_loop_post;
        result.post = try self.parseBlock();
        self.current_for_loop_component = .for_loop_body;
        result.body = try self.parseBlock();
        self.updateLocationEndFrom(&result.debug_data, nativeLocation(result.body.debug_data));
        return result;
    }

    fn parseExpressionPointer(self: *Parser) ParseError!*ASTModule.Expression {
        var expression = try self.parseExpression(false);
        errdefer expression.deinit(self.allocator);
        return ASTModule.createExpression(self.allocator, expression);
    }

    fn parseExpression(
        self: *Parser,
        unlimited_literal_argument: bool,
    ) ParseError!ASTModule.Expression {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        var elementary = try self.parseLiteralOrIdentifier(unlimited_literal_argument);
        errdefer elementary.deinit(self.allocator);
        return switch (elementary) {
            .identifier => |identifier| if (self.currentToken() == .LParen)
                .{ .function_call = try self.parseCall(&elementary) }
            else
                .{ .identifier = identifier },
            .builtin => |builtin| if (self.currentToken() == .LParen)
                .{ .function_call = try self.parseCall(&elementary) }
            else blk: {
                const name = (self.dialect.builtin(builtin.handle) catch return error.UnknownBuiltin).name;
                const description = try std.fmt.allocPrint(
                    self.allocator,
                    "Builtin function \"{s}\" must be called.",
                    .{name},
                );
                defer self.allocator.free(description);
                try self.fatalParserError(7104, nativeLocation(builtin.debug_data), description);
                break :blk error.InternalParserState;
            },
            .literal => |literal| .{ .literal = literal },
        };
    }

    fn parseLiteralOrIdentifier(
        self: *Parser,
        unlimited_literal_argument: bool,
    ) ParseError!Elementary {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        switch (self.currentToken()) {
            .Identifier => {
                const debug_data = self.createDebugData();
                const literal = self.currentLiteral();
                const builtin_handle = self.dialect.findBuiltin(literal);
                const result: Elementary = if (builtin_handle) |handle|
                    .{ .builtin = .{ .debug_data = debug_data, .handle = handle } }
                else
                    .{ .identifier = .{ .debug_data = debug_data, .name = try YulName.init(literal) } };
                _ = try self.advance();
                return result;
            },
            .StringLiteral, .HexStringLiteral, .Number, .TrueLiteral, .FalseLiteral => {
                const token = self.currentToken();
                const kind: ASTModule.LiteralKind = switch (token) {
                    .StringLiteral, .HexStringLiteral => .String,
                    .TrueLiteral, .FalseLiteral => .Boolean,
                    else => .Number,
                };
                if (kind == .Number and !isValidNumberLiteral(self.currentLiteral()))
                    try self.fatalParserError(4828, self.currentLocation(), "Invalid number literal.");
                const literal_location = self.currentLocation();
                var literal: ASTModule.Literal = .{
                    .debug_data = self.createDebugData(),
                    .kind = kind,
                    .value = try Utilities.valueOfLiteral(
                        self.allocator,
                        self.currentLiteral(),
                        kind,
                        unlimited_literal_argument and kind == .String,
                    ),
                };
                errdefer literal.deinit(self.allocator);
                _ = try self.advance();
                if (self.currentToken() == .Colon) {
                    try self.expectToken(.Colon);
                    self.updateLocationEndFrom(&literal.debug_data, self.currentLocation());
                    const typed_location = SourceLocation.smallestCovering(literal_location, self.currentLocation());
                    _ = try self.expectAsmIdentifier();
                    try self.raiseUnsupportedTypesError(typed_location);
                }
                return .{ .literal = literal };
            },
            .Illegal => {
                const description = try std.fmt.allocPrint(
                    self.allocator,
                    "Illegal token: {s}",
                    .{ScannerModule.errorMessage(self.base.scanner.currentError())},
                );
                defer self.allocator.free(description);
                try self.fatalParserError(1465, self.currentLocation(), description);
            },
            else => try self.fatalParserError(1856, self.currentLocation(), "Literal or identifier expected."),
        }
        return error.InternalParserState;
    }

    fn parseVariableDeclaration(self: *Parser) ParseError!ASTModule.VariableDeclaration {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        var result: ASTModule.VariableDeclaration = .{ .debug_data = self.createDebugData() };
        errdefer result.deinit(self.allocator);
        try self.expectToken(.Let);
        while (true) {
            try result.variables.append(self.allocator, try self.parseNameWithDebugData());
            if (self.currentToken() == .Comma)
                try self.expectToken(.Comma)
            else
                break;
        }
        if (self.currentToken() == .AssemblyAssign) {
            try self.expectToken(.AssemblyAssign);
            result.value = try self.parseExpressionPointer();
            self.updateLocationEndFrom(&result.debug_data, nativeLocation(result.value.?.debugData()));
        } else {
            self.updateLocationEndFrom(
                &result.debug_data,
                nativeLocation(result.variables.items[result.variables.items.len - 1].debug_data),
            );
        }
        return result;
    }

    fn parseFunctionDefinition(self: *Parser) ParseError!ASTModule.FunctionDefinition {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        if (self.current_for_loop_component == .for_loop_pre) try self.syntaxError(
            3441,
            self.currentLocation(),
            "Functions cannot be defined inside a for-loop init block.",
        );
        const previous_component = self.current_for_loop_component;
        defer self.current_for_loop_component = previous_component;
        self.current_for_loop_component = .none;

        var result: ASTModule.FunctionDefinition = .{ .debug_data = self.createDebugData() };
        errdefer result.deinit(self.allocator);
        try self.expectToken(.Function);
        result.name = try self.expectAsmIdentifier();
        try self.expectToken(.LParen);
        while (self.currentToken() != .RParen) {
            try result.parameters.append(self.allocator, try self.parseNameWithDebugData());
            if (self.currentToken() == .RParen) break;
            try self.expectToken(.Comma);
        }
        try self.expectToken(.RParen);
        if (self.currentToken() == .RightArrow) {
            try self.expectToken(.RightArrow);
            while (true) {
                try result.return_variables.append(self.allocator, try self.parseNameWithDebugData());
                if (self.currentToken() == .LBrace) break;
                try self.expectToken(.Comma);
            }
        }
        const previous_inside = self.inside_function;
        self.inside_function = true;
        result.body = self.parseBlock() catch |err| {
            self.inside_function = previous_inside;
            return err;
        };
        self.inside_function = previous_inside;
        self.updateLocationEndFrom(&result.debug_data, nativeLocation(result.body.debug_data));
        return result;
    }

    fn parseCall(self: *Parser, initial: *Elementary) ParseError!ASTModule.FunctionCall {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        var result: ASTModule.FunctionCall = undefined;
        var literal_arguments: []const ?ASTModule.LiteralKind = &.{};
        switch (initial.*) {
            .literal => try self.fatalParserError(9980, self.currentLocation(), "Function name expected."),
            .identifier => |identifier| result = .{
                .debug_data = identifier.debug_data,
                .function_name = .{ .identifier = identifier },
            },
            .builtin => |builtin| {
                const function = self.dialect.builtin(builtin.handle) catch return error.UnknownBuiltin;
                literal_arguments = function.literal_arguments;
                result = .{
                    .debug_data = builtin.debug_data,
                    .function_name = .{ .builtin = builtin },
                };
            },
        }
        errdefer result.deinit(self.allocator);
        var argument_index: usize = 0;
        try self.expectToken(.LParen);
        if (self.currentToken() != .RParen) {
            while (true) {
                const unlimited = argument_index < literal_arguments.len and
                    literal_arguments[argument_index] != null;
                var argument = try self.parseExpression(unlimited);
                errdefer argument.deinit(self.allocator);
                try result.arguments.append(self.allocator, argument);
                argument_index += 1;
                if (self.currentToken() == .RParen) break;
                try self.expectToken(.Comma);
            }
        }
        self.updateLocationEndFrom(&result.debug_data, self.currentLocation());
        try self.expectToken(.RParen);
        return result;
    }

    fn parseNameWithDebugData(self: *Parser) ParseError!ASTModule.NameWithDebugData {
        var guard = try self.recursionGuard();
        defer guard.deinit();
        var result: ASTModule.NameWithDebugData = .{ .debug_data = self.createDebugData() };
        const name_location = self.currentLocation();
        result.name = try self.expectAsmIdentifier();
        if (self.currentToken() == .Colon) {
            try self.expectToken(.Colon);
            self.updateLocationEndFrom(&result.debug_data, self.currentLocation());
            const typed_location = SourceLocation.smallestCovering(name_location, self.currentLocation());
            _ = try self.expectAsmIdentifier();
            try self.raiseUnsupportedTypesError(typed_location);
        }
        return result;
    }

    fn expectAsmIdentifier(self: *Parser) ParseError!YulName {
        const name = try YulName.init(self.currentLiteral());
        if (self.currentToken() == .Identifier and self.dialect.findBuiltin(try name.str()) != null) {
            const description = try std.fmt.allocPrint(
                self.allocator,
                "Cannot use builtin function name \"{s}\" as identifier name.",
                .{try name.str()},
            );
            defer self.allocator.free(description);
            try self.parserError(5568, self.currentLocation(), description);
        }
        try self.expectToken(.Identifier);
        return name;
    }

    fn checkBreakContinuePosition(self: *Parser, which: []const u8) ParseError!void {
        const suffix = switch (self.current_for_loop_component) {
            .none => " needs to be inside a for-loop body.",
            .for_loop_pre => " in for-loop init block is not allowed.",
            .for_loop_post => " in for-loop post block is not allowed.",
            .for_loop_body => return,
        };
        const error_id: u64 = switch (self.current_for_loop_component) {
            .none => 2592,
            .for_loop_pre => 9615,
            .for_loop_post => 2461,
            .for_loop_body => unreachable,
        };
        const description = try std.fmt.allocPrint(
            self.allocator,
            "Keyword \"{s}\"{s}",
            .{ which, suffix },
        );
        defer self.allocator.free(description);
        try self.syntaxError(error_id, self.currentLocation(), description);
    }

    fn raiseUnsupportedTypesError(self: *Parser, location: SourceLocation) ParseError!void {
        try self.parserError(5473, location, "Types are not supported in untyped Yul.");
    }

    fn fetchDebugDataFromComment(self: *Parser) ParseError!void {
        const comment = self.base.scanner.currentCommentLiteral();
        if (comment.len == 0) {
            self.ast_id_from_comment = null;
            return;
        }
        var origin = self.location_from_comment;
        var ast_id: ?i64 = null;
        var cursor: usize = 0;
        while (nextTag(comment, cursor)) |tag| {
            cursor = tag.arguments_start;
            if (std.mem.eql(u8, tag.name, "@src")) {
                const parsed = try self.parseSrcComment(comment[cursor..]);
                if (parsed == null) break;
                cursor += parsed.?.consumed;
                origin = parsed.?.location;
            } else if (std.mem.eql(u8, tag.name, "@ast-id")) {
                const parsed = try self.parseAstIdComment(comment[cursor..]);
                if (parsed == null) break;
                cursor += parsed.?.consumed;
                ast_id = parsed.?.ast_id;
            }
        }
        self.location_from_comment = origin;
        self.ast_id_from_comment = ast_id;
    }

    const ParsedSourceComment = struct { consumed: usize, location: SourceLocation };

    fn parseSrcComment(self: *Parser, arguments: []const u8) ParseError!?ParsedSourceComment {
        var cursor: usize = 0;
        const raw_source_index = scanSignedComponent(arguments, &cursor, true) orelse {
            try self.syntaxError(
                8387,
                self.base.scanner.currentCommentLocation(),
                "Invalid values in source location mapping. Could not parse location specification.",
            );
            return null;
        };
        const raw_start = scanSignedComponent(arguments, &cursor, true) orelse {
            try self.syntaxError(
                8387,
                self.base.scanner.currentCommentLocation(),
                "Invalid values in source location mapping. Could not parse location specification.",
            );
            return null;
        };
        const raw_end = scanSignedComponent(arguments, &cursor, false) orelse {
            try self.syntaxError(
                8387,
                self.base.scanner.currentCommentLocation(),
                "Invalid values in source location mapping. Could not parse location specification.",
            );
            return null;
        };
        if (cursor < arguments.len and !isWhitespace(arguments[cursor])) {
            try self.syntaxError(
                8387,
                self.base.scanner.currentCommentLocation(),
                "Invalid values in source location mapping. Could not parse location specification.",
            );
            return null;
        }
        while (cursor < arguments.len and isWhitespace(arguments[cursor])) : (cursor += 1) {}
        if (cursor < arguments.len and arguments[cursor] == '"') {
            cursor += 1;
            var escaped = false;
            while (cursor < arguments.len) : (cursor += 1) {
                const character = arguments[cursor];
                if (!escaped and character == '"') {
                    cursor += 1;
                    break;
                }
                if (!escaped and character == '\\') escaped = true else escaped = false;
            } else {
                try self.syntaxError(
                    1544,
                    self.base.scanner.currentCommentLocation(),
                    "Invalid code snippet in source location mapping. Quote is not terminated.",
                );
                return .{ .consumed = arguments.len, .location = .{} };
            }
        }
        const source_index: ?i32 = std.fmt.parseInt(i32, raw_source_index, 10) catch null;
        const start: ?i32 = std.fmt.parseInt(i32, raw_start, 10) catch null;
        const end: ?i32 = std.fmt.parseInt(i32, raw_end, 10) catch null;
        if (source_index == null or source_index.? < -1 or
            start == null or start.? < -1 or
            end == null or end.? < -1)
        {
            try self.syntaxError(
                6367,
                self.base.scanner.currentCommentLocation(),
                "Invalid value in source location mapping. Expected non-negative integer values or -1 for source index and location.",
            );
            return .{ .consumed = cursor, .location = .{} };
        }
        if (source_index.? == -1)
            return .{ .consumed = cursor, .location = .{ .start = start.?, .end = end.? } };
        const names = self.source_names orelse return error.InternalParserState;
        for (names) |entry| {
            if (entry.index == @as(u32, @intCast(source_index.?))) {
                return .{
                    .consumed = cursor,
                    .location = .{ .start = start.?, .end = end.?, .source_name = entry.name },
                };
            }
        }
        try self.syntaxError(
            2674,
            self.base.scanner.currentCommentLocation(),
            "Invalid source mapping. Source index not defined via @use-src.",
        );
        return .{ .consumed = cursor, .location = .{} };
    }

    const ParsedAstIdComment = struct { consumed: usize, ast_id: ?i64 };

    fn parseAstIdComment(self: *Parser, arguments: []const u8) ParseError!?ParsedAstIdComment {
        var cursor: usize = 0;
        while (cursor < arguments.len and std.ascii.isDigit(arguments[cursor])) : (cursor += 1) {}
        if (cursor == 0 or (cursor < arguments.len and !isWhitespace(arguments[cursor]))) {
            try self.syntaxError(
                1749,
                self.base.scanner.currentCommentLocation(),
                "Invalid argument for @ast-id.",
            );
            return null;
        }
        const ast_id = std.fmt.parseInt(i64, arguments[0..cursor], 10) catch {
            try self.syntaxError(
                1749,
                self.base.scanner.currentCommentLocation(),
                "Invalid argument for @ast-id.",
            );
            return .{ .consumed = cursor, .ast_id = null };
        };
        return .{ .consumed = cursor, .ast_id = ast_id };
    }
};

const RecursionGuard = struct {
    parser: *Parser,

    fn deinit(self: *RecursionGuard) void {
        std.debug.assert(self.parser.recursion_depth > 0);
        self.parser.recursion_depth -= 1;
        self.* = undefined;
    }
};

const Tag = struct {
    name: []const u8,
    arguments_start: usize,
};

fn nextTag(comment: []const u8, start: usize) ?Tag {
    var cursor = start;
    while (cursor < comment.len) : (cursor += 1) {
        if (comment[cursor] != '@') continue;
        if (cursor != start and !isWhitespace(comment[cursor - 1])) continue;
        var end = cursor + 1;
        while (end < comment.len and isTagCharacter(comment[end])) : (end += 1) {}
        if (end == cursor + 1 or (end < comment.len and !isWhitespace(comment[end]))) continue;
        while (end < comment.len and isWhitespace(comment[end])) : (end += 1) {}
        return .{ .name = comment[cursor..endTagName(comment, cursor + 1)], .arguments_start = end };
    }
    return null;
}

fn endTagName(comment: []const u8, start: usize) usize {
    var cursor = start;
    while (cursor < comment.len and isTagCharacter(comment[cursor])) : (cursor += 1) {}
    return cursor;
}

fn isTagCharacter(character: u8) bool {
    return std.ascii.isAlphanumeric(character) or character == '-' or character == '_';
}

fn isWhitespace(character: u8) bool {
    return character == ' ' or character == '\t' or character == '\r' or character == '\n' or
        character == 0x0b or character == 0x0c;
}

fn scanSignedComponent(input: []const u8, cursor: *usize, trailing_colon: bool) ?[]const u8 {
    while (cursor.* < input.len and isWhitespace(input[cursor.*])) : (cursor.* += 1) {}
    const component_start = cursor.*;
    if (cursor.* < input.len and input[cursor.*] == '-') {
        cursor.* += 1;
    }
    const start = cursor.*;
    while (cursor.* < input.len and std.ascii.isDigit(input[cursor.*])) : (cursor.* += 1) {}
    if (cursor.* == start) return null;
    const component_end = cursor.*;
    if (trailing_colon) {
        while (cursor.* < input.len and isWhitespace(input[cursor.*])) : (cursor.* += 1) {}
        if (cursor.* >= input.len or input[cursor.*] != ':') return null;
        cursor.* += 1;
        while (cursor.* < input.len and isWhitespace(input[cursor.*])) : (cursor.* += 1) {}
    }
    return input[component_start..component_end];
}

fn nativeLocation(debug_data: anytype) SourceLocation {
    const info = @typeInfo(@TypeOf(debug_data));
    if (info == .optional) {
        if (debug_data) |value| return value.native_location;
        return .{};
    }
    if (@TypeOf(debug_data) == ?*const DebugData) {
        if (debug_data) |value| return value.native_location;
        return .{};
    }
    return debug_data.native_location;
}

fn isValidNumberLiteral(literal: []const u8) bool {
    if (std.mem.startsWith(u8, literal, "0x")) {
        if (literal.len == 2) return false;
        _ = std.fmt.parseUnsigned(u256, literal[2..], 16) catch return false;
        return true;
    }
    for (literal) |character| if (!std.ascii.isDigit(character)) return false;
    if (literal.len == 0) return false;
    _ = std.fmt.parseUnsigned(u256, literal, 10) catch return false;
    return true;
}

test "parser builds and tears down a representative recursive Yul AST" {
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const source =
        "{ let x := 1 function f(a) -> r { r := a leave } " ++
        "for { let i := 0 } 1 { x := x } { if x { break } continue } " ++
        "switch x case 0 { f(x) } default { x := 2 } }";
    var ast = (try Parser.parseSource(allocator, source, "test.yul", &reporter, .{}, .{})) orelse
        return error.TestUnexpectedResult;
    defer ast.deinit();
    try std.testing.expectEqual(@as(usize, 4), ast.root().statements.items.len);
    try std.testing.expectEqual(@as(usize, 0), reporter.diagnostics().len);
}

test "parser reports nonfatal control-flow errors in source order" {
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ break continue leave }",
        "errors.yul",
        &reporter,
        .{},
        .{},
    )) orelse return error.TestUnexpectedResult;
    defer ast.deinit();
    try std.testing.expectEqual(@as(usize, 3), reporter.diagnostics().len);
    try std.testing.expectEqual(@as(u64, 2592), reporter.diagnostics()[0].error_id.value);
    try std.testing.expectEqual(@as(u64, 2592), reporter.diagnostics()[1].error_id.value);
    try std.testing.expectEqual(@as(u64, 8149), reporter.diagnostics()[2].error_id.value);
}

test "inline parser restores Solidity lookahead and propagates allocation failures" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseInlineParserRestoration, .{});
}

fn exerciseInlineParserRestoration(allocator: std.mem.Allocator) !void {
    // Yul scans a dotted name as one token. Solidity splits it into three,
    // forcing the restored lookahead to allocate a long identifier buffer.
    const source = "{ let x := 1 x := add(x, 1) if x {} for {} x {} {} } a." ++ "b" ** 256 ++ " c d";
    var stream = ScannerModule.CharStream.initBorrowed(source, "inline.sol");
    var scanner = try ScannerModule.Scanner.init(allocator, &stream, .Solidity);
    defer scanner.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var parser = Parser.init(allocator, &scanner, &reporter, .{}, .{});
    var block = (try parser.parseInline()) orelse return error.TestUnexpectedResult;
    defer block.deinit(allocator);
    try std.testing.expectEqual(ScannerModule.ScannerKind.Solidity, scanner.scannerKind());
    try std.testing.expectEqualStrings("a", scanner.currentLiteral());
    try std.testing.expectEqual(@as(usize, 4), block.statements.items.len);
}
