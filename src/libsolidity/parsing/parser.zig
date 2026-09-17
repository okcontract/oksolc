// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Recursive-descent Solidity parser translated from `Parser.cpp`.
//!
//! Covers the ordinary (non-experimental) source-unit grammar,
//! declarations, type names, statements, expressions, and inline assembly.
//! Experimental postfix syntax and some recovery paths report parser diagnostics.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTEnums = @import("../ast/ast_enums.zig");
const UserDefinableOperators = @import("../ast/user_definable_operators.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const ParserBaseModule = @import("../../liblangutil/parser_base.zig");
const ScannerModule = @import("../../liblangutil/scanner.zig");
const SemVer = @import("../../liblangutil/sem_ver_handler.zig");
const TokenModule = @import("../../liblangutil/token.zig");
const Version = @import("../interface/version.zig");
const YulAST = @import("../../libyul/ast.zig");
const YulParser = @import("../../libyul/asm_parser.zig");
const EVMDialect = @import("../../libyul/backends/evm/evm_dialect.zig");

const Token = TokenModule.Token;
const SourceLocation = ScannerModule.SourceLocation;

pub const ParseError = AST.CreateNodeError ||
    ScannerModule.ScanFailure ||
    Diagnostics.ReportError ||
    TokenModule.ElementaryTypeError ||
    YulParser.ParseError ||
    error{InvalidParserState};

pub const ParseResult = struct {
    tree: AST.Tree,

    pub fn root(self: *const ParseResult) ?*const AST.Node {
        return self.tree.root;
    }

    pub fn deinit(self: *ParseResult) void {
        self.tree.deinit();
        self.* = undefined;
    }
};

pub fn parseSource(
    allocator: std.mem.Allocator,
    source: []const u8,
    source_name: []const u8,
    error_reporter: *Diagnostics.ErrorReporter,
    evm_version: EVMVersion,
) ParseError!ParseResult {
    return parseSourceFromId(
        allocator,
        source,
        source_name,
        error_reporter,
        evm_version,
        0,
    );
}

/// Parses another source with the shared AST-ID counter used by one compiler
/// invocation. The convenience `parseSource` entry point keeps the historical
/// single-source behavior for focused unit tests.
pub fn parseSourceFromId(
    allocator: std.mem.Allocator,
    source: []const u8,
    source_name: []const u8,
    error_reporter: *Diagnostics.ErrorReporter,
    evm_version: EVMVersion,
    previous_max_id: i64,
) ParseError!ParseResult {
    return parseSourceWithIdentity(
        allocator,
        source,
        source_name,
        error_reporter,
        evm_version,
        AST.SourceId.init(0),
        previous_max_id,
    );
}

/// Parses a source with both its stable session identity and the compatibility
/// AST-ID offset for this particular compiler invocation.
pub fn parseSourceWithIdentity(
    allocator: std.mem.Allocator,
    source: []const u8,
    source_name: []const u8,
    error_reporter: *Diagnostics.ErrorReporter,
    evm_version: EVMVersion,
    source_id: AST.SourceId,
    previous_max_id: i64,
) ParseError!ParseResult {
    var tree = try AST.Tree.initWithSourceId(
        allocator,
        source_id,
        source,
        source_name,
    );
    errdefer tree.deinit();
    tree.next_node_id = previous_max_id;
    var stream = ScannerModule.CharStream.initBorrowed(tree.source, tree.source_name);
    var scanner = try ScannerModule.Scanner.init(allocator, &stream, .Solidity);
    defer scanner.deinit();
    var parser = Parser.init(allocator, &tree, &scanner, error_reporter, evm_version);
    tree.root = parser.parse() catch |err| switch (err) {
        error.FatalDiagnostic => null,
        else => return err,
    };
    return .{ .tree = tree };
}

const VarDeclKind = enum { file_level, state, other };

const VarDeclOptions = struct {
    kind: VarDeclKind = .other,
    allow_indexed: bool = false,
    allow_empty_name: bool = false,
    allow_initial_value: bool = false,
    allow_location_specifier: bool = false,
};

const FunctionHeader = struct {
    is_virtual: bool = false,
    overrides: ?*AST.Node = null,
    parameters: *AST.Node,
    return_parameters: *AST.Node,
    visibility: AST.Visibility = .Default,
    state_mutability: AST.StateMutability = .NonPayable,
    modifiers: AST.NodeList = &.{},
};

const ParsedCallArguments = struct {
    arguments: AST.NodeList = &.{},
    parameter_names: AST.StringList = &.{},
    parameter_name_locations: []const SourceLocation = &.{},
};

const LookAheadInfo = enum {
    variable_declaration,
    index_access_structure,
    expression,
};

const IndexAccessedPath = struct {
    const Index = struct {
        start: ?*AST.Node = null,
        end: ?*AST.Node = null,
        is_range: bool = false,
        location: SourceLocation,
    };

    path: std.ArrayList(*AST.Node) = .empty,
    indices: std.ArrayList(Index) = .empty,

    fn deinit(self: *IndexAccessedPath, allocator: std.mem.Allocator) void {
        self.path.deinit(allocator);
        self.indices.deinit(allocator);
        self.* = undefined;
    }

    fn empty(self: *const IndexAccessedPath) bool {
        return self.path.items.len == 0 and self.indices.items.len == 0;
    }
};

const ParsedStatementPrefix = struct {
    kind: LookAheadInfo,
    path: IndexAccessedPath = .{},
};

pub const Parser = struct {
    allocator: std.mem.Allocator,
    tree: *AST.Tree,
    base: ParserBaseModule.ParserBase,
    evm_version: EVMVersion,
    inside_modifier: bool = false,
    experimental_solidity: bool = false,

    pub fn init(
        allocator: std.mem.Allocator,
        tree: *AST.Tree,
        scanner: *ScannerModule.Scanner,
        error_reporter: *Diagnostics.ErrorReporter,
        evm_version: EVMVersion,
    ) Parser {
        return .{
            .allocator = allocator,
            .tree = tree,
            .base = ParserBaseModule.ParserBase.init(allocator, scanner, error_reporter),
            .evm_version = evm_version,
        };
    }

    pub fn maxId(self: *const Parser) i64 {
        return self.tree.next_node_id;
    }

    pub fn parse(self: *Parser) ParseError!*AST.Node {
        var factory = NodeFactory.init(self);
        var nodes: std.ArrayList(*AST.Node) = .empty;
        defer nodes.deinit(self.allocator);

        while (self.currentToken() == .Pragma)
            try nodes.append(self.allocator, try self.parsePragmaDirective(false));
        if (self.experimental_solidity)
            try self.base.scanner.setScannerMode(.ExperimentalSolidity);

        while (self.currentToken() != .EOS) {
            const node = switch (self.currentToken()) {
                .Pragma => try self.parsePragmaDirective(true),
                .Import => try self.parseImportDirective(),
                .Abstract, .Interface, .Contract, .Library => try self.parseContractDefinition(),
                .Struct => try self.parseStructDefinition(),
                .Enum => try self.parseEnumDefinition(),
                .Type => try self.parseUserDefinedValueTypeDefinition(),
                .Using => try self.parseUsingDirective(),
                .Function => try self.parseFunctionDefinition(true, true),
                .Event => try self.parseEventDefinition(),
                else => blk: {
                    if (self.isErrorDefinitionStart()) break :blk try self.parseErrorDefinition();
                    if (self.variableDeclarationStart() and self.base.scanner.peekNextToken() != .EOS) {
                        const declaration = try self.parseVariableDeclaration(.{
                            .kind = .file_level,
                            .allow_initial_value = true,
                        }, null);
                        try self.expect(.Semicolon);
                        break :blk declaration;
                    }
                    try self.fatal(
                        7858,
                        "Expected pragma, import directive or contract/interface/library/user-defined type/constant/function/error/event definition.",
                    );
                    unreachable;
                },
            };
            try nodes.append(self.allocator, node);
        }

        const owned_nodes = try self.tree.ownSlice(*AST.Node, nodes.items);
        const license = try self.findLicenseString(owned_nodes);
        const root = try factory.create(.{ .source_unit = .{
            .license = license,
            .nodes = owned_nodes,
            .experimental_solidity = self.experimental_solidity,
        } });
        return root;
    }

    fn currentToken(self: *const Parser) Token {
        return self.base.scanner.currentToken();
    }

    fn currentLocation(self: *const Parser) SourceLocation {
        return self.base.scanner.currentLocation();
    }

    fn currentLiteral(self: *const Parser) []const u8 {
        return self.base.scanner.currentLiteral();
    }

    fn advance(self: *Parser) ParseError!Token {
        return self.base.advance();
    }

    fn fatal(self: *Parser, error_id: u64, description: []const u8) ParseError!void {
        try self.base.error_reporter.fatal(
            .{ .value = error_id },
            .ParserError,
            self.currentLocation(),
            null,
            description,
        );
    }

    fn parserError(self: *Parser, error_id: u64, description: []const u8) ParseError!void {
        try self.base.error_reporter.parserError(
            .{ .value = error_id },
            self.currentLocation(),
            description,
        );
    }

    fn expect(self: *Parser, expected: Token) ParseError!void {
        try self.base.expectToken(expected, true);
    }

    fn expectWithoutAdvance(self: *Parser, expected: Token) ParseError!void {
        try self.base.expectToken(expected, false);
    }

    fn expectIdentifier(self: *Parser) ParseError![]const u8 {
        if (self.currentToken() != .Identifier) {
            const actual_name = try self.base.tokenNameAlloc(self.currentToken());
            defer self.allocator.free(actual_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Expected identifier but got {s}",
                .{actual_name},
            );
            defer self.allocator.free(message);
            try self.fatal(2314, message);
        }
        const result = try self.tree.ownString(self.currentLiteral());
        _ = try self.advance();
        return result;
    }

    fn expectIdentifierOrAddress(self: *Parser) ParseError![]const u8 {
        if (self.currentToken() == .Address) {
            _ = try self.advance();
            return self.tree.ownString("address");
        }
        return self.expectIdentifier();
    }

    fn expectIdentifierWithLocation(self: *Parser) ParseError!struct {
        name: []const u8,
        location: SourceLocation,
    } {
        const location = self.currentLocation();
        return .{ .name = try self.expectIdentifier(), .location = location };
    }

    fn parseStructuredDocumentation(self: *Parser) ParseError!?*AST.Node {
        const comment = self.base.scanner.currentCommentLiteral();
        if (comment.len == 0) return null;
        const text = try self.tree.ownString(comment);
        var factory = NodeFactory.init(self);
        factory.location = self.base.scanner.currentCommentLocation();
        return factory.create(.{ .structured_documentation = .{ .text = text } });
    }

    fn parsePragmaDirective(self: *Parser, finished_top_level: bool) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.Pragma);
        var tokens: std.ArrayList(Token) = .empty;
        defer tokens.deinit(self.allocator);
        var literals: std.ArrayList([]const u8) = .empty;
        defer literals.deinit(self.allocator);
        while (self.currentToken() != .Semicolon and self.currentToken() != .EOS) {
            const token = self.currentToken();
            if (token == .Illegal) {
                try self.parserError(
                    6281,
                    "Token incompatible with Solidity parser as part of pragma directive.",
                );
                _ = try self.advance();
                continue;
            }
            const literal = if (self.currentLiteral().len != 0)
                try self.tree.ownString(self.currentLiteral())
            else
                try self.tree.ownString(TokenModule.toString(token) orelse "");
            try tokens.append(self.allocator, token);
            try literals.append(self.allocator, literal);
            _ = try self.advance();
        }
        factory.markEndPosition();
        try self.expect(.Semicolon);
        if (literals.items.len >= 1 and std.mem.eql(u8, literals.items[0], "solidity"))
            try self.parsePragmaVersion(
                factory.location,
                tokens.items[1..],
                literals.items[1..],
            );
        if (literals.items.len >= 2 and
            std.mem.eql(u8, literals.items[0], "experimental") and
            std.mem.eql(u8, literals.items[1], "solidity"))
        {
            if (!self.evm_version.atLeast(.Constantinople))
                try self.fatal(
                    7637,
                    "Experimental solidity requires Constantinople EVM version at the minimum.",
                );
            if (finished_top_level)
                try self.fatal(8185, "Experimental pragma \"solidity\" can only be set at the beginning of the source unit.");
            self.experimental_solidity = true;
        }
        return factory.create(.{ .pragma_directive = .{
            .tokens = try self.tree.ownSlice(Token, tokens.items),
            .literals = try self.tree.ownSlice([]const u8, literals.items),
        } });
    }

    fn parsePragmaVersion(
        self: *Parser,
        location: SourceLocation,
        tokens: []const Token,
        literals: []const []const u8,
    ) ParseError!void {
        var parser = SemVer.SemVerMatchExpressionParser.init(
            self.allocator,
            tokens,
            literals,
        ) catch return error.InvalidParserState;
        var expression = parser.parse() catch |parse_error| switch (parse_error) {
            error.OutOfMemory => return error.OutOfMemory,
            else => {
                const semver_error: SemVer.SemVerError = @errorCast(parse_error);
                const detail = try parser.errorMessageAlloc(self.allocator, semver_error);
                defer self.allocator.free(detail);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Invalid version pragma. {s}",
                    .{detail},
                );
                defer self.allocator.free(message);
                try self.base.error_reporter.fatal(
                    .{ .value = 1684 },
                    .ParserError,
                    location,
                    null,
                    message,
                );
                return;
            },
        };
        defer expression.deinit();
        var current = SemVer.SemVerVersion.init(self.allocator, Version.VersionNumber) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.InvalidParserState,
        };
        defer current.deinit();
        if (!expression.matches(current)) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Source file requires different compiler version (current compiler is {s}) - note that nightly builds are considered to be strictly less than the released version",
                .{Version.VersionString},
            );
            defer self.allocator.free(message);
            try self.base.error_reporter.fatal(
                .{ .value = 5333 },
                .ParserError,
                location,
                null,
                message,
            );
        }
    }

    fn parseImportDirective(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.Import);
        var path: []const u8 = "";
        var unit_alias: []const u8 = "";
        var unit_alias_location: SourceLocation = .{};
        var aliases: std.ArrayList(AST.SymbolAlias) = .empty;
        defer aliases.deinit(self.allocator);

        if (self.isQuotedPath()) {
            path = try self.tree.ownString(self.currentLiteral());
            _ = try self.advance();
            if (self.currentToken() == .As) {
                _ = try self.advance();
                const named = try self.expectIdentifierWithLocation();
                unit_alias = named.name;
                unit_alias_location = named.location;
            }
        } else if (self.currentToken() == .Mul) {
            _ = try self.advance();
            try self.expect(.As);
            const named = try self.expectIdentifierWithLocation();
            unit_alias = named.name;
            unit_alias_location = named.location;
            try self.expectFromIdentifier();
            path = try self.parseImportPath();
        } else if (self.currentToken() == .LBrace) {
            _ = try self.advance();
            while (true) {
                const symbol_location = self.currentLocation();
                const symbol = try self.parseIdentifier();
                var alias: ?[]const u8 = null;
                var alias_location = symbol_location;
                if (self.currentToken() == .As) {
                    _ = try self.advance();
                    const named = try self.expectIdentifierWithLocation();
                    alias = named.name;
                    alias_location = named.location;
                }
                try aliases.append(self.allocator, .{
                    .symbol = symbol,
                    .alias = alias,
                    .location = alias_location,
                });
                if (self.currentToken() != .Comma) break;
                _ = try self.advance();
            }
            try self.expect(.RBrace);
            try self.expectFromIdentifier();
            path = try self.parseImportPath();
        } else {
            try self.fatal(9478, "Expected string literal (path), \"*\" or alias list.");
        }
        if (path.len == 0) try self.fatal(6326, "Import path cannot be empty.");
        factory.markEndPosition();
        try self.expect(.Semicolon);
        return factory.create(.{ .import_directive = .{
            .declaration = .{
                .name = unit_alias,
                .name_location = unit_alias_location,
            },
            .path = path,
            .symbol_aliases = try self.tree.ownSlice(AST.SymbolAlias, aliases.items),
        } });
    }

    fn expectFromIdentifier(self: *Parser) ParseError!void {
        if (self.currentToken() != .Identifier or !std.mem.eql(u8, self.currentLiteral(), "from"))
            try self.fatal(8208, "Expected \"from\".");
        _ = try self.advance();
    }

    fn isQuotedPath(self: *const Parser) bool {
        return self.currentToken() == .StringLiteral;
    }

    fn parseImportPath(self: *Parser) ParseError![]const u8 {
        if (!self.isQuotedPath()) try self.fatal(6845, "Expected import path.");
        const path = try self.tree.ownString(self.currentLiteral());
        _ = try self.advance();
        return path;
    }

    fn parseContractDefinition(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        var abstract = false;
        if (self.currentToken() == .Abstract) {
            abstract = true;
            _ = try self.advance();
        }
        const contract_kind: AST.ContractKind = switch (self.currentToken()) {
            .Interface => .Interface,
            .Contract => .Contract,
            .Library => .Library,
            else => blk: {
                try self.parserError(3515, "Expected keyword \"contract\", \"interface\" or \"library\".");
                break :blk .Contract;
            },
        };
        if (self.currentToken() == .Interface or
            self.currentToken() == .Contract or
            self.currentToken() == .Library)
            _ = try self.advance();
        const named = try self.expectIdentifierWithLocation();
        var base_contracts: std.ArrayList(*AST.Node) = .empty;
        defer base_contracts.deinit(self.allocator);
        var storage_layout: ?*AST.Node = null;
        while (true) {
            if (self.currentToken() == .Is) {
                if (base_contracts.items.len != 0) {
                    var secondary: Diagnostics.SecondarySourceLocation = .{};
                    defer secondary.deinit(self.allocator);
                    try secondary.append(
                        self.allocator,
                        "Previous list:",
                        base_contracts.items[0].location,
                    );
                    try self.base.error_reporter.reportWithSecondary(
                        .{ .value = 6668 },
                        .ParserError,
                        self.currentLocation(),
                        &secondary,
                        "More than one inheritance list.",
                    );
                }
                while (true) {
                    _ = try self.advance();
                    try base_contracts.append(self.allocator, try self.parseInheritanceSpecifier());
                    if (self.currentToken() != .Comma) break;
                }
            } else if (self.currentToken() == .Identifier and
                std.mem.eql(u8, self.currentLiteral(), "layout") and
                contract_kind == .Contract)
            {
                if (storage_layout) |previous| {
                    var secondary: Diagnostics.SecondarySourceLocation = .{};
                    defer secondary.deinit(self.allocator);
                    try secondary.append(
                        self.allocator,
                        "Previous definition:",
                        previous.location,
                    );
                    try self.base.error_reporter.reportWithSecondary(
                        .{ .value = 8714 },
                        .ParserError,
                        self.currentLocation(),
                        &secondary,
                        "More than one storage layout definition.",
                    );
                }
                storage_layout = try self.parseStorageLayoutSpecifier();
            } else break;
        }

        try self.expect(.LBrace);
        var sub_nodes: std.ArrayList(*AST.Node) = .empty;
        defer sub_nodes.deinit(self.allocator);
        while (self.currentToken() != .RBrace) {
            if (self.currentToken() == .EOS)
                try self.fatal(2314, "Expected '}' but got end of source");
            const child = switch (self.currentToken()) {
                .Function => if (self.base.scanner.peekNextToken() == .LParen) blk: {
                    const variable = try self.parseVariableDeclaration(.{
                        .kind = .state,
                        .allow_initial_value = true,
                    }, null);
                    try self.expect(.Semicolon);
                    break :blk variable;
                } else try self.parseFunctionDefinition(false, true),
                .Constructor, .Receive, .Fallback => try self.parseFunctionDefinition(false, true),
                .Struct => try self.parseStructDefinition(),
                .Enum => try self.parseEnumDefinition(),
                .Type => try self.parseUserDefinedValueTypeDefinition(),
                .Modifier => try self.parseModifierDefinition(),
                .Event => try self.parseEventDefinition(),
                .Using => try self.parseUsingDirective(),
                else => blk: {
                    if (self.isErrorDefinitionStart()) break :blk try self.parseErrorDefinition();
                    if (self.variableDeclarationStart()) {
                        const variable = try self.parseVariableDeclaration(.{
                            .kind = .state,
                            .allow_initial_value = true,
                        }, null);
                        try self.expect(.Semicolon);
                        break :blk variable;
                    }
                    try self.fatal(9182, "Function, variable, struct or modifier declaration expected.");
                    unreachable;
                },
            };
            try sub_nodes.append(self.allocator, child);
        }
        factory.markEndPosition();
        try self.expect(.RBrace);
        return factory.create(.{ .contract_definition = .{
            .declaration = .{ .name = named.name, .name_location = named.location },
            .documentation = documentation,
            .base_contracts = try self.tree.ownSlice(*AST.Node, base_contracts.items),
            .sub_nodes = try self.tree.ownSlice(*AST.Node, sub_nodes.items),
            .contract_kind = contract_kind,
            .abstract = abstract,
            .storage_layout_specifier = storage_layout,
        } });
    }

    fn parseStorageLayoutSpecifier(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        _ = try self.expectIdentifier();
        if (self.currentToken() != .Identifier or !std.mem.eql(u8, self.currentLiteral(), "at")) {
            const actual_name = try self.base.tokenNameAlloc(self.currentToken());
            defer self.allocator.free(actual_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Expected 'at' but got {s}",
                .{actual_name},
            );
            defer self.allocator.free(message);
            try self.parserError(1994, message);
        }
        _ = try self.advance();
        const expression = try self.parseExpression(null);
        factory.setEndPositionFromNode(expression);
        return factory.create(.{ .storage_layout_specifier = .{ .base_slot_expression = expression } });
    }

    fn parseInheritanceSpecifier(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const name = try self.parseIdentifierPath();
        var arguments: ?AST.NodeList = null;
        if (self.currentToken() == .LParen) {
            _ = try self.advance();
            arguments = try self.parseFunctionCallListArguments();
            factory.markEndPosition();
            try self.expect(.RParen);
        } else factory.setEndPositionFromNode(name);
        return factory.create(.{ .inheritance_specifier = .{
            .base_name = name,
            .arguments = arguments,
        } });
    }

    fn parseUsingDirective(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.Using);

        var entries: std.ArrayList(AST.FunctionAndOperator) = .empty;
        defer entries.deinit(self.allocator);
        const uses_braces = self.currentToken() == .LBrace;
        if (uses_braces) {
            try self.expect(.LBrace);
            while (true) {
                const function = try self.parseIdentifierPath();
                var operator: ?Token = null;
                if (self.currentToken() == .As) {
                    _ = try self.advance();
                    operator = self.currentToken();
                    if (!UserDefinableOperators.isUserDefinableOperator(operator.?)) {
                        const operator_name = if (self.currentLiteral().len != 0)
                            self.currentLiteral()
                        else
                            TokenModule.toString(operator.?) orelse "";
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "Not a user-definable operator: {s}. Only the following operators can be user-defined: |, &, ^, ~, +, -, *, /, %, ==, !=, <, >, <=, >=",
                            .{operator_name},
                        );
                        defer self.allocator.free(message);
                        try self.parserError(
                            4403,
                            message,
                        );
                    }
                    _ = try self.advance();
                }
                try entries.append(self.allocator, .{
                    .function_or_library = function,
                    .operator = operator,
                });
                if (self.currentToken() != .Comma) break;
                _ = try self.advance();
            }
            try self.expect(.RBrace);
        } else {
            try entries.append(self.allocator, .{
                .function_or_library = try self.parseIdentifierPath(),
            });
        }

        try self.expect(.For);
        const type_name = if (self.currentToken() == .Mul) blk: {
            _ = try self.advance();
            break :blk null;
        } else try self.parseTypeName();
        var global = false;
        if (self.currentToken() == .Identifier and std.mem.eql(u8, self.currentLiteral(), "global")) {
            global = true;
            _ = try self.advance();
        }
        factory.markEndPosition();
        try self.expect(.Semicolon);
        return factory.create(.{ .using_for_directive = .{
            .functions_and_operators = try self.tree.ownSlice(AST.FunctionAndOperator, entries.items),
            .uses_braces = uses_braces,
            .type_name = type_name,
            .global = global,
        } });
    }

    fn parseIdentifier(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        factory.markEndPosition();
        return factory.create(.{ .identifier = .{ .name = try self.expectIdentifier() } });
    }

    fn parseIdentifierPath(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        var names: std.ArrayList([]const u8) = .empty;
        defer names.deinit(self.allocator);
        var locations: std.ArrayList(SourceLocation) = .empty;
        defer locations.deinit(self.allocator);
        while (true) {
            factory.markEndPosition();
            const named = try self.expectIdentifierWithLocation();
            try names.append(self.allocator, named.name);
            try locations.append(self.allocator, named.location);
            if (self.currentToken() != .Period) break;
            _ = try self.advance();
        }
        return factory.create(.{ .identifier_path = .{
            .path = try self.tree.ownSlice([]const u8, names.items),
            .path_locations = try self.tree.ownSlice(SourceLocation, locations.items),
        } });
    }

    fn parseUserDefinedTypeName(self: *Parser) ParseError!*AST.Node {
        var factory = NodeFactory.init(self);
        const path = try self.parseIdentifierPath();
        factory.setEndPositionFromNode(path);
        return factory.create(.{ .user_defined_type_name = .{ .path_node = path } });
    }

    fn parseTypeName(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var suffix_factory = NodeFactory.init(self);
        var result: *AST.Node = undefined;
        if (TokenModule.isElementaryTypeName(self.currentToken())) {
            var factory = NodeFactory.init(self);
            factory.markEndPosition();
            const info = self.base.scanner.currentTokenInfo();
            const elementary = try TokenModule.ElementaryTypeNameToken.init(
                self.currentToken(),
                info.first,
                info.second,
            );
            const is_address = elementary.token_value == .Address;
            _ = try self.advance();
            var mutability: ?AST.StateMutability = if (is_address) .NonPayable else null;
            if (TokenModule.isStateMutabilitySpecifier(self.currentToken())) {
                if (!is_address) {
                    try self.parserError(9106, "State mutability can only be specified for address types.");
                    _ = try self.advance();
                } else {
                    factory.markEndPosition();
                    mutability = try self.parseStateMutability();
                }
            }
            result = try factory.create(.{ .elementary_type_name = .{
                .type_name = elementary,
                .state_mutability = mutability,
            } });
        } else result = switch (self.currentToken()) {
            .Function => try self.parseFunctionType(),
            .Mapping => try self.parseMapping(),
            .Identifier => try self.parseUserDefinedTypeName(),
            else => {
                try self.fatal(3546, "Expected type name");
                unreachable;
            },
        };

        return self.parseTypeNameSuffix(result, &suffix_factory);
    }

    fn parseTypeNameSuffix(
        self: *Parser,
        initial_type: *AST.Node,
        suffix_factory: *NodeFactory,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var result = initial_type;
        while (self.currentToken() == .LBrack) {
            _ = try self.advance();
            const length = if (self.currentToken() != .RBrack)
                try self.parseExpression(null)
            else
                null;
            suffix_factory.markEndPosition();
            try self.expect(.RBrack);
            result = try suffix_factory.create(.{ .array_type_name = .{
                .base_type = result,
                .length = length,
            } });
        }
        return result;
    }

    fn parseMapping(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.Mapping);
        try self.expect(.LParen);
        const key_type = if (self.currentToken() == .Identifier)
            try self.parseUserDefinedTypeName()
        else if (TokenModule.isElementaryTypeName(self.currentToken())) blk: {
            var type_factory = NodeFactory.init(self);
            const info = self.base.scanner.currentTokenInfo();
            const elementary = try TokenModule.ElementaryTypeNameToken.init(
                self.currentToken(),
                info.first,
                info.second,
            );
            type_factory.markEndPosition();
            _ = try self.advance();
            break :blk try type_factory.create(.{ .elementary_type_name = .{ .type_name = elementary } });
        } else {
            try self.fatal(1005, "Expected elementary type name or identifier for mapping key type");
            unreachable;
        };
        var key_name: []const u8 = "";
        var key_location: SourceLocation = .{};
        if (self.currentToken() == .Identifier) {
            const named = try self.expectIdentifierWithLocation();
            key_name = named.name;
            key_location = named.location;
        }
        try self.expect(.DoubleArrow);
        const value_type = try self.parseTypeName();
        var value_name: []const u8 = "";
        var value_location: SourceLocation = .{};
        if (self.currentToken() == .Identifier) {
            const named = try self.expectIdentifierWithLocation();
            value_name = named.name;
            value_location = named.location;
        }
        factory.markEndPosition();
        try self.expect(.RParen);
        return factory.create(.{ .mapping = .{
            .key_type = key_type,
            .key_name = key_name,
            .key_name_location = key_location,
            .value_type = value_type,
            .value_name = value_name,
            .value_name_location = value_location,
        } });
    }

    fn findLicenseString(self: *Parser, nodes: AST.NodeList) ParseError!?[]const u8 {
        const marker = "SPDX-License-Identifier:";
        var licenses: std.ArrayList([]const u8) = .empty;
        defer licenses.deinit(self.allocator);

        var gap_start: usize = 0;
        for (nodes) |node| {
            if (node.location.start < 0 or node.location.end < node.location.start) continue;
            const node_start: usize = @intCast(node.location.start);
            const node_end: usize = @intCast(node.location.end);
            if (node_start > self.tree.source.len or node_end > self.tree.source.len) continue;
            try collectLicenseDeclarations(
                self.allocator,
                self.tree.source,
                gap_start,
                node_start,
                marker,
                &licenses,
            );
            gap_start = @max(gap_start, node_end);
        }
        try collectLicenseDeclarations(
            self.allocator,
            self.tree.source,
            gap_start,
            self.tree.source.len,
            marker,
            &licenses,
        );

        const global_location: SourceLocation = .{ .source_name = self.tree.source_name };
        if (licenses.items.len == 1) {
            const license = licenses.items[0];
            if (license.len != 0 and allLicenseNameCharacters(license))
                return try self.tree.ownString(license);
            try self.base.error_reporter.parserError(
                .{ .value = 1114 },
                global_location,
                "Invalid SPDX license identifier.",
            );
        } else if (licenses.items.len == 0) {
            try self.base.error_reporter.warning(
                .{ .value = 1878 },
                global_location,
                "SPDX license identifier not provided in source file. Before publishing, consider adding a comment containing \"SPDX-License-Identifier: <SPDX-License>\" to each source file. Use \"SPDX-License-Identifier: UNLICENSED\" for non-open-source code. Please see https://spdx.org for more information.",
            );
        } else {
            try self.base.error_reporter.parserError(
                .{ .value = 3716 },
                global_location,
                "Multiple SPDX license identifiers found in source file. Use \"AND\" or \"OR\" to combine multiple licenses. Please see https://spdx.org for more information.",
            );
        }
        return null;
    }

    fn isErrorDefinitionStart(self: *const Parser) bool {
        return self.currentToken() == .Identifier and
            std.mem.eql(u8, self.currentLiteral(), "error") and
            self.base.scanner.peekNextToken() == .Identifier and
            self.base.scanner.peekNextNextToken() == .LParen;
    }

    fn variableDeclarationStart(self: *const Parser) bool {
        return self.currentToken() == .Identifier or
            self.currentToken() == .Mapping or
            TokenModule.isElementaryTypeName(self.currentToken()) or
            (self.currentToken() == .Function and self.base.scanner.peekNextToken() == .LParen);
    }

    fn parseVisibility(self: *Parser) ParseError!AST.Visibility {
        const result: AST.Visibility = switch (self.currentToken()) {
            .Public => .Public,
            .Internal => .Internal,
            .Private => .Private,
            .External => .External,
            else => return error.InvalidParserState,
        };
        _ = try self.advance();
        return result;
    }

    fn parseStateMutability(self: *Parser) ParseError!AST.StateMutability {
        const result: AST.StateMutability = switch (self.currentToken()) {
            .Payable => .Payable,
            .View => .View,
            .Pure => .Pure,
            else => return error.InvalidParserState,
        };
        _ = try self.advance();
        return result;
    }

    fn parseOverrideSpecifier(self: *Parser) ParseError!*AST.Node {
        var factory = NodeFactory.init(self);
        factory.markEndPosition();
        try self.expect(.Override);
        var overrides: std.ArrayList(*AST.Node) = .empty;
        defer overrides.deinit(self.allocator);
        if (self.currentToken() == .LParen) {
            _ = try self.advance();
            while (true) {
                try overrides.append(self.allocator, try self.parseIdentifierPath());
                if (self.currentToken() == .RParen) break;
                try self.expect(.Comma);
            }
            factory.markEndPosition();
            try self.expect(.RParen);
        }
        return factory.create(.{ .override_specifier = .{
            .overrides = try self.tree.ownSlice(*AST.Node, overrides.items),
        } });
    }

    fn parseParameterList(
        self: *Parser,
        base_options: VarDeclOptions,
        allow_empty: bool,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        var parameters: std.ArrayList(*AST.Node) = .empty;
        defer parameters.deinit(self.allocator);
        var options = base_options;
        options.allow_empty_name = true;
        try self.expect(.LParen);
        if (!allow_empty or self.currentToken() != .RParen) {
            try parameters.append(self.allocator, try self.parseVariableDeclaration(options, null));
            while (self.currentToken() != .RParen) {
                if (self.currentToken() == .Comma and self.base.scanner.peekNextToken() == .RParen)
                    try self.fatal(7591, "Unexpected trailing comma in parameter list.");
                try self.expect(.Comma);
                try parameters.append(self.allocator, try self.parseVariableDeclaration(options, null));
            }
        }
        factory.markEndPosition();
        try self.expect(.RParen);
        return factory.create(.{ .parameter_list = .{
            .parameters = try self.tree.ownSlice(*AST.Node, parameters.items),
        } });
    }

    fn createEmptyParameterList(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        factory.location.end = factory.location.start;
        return factory.create(.{ .parameter_list = .{} });
    }

    fn parseFunctionHeader(self: *Parser, is_state_variable: bool) ParseError!FunctionHeader {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var result: FunctionHeader = undefined;
        result = .{
            .parameters = try self.parseParameterList(.{
                .allow_location_specifier = true,
            }, true),
            .return_parameters = undefined,
        };
        var modifiers: std.ArrayList(*AST.Node) = .empty;
        defer modifiers.deinit(self.allocator);
        while (true) {
            const token = self.currentToken();
            if (!is_state_variable and token == .Identifier) {
                try modifiers.append(self.allocator, try self.parseModifierInvocation());
            } else if (TokenModule.isVisibilitySpecifier(token)) {
                if (result.visibility != .Default) {
                    if (is_state_variable and
                        (result.visibility == .External or result.visibility == .Internal))
                        break;
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Visibility already specified as \"{s}\".",
                        .{visibilityToString(result.visibility)},
                    );
                    defer self.allocator.free(message);
                    try self.parserError(9439, message);
                    _ = try self.advance();
                } else result.visibility = try self.parseVisibility();
            } else if (TokenModule.isStateMutabilitySpecifier(token)) {
                if (result.state_mutability != .NonPayable) {
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "State mutability already specified as \"{s}\".",
                        .{ASTEnums.stateMutabilityToString(result.state_mutability)},
                    );
                    defer self.allocator.free(message);
                    try self.parserError(9680, message);
                    _ = try self.advance();
                } else result.state_mutability = try self.parseStateMutability();
            } else if (!is_state_variable and token == .Override) {
                if (result.overrides != null) try self.parserError(1827, "Override already specified.");
                result.overrides = try self.parseOverrideSpecifier();
            } else if (!is_state_variable and token == .Virtual) {
                if (result.is_virtual) try self.parserError(6879, "Virtual already specified.");
                result.is_virtual = true;
                _ = try self.advance();
            } else break;
        }
        if (self.currentToken() == .Returns) {
            _ = try self.advance();
            result.return_parameters = try self.parseParameterList(.{
                .allow_location_specifier = true,
            }, false);
        } else result.return_parameters = try self.createEmptyParameterList();
        result.modifiers = try self.tree.ownSlice(*AST.Node, modifiers.items);
        return result;
    }

    fn parseFunctionType(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.Function);
        const header = try self.parseFunctionHeader(true);
        return factory.create(.{ .function_type_name = .{
            .parameter_types = header.parameters,
            .return_types = header.return_parameters,
            .visibility = header.visibility,
            .state_mutability = header.state_mutability,
        } });
    }

    fn parseModifierInvocation(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const name = try self.parseIdentifierPath();
        var arguments: ?AST.NodeList = null;
        if (self.currentToken() == .LParen) {
            _ = try self.advance();
            arguments = try self.parseFunctionCallListArguments();
            factory.markEndPosition();
            try self.expect(.RParen);
        } else factory.setEndPositionFromNode(name);
        return factory.create(.{ .modifier_invocation = .{
            .modifier_name = name,
            .arguments = arguments,
        } });
    }

    fn parseFunctionDefinition(
        self: *Parser,
        free_function: bool,
        allow_body: bool,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        const kind = self.currentToken();
        var name: []const u8 = "";
        var name_location: SourceLocation = .{};
        if (kind == .Function) {
            _ = try self.advance();
            if (self.currentToken() == .Constructor or
                self.currentToken() == .Fallback or
                self.currentToken() == .Receive)
            {
                const name_token = self.currentToken();
                const token_name = TokenModule.toString(name_token) orelse
                    return error.InvalidParserState;
                const expected = switch (name_token) {
                    .Constructor => "constructor",
                    .Fallback => "fallback function",
                    .Receive => "receive function",
                    else => unreachable,
                };
                name_location = self.currentLocation();
                name = try self.tree.ownString(token_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "This function is named \"{s}\" but is not the {s} of the contract. If you intend this to be a {s}, use \"{s}(...) {{ ... }}\" without the \"function\" keyword to define it.",
                    .{ name, expected, expected, name },
                );
                defer self.allocator.free(message);
                if (name_token == .Constructor)
                    try self.parserError(3323, message)
                else
                    try self.base.error_reporter.warning(
                        .{ .value = 3445 },
                        self.currentLocation(),
                        message,
                    );
                _ = try self.advance();
            } else {
                const named = try self.expectIdentifierWithLocation();
                name = named.name;
                name_location = named.location;
            }
        } else if (kind == .Constructor or kind == .Fallback or kind == .Receive) {
            _ = try self.advance();
        } else return error.InvalidParserState;

        const header = try self.parseFunctionHeader(false);
        var body: ?*AST.Node = null;
        factory.markEndPosition();
        if (!allow_body) {
            try self.expect(.Semicolon);
        } else if (self.currentToken() == .Semicolon) {
            _ = try self.advance();
        } else {
            body = try self.parseBlock(false, null);
            factory.setEndPositionFromNode(body.?);
        }
        return factory.create(.{ .function_definition = .{
            .callable = .{
                .declaration = .{
                    .name = name,
                    .name_location = name_location,
                    .visibility = header.visibility,
                },
                .parameters = header.parameters,
                .overrides = header.overrides,
                .return_parameters = header.return_parameters,
                .marked_virtual = header.is_virtual,
            },
            .documentation = documentation,
            .state_mutability = header.state_mutability,
            .free = free_function,
            .kind = kind,
            .modifiers = header.modifiers,
            .body = body,
        } });
    }

    fn parseVariableDeclaration(
        self: *Parser,
        options: VarDeclOptions,
        lookahead_type: ?*AST.Node,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = if (lookahead_type) |child|
            NodeFactory.fromNode(self, child)
        else
            NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        const type_name = lookahead_type orelse try self.parseTypeName();
        factory.setEndPositionFromNode(type_name);
        if (type_name.nodeKind() == .function_type_name and
            options.kind == .state and
            self.currentToken() == .LBrace)
            try self.fatal(
                2915,
                "Expected a state variable declaration. If you intended this as a fallback function or a function to handle plain ether transactions, use the \"fallback\" keyword or the \"receive\" keyword instead.",
            );
        var indexed = false;
        var mutability: AST.VariableMutability = .Mutable;
        var overrides: ?*AST.Node = null;
        var visibility: AST.Visibility = .Default;
        var reference_location: AST.VariableLocation = .Unspecified;

        while (true) {
            const token = self.currentToken();
            if (options.kind == .state and TokenModule.isVariableVisibilitySpecifier(token)) {
                factory.markEndPosition();
                if (visibility != .Default) {
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Visibility already specified as \"{s}\".",
                        .{visibilityToString(visibility)},
                    );
                    defer self.allocator.free(message);
                    try self.parserError(4110, message);
                    _ = try self.advance();
                } else visibility = try self.parseVisibility();
            } else if (options.kind == .state and token == .Override) {
                if (overrides != null) try self.parserError(9125, "Override already specified.");
                overrides = try self.parseOverrideSpecifier();
            } else if (options.allow_indexed and token == .Indexed) {
                if (indexed) try self.parserError(5399, "Indexed already specified.");
                indexed = true;
                factory.markEndPosition();
                _ = try self.advance();
            } else if (token == .Constant or token == .Immutable) {
                if (mutability != .Mutable) {
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Mutability already set to \"{s}\"",
                        .{if (mutability == .Constant) "constant" else "immutable"},
                    );
                    defer self.allocator.free(message);
                    try self.parserError(3109, message);
                } else mutability = if (token == .Constant) .Constant else .Immutable;
                factory.markEndPosition();
                _ = try self.advance();
            } else if (options.allow_location_specifier and TokenModule.isLocationSpecifier(token)) {
                if (reference_location != .Unspecified) {
                    try self.parserError(3548, "Location already specified.");
                } else reference_location = switch (token) {
                    .Storage => .Storage,
                    .Memory => .Memory,
                    .CallData => .CallData,
                    else => return error.InvalidParserState,
                };
                factory.markEndPosition();
                _ = try self.advance();
            } else if (options.kind == .state and token == .Identifier and
                std.mem.eql(u8, self.currentLiteral(), "transient") and
                self.base.scanner.peekNextToken() != .Assign and
                self.base.scanner.peekNextToken() != .Semicolon)
            {
                if (reference_location != .Unspecified)
                    try self.parserError(3548, "Location already specified.")
                else
                    reference_location = .Transient;
                factory.markEndPosition();
                _ = try self.advance();
            } else break;
        }

        var name: []const u8 = "";
        var name_location: SourceLocation = .{};
        if (!options.allow_empty_name or self.currentToken() == .Identifier) {
            factory.markEndPosition();
            const named = try self.expectIdentifierWithLocation();
            name = named.name;
            name_location = named.location;
        }
        var value: ?*AST.Node = null;
        if (options.allow_initial_value and self.currentToken() == .Assign) {
            _ = try self.advance();
            value = try self.parseExpression(null);
            factory.setEndPositionFromNode(value.?);
        }
        return factory.create(.{ .variable_declaration = .{
            .declaration = .{
                .name = name,
                .name_location = name_location,
                .visibility = visibility,
            },
            .documentation = documentation,
            .type_name = type_name,
            .value = value,
            .indexed = indexed,
            .mutability = mutability,
            .overrides = overrides,
            .reference_location = reference_location,
        } });
    }

    fn parseStructDefinition(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        try self.expect(.Struct);
        const named = try self.expectIdentifierWithLocation();
        try self.expect(.LBrace);
        var members: std.ArrayList(*AST.Node) = .empty;
        defer members.deinit(self.allocator);
        while (self.currentToken() != .RBrace) {
            try members.append(self.allocator, try self.parseVariableDeclaration(.{}, null));
            try self.expect(.Semicolon);
        }
        factory.markEndPosition();
        try self.expect(.RBrace);
        return factory.create(.{ .struct_definition = .{
            .declaration = .{ .name = named.name, .name_location = named.location },
            .documentation = documentation,
            .members = try self.tree.ownSlice(*AST.Node, members.items),
        } });
    }

    fn parseEnumDefinition(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        try self.expect(.Enum);
        const named = try self.expectIdentifierWithLocation();
        try self.expect(.LBrace);
        var members: std.ArrayList(*AST.Node) = .empty;
        defer members.deinit(self.allocator);
        while (self.currentToken() != .RBrace) {
            try members.append(self.allocator, try self.parseEnumValue());
            if (self.currentToken() == .RBrace) break;
            try self.expect(.Comma);
            if (self.currentToken() != .Identifier)
                try self.fatal(1612, "Expected identifier after ','");
        }
        if (members.items.len == 0) try self.parserError(3147, "Enum with no members is not allowed.");
        factory.markEndPosition();
        try self.expect(.RBrace);
        return factory.create(.{ .enum_definition = .{
            .declaration = .{ .name = named.name, .name_location = named.location },
            .documentation = documentation,
            .members = try self.tree.ownSlice(*AST.Node, members.items),
        } });
    }

    fn parseEnumValue(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        factory.markEndPosition();
        const name = try self.expectIdentifier();
        return factory.create(.{ .enum_value = .{
            .declaration = .{
                .name = name,
                .name_location = factory.location,
            },
            .documentation = documentation,
        } });
    }

    fn parseUserDefinedValueTypeDefinition(self: *Parser) ParseError!*AST.Node {
        var factory = NodeFactory.init(self);
        try self.expect(.Type);
        const named = try self.expectIdentifierWithLocation();
        try self.expect(.Is);
        const type_name = try self.parseTypeName();
        factory.markEndPosition();
        try self.expect(.Semicolon);
        return factory.create(.{ .user_defined_value_type_definition = .{
            .declaration = .{ .name = named.name, .name_location = named.location },
            .underlying_type = type_name,
        } });
    }

    fn parseModifierDefinition(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        try self.expect(.Modifier);
        const named = try self.expectIdentifierWithLocation();
        const parameters = if (self.currentToken() == .LParen)
            try self.parseParameterList(.{ .allow_location_specifier = true }, true)
        else
            try self.createEmptyParameterList();
        var overrides: ?*AST.Node = null;
        var is_virtual = false;
        while (true) {
            if (self.currentToken() == .Override) {
                if (overrides != null) try self.parserError(9102, "Override already specified.");
                overrides = try self.parseOverrideSpecifier();
            } else if (self.currentToken() == .Virtual) {
                if (is_virtual) try self.parserError(2662, "Virtual already specified.");
                is_virtual = true;
                _ = try self.advance();
            } else break;
        }
        var body: ?*AST.Node = null;
        factory.markEndPosition();
        if (self.currentToken() == .Semicolon) {
            _ = try self.advance();
        } else {
            const previous = self.inside_modifier;
            self.inside_modifier = true;
            defer self.inside_modifier = previous;
            body = try self.parseBlock(false, null);
            factory.setEndPositionFromNode(body.?);
        }
        return factory.create(.{ .modifier_definition = .{
            .callable = .{
                .declaration = .{
                    .name = named.name,
                    .name_location = named.location,
                    .visibility = .Internal,
                },
                .parameters = parameters,
                .overrides = overrides,
                .marked_virtual = is_virtual,
            },
            .documentation = documentation,
            .body = body,
        } });
    }

    fn parseEventDefinition(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        try self.expect(.Event);
        const named = try self.expectIdentifierWithLocation();
        const parameters = try self.parseParameterList(.{ .allow_indexed = true }, true);
        var anonymous = false;
        if (self.currentToken() == .Anonymous) {
            anonymous = true;
            _ = try self.advance();
        }
        factory.markEndPosition();
        try self.expect(.Semicolon);
        return factory.create(.{ .event_definition = .{
            .callable = .{
                .declaration = .{ .name = named.name, .name_location = named.location },
                .parameters = parameters,
            },
            .documentation = documentation,
            .anonymous = anonymous,
        } });
    }

    fn parseErrorDefinition(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const documentation = try self.parseStructuredDocumentation();
        const error_keyword = try self.expectIdentifier();
        if (!std.mem.eql(u8, error_keyword, "error")) return error.InvalidParserState;
        const named = try self.expectIdentifierWithLocation();
        const parameters = try self.parseParameterList(.{}, true);
        factory.markEndPosition();
        try self.expect(.Semicolon);
        return factory.create(.{ .error_definition = .{
            .callable = .{
                .declaration = .{ .name = named.name, .name_location = named.location },
                .parameters = parameters,
            },
            .documentation = documentation,
        } });
    }

    fn statementDocumentation(self: *Parser) ParseError!?[]const u8 {
        const value = self.base.scanner.currentCommentLiteral();
        return if (value.len == 0) null else try self.tree.ownString(value);
    }

    fn parseBlock(
        self: *Parser,
        allow_unchecked: bool,
        documentation: ?[]const u8,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const unchecked = self.currentToken() == .Unchecked;
        if (unchecked) {
            if (!allow_unchecked)
                try self.parserError(5296, "\"unchecked\" blocks can only be used inside regular blocks.");
            _ = try self.advance();
        }
        try self.expect(.LBrace);
        var statements: std.ArrayList(*AST.Node) = .empty;
        defer statements.deinit(self.allocator);
        while (self.currentToken() != .RBrace) {
            if (self.currentToken() == .EOS)
                try self.fatal(2314, "Expected '}' but got end of source");
            try statements.append(self.allocator, try self.parseStatement(true));
        }
        factory.markEndPosition();
        try self.expect(.RBrace);
        return factory.create(.{ .block = .{
            .statement = .{ .documentation = documentation },
            .statements = try self.tree.ownSlice(*AST.Node, statements.items),
            .unchecked = unchecked,
        } });
    }

    fn parseStatement(self: *Parser, allow_unchecked: bool) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        const documentation = try self.statementDocumentation();
        switch (self.currentToken()) {
            .If => return self.parseIfStatement(documentation),
            .While => return self.parseWhileStatement(documentation),
            .Do => return self.parseDoWhileStatement(documentation),
            .For => return self.parseForStatement(documentation),
            .Unchecked, .LBrace => return self.parseBlock(allow_unchecked, documentation),
            .Try => return self.parseTryStatement(documentation),
            .Assembly => return self.parseInlineAssembly(documentation),
            else => {},
        }

        var statement: *AST.Node = undefined;
        switch (self.currentToken()) {
            .Continue => {
                var factory = NodeFactory.init(self);
                statement = try factory.create(.{ .continue_statement = .{
                    .statement = .{ .documentation = documentation },
                } });
                _ = try self.advance();
            },
            .Break => {
                var factory = NodeFactory.init(self);
                statement = try factory.create(.{ .break_statement = .{
                    .statement = .{ .documentation = documentation },
                } });
                _ = try self.advance();
            },
            .Return => {
                var factory = NodeFactory.init(self);
                _ = try self.advance();
                const expression = if (self.currentToken() != .Semicolon)
                    try self.parseExpression(null)
                else
                    null;
                if (expression) |child| factory.setEndPositionFromNode(child);
                statement = try factory.create(.{ .return_statement = .{
                    .statement = .{ .documentation = documentation },
                    .expression = expression,
                } });
            },
            .Throw => {
                var factory = NodeFactory.init(self);
                statement = try factory.create(.{ .throw_statement = .{
                    .statement = .{ .documentation = documentation },
                } });
                _ = try self.advance();
            },
            .Emit => statement = try self.parseEmitStatement(documentation),
            .Identifier => {
                if (std.mem.eql(u8, self.currentLiteral(), "revert") and
                    self.base.scanner.peekNextToken() == .Identifier)
                {
                    statement = try self.parseRevertStatement(documentation);
                } else if (self.inside_modifier and std.mem.eql(u8, self.currentLiteral(), "_")) {
                    var factory = NodeFactory.init(self);
                    statement = try factory.create(.{ .placeholder_statement = .{
                        .statement = .{ .documentation = documentation },
                    } });
                    _ = try self.advance();
                } else statement = try self.parseSimpleStatement(documentation);
            },
            else => statement = try self.parseSimpleStatement(documentation),
        }
        try self.expect(.Semicolon);
        return statement;
    }

    fn parseInlineAssembly(
        self: *Parser,
        documentation: ?[]const u8,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var location = self.currentLocation();
        try self.expect(.Assembly);
        const dialect = EVMDialect.strictAssemblyForEVM(self.evm_version) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.InvalidParserState,
        };
        if (self.currentToken() == .StringLiteral) {
            if (!std.mem.eql(u8, self.currentLiteral(), "evmasm"))
                try self.fatal(4531, "Only \"evmasm\" supported.");
            _ = try self.advance();
        }

        var flags_storage: std.ArrayList(?[]const u8) = .empty;
        defer flags_storage.deinit(self.allocator);
        var flags_present = false;
        if (self.currentToken() == .LParen) {
            flags_present = true;
            while (true) {
                _ = try self.advance();
                if (self.currentToken() != .StringLiteral)
                    try self.fatal(2314, "Expected string literal for inline assembly flag.");
                try flags_storage.append(self.allocator, try self.tree.ownString(self.currentLiteral()));
                _ = try self.advance();
                if (self.currentToken() != .Comma) break;
            }
            try self.expect(.RParen);
        }

        var yul_parser = YulParser.Parser.init(
            self.allocator,
            self.base.scanner,
            self.base.error_reporter,
            dialect.dialect(),
            .{},
        );
        const block = (try yul_parser.parseInline()) orelse return error.FatalDiagnostic;
        var yul_ast = YulAST.AST.init(self.allocator, dialect.dialect(), block);
        errdefer yul_ast.deinit();
        const operations = try self.tree.adoptYulAst(&yul_ast);
        if (operations.root().debug_data) |debug_data| location.end = debug_data.native_location.end;

        var factory = NodeFactory.init(self);
        factory.setLocation(location);
        return factory.create(.{ .inline_assembly = .{
            .statement = .{ .documentation = documentation },
            .dialect = dialect.dialect(),
            .flags = if (flags_present)
                try self.tree.ownSlice(?[]const u8, flags_storage.items)
            else
                null,
            .operations = operations,
        } });
    }

    fn parseIfStatement(self: *Parser, documentation: ?[]const u8) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.If);
        try self.expect(.LParen);
        const condition = try self.parseExpression(null);
        try self.expect(.RParen);
        const true_body = try self.parseStatement(false);
        var false_body: ?*AST.Node = null;
        if (self.currentToken() == .Else) {
            _ = try self.advance();
            false_body = try self.parseStatement(false);
            factory.setEndPositionFromNode(false_body.?);
        } else factory.setEndPositionFromNode(true_body);
        return factory.create(.{ .if_statement = .{
            .statement = .{ .documentation = documentation },
            .condition = condition,
            .true_body = true_body,
            .false_body = false_body,
        } });
    }

    fn parseWhileStatement(self: *Parser, documentation: ?[]const u8) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.While);
        try self.expect(.LParen);
        const condition = try self.parseExpression(null);
        try self.expect(.RParen);
        const body = try self.parseStatement(false);
        factory.setEndPositionFromNode(body);
        return factory.create(.{ .while_statement = .{
            .statement = .{ .documentation = documentation },
            .condition = condition,
            .body = body,
        } });
    }

    fn parseDoWhileStatement(self: *Parser, documentation: ?[]const u8) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.Do);
        const body = try self.parseStatement(false);
        try self.expect(.While);
        try self.expect(.LParen);
        const condition = try self.parseExpression(null);
        try self.expect(.RParen);
        factory.markEndPosition();
        try self.expect(.Semicolon);
        return factory.create(.{ .while_statement = .{
            .statement = .{ .documentation = documentation },
            .condition = condition,
            .body = body,
            .is_do_while = true,
        } });
    }

    fn parseForStatement(self: *Parser, documentation: ?[]const u8) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.For);
        try self.expect(.LParen);
        const initialization = if (self.currentToken() != .Semicolon)
            try self.parseSimpleStatement(null)
        else
            null;
        try self.expect(.Semicolon);
        const condition = if (self.currentToken() != .Semicolon)
            try self.parseExpression(null)
        else
            null;
        try self.expect(.Semicolon);
        const loop_expression = if (self.currentToken() != .RParen)
            try self.parseExpressionStatement(null, null)
        else
            null;
        try self.expect(.RParen);
        const body = try self.parseStatement(false);
        factory.setEndPositionFromNode(body);
        return factory.create(.{ .for_statement = .{
            .statement = .{ .documentation = documentation },
            .initialization_expression = initialization,
            .condition = condition,
            .loop_expression = loop_expression,
            .body = body,
        } });
    }

    fn parseTryStatement(self: *Parser, documentation: ?[]const u8) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.Try);
        const external_call = try self.parseExpression(null);
        var clauses: std.ArrayList(*AST.Node) = .empty;
        defer clauses.deinit(self.allocator);
        var success_factory = NodeFactory.init(self);
        var return_parameters: ?*AST.Node = null;
        if (self.currentToken() == .Returns) {
            _ = try self.advance();
            return_parameters = try self.parseParameterList(.{
                .allow_empty_name = true,
                .allow_location_specifier = true,
            }, false);
        }
        const success_block = try self.parseBlock(false, null);
        success_factory.setEndPositionFromNode(success_block);
        try clauses.append(self.allocator, try success_factory.create(.{ .try_catch_clause = .{
            .parameters = return_parameters,
            .block = success_block,
        } }));
        try clauses.append(self.allocator, try self.parseCatchClause());
        while (self.currentToken() == .Catch)
            try clauses.append(self.allocator, try self.parseCatchClause());
        factory.setEndPositionFromNode(clauses.items[clauses.items.len - 1]);
        return factory.create(.{ .try_statement = .{
            .statement = .{ .documentation = documentation },
            .external_call = external_call,
            .clauses = try self.tree.ownSlice(*AST.Node, clauses.items),
        } });
    }

    fn parseCatchClause(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        try self.expect(.Catch);
        var error_name: []const u8 = "";
        var parameters: ?*AST.Node = null;
        if (self.currentToken() != .LBrace) {
            if (self.currentToken() == .Identifier) error_name = try self.expectIdentifier();
            parameters = try self.parseParameterList(.{
                .allow_empty_name = true,
                .allow_location_specifier = true,
            }, error_name.len != 0);
        }
        const block = try self.parseBlock(false, null);
        factory.setEndPositionFromNode(block);
        return factory.create(.{ .try_catch_clause = .{
            .error_name = error_name,
            .parameters = parameters,
            .block = block,
        } });
    }

    fn parseEmitStatement(self: *Parser, documentation: ?[]const u8) ParseError!*AST.Node {
        try self.expectWithoutAdvance(.Emit);
        var factory = NodeFactory.init(self);
        _ = try self.advance();
        var call_factory = NodeFactory.init(self);
        if (self.currentToken() != .Identifier)
            try self.fatal(5620, "Expected event name or path.");

        var path: IndexAccessedPath = .{};
        defer path.deinit(self.allocator);
        while (true) {
            try path.path.append(self.allocator, try self.parseIdentifier());
            if (self.currentToken() != .Period) break;
            _ = try self.advance();
        }
        const event_name = try self.expressionFromIndexAccessStructure(&path);
        try self.expect(.LParen);
        const arguments = try self.parseFunctionCallArguments();
        call_factory.markEndPosition();
        factory.markEndPosition();
        try self.expect(.RParen);
        const call = try call_factory.create(.{ .function_call = .{
            .expression = event_name,
            .arguments = arguments.arguments,
            .names = arguments.parameter_names,
            .name_locations = arguments.parameter_name_locations,
        } });
        return factory.create(.{ .emit_statement = .{
            .statement = .{ .documentation = documentation },
            .event_call = call,
        } });
    }

    fn parseRevertStatement(self: *Parser, documentation: ?[]const u8) ParseError!*AST.Node {
        var factory = NodeFactory.init(self);
        const revert_name = try self.expectIdentifier();
        if (!std.mem.eql(u8, revert_name, "revert")) return error.InvalidParserState;
        var call_factory = NodeFactory.init(self);
        if (self.currentToken() != .Identifier) return error.InvalidParserState;

        var path: IndexAccessedPath = .{};
        defer path.deinit(self.allocator);
        while (true) {
            try path.path.append(self.allocator, try self.parseIdentifier());
            if (self.currentToken() != .Period) break;
            _ = try self.advance();
        }
        const error_name = try self.expressionFromIndexAccessStructure(&path);
        try self.expect(.LParen);
        const arguments = try self.parseFunctionCallArguments();
        call_factory.markEndPosition();
        factory.markEndPosition();
        try self.expect(.RParen);
        const call = try call_factory.create(.{ .function_call = .{
            .expression = error_name,
            .arguments = arguments.arguments,
            .names = arguments.parameter_names,
            .name_locations = arguments.parameter_name_locations,
        } });
        return factory.create(.{ .revert_statement = .{
            .statement = .{ .documentation = documentation },
            .error_call = call,
        } });
    }

    fn peekStatementType(self: *const Parser) LookAheadInfo {
        const token = self.currentToken();
        if (token == .Mapping or token == .Function) return .variable_declaration;
        if (TokenModule.isElementaryTypeName(token) or token == .Identifier) {
            const next = self.base.scanner.peekNextToken();
            if (TokenModule.isElementaryTypeName(token) and
                TokenModule.isStateMutabilitySpecifier(next))
                return .variable_declaration;
            if (next == .Identifier or TokenModule.isLocationSpecifier(next))
                return .variable_declaration;
            if (next == .LBrack or next == .Period) return .index_access_structure;
        }
        return .expression;
    }

    fn tryParseIndexAccessedPath(self: *Parser) ParseError!ParsedStatementPrefix {
        const initial = self.peekStatementType();
        if (initial != .index_access_structure) return .{ .kind = initial };
        var path = try self.parseIndexAccessedPath();
        errdefer path.deinit(self.allocator);
        const kind: LookAheadInfo = if (self.currentToken() == .Identifier or
            TokenModule.isLocationSpecifier(self.currentToken()))
            .variable_declaration
        else
            .expression;
        return .{ .kind = kind, .path = path };
    }

    fn parseIndexAccessedPath(self: *Parser) ParseError!IndexAccessedPath {
        var result: IndexAccessedPath = .{};
        errdefer result.deinit(self.allocator);

        if (self.currentToken() == .Identifier) {
            try result.path.append(self.allocator, try self.parseIdentifier());
            while (self.currentToken() == .Period) {
                _ = try self.advance();
                try result.path.append(self.allocator, try self.parseIdentifierOrAddressNode());
            }
        } else {
            const info = self.base.scanner.currentTokenInfo();
            const elementary = try TokenModule.ElementaryTypeNameToken.init(
                self.currentToken(),
                info.first,
                info.second,
            );
            var type_factory = NodeFactory.init(self);
            const type_name = try type_factory.create(.{ .elementary_type_name = .{
                .type_name = elementary,
            } });
            var expression_factory = NodeFactory.init(self);
            const expression = try expression_factory.create(.{ .elementary_type_name_expression = .{
                .type_name = type_name,
            } });
            try result.path.append(self.allocator, expression);
            _ = try self.advance();
        }

        while (self.currentToken() == .LBrack) {
            try self.expect(.LBrack);
            const start = if (self.currentToken() != .RBrack and self.currentToken() != .Colon)
                try self.parseExpression(null)
            else
                null;
            var index_location = result.path.items[0].location;
            if (self.currentToken() == .Colon) {
                try self.expect(.Colon);
                const end = if (self.currentToken() != .RBrack)
                    try self.parseExpression(null)
                else
                    null;
                index_location.end = self.currentLocation().end;
                try result.indices.append(self.allocator, .{
                    .start = start,
                    .end = end,
                    .is_range = true,
                    .location = index_location,
                });
            } else {
                index_location.end = self.currentLocation().end;
                try result.indices.append(self.allocator, .{
                    .start = start,
                    .location = index_location,
                });
            }
            try self.expect(.RBrack);
        }
        return result;
    }

    fn parseIdentifierOrAddressNode(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        if (self.currentToken() != .Address) return self.parseIdentifier();
        var factory = NodeFactory.init(self);
        factory.markEndPosition();
        _ = try self.advance();
        return factory.create(.{ .identifier = .{ .name = "address" } });
    }

    fn typeNameFromIndexAccessStructure(
        self: *Parser,
        path: *const IndexAccessedPath,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        if (path.empty()) return error.InvalidParserState;
        var location = path.path.items[0].location;
        location.end = path.path.items[path.path.items.len - 1].location.end;
        var factory = NodeFactory.init(self);
        factory.setLocation(location);

        var type_name: *AST.Node = switch (path.path.items[0].payload) {
            .elementary_type_name_expression => |value| blk: {
                if (path.path.items.len != 1) return error.InvalidParserState;
                const elementary = value.type_name.payload.elementary_type_name;
                break :blk try factory.create(.{ .elementary_type_name = elementary });
            },
            .identifier => blk: {
                var names: std.ArrayList([]const u8) = .empty;
                defer names.deinit(self.allocator);
                var locations: std.ArrayList(SourceLocation) = .empty;
                defer locations.deinit(self.allocator);
                for (path.path.items) |element| {
                    const identifier = switch (element.payload) {
                        .identifier => |value| value,
                        else => return error.InvalidParserState,
                    };
                    try names.append(self.allocator, identifier.name);
                    try locations.append(self.allocator, element.location);
                }
                const identifier_path = try factory.create(.{ .identifier_path = .{
                    .path = try self.tree.ownSlice([]const u8, names.items),
                    .path_locations = try self.tree.ownSlice(SourceLocation, locations.items),
                } });
                break :blk try factory.create(.{ .user_defined_type_name = .{
                    .path_node = identifier_path,
                } });
            },
            else => return error.InvalidParserState,
        };

        for (path.indices.items) |index| {
            if (index.is_range) {
                try self.base.error_reporter.parserError(
                    .{ .value = 5464 },
                    index.location,
                    "Expected array length expression.",
                );
            }
            factory.setLocation(index.location);
            type_name = try factory.create(.{ .array_type_name = .{
                .base_type = type_name,
                .length = index.start,
            } });
        }
        return type_name;
    }

    fn expressionFromIndexAccessStructure(
        self: *Parser,
        path: *const IndexAccessedPath,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        if (path.empty()) return error.InvalidParserState;
        var expression = path.path.items[0];
        var factory = NodeFactory.fromNode(self, expression);
        for (path.path.items[1..]) |element| {
            const identifier = switch (element.payload) {
                .identifier => |value| value,
                else => return error.InvalidParserState,
            };
            var location = path.path.items[0].location;
            location.end = element.location.end;
            factory.setLocation(location);
            expression = try factory.create(.{ .member_access = .{
                .expression = expression,
                .member_name = identifier.name,
                .member_location = element.location,
            } });
        }
        for (path.indices.items) |index| {
            factory.setLocation(index.location);
            expression = if (index.is_range)
                try factory.create(.{ .index_range_access = .{
                    .base = expression,
                    .start = index.start,
                    .end = index.end,
                } })
            else
                try factory.create(.{ .index_access = .{
                    .base = expression,
                    .index = index.start,
                } });
        }
        return expression;
    }

    fn parseSimpleStatement(self: *Parser, documentation: ?[]const u8) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        if (self.currentToken() == .LParen)
            return self.parseTupleDeclarationOrExpressionStatement(documentation);

        var prefix = try self.tryParseIndexAccessedPath();
        defer prefix.path.deinit(self.allocator);
        return switch (prefix.kind) {
            .variable_declaration => self.parseVariableDeclarationStatement(
                documentation,
                if (prefix.path.empty()) null else try self.typeNameFromIndexAccessStructure(&prefix.path),
            ),
            .expression => self.parseExpressionStatement(
                documentation,
                if (prefix.path.empty()) null else try self.expressionFromIndexAccessStructure(&prefix.path),
            ),
            .index_access_structure => error.InvalidParserState,
        };
    }

    fn parseVariableDeclarationStatement(
        self: *Parser,
        documentation: ?[]const u8,
        lookahead_type: ?*AST.Node,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = if (lookahead_type) |type_name|
            NodeFactory.fromNode(self, type_name)
        else
            NodeFactory.init(self);
        const variable = try self.parseVariableDeclaration(.{
            .allow_location_specifier = true,
        }, lookahead_type);
        var initial_value: ?*AST.Node = null;
        if (self.currentToken() == .Assign) {
            _ = try self.advance();
            initial_value = try self.parseExpression(null);
            factory.setEndPositionFromNode(initial_value.?);
        } else factory.setEndPositionFromNode(variable);
        return factory.create(.{ .variable_declaration_statement = .{
            .statement = .{ .documentation = documentation },
            .declarations = try self.tree.ownSlice(?*AST.Node, &.{variable}),
            .initial_value = initial_value,
        } });
    }

    fn parseTupleDeclarationOrExpressionStatement(
        self: *Parser,
        documentation: ?[]const u8,
    ) ParseError!*AST.Node {
        var factory = NodeFactory.init(self);
        try self.expect(.LParen);
        var empty_components: usize = 0;
        while (self.currentToken() == .Comma) {
            _ = try self.advance();
            empty_components += 1;
        }

        var prefix = try self.tryParseIndexAccessedPath();
        defer prefix.path.deinit(self.allocator);
        switch (prefix.kind) {
            .variable_declaration => {
                var variables: std.ArrayList(?*AST.Node) = .empty;
                defer variables.deinit(self.allocator);
                for (0..empty_components) |_| try variables.append(self.allocator, null);
                const first_type = if (prefix.path.empty())
                    null
                else
                    try self.typeNameFromIndexAccessStructure(&prefix.path);
                try variables.append(self.allocator, try self.parseVariableDeclaration(.{
                    .allow_location_specifier = true,
                }, first_type));
                while (self.currentToken() != .RParen) {
                    try self.expect(.Comma);
                    if (self.currentToken() == .Comma or self.currentToken() == .RParen) {
                        try variables.append(self.allocator, null);
                    } else {
                        try variables.append(self.allocator, try self.parseVariableDeclaration(.{
                            .allow_location_specifier = true,
                        }, null));
                    }
                }
                try self.expect(.RParen);
                try self.expect(.Assign);
                const value = try self.parseExpression(null);
                factory.setEndPositionFromNode(value);
                return factory.create(.{ .variable_declaration_statement = .{
                    .statement = .{ .documentation = documentation },
                    .declarations = try self.tree.ownSlice(?*AST.Node, variables.items),
                    .initial_value = value,
                } });
            },
            .expression => {
                var components: std.ArrayList(?*AST.Node) = .empty;
                defer components.deinit(self.allocator);
                for (0..empty_components) |_| try components.append(self.allocator, null);
                const partial = if (prefix.path.empty())
                    null
                else
                    try self.expressionFromIndexAccessStructure(&prefix.path);
                try components.append(self.allocator, try self.parseExpression(partial));
                while (self.currentToken() != .RParen) {
                    try self.expect(.Comma);
                    if (self.currentToken() == .Comma or self.currentToken() == .RParen) {
                        try components.append(self.allocator, null);
                    } else {
                        try components.append(self.allocator, try self.parseExpression(null));
                    }
                }
                factory.markEndPosition();
                try self.expect(.RParen);
                const tuple = try factory.create(.{ .tuple_expression = .{
                    .components = try self.tree.ownSlice(?*AST.Node, components.items),
                } });
                return self.parseExpressionStatement(documentation, tuple);
            },
            .index_access_structure => return error.InvalidParserState,
        }
    }

    fn parseExpressionStatement(
        self: *Parser,
        documentation: ?[]const u8,
        partial: ?*AST.Node,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        const expression = try self.parseExpression(partial);
        var factory = NodeFactory.fromNode(self, expression);
        return factory.create(.{ .expression_statement = .{
            .statement = .{ .documentation = documentation },
            .expression = expression,
        } });
    }

    fn parseExpression(self: *Parser, partial: ?*AST.Node) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var expression = try self.parseBinaryExpression(4, partial);
        if (TokenModule.isAssignmentOp(self.currentToken())) {
            const operator = self.currentToken();
            _ = try self.advance();
            const right = try self.parseExpression(null);
            var factory = NodeFactory.fromNode(self, expression);
            factory.setEndPositionFromNode(right);
            expression = try factory.create(.{ .assignment = .{
                .left_hand_side = expression,
                .operator = operator,
                .right_hand_side = right,
            } });
        } else if (self.currentToken() == .Conditional) {
            _ = try self.advance();
            const true_expression = try self.parseExpression(null);
            try self.expect(.Colon);
            const false_expression = try self.parseExpression(null);
            var factory = NodeFactory.fromNode(self, expression);
            factory.setEndPositionFromNode(false_expression);
            expression = try factory.create(.{ .conditional = .{
                .condition = expression,
                .true_expression = true_expression,
                .false_expression = false_expression,
            } });
        }
        return expression;
    }

    fn parseBinaryExpression(
        self: *Parser,
        minimum_precedence: i8,
        partial: ?*AST.Node,
    ) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var expression = try self.parseUnaryExpression(partial);
        var factory = NodeFactory.fromNode(self, expression);
        var precedence = TokenModule.precedence(self.currentToken());
        while (precedence >= minimum_precedence) : (precedence -= 1) {
            while (TokenModule.precedence(self.currentToken()) == precedence) {
                const operator = self.currentToken();
                _ = try self.advance();
                const right = if (operator == .Exp)
                    try self.parseBinaryExpression(precedence, null)
                else
                    try self.parseBinaryExpression(precedence + 1, null);
                factory.setEndPositionFromNode(right);
                expression = try factory.create(.{ .binary_operation = .{
                    .left = expression,
                    .operator = operator,
                    .right = right,
                } });
            }
        }
        return expression;
    }

    fn parseUnaryExpression(self: *Parser, partial: ?*AST.Node) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = if (partial) |child|
            NodeFactory.fromNode(self, child)
        else
            NodeFactory.init(self);
        const token = self.currentToken();
        if (partial == null and token == .Add)
            try self.fatal(9636, "Use of unary + is disallowed.");
        if (partial == null and (TokenModule.isUnaryOp(token) or TokenModule.isCountOp(token))) {
            _ = try self.advance();
            const child = try self.parseUnaryExpression(null);
            factory.setEndPositionFromNode(child);
            return factory.create(.{ .unary_operation = .{
                .operator = token,
                .sub_expression = child,
                .is_prefix = true,
            } });
        }
        const child = try self.parseLeftHandSideExpression(partial);
        if (!TokenModule.isCountOp(self.currentToken())) return child;
        const operator = self.currentToken();
        factory.markEndPosition();
        _ = try self.advance();
        return factory.create(.{ .unary_operation = .{
            .operator = operator,
            .sub_expression = child,
            .is_prefix = false,
        } });
    }

    fn parseLeftHandSideExpression(self: *Parser, partial: ?*AST.Node) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = if (partial) |child|
            NodeFactory.fromNode(self, child)
        else
            NodeFactory.init(self);
        var expression: *AST.Node = if (partial) |child| child else blk: {
            if (self.currentToken() == .New) {
                try self.expect(.New);
                const type_name = try self.parseTypeName();
                factory.setEndPositionFromNode(type_name);
                break :blk try factory.create(.{ .new_expression = .{ .type_name = type_name } });
            }
            if (self.currentToken() == .Payable) {
                try self.expect(.Payable);
                factory.markEndPosition();
                const elementary = try TokenModule.ElementaryTypeNameToken.init(.Address, 0, 0);
                const type_name = try factory.create(.{ .elementary_type_name = .{
                    .type_name = elementary,
                    .state_mutability = .Payable,
                } });
                try self.expectWithoutAdvance(.LParen);
                break :blk try factory.create(.{ .elementary_type_name_expression = .{
                    .type_name = type_name,
                } });
            }
            break :blk try self.parsePrimaryExpression();
        };

        while (true) switch (self.currentToken()) {
            .LBrack => {
                _ = try self.advance();
                const start = if (self.currentToken() != .RBrack and self.currentToken() != .Colon)
                    try self.parseExpression(null)
                else
                    null;
                if (self.currentToken() == .Colon) {
                    _ = try self.advance();
                    const end = if (self.currentToken() != .RBrack)
                        try self.parseExpression(null)
                    else
                        null;
                    factory.markEndPosition();
                    try self.expect(.RBrack);
                    expression = try factory.create(.{ .index_range_access = .{
                        .base = expression,
                        .start = start,
                        .end = end,
                    } });
                } else {
                    factory.markEndPosition();
                    try self.expect(.RBrack);
                    expression = try factory.create(.{ .index_access = .{
                        .base = expression,
                        .index = start,
                    } });
                }
            },
            .Period => {
                _ = try self.advance();
                factory.markEndPosition();
                const member_location = self.currentLocation();
                const member_name = try self.expectIdentifierOrAddress();
                expression = try factory.create(.{ .member_access = .{
                    .expression = expression,
                    .member_name = member_name,
                    .member_location = member_location,
                } });
            },
            .LParen => {
                _ = try self.advance();
                const arguments = try self.parseFunctionCallArguments();
                factory.markEndPosition();
                try self.expect(.RParen);
                expression = try factory.create(.{ .function_call = .{
                    .expression = expression,
                    .arguments = arguments.arguments,
                    .names = arguments.parameter_names,
                    .name_locations = arguments.parameter_name_locations,
                } });
            },
            .LBrace => {
                if (self.base.scanner.peekNextToken() != .Identifier or
                    self.base.scanner.peekNextNextToken() != .Colon)
                {
                    return expression;
                }
                _ = try self.advance();
                const options = try self.parseNamedArguments();
                factory.markEndPosition();
                try self.expect(.RBrace);
                expression = try factory.create(.{ .function_call_options = .{
                    .expression = expression,
                    .options = options.arguments,
                    .names = options.parameter_names,
                } });
            },
            else => return expression,
        };
    }

    fn parseLiteral(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        const initial_token = self.currentToken();
        var bytes: std.ArrayList(u8) = .empty;
        defer bytes.deinit(self.allocator);
        try bytes.appendSlice(self.allocator, self.currentLiteral());
        switch (initial_token) {
            .TrueLiteral, .FalseLiteral, .Number => {
                factory.markEndPosition();
                _ = try self.advance();
            },
            .StringLiteral, .UnicodeStringLiteral, .HexStringLiteral => {
                while (self.base.scanner.peekNextToken() == initial_token) {
                    _ = try self.advance();
                    try bytes.appendSlice(self.allocator, self.currentLiteral());
                }
                factory.markEndPosition();
                _ = try self.advance();
                if (self.currentToken() == .Illegal)
                    try self.fatal(5428, ScannerModule.errorMessage(self.base.scanner.currentError()));
            },
            else => return error.InvalidParserState,
        }
        var denomination: AST.LiteralSubDenomination = .None;
        if (initial_token == .Number and
            (TokenModule.isEtherSubdenomination(self.currentToken()) or
                TokenModule.isTimeSubdenomination(self.currentToken())))
        {
            factory.markEndPosition();
            denomination = @enumFromInt(@intFromEnum(self.currentToken()));
            _ = try self.advance();
        }
        return factory.create(.{ .literal = .{
            .token = initial_token,
            .value = try self.tree.ownString(bytes.items),
            .sub_denomination = denomination,
        } });
    }

    fn parsePrimaryExpression(self: *Parser) ParseError!*AST.Node {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var factory = NodeFactory.init(self);
        return switch (self.currentToken()) {
            .TrueLiteral,
            .FalseLiteral,
            .Number,
            .StringLiteral,
            .UnicodeStringLiteral,
            .HexStringLiteral,
            => self.parseLiteral(),
            .Identifier => blk: {
                factory.markEndPosition();
                break :blk factory.create(.{ .identifier = .{ .name = try self.expectIdentifier() } });
            },
            .Type => blk: {
                factory.markEndPosition();
                _ = try self.advance();
                break :blk factory.create(.{ .identifier = .{ .name = try self.tree.ownString("type") } });
            },
            .LParen, .LBrack => blk: {
                const opening = self.currentToken();
                const closing: Token = if (opening == .LParen) .RParen else .RBrack;
                const is_array = opening == .LBrack;
                _ = try self.advance();
                var components: std.ArrayList(?*AST.Node) = .empty;
                defer components.deinit(self.allocator);
                if (self.currentToken() != closing) while (true) {
                    if (self.currentToken() != .Comma and self.currentToken() != closing) {
                        try components.append(self.allocator, try self.parseExpression(null));
                    } else if (is_array) {
                        try self.parserError(4799, "Expected expression (inline array elements cannot be omitted).");
                    } else try components.append(self.allocator, null);
                    if (self.currentToken() == closing) break;
                    try self.expect(.Comma);
                };
                factory.markEndPosition();
                try self.expect(closing);
                break :blk factory.create(.{ .tuple_expression = .{
                    .components = try self.tree.ownSlice(?*AST.Node, components.items),
                    .is_inline_array = is_array,
                } });
            },
            .Illegal => {
                try self.fatal(8936, ScannerModule.errorMessage(self.base.scanner.currentError()));
                unreachable;
            },
            else => blk: {
                if (!TokenModule.isElementaryTypeName(self.currentToken())) {
                    try self.fatal(6933, "Expected primary expression.");
                    unreachable;
                }
                const info = self.base.scanner.currentTokenInfo();
                const elementary = try TokenModule.ElementaryTypeNameToken.init(
                    self.currentToken(),
                    info.first,
                    info.second,
                );
                factory.markEndPosition();
                const type_name = try factory.create(.{ .elementary_type_name = .{
                    .type_name = elementary,
                } });
                _ = try self.advance();
                break :blk factory.create(.{ .elementary_type_name_expression = .{
                    .type_name = type_name,
                } });
            },
        };
    }

    fn parseFunctionCallListArguments(self: *Parser) ParseError!AST.NodeList {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        var arguments: std.ArrayList(*AST.Node) = .empty;
        defer arguments.deinit(self.allocator);
        if (self.currentToken() != .RParen) {
            try arguments.append(self.allocator, try self.parseExpression(null));
            while (self.currentToken() != .RParen) {
                try self.expect(.Comma);
                try arguments.append(self.allocator, try self.parseExpression(null));
            }
        }
        return self.tree.ownSlice(*AST.Node, arguments.items);
    }

    fn parseFunctionCallArguments(self: *Parser) ParseError!ParsedCallArguments {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();
        if (self.currentToken() == .LBrace) {
            _ = try self.advance();
            const result = try self.parseNamedArguments();
            try self.expect(.RBrace);
            return result;
        }
        return .{ .arguments = try self.parseFunctionCallListArguments() };
    }

    fn parseNamedArguments(self: *Parser) ParseError!ParsedCallArguments {
        var arguments: std.ArrayList(*AST.Node) = .empty;
        defer arguments.deinit(self.allocator);
        var names: std.ArrayList([]const u8) = .empty;
        defer names.deinit(self.allocator);
        var locations: std.ArrayList(SourceLocation) = .empty;
        defer locations.deinit(self.allocator);
        var first = true;
        while (self.currentToken() != .RBrace) {
            if (!first) try self.expect(.Comma);
            const named = try self.expectIdentifierWithLocation();
            try names.append(self.allocator, named.name);
            try locations.append(self.allocator, named.location);
            try self.expect(.Colon);
            try arguments.append(self.allocator, try self.parseExpression(null));
            if (self.currentToken() == .Comma and self.base.scanner.peekNextToken() == .RBrace) {
                try self.parserError(2074, "Unexpected trailing comma.");
                _ = try self.advance();
            }
            first = false;
        }
        return .{
            .arguments = try self.tree.ownSlice(*AST.Node, arguments.items),
            .parameter_names = try self.tree.ownSlice([]const u8, names.items),
            .parameter_name_locations = try self.tree.ownSlice(SourceLocation, locations.items),
        };
    }
};

fn visibilityToString(value: AST.Visibility) []const u8 {
    return switch (value) {
        .Public => "public",
        .Internal => "internal",
        .Private => "private",
        .External => "external",
        .Default => "default",
    };
}

const NodeFactory = struct {
    parser: *Parser,
    location: SourceLocation,

    fn init(parser: *Parser) NodeFactory {
        const current = parser.currentLocation();
        return .{
            .parser = parser,
            .location = .{
                .start = current.start,
                .end = -1,
                .source_name = parser.tree.source_name,
            },
        };
    }

    fn fromNode(parser: *Parser, child: *const AST.Node) NodeFactory {
        return .{ .parser = parser, .location = child.location };
    }

    fn markEndPosition(self: *NodeFactory) void {
        self.location.end = self.parser.currentLocation().end;
    }

    fn setEndPositionFromNode(self: *NodeFactory, child: *const AST.Node) void {
        self.location.end = child.location.end;
    }

    fn setLocation(self: *NodeFactory, location: SourceLocation) void {
        self.location = location;
        if (self.location.source_name != null) self.location.source_name = self.parser.tree.source_name;
    }

    fn create(self: *NodeFactory, payload: AST.Payload) ParseError!*AST.Node {
        if (self.location.end < 0) self.markEndPosition();
        return self.parser.tree.createNode(self.location, payload);
    }
};

fn collectLicenseDeclarations(
    allocator: std.mem.Allocator,
    source: []const u8,
    start: usize,
    end: usize,
    marker: []const u8,
    output: *std.ArrayList([]const u8),
) std.mem.Allocator.Error!void {
    if (start >= end) return;
    var search = start;
    while (search < end) {
        const marker_start = std.mem.findPos(u8, source[0..end], search, marker) orelse return;
        var content_start = marker_start + marker.len;
        while (content_start < end and isRegexWhitespace(source[content_start])) : (content_start += 1) {}

        var terminator = content_start;
        while (terminator < end and source[terminator] != '\n' and source[terminator] != '\r' and
            !(source[terminator] == '*' and terminator + 1 < end and source[terminator + 1] == '/'))
        {
            terminator += 1;
        }
        if (terminator == end) return;
        const license = std.mem.trim(u8, source[content_start..terminator], " \t\n\r\x0b\x0c");
        try output.append(allocator, license);
        search = if (source[terminator] == '*') terminator + 2 else terminator + 1;
    }
}

fn isRegexWhitespace(byte: u8) bool {
    return byte == ' ' or byte == '\t' or byte == '\n' or byte == '\r' or byte == 0x0b or byte == 0x0c;
}

fn allLicenseNameCharacters(value: []const u8) bool {
    for (value) |byte| {
        const valid = (byte >= 'a' and byte <= 'z') or
            (byte >= 'A' and byte <= 'Z') or
            (byte >= '0' and byte <= '9') or
            byte == ' ' or byte == '(' or byte == ')' or byte == '+' or
            byte == '.' or byte == '-';
        if (!valid) return false;
    }
    return true;
}

test "Solidity parser owns source bytes and builds the ordinary declaration tree" {
    const source_text =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { uint public x; function f(uint a) external pure returns (uint) { return a + 2 * 3; } }";
    const source = try std.testing.allocator.dupe(u8, source_text);
    defer std.testing.allocator.free(source);

    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try parseSource(
        std.testing.allocator,
        source,
        "C.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();

    @memset(source, '?');
    try std.testing.expectEqualStrings(source_text, parsed.tree.source);
    try std.testing.expectEqual(@as(usize, 0), reporter.diagnostics().len);

    const root = parsed.tree.root.?;
    try std.testing.expectEqual(AST.Kind.source_unit, root.nodeKind());
    try std.testing.expectEqual(
        @as(i64, @intCast(std.mem.find(u8, source_text, "contract").?)),
        root.location.start,
    );
    try std.testing.expectEqual(@as(i64, source_text.len), root.location.end);
    try std.testing.expectEqualStrings("C.sol", root.location.source_name.?);

    const unit = root.payload.source_unit;
    try std.testing.expectEqual(@as(usize, 1), unit.nodes.len);
    const contract_node = unit.nodes[0];
    const contract = contract_node.payload.contract_definition;
    try std.testing.expectEqualStrings("C", contract.declaration.name);
    try std.testing.expectEqual(@as(usize, 2), contract.sub_nodes.len);

    const state_variable = contract.sub_nodes[0].payload.variable_declaration;
    try std.testing.expectEqualStrings("x", state_variable.declaration.name);
    try std.testing.expectEqual(AST.Visibility.Public, state_variable.declaration.visibility);

    const function = contract.sub_nodes[1].payload.function_definition;
    try std.testing.expectEqualStrings("f", function.callable.declaration.name);
    try std.testing.expectEqual(AST.Visibility.External, function.callable.declaration.visibility);
    try std.testing.expectEqual(AST.StateMutability.Pure, function.state_mutability);
    try std.testing.expect(function.implemented());
    try std.testing.expectEqual(@as(usize, 1), function.callable.parameters.payload.parameter_list.parameters.len);
    try std.testing.expectEqual(@as(usize, 1), function.callable.return_parameters.?.payload.parameter_list.parameters.len);
}

test "Solidity parser preserves binary-expression precedence" {
    const source = "// SPDX-License-Identifier: UNLICENSED\n" ++
        "function f() pure returns (uint) { return 1 + 2 * 3 ** 4; }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try parseSource(
        std.testing.allocator,
        source,
        "precedence.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 0), reporter.diagnostics().len);
    const function = parsed.tree.root.?.payload.source_unit.nodes[0].payload.function_definition;
    const return_statement = function.body.?.payload.block.statements[0].payload.return_statement;
    const addition = return_statement.expression.?.payload.binary_operation;
    try std.testing.expectEqual(Token.Add, addition.operator);
    const multiplication = addition.right.payload.binary_operation;
    try std.testing.expectEqual(Token.Mul, multiplication.operator);
    const exponentiation = multiplication.right.payload.binary_operation;
    try std.testing.expectEqual(Token.Exp, exponentiation.operator);
    try std.testing.expectEqualStrings("3", exponentiation.left.payload.literal.value);
    try std.testing.expectEqualStrings("4", exponentiation.right.payload.literal.value);
}

test "Solidity parser keeps recoverable diagnostics ahead of the fatal diagnostic" {
    const source = "contract C { uint public private x; function f( }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try parseSource(
        std.testing.allocator,
        source,
        "broken.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();

    try std.testing.expect(parsed.tree.root == null);
    const diagnostics = reporter.diagnostics();
    try std.testing.expectEqual(@as(usize, 2), diagnostics.len);
    try std.testing.expectEqual(@as(u64, 4110), diagnostics[0].error_id.value);
    try std.testing.expectEqual(Diagnostics.ErrorType.ParserError, diagnostics[0].error_type);
    try std.testing.expectEqual(@as(u64, 3546), diagnostics[1].error_id.value);
    try std.testing.expectEqual(Diagnostics.ErrorType.ParserError, diagnostics[1].error_type);
}

test "Solidity parser enforces the upstream recursion-depth limit" {
    var source: std.ArrayList(u8) = .empty;
    defer source.deinit(std.testing.allocator);
    try source.appendSlice(
        std.testing.allocator,
        "// SPDX-License-Identifier: UNLICENSED\nfunction f() pure returns (bool) { return ",
    );
    try source.appendNTimes(std.testing.allocator, '!', 1300);
    try source.appendSlice(std.testing.allocator, "true; }");

    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try parseSource(
        std.testing.allocator,
        source.items,
        "deep.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();

    try std.testing.expect(parsed.tree.root == null);
    const diagnostics = reporter.diagnostics();
    try std.testing.expectEqual(@as(usize, 1), diagnostics.len);
    try std.testing.expectEqual(@as(u64, 7319), diagnostics[0].error_id.value);
    try std.testing.expectEqualStrings("Maximum recursion depth reached during parsing.", diagnostics[0].description);
}

test "Solidity parser keeps payable conversion parentheses in the call expression" {
    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { function f(address a) external pure returns (address payable) { return payable(a); } }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try parseSource(
        std.testing.allocator,
        source,
        "payable.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 0), reporter.diagnostics().len);
    const contract = parsed.tree.root.?.payload.source_unit.nodes[0].payload.contract_definition;
    const function = contract.sub_nodes[0].payload.function_definition;
    const return_statement = function.body.?.payload.block.statements[0].payload.return_statement;
    const call = return_statement.expression.?.payload.function_call;
    try std.testing.expectEqual(@as(usize, 1), call.arguments.len);
    const callee_type = call.expression.payload.elementary_type_name_expression.type_name.payload.elementary_type_name;
    try std.testing.expectEqual(Token.Address, callee_type.type_name.token_value);
    try std.testing.expectEqual(AST.StateMutability.Payable, callee_type.state_mutability.?);
}

test "Solidity parser disambiguates indexed types, indexed expressions, and tuples" {
    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { " ++
        "struct S { uint x; } " ++
        "function f(S[] memory a) external { " ++
        "S[] memory c = a; " ++
        "a[1].x = 2; " ++
        "(uint x,, uint y) = (1, 2, 3); " ++
        "(x, y) = (y, x); " ++
        "} }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try parseSource(
        std.testing.allocator,
        source,
        "ambiguity.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();

    try std.testing.expectEqual(@as(usize, 0), reporter.diagnostics().len);
    const contract = parsed.tree.root.?.payload.source_unit.nodes[0].payload.contract_definition;
    const function = contract.sub_nodes[1].payload.function_definition;
    const statements = function.body.?.payload.block.statements;
    try std.testing.expectEqual(@as(usize, 4), statements.len);

    const indexed_declaration = statements[0].payload.variable_declaration_statement;
    try std.testing.expectEqual(
        AST.Kind.array_type_name,
        indexed_declaration.declarations[0].?.payload.variable_declaration.type_name.?.nodeKind(),
    );

    const indexed_assignment = statements[1].payload.expression_statement.expression.payload.assignment;
    const member = indexed_assignment.left_hand_side.payload.member_access;
    try std.testing.expectEqualStrings("x", member.member_name);
    try std.testing.expectEqual(AST.Kind.index_access, member.expression.nodeKind());

    const tuple_declaration = statements[2].payload.variable_declaration_statement;
    try std.testing.expectEqual(@as(usize, 3), tuple_declaration.declarations.len);
    try std.testing.expect(tuple_declaration.declarations[1] == null);
    try std.testing.expectEqualStrings(
        "y",
        tuple_declaration.declarations[2].?.payload.variable_declaration.declaration.name,
    );

    const tuple_assignment = statements[3].payload.expression_statement.expression.payload.assignment;
    try std.testing.expectEqual(AST.Kind.tuple_expression, tuple_assignment.left_hand_side.nodeKind());
    try std.testing.expectEqual(AST.Kind.tuple_expression, tuple_assignment.right_hand_side.nodeKind());
}

test "stable node references do not depend on compatibility AST-ID offsets" {
    const source = "contract C { function f() external {} }";
    const source_id = AST.SourceId.init(23);
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();

    var first = try parseSourceWithIdentity(
        std.testing.allocator,
        source,
        "C.sol",
        &reporter,
        EVMVersion.current(),
        source_id,
        0,
    );
    defer first.deinit();
    var shifted = try parseSourceWithIdentity(
        std.testing.allocator,
        source,
        "C.sol",
        &reporter,
        EVMVersion.current(),
        source_id,
        100,
    );
    defer shifted.deinit();

    const first_root = first.tree.root.?;
    const shifted_root = shifted.tree.root.?;
    try std.testing.expect(first_root.node_ref.eql(shifted_root.node_ref));
    try std.testing.expectEqual(first_root.id + 100, shifted_root.id);
    const first_contract = first_root.payload.source_unit.nodes[0];
    const shifted_contract = shifted_root.payload.source_unit.nodes[0];
    try std.testing.expect(first_contract.node_ref.eql(shifted_contract.node_ref));
    try std.testing.expectEqual(first_contract.id + 100, shifted_contract.id);
}
