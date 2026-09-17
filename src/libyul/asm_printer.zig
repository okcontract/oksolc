// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Exact textual rendering of owned Yul ASTs.

const std = @import("std");
const common_data = @import("../libsolutil/common_data.zig");
const ASTModule = @import("ast.zig");
const Utilities = @import("utilities.zig");
const CharStreamProvider = @import("../liblangutil/char_stream_provider.zig").CharStreamProvider;
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;

pub const SourceIndexName = struct {
    index: u32,
    name: []const u8,
};

pub const PrintError = std.mem.Allocator.Error || error{
    InvalidAST,
    InvalidYulStringHandle,
    UnknownBuiltin,
    UnknownSourceName,
    SourceNameMismatch,
};

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

    pub fn renderExpression(
        self: *AsmPrinter,
        expression: *const ASTModule.Expression,
    ) PrintError![]u8 {
        return switch (expression.*) {
            .function_call => |*value| self.renderFunctionCall(value),
            .identifier => |*value| self.renderIdentifier(value),
            .literal => |*value| self.renderLiteral(value),
        };
    }

    pub fn renderStatement(
        self: *AsmPrinter,
        statement: *const ASTModule.Statement,
    ) PrintError![]u8 {
        return switch (statement.*) {
            .expression_statement => |*value| self.renderExpressionStatement(value),
            .assignment => |*value| self.renderAssignment(value),
            .variable_declaration => |*value| self.renderVariableDeclaration(value),
            .function_definition => |*value| self.renderFunctionDefinition(value),
            .if_statement => |*value| self.renderIf(value),
            .switch_statement => |*value| self.renderSwitch(value),
            .for_loop => |*value| self.renderForLoop(value),
            .break_statement => |*value| self.renderKeyword(value.debug_data, "break"),
            .continue_statement => |*value| self.renderKeyword(value.debug_data, "continue"),
            .leave_statement => |*value| self.renderKeyword(value.debug_data, "leave"),
            .block => |*value| self.renderBlock(value),
        };
    }

    pub fn renderLiteral(
        self: *AsmPrinter,
        literal: *const ASTModule.Literal,
    ) PrintError![]u8 {
        if (!Utilities.validLiteral(literal)) return error.InvalidAST;
        const debug = try self.formatDebugDataAlloc(literal.debug_data, false);
        defer self.allocator.free(debug);
        const formatted = Utilities.formatLiteralAlloc(self.allocator, literal, true) catch |err| switch (err) {
            error.InvalidLiteral, error.InvalidNumberLiteral, error.UnexpectedBoolLiteral => return error.InvalidAST,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer self.allocator.free(formatted);
        if (literal.kind != .String)
            return concatAlloc(self.allocator, &.{ debug, formatted });
        const quoted = try common_data.escapeAndQuoteStringAlloc(self.allocator, formatted);
        defer self.allocator.free(quoted);
        return concatAlloc(self.allocator, &.{ debug, quoted });
    }

    pub fn renderIdentifier(
        self: *AsmPrinter,
        identifier: *const ASTModule.Identifier,
    ) PrintError![]u8 {
        if (identifier.name.empty()) return error.InvalidAST;
        const debug = try self.formatDebugDataAlloc(identifier.debug_data, false);
        defer self.allocator.free(debug);
        const name = identifier.name.str() catch return error.InvalidYulStringHandle;
        return concatAlloc(self.allocator, &.{ debug, name });
    }

    pub fn renderBuiltinName(
        self: *AsmPrinter,
        builtin_name: *const ASTModule.BuiltinName,
    ) PrintError![]u8 {
        const debug = try self.formatDebugDataAlloc(builtin_name.debug_data, false);
        defer self.allocator.free(debug);
        const builtin = self.dialect.builtin(builtin_name.handle) catch return error.UnknownBuiltin;
        return concatAlloc(self.allocator, &.{ debug, builtin.name });
    }

    fn renderFunctionName(
        self: *AsmPrinter,
        function_name: *const ASTModule.FunctionName,
    ) PrintError![]u8 {
        return switch (function_name.*) {
            .identifier => |*value| self.renderIdentifier(value),
            .builtin => |*value| self.renderBuiltinName(value),
        };
    }

    pub fn renderExpressionStatement(
        self: *AsmPrinter,
        statement: *const ASTModule.ExpressionStatement,
    ) PrintError![]u8 {
        const debug = try self.formatDebugDataAlloc(statement.debug_data, true);
        defer self.allocator.free(debug);
        const expression = try self.renderExpression(&statement.expression);
        defer self.allocator.free(expression);
        return concatAlloc(self.allocator, &.{ debug, expression });
    }

    pub fn renderAssignment(
        self: *AsmPrinter,
        assignment: *const ASTModule.Assignment,
    ) PrintError![]u8 {
        if (assignment.variable_names.items.len == 0 or assignment.value == null)
            return error.InvalidAST;
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        const debug = try self.formatDebugDataAlloc(assignment.debug_data, true);
        defer self.allocator.free(debug);
        try output.appendSlice(self.allocator, debug);
        for (assignment.variable_names.items, 0..) |*variable, index| {
            if (index != 0) try output.appendSlice(self.allocator, ", ");
            const rendered = try self.renderIdentifier(variable);
            defer self.allocator.free(rendered);
            try output.appendSlice(self.allocator, rendered);
        }
        try output.appendSlice(self.allocator, " := ");
        const value = try self.renderExpression(assignment.value.?);
        defer self.allocator.free(value);
        try output.appendSlice(self.allocator, value);
        return output.toOwnedSlice(self.allocator);
    }

    pub fn renderVariableDeclaration(
        self: *AsmPrinter,
        declaration: *const ASTModule.VariableDeclaration,
    ) PrintError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        const debug = try self.formatDebugDataAlloc(declaration.debug_data, true);
        defer self.allocator.free(debug);
        try output.appendSlice(self.allocator, debug);
        try output.appendSlice(self.allocator, "let ");
        for (declaration.variables.items, 0..) |variable, index| {
            if (index != 0) try output.appendSlice(self.allocator, ", ");
            const rendered = try self.formatNameWithDebugDataAlloc(variable);
            defer self.allocator.free(rendered);
            try output.appendSlice(self.allocator, rendered);
        }
        if (declaration.value) |value| {
            try output.appendSlice(self.allocator, " := ");
            const rendered = try self.renderExpression(value);
            defer self.allocator.free(rendered);
            try output.appendSlice(self.allocator, rendered);
        }
        return output.toOwnedSlice(self.allocator);
    }

    pub fn renderFunctionDefinition(
        self: *AsmPrinter,
        definition: *const ASTModule.FunctionDefinition,
    ) PrintError![]u8 {
        if (definition.name.empty()) return error.InvalidAST;
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        const debug = try self.formatDebugDataAlloc(definition.debug_data, true);
        defer self.allocator.free(debug);
        const name = definition.name.str() catch return error.InvalidYulStringHandle;
        try output.appendSlice(self.allocator, debug);
        try output.appendSlice(self.allocator, "function ");
        try output.appendSlice(self.allocator, name);
        try output.append(self.allocator, '(');
        try self.appendNames(&output, definition.parameters.items);
        try output.append(self.allocator, ')');
        if (definition.return_variables.items.len != 0) {
            try output.appendSlice(self.allocator, " -> ");
            try self.appendNames(&output, definition.return_variables.items);
        }
        try output.append(self.allocator, '\n');
        const body = try self.renderBlock(&definition.body);
        defer self.allocator.free(body);
        try output.appendSlice(self.allocator, body);
        return output.toOwnedSlice(self.allocator);
    }

    pub fn renderFunctionCall(
        self: *AsmPrinter,
        call: *const ASTModule.FunctionCall,
    ) PrintError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        const debug = try self.formatDebugDataAlloc(call.debug_data, false);
        defer self.allocator.free(debug);
        try output.appendSlice(self.allocator, debug);
        const name = try self.renderFunctionName(&call.function_name);
        defer self.allocator.free(name);
        try output.appendSlice(self.allocator, name);
        try output.append(self.allocator, '(');
        for (call.arguments.items, 0..) |*argument, index| {
            if (index != 0) try output.appendSlice(self.allocator, ", ");
            const rendered = try self.renderExpression(argument);
            defer self.allocator.free(rendered);
            try output.appendSlice(self.allocator, rendered);
        }
        try output.append(self.allocator, ')');
        return output.toOwnedSlice(self.allocator);
    }

    pub fn renderIf(self: *AsmPrinter, if_statement: *const ASTModule.If) PrintError![]u8 {
        const condition = if_statement.condition orelse return error.InvalidAST;
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        const debug = try self.formatDebugDataAlloc(if_statement.debug_data, true);
        defer self.allocator.free(debug);
        try output.appendSlice(self.allocator, debug);
        try output.appendSlice(self.allocator, "if ");
        const rendered_condition = try self.renderExpression(condition);
        defer self.allocator.free(rendered_condition);
        try output.appendSlice(self.allocator, rendered_condition);
        const body = try self.renderBlock(&if_statement.body);
        defer self.allocator.free(body);
        try output.append(self.allocator, if (std.mem.findScalar(u8, body, '\n') == null) ' ' else '\n');
        try output.appendSlice(self.allocator, body);
        return output.toOwnedSlice(self.allocator);
    }

    pub fn renderSwitch(self: *AsmPrinter, switch_statement: *const ASTModule.Switch) PrintError![]u8 {
        const expression = switch_statement.expression orelse return error.InvalidAST;
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        const debug = try self.formatDebugDataAlloc(switch_statement.debug_data, true);
        defer self.allocator.free(debug);
        try output.appendSlice(self.allocator, debug);
        try output.appendSlice(self.allocator, "switch ");
        const rendered_expression = try self.renderExpression(expression);
        defer self.allocator.free(rendered_expression);
        try output.appendSlice(self.allocator, rendered_expression);
        for (switch_statement.cases.items) |*case_value| {
            if (case_value.value) |literal| {
                try output.appendSlice(self.allocator, "\ncase ");
                const rendered_literal = try self.renderLiteral(literal);
                defer self.allocator.free(rendered_literal);
                try output.appendSlice(self.allocator, rendered_literal);
                try output.append(self.allocator, ' ');
            } else {
                try output.appendSlice(self.allocator, "\ndefault ");
            }
            const body = try self.renderBlock(&case_value.body);
            defer self.allocator.free(body);
            try output.appendSlice(self.allocator, body);
        }
        return output.toOwnedSlice(self.allocator);
    }

    pub fn renderForLoop(self: *AsmPrinter, loop: *const ASTModule.ForLoop) PrintError![]u8 {
        const condition = loop.condition orelse return error.InvalidAST;
        const debug = try self.formatDebugDataAlloc(loop.debug_data, true);
        defer self.allocator.free(debug);
        const pre = try self.renderBlock(&loop.pre);
        defer self.allocator.free(pre);
        const rendered_condition = try self.renderExpression(condition);
        defer self.allocator.free(rendered_condition);
        const post = try self.renderBlock(&loop.post);
        defer self.allocator.free(post);
        const delimiter: u8 = if (pre.len + rendered_condition.len + post.len < 60 and
            std.mem.findScalar(u8, pre, '\n') == null and
            std.mem.findScalar(u8, post, '\n') == null) ' ' else '\n';
        const body = try self.renderBlock(&loop.body);
        defer self.allocator.free(body);

        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        try output.appendSlice(self.allocator, debug);
        try output.appendSlice(self.allocator, "for ");
        try output.appendSlice(self.allocator, pre);
        try output.append(self.allocator, delimiter);
        try output.appendSlice(self.allocator, rendered_condition);
        try output.append(self.allocator, delimiter);
        try output.appendSlice(self.allocator, post);
        try output.append(self.allocator, '\n');
        try output.appendSlice(self.allocator, body);
        return output.toOwnedSlice(self.allocator);
    }

    fn renderKeyword(
        self: *AsmPrinter,
        debug_data: ?DebugData,
        keyword: []const u8,
    ) PrintError![]u8 {
        const debug = try self.formatDebugDataAlloc(debug_data, true);
        defer self.allocator.free(debug);
        return concatAlloc(self.allocator, &.{ debug, keyword });
    }

    pub fn renderBlock(self: *AsmPrinter, block: *const ASTModule.Block) PrintError![]u8 {
        const debug = try self.formatDebugDataAlloc(block.debug_data, true);
        defer self.allocator.free(debug);
        if (block.statements.items.len == 0)
            return concatAlloc(self.allocator, &.{ debug, "{ }" });

        var body: std.ArrayList(u8) = .empty;
        defer body.deinit(self.allocator);
        for (block.statements.items, 0..) |*statement, index| {
            if (index != 0) try body.append(self.allocator, '\n');
            const rendered = try self.renderStatement(statement);
            defer self.allocator.free(rendered);
            try body.appendSlice(self.allocator, rendered);
        }
        if (body.items.len < 30 and std.mem.findScalar(u8, body.items, '\n') == null)
            return concatAlloc(self.allocator, &.{ debug, "{ ", body.items, " }" });

        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        try output.appendSlice(self.allocator, debug);
        try output.appendSlice(self.allocator, "{\n    ");
        for (body.items) |character| {
            try output.append(self.allocator, character);
            if (character == '\n') try output.appendSlice(self.allocator, "    ");
        }
        try output.appendSlice(self.allocator, "\n}");
        return output.toOwnedSlice(self.allocator);
    }

    fn appendNames(
        self: *AsmPrinter,
        output: *std.ArrayList(u8),
        names: []const ASTModule.NameWithDebugData,
    ) PrintError!void {
        for (names, 0..) |name, index| {
            if (index != 0) try output.appendSlice(self.allocator, ", ");
            const rendered = try self.formatNameWithDebugDataAlloc(name);
            defer self.allocator.free(rendered);
            try output.appendSlice(self.allocator, rendered);
        }
    }

    fn formatNameWithDebugDataAlloc(
        self: *AsmPrinter,
        variable: ASTModule.NameWithDebugData,
    ) PrintError![]u8 {
        if (variable.name.empty()) return error.InvalidAST;
        const debug = try self.formatDebugDataAlloc(variable.debug_data, true);
        defer self.allocator.free(debug);
        const name = variable.name.str() catch return error.InvalidYulStringHandle;
        return concatAlloc(self.allocator, &.{ debug, name });
    }

    fn formatDebugDataAlloc(
        self: *AsmPrinter,
        debug_data: ?DebugData,
        statement: bool,
    ) PrintError![]u8 {
        const data = debug_data orelse return self.allocator.alloc(u8, 0);
        if (self.debug_info_selection.none()) return self.allocator.alloc(u8, 0);

        var items: [2][]u8 = undefined;
        var item_count: usize = 0;
        defer for (items[0..item_count]) |item| self.allocator.free(item);
        if (data.ast_id) |ast_id| {
            if (self.debug_info_selection.ast_id) {
                items[item_count] = try std.fmt.allocPrint(self.allocator, "@ast-id {d}", .{ast_id});
                item_count += 1;
            }
        }
        if (!self.last_location.eql(data.origin_location) and self.source_index_to_name.len != 0) {
            self.last_location = data.origin_location;
            items[item_count] = try formatSourceLocation(
                self.allocator,
                data.origin_location,
                self.source_index_to_name,
                self.debug_info_selection,
                self.solidity_source_provider,
            );
            item_count += 1;
        }
        if (item_count == 0) return self.allocator.alloc(u8, 0);

        var body: std.ArrayList(u8) = .empty;
        defer body.deinit(self.allocator);
        for (items[0..item_count], 0..) |item, index| {
            if (index != 0) try body.append(self.allocator, ' ');
            try body.appendSlice(self.allocator, item);
        }
        return if (statement)
            std.fmt.allocPrint(self.allocator, "/// {s}\n", .{body.items})
        else
            std.fmt.allocPrint(self.allocator, "/** {s} */ ", .{body.items});
    }
};

pub fn formatSourceLocation(
    allocator: std.mem.Allocator,
    location: SourceLocation,
    source_index_to_name: []const SourceIndexName,
    debug_info_selection: DebugInfoSelection,
    solidity_source_provider: ?CharStreamProvider,
) PrintError![]u8 {
    if (source_index_to_name.len == 0) return error.UnknownSourceName;
    if (debug_info_selection.snippet and !debug_info_selection.location) return error.InvalidAST;
    if (debug_info_selection.none()) return allocator.alloc(u8, 0);

    var source_index: ?u32 = null;
    var snippet: ?[]u8 = null;
    defer if (snippet) |owned| allocator.free(owned);
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
                if (!stream.isImportedFromAST()) {
                    const raw = try stream.singleLineSnippetAlloc(allocator, location);
                    defer allocator.free(raw);
                    const quoted = try common_data.escapeAndQuoteStringAlloc(allocator, raw);
                    defer allocator.free(quoted);
                    snippet = try escapeCommentTerminatorAlloc(allocator, quoted);
                }
            }
        }
    }

    const prefix = if (source_index) |index|
        try std.fmt.allocPrint(allocator, "@src {d}:{d}:{d}", .{ index, location.start, location.end })
    else
        try std.fmt.allocPrint(allocator, "@src -1:{d}:{d}", .{ location.start, location.end });
    defer allocator.free(prefix);
    if (snippet) |quoted| return concatAlloc(allocator, &.{ prefix, "  ", quoted });
    return allocator.dupe(u8, prefix);
}

fn escapeCommentTerminatorAlloc(
    allocator: std.mem.Allocator,
    input: []const u8,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var index: usize = 0;
    while (index < input.len) {
        if (index + 1 < input.len and input[index] == '*' and input[index + 1] == '/') {
            try output.appendSlice(allocator, "*\\/");
            index += 2;
        } else {
            try output.append(allocator, input[index]);
            index += 1;
        }
    }
    return output.toOwnedSlice(allocator);
}

fn concatAlloc(
    allocator: std.mem.Allocator,
    parts: []const []const u8,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (parts) |part| try output.appendSlice(allocator, part);
    return output.toOwnedSlice(allocator);
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
