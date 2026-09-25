// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Ownership-safe deep copier for Yul ASTs, with identifier and scope hooks.

const std = @import("std");
const AST = @import("../ast.zig");
const YulName = @import("../yul_name.zig").YulName;
const DebugData = @import("../../liblangutil/debug_data.zig").DebugData;

pub const Hooks = struct {
    /// Rebind borrowed source names when copying across ownership boundaries.
    /// Replacement nodes returned by expression/identifier hooks own their
    /// annotation policy and bypass this hook, like their name translation.
    translate_debug_data: ?*const fn (?*anyopaque, ?DebugData) anyerror!?DebugData = null,
    translate_expression: ?*const fn (
        ?*anyopaque,
        *ASTCopier,
        *const AST.Expression,
    ) anyerror!?AST.Expression = null,
    /// Called with the original identifier node before name-only translation.
    /// This permits pointer-identity based rewrites such as Solidity inline
    /// assembly external references while preserving the lightweight name hook.
    translate_identifier_node: ?*const fn (
        ?*anyopaque,
        *ASTCopier,
        *const AST.Identifier,
    ) anyerror!?AST.Identifier = null,
    translate_identifier: ?*const fn (?*anyopaque, YulName) anyerror!YulName = null,
    enter_scope: ?*const fn (?*anyopaque, *const AST.Block) anyerror!void = null,
    leave_scope: ?*const fn (?*anyopaque, *const AST.Block) anyerror!void = null,
    enter_function: ?*const fn (?*anyopaque, *const AST.FunctionDefinition) anyerror!void = null,
    leave_function: ?*const fn (?*anyopaque, *const AST.FunctionDefinition) anyerror!void = null,
};

pub const ASTCopier = struct {
    allocator: std.mem.Allocator,
    context: ?*anyopaque = null,
    hooks: Hooks = .{},

    pub fn init(allocator: std.mem.Allocator) ASTCopier {
        return .{ .allocator = allocator };
    }

    pub fn initWithHooks(
        allocator: std.mem.Allocator,
        context: ?*anyopaque,
        hooks: Hooks,
    ) ASTCopier {
        return .{ .allocator = allocator, .context = context, .hooks = hooks };
    }

    pub fn translateAst(
        self: *ASTCopier,
        ast: *const AST.AST,
    ) anyerror!AST.AST {
        return AST.AST.init(self.allocator, ast.dialect().*, try self.translateBlock(ast.root()));
    }

    pub fn translateExpression(
        self: *ASTCopier,
        expression: *const AST.Expression,
    ) anyerror!AST.Expression {
        if (self.hooks.translate_expression) |callback|
            if (try callback(self.context, self, expression)) |replacement| return replacement;
        return switch (expression.*) {
            .literal => |*value| .{ .literal = try self.translateLiteral(value) },
            .identifier => |*value| .{ .identifier = try self.translateIdentifier(value) },
            .function_call => |*value| .{ .function_call = try self.translateFunctionCall(value) },
        };
    }

    pub fn translateStatement(
        self: *ASTCopier,
        statement: *const AST.Statement,
    ) anyerror!AST.Statement {
        return switch (statement.*) {
            .expression_statement => |*value| .{ .expression_statement = .{
                .debug_data = try self.translateDebugData(value.debug_data),
                .expression = try self.translateExpression(&value.expression),
            } },
            .assignment => |*value| .{ .assignment = try self.translateAssignment(value) },
            .variable_declaration => |*value| .{
                .variable_declaration = try self.translateVariableDeclaration(value),
            },
            .function_definition => |*value| .{
                .function_definition = try self.translateFunctionDefinition(value),
            },
            .if_statement => |*value| .{ .if_statement = try self.translateIf(value) },
            .switch_statement => |*value| .{ .switch_statement = try self.translateSwitch(value) },
            .for_loop => |*value| .{ .for_loop = try self.translateForLoop(value) },
            .break_statement => |value| .{ .break_statement = .{ .debug_data = try self.translateDebugData(value.debug_data) } },
            .continue_statement => |value| .{ .continue_statement = .{ .debug_data = try self.translateDebugData(value.debug_data) } },
            .leave_statement => |value| .{ .leave_statement = .{ .debug_data = try self.translateDebugData(value.debug_data) } },
            .block => |*value| .{ .block = try self.translateBlock(value) },
        };
    }

    pub fn translateBlock(
        self: *ASTCopier,
        block: *const AST.Block,
    ) anyerror!AST.Block {
        try self.enterScope(block);
        var scope_open = true;
        errdefer if (scope_open) self.leaveScope(block) catch {}; // zlinter-disable-current-line no_swallow_error - rollback cleanup must preserve the initiating error
        var result: AST.Block = .{ .debug_data = try self.translateDebugData(block.debug_data) };
        errdefer result.deinit(self.allocator);
        try result.statements.ensureTotalCapacityPrecise(self.allocator, block.statements.items.len);
        for (block.statements.items) |*statement|
            result.statements.appendAssumeCapacity(try self.translateStatement(statement));
        scope_open = false;
        try self.leaveScope(block);
        return result;
    }

    fn translateAssignment(
        self: *ASTCopier,
        assignment: *const AST.Assignment,
    ) anyerror!AST.Assignment {
        var result: AST.Assignment = .{ .debug_data = try self.translateDebugData(assignment.debug_data) };
        errdefer result.deinit(self.allocator);
        try result.variable_names.ensureTotalCapacityPrecise(self.allocator, assignment.variable_names.items.len);
        for (assignment.variable_names.items) |*identifier|
            result.variable_names.appendAssumeCapacity(try self.translateIdentifier(identifier));
        result.value = try self.translateOptionalExpression(assignment.value);
        return result;
    }

    fn translateVariableDeclaration(
        self: *ASTCopier,
        declaration: *const AST.VariableDeclaration,
    ) anyerror!AST.VariableDeclaration {
        var result: AST.VariableDeclaration = .{ .debug_data = try self.translateDebugData(declaration.debug_data) };
        errdefer result.deinit(self.allocator);
        try result.variables.ensureTotalCapacityPrecise(self.allocator, declaration.variables.items.len);
        for (declaration.variables.items) |*variable|
            result.variables.appendAssumeCapacity(try self.translateNameWithDebugData(variable));
        result.value = try self.translateOptionalExpression(declaration.value);
        return result;
    }

    fn translateFunctionCall(
        self: *ASTCopier,
        call: *const AST.FunctionCall,
    ) anyerror!AST.FunctionCall {
        var result: AST.FunctionCall = .{
            .debug_data = try self.translateDebugData(call.debug_data),
            .function_name = try self.translateFunctionName(&call.function_name),
        };
        errdefer result.deinit(self.allocator);
        try result.arguments.ensureTotalCapacityPrecise(self.allocator, call.arguments.items.len);
        for (call.arguments.items) |*argument|
            result.arguments.appendAssumeCapacity(try self.translateExpression(argument));
        return result;
    }

    fn translateIf(
        self: *ASTCopier,
        if_statement: *const AST.If,
    ) anyerror!AST.If {
        var result: AST.If = .{ .debug_data = try self.translateDebugData(if_statement.debug_data) };
        errdefer result.deinit(self.allocator);
        result.condition = try self.translateOptionalExpression(if_statement.condition);
        result.body = try self.translateBlock(&if_statement.body);
        return result;
    }

    fn translateSwitch(
        self: *ASTCopier,
        switch_statement: *const AST.Switch,
    ) anyerror!AST.Switch {
        var result: AST.Switch = .{ .debug_data = try self.translateDebugData(switch_statement.debug_data) };
        errdefer result.deinit(self.allocator);
        result.expression = try self.translateOptionalExpression(switch_statement.expression);
        try result.cases.ensureTotalCapacityPrecise(self.allocator, switch_statement.cases.items.len);
        for (switch_statement.cases.items) |*case_value|
            result.cases.appendAssumeCapacity(try self.translateCase(case_value));
        return result;
    }

    pub fn translateFunctionDefinition(
        self: *ASTCopier,
        definition: *const AST.FunctionDefinition,
    ) anyerror!AST.FunctionDefinition {
        const translated_name = try self.translateIdentifierName(definition.name);
        try self.enterFunction(definition);
        var function_scope_open = true;
        errdefer if (function_scope_open) self.leaveFunction(definition) catch {}; // zlinter-disable-current-line no_swallow_error - rollback cleanup must preserve the initiating error

        var result: AST.FunctionDefinition = .{
            .debug_data = try self.translateDebugData(definition.debug_data),
            .name = translated_name,
        };
        errdefer result.deinit(self.allocator);
        try result.parameters.ensureTotalCapacityPrecise(self.allocator, definition.parameters.items.len);
        for (definition.parameters.items) |*parameter|
            result.parameters.appendAssumeCapacity(try self.translateNameWithDebugData(parameter));
        try result.return_variables.ensureTotalCapacityPrecise(self.allocator, definition.return_variables.items.len);
        for (definition.return_variables.items) |*return_variable|
            result.return_variables.appendAssumeCapacity(try self.translateNameWithDebugData(return_variable));
        result.body = try self.translateBlock(&definition.body);
        function_scope_open = false;
        try self.leaveFunction(definition);
        return result;
    }

    fn translateForLoop(
        self: *ASTCopier,
        loop: *const AST.ForLoop,
    ) anyerror!AST.ForLoop {
        try self.enterScope(&loop.pre);
        var loop_scope_open = true;
        errdefer if (loop_scope_open) self.leaveScope(&loop.pre) catch {}; // zlinter-disable-current-line no_swallow_error - rollback cleanup must preserve the initiating error
        var result: AST.ForLoop = .{ .debug_data = try self.translateDebugData(loop.debug_data) };
        errdefer result.deinit(self.allocator);
        result.pre = try self.translateBlock(&loop.pre);
        result.condition = try self.translateOptionalExpression(loop.condition);
        result.post = try self.translateBlock(&loop.post);
        result.body = try self.translateBlock(&loop.body);
        loop_scope_open = false;
        try self.leaveScope(&loop.pre);
        return result;
    }

    fn translateCase(
        self: *ASTCopier,
        case_value: *const AST.Case,
    ) anyerror!AST.Case {
        var result: AST.Case = .{ .debug_data = try self.translateDebugData(case_value.debug_data) };
        errdefer result.deinit(self.allocator);
        if (case_value.value) |literal| {
            var translated = try self.translateLiteral(literal);
            errdefer translated.deinit(self.allocator);
            result.value = try AST.createLiteral(self.allocator, translated);
        }
        result.body = try self.translateBlock(&case_value.body);
        return result;
    }

    fn translateLiteral(
        self: *ASTCopier,
        literal: *const AST.Literal,
    ) anyerror!AST.Literal {
        return .{
            .debug_data = try self.translateDebugData(literal.debug_data),
            .kind = literal.kind,
            .value = try literal.value.clone(self.allocator),
        };
    }

    fn translateIdentifier(self: *ASTCopier, identifier: *const AST.Identifier) anyerror!AST.Identifier {
        if (self.hooks.translate_identifier_node) |callback|
            if (try callback(self.context, self, identifier)) |replacement| return replacement;
        return .{
            .debug_data = try self.translateDebugData(identifier.debug_data),
            .name = try self.translateIdentifierName(identifier.name),
        };
    }

    fn translateFunctionName(
        self: *ASTCopier,
        function_name: *const AST.FunctionName,
    ) anyerror!AST.FunctionName {
        return switch (function_name.*) {
            .identifier => |*identifier| .{ .identifier = try self.translateIdentifier(identifier) },
            .builtin => |builtin| .{ .builtin = .{ .handle = builtin.handle, .debug_data = try self.translateDebugData(builtin.debug_data) } },
        };
    }

    fn translateNameWithDebugData(
        self: *ASTCopier,
        value: *const AST.NameWithDebugData,
    ) anyerror!AST.NameWithDebugData {
        return .{
            .debug_data = try self.translateDebugData(value.debug_data),
            .name = try self.translateIdentifierName(value.name),
        };
    }

    fn translateOptionalExpression(
        self: *ASTCopier,
        expression: ?*const AST.Expression,
    ) anyerror!?*AST.Expression {
        const value = expression orelse return null;
        var translated = try self.translateExpression(value);
        errdefer translated.deinit(self.allocator);
        return AST.createExpression(self.allocator, translated);
    }

    fn translateDebugData(self: *ASTCopier, data: ?DebugData) anyerror!?DebugData {
        if (self.hooks.translate_debug_data) |callback| return callback(self.context, data);
        return data;
    }

    fn translateIdentifierName(self: *ASTCopier, name: YulName) anyerror!YulName {
        if (self.hooks.translate_identifier) |callback| return callback(self.context, name);
        return name;
    }

    fn enterScope(self: *ASTCopier, block: *const AST.Block) anyerror!void {
        if (self.hooks.enter_scope) |callback| try callback(self.context, block);
    }

    fn leaveScope(self: *ASTCopier, block: *const AST.Block) anyerror!void {
        if (self.hooks.leave_scope) |callback| try callback(self.context, block);
    }

    fn enterFunction(self: *ASTCopier, definition: *const AST.FunctionDefinition) anyerror!void {
        if (self.hooks.enter_function) |callback| try callback(self.context, definition);
    }

    fn leaveFunction(self: *ASTCopier, definition: *const AST.FunctionDefinition) anyerror!void {
        if (self.hooks.leave_function) |callback| try callback(self.context, definition);
    }
};

pub const NameTranslation = struct {
    from: YulName,
    to: YulName,
};

pub const FunctionCopier = struct {
    copier: ASTCopier,
    translations: []const NameTranslation,

    pub fn init(
        allocator: std.mem.Allocator,
        translations: []const NameTranslation,
    ) FunctionCopier {
        return .{
            .copier = ASTCopier.initWithHooks(allocator, null, .{
                .translate_identifier = translateIdentifier,
            }),
            .translations = translations,
        };
    }

    /// Rebinds the self-referential callback context after this value has moved.
    pub fn bind(self: *FunctionCopier) void {
        self.copier.context = self;
    }

    fn translateIdentifier(context: ?*anyopaque, name: YulName) anyerror!YulName {
        const self: *FunctionCopier = @ptrCast(@alignCast(context.?));
        for (self.translations) |translation| {
            if (translation.from.eql(name)) return translation.to;
        }
        return name;
    }
};

test "AST copier deep-copies owned literals and applies function renames" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := \"abc\" function f(x) -> r { r := x } f(x) }",
        "copy.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    const x = try YulName.init("x");
    const renamed = try YulName.init("renamed");
    var function_copier = FunctionCopier.init(allocator, &.{.{ .from = x, .to = renamed }});
    function_copier.bind();
    var copy = try function_copier.copier.translateAst(&ast);
    defer copy.deinit();
    const rendered = try Printer.formatDefault(allocator, &copy);
    defer allocator.free(rendered);
    try std.testing.expectEqualStrings(
        "{\n    let renamed := \"abc\"\n    function f(renamed) -> r\n    { r := renamed }\n    f(renamed)\n}",
        rendered,
    );
}

test "Yul AST copier releases partial nested copies on allocation failure" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Encoding = @import("../ast_encoding.zig");
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator,
        \\{ function f(a, b) -> r, s {
        \\  for { let i := 0 } lt(i, a) { i := add(i, 1) } {
        \\   switch i case 0 { r := b continue } default { s := add(s, 1) }
        \\   if s { break }
        \\  }
        \\  leave
        \\ }
        \\ let x, y := f(3, 7) x, y := f(5, 6) x := "abc" { pop(x) }
        \\}
    , "copy.yul", &reporter, .{}, .{})).?;
    defer ast.deinit();
    const Check = struct {
        fn run(failing: std.mem.Allocator, source: *const AST.Block) !void {
            var copier = ASTCopier.init(failing);
            var result = try copier.translateBlock(source);
            defer result.deinit(failing);
            try std.testing.expectEqualDeep(try Encoding.hashBlock(source), try Encoding.hashBlock(&result));
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ast.root()});
}
