// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Clones non-recursive functions with literal call arguments materialized in
//! their bodies, leaving only dynamic parameters at the call site.

const std = @import("std");
const AST = @import("../ast.zig");
const ASTCopierModule = @import("ast_copier.zig");
const CallGraphModule = @import("call_graph_generator.zig");
const NameCollector = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const YulName = @import("../yul_name.zig").YulName;

pub const LiteralArguments = struct {
    items: std.ArrayList(?AST.Expression) = .empty,

    fn deinit(self: *LiteralArguments, allocator: std.mem.Allocator) void {
        for (self.items.items) |*maybe_expression| if (maybe_expression.*) |*expression|
            expression.deinit(allocator);
        self.items.deinit(allocator);
        self.* = undefined;
    }
};

const Specialization = struct {
    new_name: YulName,
    arguments: LiteralArguments,

    fn deinit(self: *Specialization, allocator: std.mem.Allocator) void {
        self.arguments.deinit(allocator);
        self.* = undefined;
    }
};

const SpecializationList = std.ArrayList(Specialization);
const SpecializationMap = std.AutoHashMap(YulName, SpecializationList);

pub const FunctionSpecializer = struct {
    allocator: std.mem.Allocator,
    recursive_functions: *const CallGraphModule.FunctionHandleSet,
    name_dispenser: *NameDispenser,
    old_to_new: SpecializationMap,

    pub const name = "FunctionSpecializer";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        var graph = try CallGraphModule.CallGraphGenerator.callGraph(allocator, ast);
        defer graph.deinit();
        var recursive = try graph.recursiveFunctions();
        defer recursive.deinit(allocator);
        var specializer: FunctionSpecializer = .{
            .allocator = allocator,
            .recursive_functions = &recursive,
            .name_dispenser = context.dispenser,
            .old_to_new = SpecializationMap.init(allocator),
        };
        defer specializer.deinit();
        try specializer.visitBlock(ast);
        try specializer.insertSpecializedFunctions(ast);
    }

    fn deinit(self: *FunctionSpecializer) void {
        var lists = self.old_to_new.valueIterator();
        while (lists.next()) |list| {
            for (list.items) |*specialization| specialization.deinit(self.allocator);
            list.deinit(self.allocator);
        }
        self.old_to_new.deinit();
        self.* = undefined;
    }

    fn visitBlock(self: *FunctionSpecializer, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *FunctionSpecializer, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| try self.visitExpression(value.value orelse return error.InvalidAst),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| {
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                try self.visitExpression(value.expression orelse return error.InvalidAst);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *FunctionSpecializer, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
                try self.visitFunctionCall(call);
            },
            .identifier, .literal => {},
        }
    }

    fn visitFunctionCall(self: *FunctionSpecializer, call: *AST.FunctionCall) anyerror!void {
        const identifier = switch (call.function_name) {
            .identifier => |*value| value,
            .builtin => return,
        };
        if (self.recursive_functions.contains(.{ .user = identifier.name })) return;

        var arguments = try self.specializableArguments(call);
        var arguments_owned = true;
        defer if (arguments_owned) arguments.deinit(self.allocator);
        var has_literal = false;
        for (arguments.items.items) |argument| if (argument != null) {
            has_literal = true;
            break;
        };
        if (!has_literal) return;

        const old_name = identifier.name;
        const new_name = try self.name_dispenser.newName(old_name);
        identifier.name = new_name;

        var kept_arguments: std.ArrayList(AST.Expression) = .empty;
        errdefer {
            for (kept_arguments.items) |*argument| argument.deinit(self.allocator);
            kept_arguments.deinit(self.allocator);
        }
        try kept_arguments.ensureTotalCapacity(self.allocator, call.arguments.items.len);
        for (call.arguments.items, arguments.items.items) |*argument, specialized| {
            if (specialized != null) {
                argument.deinit(self.allocator);
            } else {
                kept_arguments.appendAssumeCapacity(argument.*);
                argument.* = emptyExpression();
            }
        }
        call.arguments.deinit(self.allocator);
        call.arguments = kept_arguments;
        kept_arguments = .empty;

        const entry = try self.old_to_new.getOrPut(old_name);
        if (!entry.found_existing) entry.value_ptr.* = .empty;
        try entry.value_ptr.append(self.allocator, .{
            .new_name = new_name,
            .arguments = arguments,
        });
        arguments_owned = false;
    }

    fn specializableArguments(
        self: *FunctionSpecializer,
        call: *const AST.FunctionCall,
    ) anyerror!LiteralArguments {
        var result: LiteralArguments = .{};
        errdefer result.deinit(self.allocator);
        var copier = ASTCopierModule.ASTCopier.init(self.allocator);
        for (call.arguments.items) |*argument| {
            if (argument.* == .literal)
                try result.items.append(self.allocator, try copier.translateExpression(argument))
            else
                try result.items.append(self.allocator, null);
        }
        return result;
    }

    fn insertSpecializedFunctions(self: *FunctionSpecializer, ast: *AST.Block) anyerror!void {
        var replacement: std.ArrayList(AST.Statement) = .empty;
        errdefer {
            for (replacement.items) |*statement| statement.deinit(self.allocator);
            replacement.deinit(self.allocator);
        }
        for (ast.statements.items) |*statement| {
            if (statement.* == .function_definition) {
                const function = &statement.function_definition;
                if (self.old_to_new.getPtr(function.name)) |specializations| {
                    for (specializations.items) |*specialization| {
                        var specialized = try self.specialize(function, specialization);
                        errdefer specialized.deinit(self.allocator);
                        try replacement.append(self.allocator, .{ .function_definition = specialized });
                    }
                }
            }
            try replacement.append(self.allocator, statement.*);
            statement.* = emptyStatement();
        }
        ast.statements.deinit(self.allocator);
        ast.statements = replacement;
        replacement = .empty;
    }

    fn specialize(
        self: *FunctionSpecializer,
        function: *const AST.FunctionDefinition,
        specialization: *Specialization,
    ) anyerror!AST.FunctionDefinition {
        if (specialization.arguments.items.items.len != function.parameters.items.len)
            return error.InvalidSpecializationArity;

        var names = try NameCollector.NameCollector.initFunction(
            self.allocator,
            function,
            .only_variables,
        );
        defer names.deinit();
        var translations: std.ArrayList(ASTCopierModule.NameTranslation) = .empty;
        defer translations.deinit(self.allocator);
        for (0..names.names().len()) |index| {
            const old_name = names.names().at(index);
            try translations.append(self.allocator, .{
                .from = old_name,
                .to = try self.name_dispenser.newName(old_name),
            });
        }
        var copier = ASTCopierModule.FunctionCopier.init(self.allocator, translations.items);
        copier.bind();
        var new_function = try copier.copier.translateFunctionDefinition(function);
        errdefer new_function.deinit(self.allocator);

        var specialized_mask: std.ArrayList(bool) = .empty;
        defer specialized_mask.deinit(self.allocator);
        for (specialization.arguments.items.items) |argument|
            try specialized_mask.append(self.allocator, argument != null);

        var declarations: std.ArrayList(AST.Statement) = .empty;
        defer declarations.deinit(self.allocator);
        for (specialization.arguments.items.items, 0..) |*maybe_argument, index| {
            if (maybe_argument.*) |*argument| {
                const value = try self.allocator.create(AST.Expression);
                value.* = argument.*;
                maybe_argument.* = null;
                var declaration: AST.VariableDeclaration = .{ .debug_data = function.debug_data };
                errdefer declaration.deinit(self.allocator);
                try declaration.variables.append(self.allocator, new_function.parameters.items[index]);
                declaration.value = value;
                try declarations.append(self.allocator, .{ .variable_declaration = declaration });
            }
        }

        var body_statements: std.ArrayList(AST.Statement) = .empty;
        errdefer {
            for (body_statements.items) |*statement| statement.deinit(self.allocator);
            body_statements.deinit(self.allocator);
        }
        try body_statements.ensureTotalCapacity(
            self.allocator,
            declarations.items.len + new_function.body.statements.items.len,
        );
        for (declarations.items) |*statement| {
            body_statements.appendAssumeCapacity(statement.*);
            statement.* = emptyStatement();
        }
        for (new_function.body.statements.items) |*statement| {
            body_statements.appendAssumeCapacity(statement.*);
            statement.* = emptyStatement();
        }
        new_function.body.statements.deinit(self.allocator);
        new_function.body.statements = body_statements;
        body_statements = .empty;

        var parameters: std.ArrayList(AST.NameWithDebugData) = .empty;
        errdefer parameters.deinit(self.allocator);
        for (new_function.parameters.items, specialized_mask.items) |parameter, specialized|
            if (!specialized) try parameters.append(self.allocator, parameter);
        new_function.parameters.deinit(self.allocator);
        new_function.parameters = parameters;
        parameters = .empty;
        new_function.name = specialization.new_name;

        specialization.arguments.items.deinit(self.allocator);
        specialization.arguments.items = .empty;
        return new_function;
    }
};

fn emptyStatement() AST.Statement {
    return .{ .block = .{} };
}

fn emptyExpression() AST.Expression {
    return .{ .identifier = .{} };
}

test "function specializer materializes literal parameters" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a, b) { pop(add(a, b)) } let x := 1 f(x, 5) }",
        "function-specializer.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(
        allocator,
        dialect.dialect(),
        ast.root(),
        &reserved,
    );
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = dialect.dialect(),
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    try FunctionSpecializer.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "function f_1") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "f_1(x)") != null);
}
