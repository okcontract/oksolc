// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Inlines side-effect-free single-expression functions at expression sites.

const std = @import("std");
const AST = @import("../ast.zig");
const FinderModule = @import("inlinable_expression_function_finder.zig");
const Metrics = @import("metrics.zig");
const NameCollector = @import("name_collector.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");
const SubstitutionModule = @import("substitution.zig");

pub const ExpressionInliner = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    inlinable_functions: *const NameCollector.FunctionDefinitionMap,

    pub const name = "ExpressionInliner";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        var finder = FinderModule.InlinableExpressionFunctionFinder.init(allocator);
        defer finder.deinit();
        try finder.run(ast);
        var inliner: ExpressionInliner = .{
            .allocator = allocator,
            .dialect = context.dialect,
            .inlinable_functions = finder.inlinableFunctions(),
        };
        try inliner.visitBlock(ast);
    }

    fn visitBlock(self: *ExpressionInliner, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *ExpressionInliner, statement: *AST.Statement) anyerror!void {
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

    fn visitExpression(self: *ExpressionInliner, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
            .identifier, .literal => return,
        }

        const call = &expression.function_call;
        const function_name = switch (call.function_name) {
            .identifier => |identifier| identifier.name,
            .builtin => return,
        };
        const function = (self.inlinable_functions.get(function_name) orelse return).*;
        if (call.arguments.items.len != function.parameters.items.len) return error.InvalidCallArity;

        var references = try NameCollector.ReferencesCounter.countReferencesBlock(
            self.allocator,
            &function.body,
        );
        defer references.deinit(self.allocator);
        var substitutions = SubstitutionModule.SubstitutionMap.init(self.allocator);
        defer substitutions.deinit();
        for (call.arguments.items, function.parameters.items) |*argument, parameter| {
            const effects = try Semantics.SideEffectsCollector.collectExpression(
                self.dialect,
                argument,
                null,
            );
            if (!effects.movable()) return;
            const reference_count = if (references.get(.{ .user = parameter.name })) |count|
                count.*
            else
                0;
            const cost = try Metrics.CodeCost.codeCost(self.allocator, self.dialect, argument);
            if (reference_count > 1 and cost > 1) return;
            try substitutions.put(parameter.name, argument);
        }

        const assignment = switch (function.body.statements.items[0]) {
            .assignment => |*value| value,
            else => return error.InvalidInlinableFunction,
        };
        var substitution = SubstitutionModule.Substitution.init(self.allocator, &substitutions);
        var replacement = try substitution.translateExpression(
            assignment.value orelse return error.InvalidAst,
        );
        errdefer replacement.deinit(self.allocator);
        expression.deinit(self.allocator);
        expression.* = replacement;
    }
};

test "expression inliner substitutes cheap movable arguments" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a) -> r { r := add(a, 1) } pop(f(2)) }",
        "expression-inliner.yul",
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
    try ExpressionInliner.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "pop(add(2, 1))") != null);
}
