// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Replaces variable references by their current movable expressions when the
//! duplication cost and loop/scope constraints match upstream Yul semantics.

const std = @import("std");
const AST = @import("../ast.zig");
const ASTCopier = @import("ast_copier.zig").ASTCopier;
const DataFlow = @import("data_flow_analyzer.zig");
const Metrics = @import("metrics.zig");
const NameCollector = @import("name_collector.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const YulName = @import("../yul_name.zig").YulName;

pub const Rematerialiser = struct {
    const Self = @This();
    const Analyzer = DataFlow.DataFlowAnalyzer(Self, .ignore);

    allocator: std.mem.Allocator,
    analyzer: Analyzer,
    reference_counts: NameCollector.VariableReferenceMap,
    vars_to_always_rematerialize: ?*const NameCollector.NameSet,
    only_selected_variables: bool,

    pub const name = "Rematerialiser";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        try applyWithScratch(
            context.dispenser.allocator,
            context.scratchAllocator(),
            context.dialect,
            ast,
            null,
            false,
        );
    }

    pub inline fn apply(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *AST.Block,
        vars_to_always_rematerialize: ?*const NameCollector.NameSet,
        only_selected_variables: bool,
    ) anyerror!void {
        return applyWithScratch(allocator, allocator, dialect, ast, vars_to_always_rematerialize, only_selected_variables);
    }

    fn applyWithScratch(
        allocator: std.mem.Allocator,
        scratch_allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *AST.Block,
        vars_to_always_rematerialize: ?*const NameCollector.NameSet,
        only_selected_variables: bool,
    ) anyerror!void {
        var reference_counts = try NameCollector.VariableReferencesCounter.countReferencesBlock(
            scratch_allocator,
            ast,
        );
        errdefer reference_counts.deinit(scratch_allocator);
        var rematerialiser: Rematerialiser = .{
            .allocator = allocator,
            .analyzer = Analyzer.init(scratch_allocator, dialect, null),
            .reference_counts = reference_counts,
            .vars_to_always_rematerialize = vars_to_always_rematerialize,
            .only_selected_variables = only_selected_variables,
        };
        reference_counts = .{};
        defer rematerialiser.deinit();
        try rematerialiser.analyzer.run(&rematerialiser, ast);
    }

    fn deinit(self: *Rematerialiser) void {
        self.reference_counts.deinit(self.analyzer.allocator);
        self.analyzer.deinit();
        self.* = undefined;
    }

    pub fn visitExpression(
        self: *Self,
        analyzer: *Analyzer,
        expression: *AST.Expression,
    ) anyerror!DataFlow.ExpressionVisit {
        const identifier = switch (expression.*) {
            .identifier => |value| value,
            else => return .descend,
        };
        const variable = identifier.name;
        const assigned = analyzer.variableValue(variable) orelse return .descend;
        const assigned_expression = assigned.value orelse return error.InvalidAssignedValue;
        const references = if (self.reference_counts.get(variable)) |count| count.* else 0;
        const cost = try Metrics.CodeCost.codeCost(
            analyzer.allocator,
            analyzer.dialect,
            assigned_expression,
        );
        const selected = if (self.vars_to_always_rematerialize) |variables|
            variables.contains(variable)
        else
            false;
        const eligible = ((!self.only_selected_variables and
            ((references <= 1 and assigned.loop_depth == analyzer.currentLoopDepth()) or
                cost == 0 or
                (references <= 5 and cost <= 1 and analyzer.currentLoopDepth() == 0))) or
            selected);
        if (!eligible) return .descend;

        if (analyzer.sortedReferences(variable)) |sorted_references| {
            for (0..sorted_references.len()) |index|
                if (!analyzer.inScope(sorted_references.at(index))) return .descend;
        }

        const count = self.reference_counts.getPtr(variable) orelse return error.InvalidReferenceCount;
        if (count.* == 0) return error.InvalidReferenceCount;
        count.* -= 1;
        var nested_references = try NameCollector.VariableReferencesCounter.countReferencesExpression(
            analyzer.allocator,
            assigned_expression,
        );
        defer nested_references.deinit(analyzer.allocator);
        for (nested_references.items()) |entry| {
            if (self.reference_counts.getPtr(entry.key)) |existing|
                existing.* += entry.value
            else
                _ = try self.reference_counts.insert(analyzer.allocator, entry.key, entry.value);
        }

        var copier = ASTCopier.init(self.allocator);
        var replacement = try copier.translateExpression(assigned_expression);
        errdefer replacement.deinit(self.allocator);
        expression.deinit(self.allocator);
        expression.* = replacement;
        replacement = undefined;
        return .descend;
    }
};

pub const LiteralRematerialiser = struct {
    const Self = @This();
    const Analyzer = DataFlow.DataFlowAnalyzer(Self, .ignore);

    allocator: std.mem.Allocator,
    analyzer: Analyzer,

    pub const name = "LiteralRematerialiser";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        try applyWithScratch(context.dispenser.allocator, context.scratchAllocator(), context.dialect, ast);
    }

    pub inline fn apply(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *AST.Block,
    ) anyerror!void {
        return applyWithScratch(allocator, allocator, dialect, ast);
    }

    fn applyWithScratch(
        allocator: std.mem.Allocator,
        scratch_allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *AST.Block,
    ) anyerror!void {
        var rematerialiser: LiteralRematerialiser = .{
            .allocator = allocator,
            .analyzer = Analyzer.init(scratch_allocator, dialect, null),
        };
        defer rematerialiser.analyzer.deinit();
        try rematerialiser.analyzer.run(&rematerialiser, ast);
    }

    pub fn visitExpression(
        self: *Self,
        analyzer: *Analyzer,
        expression: *AST.Expression,
    ) anyerror!DataFlow.ExpressionVisit {
        const identifier = switch (expression.*) {
            .identifier => |value| value,
            else => return .descend,
        };
        const assigned = analyzer.variableValue(identifier.name) orelse return .descend;
        const assigned_expression = assigned.value orelse return error.InvalidAssignedValue;
        if (assigned_expression.* != .literal) return .descend;
        var copier = ASTCopier.init(self.allocator);
        var replacement = try copier.translateExpression(assigned_expression);
        errdefer replacement.deinit(self.allocator);
        expression.deinit(self.allocator);
        expression.* = replacement;
        replacement = undefined;
        return .descend;
    }
};

test "rematerialisers replace movable values and literal aliases" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := 7 let y := x pop(y) }",
        "rematerialise.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = .{},
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    try Rematerialiser.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "let y := 7") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "pop(7)") != null);
}
