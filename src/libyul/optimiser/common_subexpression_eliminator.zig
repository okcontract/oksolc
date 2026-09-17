// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Replaces expressions by in-scope variables currently holding an identical
//! movable value.

const std = @import("std");
const AST = @import("../ast.zig");
const DataFlow = @import("data_flow_analyzer.zig");
const NameCollector = @import("name_collector.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const SyntacticalEquality = @import("syntactical_equality.zig");
const Utilities = @import("../utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

const ExpressionKey = struct {
    expression: *const AST.Expression,
    hash_value: u64,
};

const ExpressionKeyContext = struct {
    pub fn hash(_: @This(), key: ExpressionKey) u64 {
        return key.hash_value;
    }

    pub fn eql(_: @This(), lhs: ExpressionKey, rhs: ExpressionKey) bool {
        return lhs.hash_value == rhs.hash_value and
            SyntacticalEquality.SyntacticallyEqualExpression.eqlNoAlloc(
                lhs.expression,
                rhs.expression,
            );
    }
};

const CandidateMap = std.HashMapUnmanaged(
    ExpressionKey,
    NameCollector.NameSet,
    ExpressionKeyContext,
    80,
);

pub const CommonSubexpressionEliminator = struct {
    const Self = @This();
    const Analyzer = DataFlow.DataFlowAnalyzer(Self, .ignore);

    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    analyzer: Analyzer,
    return_variables: NameCollector.NameSet = .{},
    replacement_candidates: CandidateMap = .empty,

    pub const name = "CommonSubexpressionEliminator";
    pub const tracks_expression_fingerprint = true;

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        const scratch_allocator = context.scratchAllocator();
        var function_analysis = try context.functionAnalysis(ast);
        defer function_analysis.deinit();
        var eliminator: CommonSubexpressionEliminator = .{
            .allocator = allocator,
            .scratch_allocator = scratch_allocator,
            .analyzer = Analyzer.init(
                scratch_allocator,
                context.dialect,
                function_analysis.sideEffects(),
            ),
        };
        defer eliminator.deinit();
        try eliminator.analyzer.run(&eliminator, ast);
    }

    fn deinit(self: *CommonSubexpressionEliminator) void {
        self.analyzer.deinit();
        self.return_variables.deinit(self.scratch_allocator);
        deinitCandidates(self.scratch_allocator, &self.replacement_candidates);
        self.* = undefined;
    }

    pub fn visitExpression(
        self: *Self,
        analyzer: *Analyzer,
        expression: *AST.Expression,
    ) anyerror!DataFlow.ExpressionVisit {
        var descend = true;
        if (expression.* == .function_call) {
            const call = &expression.function_call;
            if (try Utilities.resolveBuiltinFunction(&call.function_name, analyzer.dialect)) |builtin| {
                try analyzer.baseVisitExpressionSkippingLiteralArguments(
                    expression,
                    builtin,
                );
                descend = false;
            }
        }
        if (descend) try analyzer.baseVisitExpression(expression);

        if (expression.* == .identifier) {
            const identifier_name = expression.identifier.name;
            if (analyzer.variableValue(identifier_name)) |assigned| {
                const value = assigned.value orelse return error.InvalidAssignedValue;
                if (value.* == .identifier and analyzer.inScope(value.identifier.name)) {
                    expression.identifier.name = value.identifier.name;
                    return .modified;
                }
            }
            return .handled;
        }

        if (self.replacement_candidates.getPtr(try expressionKey(analyzer, expression))) |variables| {
            for (0..variables.len()) |index| {
                const variable = variables.at(index);
                const assigned = analyzer.variableValue(variable) orelse continue;
                const value = assigned.value orelse return error.InvalidAssignedValue;
                if (self.return_variables.contains(variable) and isZeroLiteral(value)) continue;
                if (analyzer.inScope(variable) and
                    SyntacticalEquality.SyntacticallyEqualExpression.eqlNoAlloc(expression, value))
                {
                    const debug_data = if (expression.debugData()) |data| data.* else null;
                    expression.deinit(self.allocator);
                    expression.* = .{ .identifier = .{
                        .debug_data = debug_data,
                        .name = variable,
                    } };
                    return .modified;
                }
            }
        }
        return .handled;
    }

    pub fn assignValue(
        self: *Self,
        analyzer: *Analyzer,
        variable: YulName,
        value: ?*const AST.Expression,
    ) anyerror!bool {
        if (value) |expression| try self.addCandidate(analyzer, expression, variable);
        try analyzer.baseAssignValue(variable, value);
        return true;
    }

    pub fn visitFunction(
        self: *Self,
        analyzer: *Analyzer,
        function: *AST.FunctionDefinition,
    ) anyerror!bool {
        const parent_return_variables = self.takeReturnVariables();
        const parent_candidates = self.takeReplacementCandidates();
        defer {
            self.return_variables.deinit(self.scratch_allocator);
            deinitCandidates(self.scratch_allocator, &self.replacement_candidates);
            self.return_variables = parent_return_variables;
            self.replacement_candidates = parent_candidates;
        }
        for (function.return_variables.items) |variable|
            _ = try self.return_variables.insert(self.scratch_allocator, variable.name);
        try analyzer.baseVisitFunction(function);
        return true;
    }

    fn takeReturnVariables(self: *CommonSubexpressionEliminator) NameCollector.NameSet {
        return self.return_variables.take();
    }

    fn takeReplacementCandidates(self: *CommonSubexpressionEliminator) CandidateMap {
        const result = self.replacement_candidates;
        self.replacement_candidates = .empty;
        return result;
    }

    fn addCandidate(
        self: *CommonSubexpressionEliminator,
        analyzer: *Analyzer,
        expression: *const AST.Expression,
        variable: YulName,
    ) anyerror!void {
        const result = try self.replacement_candidates.getOrPut(
            self.scratch_allocator,
            try expressionKey(analyzer, expression),
        );
        if (!result.found_existing) result.value_ptr.* = .{};
        _ = try result.value_ptr.insert(self.scratch_allocator, variable);
    }
};

fn isZeroLiteral(expression: *const AST.Expression) bool {
    return switch (expression.*) {
        .literal => |*literal| blk: {
            if (literal.value.unlimited()) break :blk false;
            const value = literal.value.numeric_value orelse break :blk false;
            break :blk value == 0;
        },
        else => false,
    };
}

fn expressionKey(analyzer: anytype, expression: *const AST.Expression) anyerror!ExpressionKey {
    return .{
        .expression = expression,
        .hash_value = try analyzer.expressionFingerprint(expression),
    };
}

fn deinitCandidates(allocator: std.mem.Allocator, candidates: *CandidateMap) void {
    var values = candidates.valueIterator();
    while (values.next()) |variables| variables.deinit(allocator);
    candidates.deinit(allocator);
}

test "zero-literal detection safely rejects unlimited literals" {
    const unlimited: AST.Expression = .{ .literal = .{
        .kind = .String,
        .value = .{},
    } };
    const zero: AST.Expression = .{ .literal = .{
        .kind = .Number,
        .value = .{ .numeric_value = 0 },
    } };
    try std.testing.expect(!isZeroLiteral(&unlimited));
    try std.testing.expect(isZeroLiteral(&zero));
}

test "common subexpression elimination reuses an in-scope movable value" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
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
        "{ let a := add(1, 2) let b := add(1, 2) pop(b) }",
        "cse.yul",
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
    try CommonSubexpressionEliminator.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "let b := a") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "pop(a)") != null);
}

test "common subexpression fingerprints follow rewritten aliases" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
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
        "{ let x := 1 let y := x let a := add(y, 2) let b := add(x, 2) pop(b) }",
        "cse-alias.yul",
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
    try CommonSubexpressionEliminator.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "let a := add(x, 2)") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "let b := a") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "pop(a)") != null);
}
