// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Data-flow-aware application of the ordered Yul simplification rules.

const std = @import("std");
const SemanticInformation = @import("../../libevmasm/semantic_information.zig");
const AST = @import("../ast.zig");
const DataFlow = @import("data_flow_analyzer.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const SimplificationRulesModule = @import("simplification_rules.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const ExpressionSimplifier = struct {
    const Self = @This();
    const Analyzer = DataFlow.DataFlowAnalyzer(Self, .ignore);

    allocator: std.mem.Allocator,
    analyzer: Analyzer,

    pub const name = "ExpressionSimplifier";

    pub fn init(allocator: std.mem.Allocator, dialect: AST.Dialect) ExpressionSimplifier {
        return .{
            .allocator = allocator,
            .analyzer = Analyzer.init(allocator, dialect, null),
        };
    }

    pub fn deinit(self: *ExpressionSimplifier) void {
        self.analyzer.deinit();
        self.* = undefined;
    }

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var simplifier = ExpressionSimplifier.init(context.dispenser.allocator, context.dialect);
        defer simplifier.deinit();
        try simplifier.analyzer.run(&simplifier, ast);
    }

    pub fn visitExpression(
        self: *Self,
        analyzer: *Analyzer,
        expression: *AST.Expression,
    ) anyerror!DataFlow.ExpressionVisit {
        // Descendants are simplified first, in reverse argument evaluation
        // order, just like ASTModifier::visit in the C++ implementation.
        try analyzer.baseVisitExpression(expression);

        var modified = false;
        while (try SimplificationRulesModule.SimplificationRules.findFirstMatch(
            self.allocator,
            expression,
            analyzer.dialect,
            .{ .context = self, .resolve = resolveSSAValue },
        )) |replacement_value| {
            var replacement = replacement_value;
            errdefer replacement.deinit(self.allocator);
            expression.deinit(self.allocator);
            expression.* = replacement;
            modified = true;
        }

        if (SimplificationRulesModule.SimplificationRules.instructionAndArguments(
            analyzer.dialect,
            expression,
        )) |operation| {
            const operations = try SemanticInformation.readWriteOperations(operation.instruction);
            for (operations.slice()) |read_write| {
                const start_index = read_write.start_parameter orelse continue;
                const length_index = read_write.length_parameter orelse continue;
                if (start_index >= operation.arguments.len or length_index >= operation.arguments.len)
                    return error.InvalidBuiltinArity;
                const call = &expression.function_call;
                const start_argument = &call.arguments.items[start_index];
                const length_argument = &call.arguments.items[length_index];
                if (try self.knownToBeZero(length_argument) and
                    !try self.knownToBeZero(start_argument) and
                    start_argument.* != .function_call)
                {
                    const debug_data = if (start_argument.debugData()) |value| value.* else null;
                    start_argument.deinit(self.allocator);
                    start_argument.* = .{ .literal = .{
                        .debug_data = debug_data,
                        .kind = .Number,
                        .value = try AST.LiteralValue.initNumeric(self.allocator, 0, null),
                    } };
                    modified = true;
                }
            }
        }
        return if (modified) .modified else .handled;
    }

    fn resolveSSAValue(
        opaque_context: ?*const anyopaque,
        variable: YulName,
    ) anyerror!?*const DataFlow.AssignedValue {
        const self: *const ExpressionSimplifier = @ptrCast(@alignCast(opaque_context.?));
        const value = self.analyzer.variableValue(variable) orelse return null;
        if (value.value == null) return null;

        const references = self.analyzer.sortedReferences(variable) orelse return null;
        for (0..references.len()) |index|
            if (!self.analyzer.inScope(references.at(index))) return null;
        return value;
    }

    fn knownToBeZero(
        self: *const ExpressionSimplifier,
        expression: *const AST.Expression,
    ) anyerror!bool {
        return switch (expression.*) {
            .literal => |*literal| (literal.value.value() catch return false) == 0,
            .identifier => |identifier| (try self.analyzer.valueOfIdentifier(identifier.name)) == 0,
            .function_call => false,
        };
    }
};

test "expression simplifier folds constants through tracked declarations" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const NameCollector = @import("name_collector.zig");
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
        "{ let x := 2 let y := add(x, 3) pop(mul(y, 1)) }",
        "expression-simplifier.yul",
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
    try ExpressionSimplifier.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "let y := 5") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "pop(5)") != null);
}
