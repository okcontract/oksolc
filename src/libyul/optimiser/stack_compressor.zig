// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Stack-pressure reduction by targeted rematerialisation.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const ASTCopier = @import("ast_copier.zig").ASTCopier;
const AsmAnalysis = @import("../asm_analysis.zig");
const Compilability = @import("../compilability_checker.zig");
const ControlFlowGraphBuilder = @import("../backends/evm/control_flow_graph_builder.zig").ControlFlowGraphBuilder;
const DataFlow = @import("data_flow_analyzer.zig");
const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
const Metrics = @import("metrics.zig");
const NameCollectorModule = @import("name_collector.zig");
const Object = @import("../object.zig").Object;
const Rematerialiser = @import("rematerialiser.zig").Rematerialiser;
const Semantics = @import("semantics.zig");
const StackLayout = @import("../backends/evm/stack_layout_generator.zig");
const UnusedPruner = @import("unused_pruner.zig").UnusedPruner;
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

const CostMap = ordered.OrderedMap(YulName, usize, lessYulName);
const ReferenceCountMap = ordered.OrderedMap(YulName, usize, lessYulName);

const Candidate = struct {
    function_name: YulName,
    variable: YulName,
    occurrence: usize,
};

const RankedCandidate = struct {
    variable: YulName,
    cost: usize,
    occurrence: usize,
};

/// Discovers variables whose movable assigned expression remains available at
/// every reference. Candidate occurrence order is retained for equal costs.
const RematCandidateSelector = struct {
    const Self = @This();
    const Analyzer = DataFlow.DataFlowAnalyzer(Self, .ignore);

    allocator: std.mem.Allocator,
    analyzer: Analyzer,
    current_function_name: YulName = .{},
    candidates: std.ArrayList(Candidate) = .empty,
    expression_code_cost: CostMap = .{},
    num_references: ReferenceCountMap = .{},

    fn init(allocator: std.mem.Allocator, dialect: AST.Dialect) RematCandidateSelector {
        return .{
            .allocator = allocator,
            .analyzer = Analyzer.init(allocator, dialect, null),
        };
    }

    fn deinit(self: *RematCandidateSelector) void {
        self.analyzer.deinit();
        self.candidates.deinit(self.allocator);
        self.expression_code_cost.deinit(self.allocator);
        self.num_references.deinit(self.allocator);
        self.* = undefined;
    }

    fn run(self: *RematCandidateSelector, ast: *AST.Block) !void {
        try self.analyzer.run(self, ast);
    }

    pub fn visitFunction(
        self: *Self,
        analyzer: *Analyzer,
        function: *AST.FunctionDefinition,
    ) anyerror!bool {
        if (!self.current_function_name.empty()) return error.NestedFunctionDefinition;
        self.current_function_name = function.name;
        defer self.current_function_name = .{};
        try analyzer.baseVisitFunction(function);
        return true;
    }

    pub fn beforeStatement(
        self: *Self,
        _: *Analyzer,
        statement: *const AST.Statement,
    ) anyerror!void {
        switch (statement.*) {
            .assignment => |*assignment| for (assignment.variable_names.items) |variable|
                self.rematImpossible(variable.name),
            else => {},
        }
    }

    pub fn afterStatement(
        self: *Self,
        analyzer: *Analyzer,
        statement: *const AST.Statement,
    ) anyerror!void {
        const declaration = switch (statement.*) {
            .variable_declaration => |*value| value,
            else => return,
        };
        if (declaration.variables.items.len != 1) return;
        const variable = declaration.variables.items[0].name;
        const assigned = analyzer.variableValue(variable) orelse return;
        const expression = assigned.value orelse return;
        if (self.expression_code_cost.contains(variable)) return error.DuplicateRematCandidate;
        try self.candidates.append(self.allocator, .{
            .function_name = self.current_function_name,
            .variable = variable,
            .occurrence = self.candidates.items.len,
        });
        _ = try self.expression_code_cost.insert(
            self.allocator,
            variable,
            try Metrics.CodeCost.codeCost(self.allocator, analyzer.dialect, expression),
        );
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
        if (!self.expression_code_cost.contains(identifier.name)) return .descend;
        if (analyzer.variableValue(identifier.name) == null) {
            self.rematImpossible(identifier.name);
        } else if (self.num_references.getPtr(identifier.name)) |count| {
            count.* += 1;
        } else {
            _ = try self.num_references.insert(self.allocator, identifier.name, 1);
        }
        return .descend;
    }

    fn rematImpossible(self: *RematCandidateSelector, variable: YulName) void {
        _ = self.num_references.remove(variable);
        _ = self.expression_code_cost.remove(variable);
    }

    fn totalCost(self: *const RematCandidateSelector, variable: YulName) ?usize {
        const expression_cost = self.expression_code_cost.get(variable) orelse return null;
        const references = self.num_references.get(variable);
        return expression_cost.* *| if (references) |count| count.* else 0;
    }
};

pub const RunResult = struct {
    success: bool,
    ast: AST.Block,

    pub fn deinit(self: *RunResult, allocator: std.mem.Allocator) void {
        self.ast.deinit(allocator);
        self.* = undefined;
    }
};

pub const StackCompressor = struct {
    pub fn run(
        allocator: std.mem.Allocator,
        object: *const Object,
        optimize_stack_allocation: bool,
        max_iterations: usize,
    ) !RunResult {
        const code = object.code() orelse return error.MissingObjectCode;
        const dialect = object.dialect() orelse return error.MissingDialect;
        if (code.root().statements.items.len == 0 or
            code.root().statements.items[0] != .block)
            return error.FunctionGrouperNotRun;

        const evm_dialect = EVMDialectModule.fromDialect(dialect.*);
        const use_optimized_codegen = if (evm_dialect) |evm|
            optimize_stack_allocation and
                evm.evmVersion().canOverchargeGasForCall() and
                evm.providesObjectAccess()
        else
            false;
        const allow_msize_optimization = !try Semantics.MSizeFinder.containsMSize(
            dialect.*,
            code.root(),
        );

        var copier = ASTCopier.init(allocator);
        var ast_root = try copier.translateBlock(code.root());
        errdefer ast_root.deinit(allocator);

        if (use_optimized_codegen) {
            const evm = evm_dialect.?;
            var structure = try object.summarizeStructure();
            defer structure.deinit();
            var analysis_info = try AsmAnalysis.analyzeStrictBlock(
                allocator,
                dialect.*,
                &ast_root,
                &structure,
                AsmAnalysis.instructionValidatorForEVMDialect(evm),
            );
            defer analysis_info.deinit();
            var cfg = try ControlFlowGraphBuilder.build(
                allocator,
                &analysis_info,
                dialect.*,
                &ast_root,
            );
            defer cfg.deinit();
            var unreachables = try StackLayout.StackLayoutGenerator.reportStackTooDeepAll(
                allocator,
                &cfg,
                evm,
            );
            defer StackLayout.deinitStackTooDeepByFunction(allocator, &unreachables);
            try eliminateVariablesOptimizedCodegen(
                allocator,
                dialect.*,
                &ast_root,
                &unreachables,
                allow_msize_optimization,
            );
        } else {
            for (0..max_iterations) |_| {
                var checker = try Compilability.CompilabilityChecker.initWithBlock(
                    allocator,
                    object,
                    &ast_root,
                    optimize_stack_allocation,
                );
                defer checker.deinit();
                if (checker.stackDeficit().isEmpty())
                    return .{ .success = true, .ast = ast_root };
                try eliminateVariables(
                    allocator,
                    dialect.*,
                    &ast_root,
                    checker.stackDeficit(),
                    allow_msize_optimization,
                );
            }
        }
        return .{ .success = false, .ast = ast_root };
    }
};

fn rankedLessThan(_: void, left: RankedCandidate, right: RankedCandidate) bool {
    if (left.cost != right.cost) return left.cost < right.cost;
    return left.occurrence < right.occurrence;
}

fn rankedCandidatesForFunction(
    allocator: std.mem.Allocator,
    selector: *const RematCandidateSelector,
    function_name: YulName,
) !std.ArrayList(RankedCandidate) {
    var result: std.ArrayList(RankedCandidate) = .empty;
    errdefer result.deinit(allocator);
    for (selector.candidates.items) |candidate| {
        if (!candidate.function_name.eql(function_name)) continue;
        const cost = selector.totalCost(candidate.variable) orelse continue;
        try result.append(allocator, .{
            .variable = candidate.variable,
            .cost = cost,
            .occurrence = candidate.occurrence,
        });
    }
    std.sort.insertion(RankedCandidate, result.items, {}, rankedLessThan);
    return result;
}

fn selectOptimizedCodegenCandidates(
    allocator: std.mem.Allocator,
    selected: *NameCollectorModule.NameSet,
    ranked: []const RankedCandidate,
    initial_needed_slots: usize,
) !void {
    var needed_slots = initial_needed_slots;
    var group_start: usize = 0;
    while (group_start < ranked.len) {
        var group_end = group_start + 1;
        while (group_end < ranked.len and ranked[group_end].cost == ranked[group_start].cost)
            group_end += 1;

        // Preserve the upstream cost-bucket loop and its size_t post-decrement
        // exactly. When a bucket has another candidate after the deficit reaches
        // zero, the failed condition wraps needed_slots and advances to the next
        // cost bucket. Changing this alters rematerialisation and bytecode.
        for (ranked[group_start..group_end]) |candidate| {
            const eliminate = needed_slots != 0;
            needed_slots -%= 1;
            if (!eliminate) break;
            _ = try selected.insert(allocator, candidate.variable);
        }
        if (needed_slots == 0) break;
        group_start = group_end;
    }
}

fn eliminateVariables(
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    ast: *AST.Block,
    deficits: *const Compilability.StackDeficit,
    allow_msize_optimization: bool,
) !void {
    var selector = RematCandidateSelector.init(allocator, dialect);
    defer selector.deinit();
    try selector.run(ast);

    var variables: NameCollectorModule.NameSet = .{};
    defer variables.deinit(allocator);
    for (deficits.items()) |entry| {
        if (entry.value <= 0) return error.InvalidStackDeficit;
        var ranked = try rankedCandidatesForFunction(allocator, &selector, entry.key);
        defer ranked.deinit(allocator);
        const count: usize = @intCast(entry.value);
        for (ranked.items[0..@min(count, ranked.items.len)]) |candidate|
            _ = try variables.insert(allocator, candidate.variable);
    }

    try Rematerialiser.apply(allocator, dialect, ast, &variables, false);
    try prunePreservingFunctions(allocator, dialect, ast, allow_msize_optimization);
}

fn eliminateVariablesOptimizedCodegen(
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    ast: *AST.Block,
    unreachables: *const StackLayout.StackTooDeepByFunction,
    allow_msize_optimization: bool,
) !void {
    var any_unreachable = false;
    var values = unreachables.valueIterator();
    while (values.next()) |errors| any_unreachable = any_unreachable or errors.items.len != 0;
    if (!any_unreachable) return;

    var selector = RematCandidateSelector.init(allocator, dialect);
    defer selector.deinit();
    try selector.run(ast);

    var variables: NameCollectorModule.NameSet = .{};
    defer variables.deinit(allocator);
    var iterator = unreachables.iterator();
    while (iterator.next()) |entry| for (entry.value_ptr.items) |stack_error| {
        var ranked: std.ArrayList(RankedCandidate) = .empty;
        defer ranked.deinit(allocator);
        var needed_slots = stack_error.deficit;
        for (stack_error.variable_choices.items, 0..) |variable, occurrence| {
            if (variables.contains(variable)) {
                needed_slots -%= 1;
                continue;
            }
            const cost = selector.totalCost(variable) orelse continue;
            var duplicate = false;
            for (ranked.items) |candidate| if (candidate.variable.eql(variable)) {
                duplicate = true;
                break;
            };
            if (!duplicate) try ranked.append(allocator, .{
                .variable = variable,
                .cost = cost,
                .occurrence = occurrence,
            });
        }
        std.sort.insertion(RankedCandidate, ranked.items, {}, rankedLessThan);
        try selectOptimizedCodegenCandidates(allocator, &variables, ranked.items, needed_slots);
    };

    try Rematerialiser.apply(allocator, dialect, ast, &variables, true);
    try prunePreservingFunctions(allocator, dialect, ast, allow_msize_optimization);
}

fn prunePreservingFunctions(
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    ast: *AST.Block,
    allow_msize_optimization: bool,
) !void {
    var functions = try NameCollectorModule.NameCollector.initBlock(
        allocator,
        ast,
        .only_functions,
    );
    defer functions.deinit();
    try UnusedPruner.runUntilStabilised(
        allocator,
        dialect,
        ast,
        allow_msize_optimization,
        null,
        functions.names(),
    );
}

test "optimized candidate buckets preserve upstream post-decrement behavior" {
    const allocator = std.testing.allocator;
    const first = try YulName.init("first");
    const skipped = try YulName.init("skipped");
    const later_bucket = try YulName.init("later_bucket");
    const ranked = [_]RankedCandidate{
        .{ .variable = first, .cost = 4, .occurrence = 0 },
        .{ .variable = skipped, .cost = 4, .occurrence = 1 },
        .{ .variable = later_bucket, .cost = 35, .occurrence = 2 },
    };
    var selected: NameCollectorModule.NameSet = .{};
    defer selected.deinit(allocator);

    try selectOptimizedCodegenCandidates(allocator, &selected, &ranked, 1);

    try std.testing.expect(selected.contains(first));
    try std.testing.expect(!selected.contains(skipped));
    try std.testing.expect(selected.contains(later_bucket));
}

test "classic stack compression rematerializes a deeply buried value" {
    const AsmParser = @import("../asm_parser.zig");
    const AsmPrinter = @import("../asm_printer.zig");
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(
        allocator,
        EVMVersion.init(.Homestead),
        false,
    );
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const source =
        "{ { let x := 8 let y := calldataload(calldataload(9)) " ++
        "mstore(y, add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(y, 1), 1), 1), 1), 1), 1), 1), 1), 1), 1), 1), 1), 1), 1), 1), 1), 1), 1)) } }";
    var ast = (try AsmParser.Parser.parseSource(
        allocator,
        source,
        "stack-compressor.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )) orelse return error.ParserRejectedStackCompressorTest;
    const object = try Object.create(allocator, "");
    defer object.destroy();
    object.setCode(ast, null);
    ast = undefined;

    var result = try StackCompressor.run(allocator, object, true, 16);
    defer result.deinit(allocator);
    try std.testing.expect(result.success);
    var printer = AsmPrinter.AsmPrinter.init(
        allocator,
        dialect.dialect(),
        &.{},
        .defaultValue(),
        null,
    );
    const rendered = try printer.renderBlock(&result.ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "let y") == null);
    try std.testing.expect(std.mem.count(u8, rendered, "calldataload(calldataload(9))") >= 2);
}
