// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Removes memory and storage writes that repeat the currently known value.

const std = @import("std");
const AST = @import("../ast.zig");
const CallGraph = @import("call_graph_generator.zig");
const DataFlow = @import("data_flow_analyzer.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const OptimizerUtilities = @import("optimizer_utilities.zig");
const Semantics = @import("semantics.zig");

pub const EqualStoreEliminator = struct {
    const Self = @This();
    const Analyzer = DataFlow.DataFlowAnalyzer(Self, .analyze);

    allocator: std.mem.Allocator,
    analyzer: Analyzer,
    pending_removals: OptimizerUtilities.StatementSet,

    pub const name = "EqualStoreEliminator";

    pub fn run(context: *const OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        var graph = try CallGraph.CallGraphGenerator.callGraph(allocator, ast);
        defer graph.deinit();
        var function_side_effects = try Semantics.SideEffectsPropagator.sideEffects(
            allocator,
            context.dialect,
            &graph,
        );
        defer function_side_effects.deinit(allocator);
        var eliminator: EqualStoreEliminator = .{
            .allocator = allocator,
            .analyzer = Analyzer.init(
                allocator,
                context.dialect,
                &function_side_effects,
            ),
            .pending_removals = OptimizerUtilities.StatementSet.init(allocator),
        };
        defer eliminator.deinit();
        try eliminator.analyzer.run(&eliminator, ast);
        try OptimizerUtilities.StatementRemover.run(
            allocator,
            ast,
            &eliminator.pending_removals,
        );
    }

    fn deinit(self: *EqualStoreEliminator) void {
        self.pending_removals.deinit();
        self.analyzer.deinit();
        self.* = undefined;
    }

    pub fn beforeStatement(
        self: *Self,
        analyzer: *Analyzer,
        statement: *const AST.Statement,
    ) anyerror!void {
        const expression_statement = switch (statement.*) {
            .expression_statement => |*value| value,
            else => return,
        };
        if (analyzer.isSimpleStore(.storage, expression_statement)) |variables| {
            if (analyzer.storageValue(variables.first)) |current|
                if (current.eql(variables.second)) try self.pending_removals.put(statement, {});
            return;
        }
        if (analyzer.isSimpleStore(.memory, expression_statement)) |variables|
            if (analyzer.memoryValue(variables.first)) |current|
                if (current.eql(variables.second)) try self.pending_removals.put(statement, {});
    }
};

test "equal store eliminator removes only the repeated simple write" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const NameCollector = @import("name_collector.zig");
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let p := 0 let v := 1 mstore(p, v) mstore(p, v) }",
        "equal-store.yul",
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
    const context: OptimiserStepContext = .{
        .dialect = dialect.dialect(),
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    try EqualStoreEliminator.run(&context, &ast.root_block);
    try std.testing.expectEqual(@as(usize, 3), ast.root().statements.items.len);
}
