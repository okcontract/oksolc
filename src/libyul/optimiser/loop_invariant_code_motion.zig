// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Hoists movable SSA declarations out of Yul loop bodies and post blocks.

const std = @import("std");
const AST = @import("../ast.zig");
const ASTWalker = @import("ast_walker.zig").ASTWalker;
const NameCollector = @import("name_collector.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");
const SSAValueTracker = @import("ssa_value_tracker.zig").SSAValueTracker;

pub const LoopInvariantCodeMotion = struct {
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    ssa_variables: *const NameCollector.NameSet,
    function_side_effects: *const Semantics.FunctionSideEffects,
    contains_msize: bool,

    pub const name = "LoopInvariantCodeMotion";
    pub const preserves_function_analysis = true;

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        const scratch_allocator = context.scratchAllocator();
        var function_analysis = try context.functionAnalysis(ast);
        defer function_analysis.deinit();
        var ssa_variables = try SSAValueTracker.ssaVariables(scratch_allocator, ast);
        defer ssa_variables.deinit(scratch_allocator);
        var mover: LoopInvariantCodeMotion = .{
            .allocator = allocator,
            .scratch_allocator = scratch_allocator,
            .dialect = context.dialect,
            .ssa_variables = &ssa_variables,
            .function_side_effects = function_analysis.sideEffects(),
            .contains_msize = try Semantics.MSizeFinder.containsMSize(context.dialect, ast),
        };
        try mover.visitBlock(ast);
    }

    fn visitBlock(self: *LoopInvariantCodeMotion, block: *AST.Block) anyerror!void {
        var index: usize = 0;
        while (index < block.statements.items.len) {
            try self.visitStatementChildren(&block.statements.items[index]);
            if (block.statements.items[index] == .for_loop) {
                var promoted = try self.rewriteLoop(&block.statements.items[index].for_loop);
                defer deinitStatements(self.allocator, &promoted);
                if (promoted.items.len != 0) {
                    try promoted.ensureUnusedCapacity(self.allocator, 1);
                    try block.statements.ensureUnusedCapacity(self.allocator, promoted.items.len);
                    const loop_statement = block.statements.orderedRemove(index);
                    promoted.appendAssumeCapacity(loop_statement);
                    block.statements.insertSliceAssumeCapacity(index, promoted.items);
                    const inserted = promoted.items.len;
                    promoted.clearRetainingCapacity();
                    index += inserted;
                    continue;
                }
            }
            index += 1;
        }
    }

    fn visitStatementChildren(
        self: *LoopInvariantCodeMotion,
        statement: *AST.Statement,
    ) anyerror!void {
        switch (statement.*) {
            .function_definition => |*function| try self.visitBlock(&function.body),
            .if_statement => |*if_statement| try self.visitBlock(&if_statement.body),
            .switch_statement => |*switch_statement| for (switch_statement.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*loop| {
                try self.visitBlock(&loop.pre);
                try self.visitBlock(&loop.post);
                try self.visitBlock(&loop.body);
            },
            .block => |*nested| try self.visitBlock(nested),
            else => {},
        }
    }

    fn canBePromoted(
        self: *LoopInvariantCodeMotion,
        declaration: *const AST.VariableDeclaration,
        variables_defined_in_scope: *const NameCollector.NameSet,
        loop_side_effects: @import("../side_effects.zig").SideEffects,
    ) anyerror!bool {
        for (declaration.variables.items) |variable|
            if (!self.ssa_variables.contains(variable.name)) return false;
        if (declaration.value) |expression| {
            if (!ReferenceAvailability.check(expression, self.ssa_variables, variables_defined_in_scope))
                return false;
            const effects = try Semantics.SideEffectsCollector.collectExpression(
                self.dialect,
                expression,
                self.function_side_effects,
            );
            if (!effects.movableRelativeTo(loop_side_effects, self.contains_msize))
                return false;
        }
        return true;
    }

    /// Removes promotable declarations from post/body and returns them in
    /// upstream order. The caller appends the still-owned loop statement.
    fn rewriteLoop(
        self: *LoopInvariantCodeMotion,
        loop: *AST.ForLoop,
    ) anyerror!std.ArrayList(AST.Statement) {
        if (loop.pre.statements.items.len != 0) return error.ForLoopInitRewriterNotRun;
        const loop_effects = (try Semantics.SideEffectsCollector.collectForLoop(
            self.dialect,
            loop,
            self.function_side_effects,
        )).sideEffects();
        var promoted: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(self.allocator, &promoted);
        for ([2]*AST.Block{ &loop.post, &loop.body }) |candidate_block| {
            var variables_defined_in_scope: NameCollector.NameSet = .{};
            defer variables_defined_in_scope.deinit(self.scratch_allocator);
            var index: usize = 0;
            while (index < candidate_block.statements.items.len) {
                const statement = &candidate_block.statements.items[index];
                if (statement.* == .variable_declaration) {
                    const declaration = &statement.variable_declaration;
                    if (try self.canBePromoted(
                        declaration,
                        &variables_defined_in_scope,
                        loop_effects,
                    )) {
                        var moved = candidate_block.statements.orderedRemove(index);
                        errdefer moved.deinit(self.allocator);
                        try promoted.append(self.allocator, moved);
                        continue;
                    }
                    for (declaration.variables.items) |variable|
                        _ = try variables_defined_in_scope.insert(
                            self.scratch_allocator,
                            variable.name,
                        );
                }
                index += 1;
            }
        }
        return promoted;
    }
};

/// Promotion needs availability for every referenced name. Duplicate occurrences
/// do not change the result, so no reference-count map is needed.
const ReferenceAvailability = struct {
    ssa_variables: *const NameCollector.NameSet,
    variables_defined_in_scope: *const NameCollector.NameSet,
    available: bool = true,

    fn check(expression: *const AST.Expression, ssa: *const NameCollector.NameSet, scoped: *const NameCollector.NameSet) bool {
        var state: ReferenceAvailability = .{ .ssa_variables = ssa, .variables_defined_in_scope = scoped };
        var walker = ASTWalker.init(&state, .{ .identifier = visitIdentifier });
        walker.visitExpression(expression);
        return state.available;
    }

    fn visitIdentifier(context: ?*anyopaque, _: *ASTWalker, identifier: *const AST.Identifier) void {
        const self: *ReferenceAvailability = @ptrCast(@alignCast(context.?));
        self.available = self.available and
            !self.variables_defined_in_scope.contains(identifier.name) and
            self.ssa_variables.contains(identifier.name);
    }
};

fn deinitStatements(
    allocator: std.mem.Allocator,
    statements: *std.ArrayList(AST.Statement),
) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(allocator);
}

test "loop-invariant SSA declarations move before their loop" {
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
        "{ let outer := 1 for {} 1 {} { let invariant := add(outer, 2) pop(invariant) } }",
        "licm.yul",
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
    try LoopInvariantCodeMotion.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    const declaration = std.mem.find(u8, rendered, "let invariant").?;
    const loop_keyword = std.mem.find(u8, rendered, "for").?;
    try std.testing.expect(declaration < loop_keyword);
}

test "loop-invariant reference checks match counted references without materialization" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const YulName = @import("../yul_name.zig").YulName;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let r := user(outer, add(outer, scoped)) let c := add(1, 2) }",
        "loop-references.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    const names = [_]YulName{ try YulName.init("outer"), try YulName.init("scoped"), try YulName.init("unused") };
    for (ast.root().statements.items) |*statement| {
        const expression = statement.variable_declaration.value.?;
        var references = try NameCollector.VariableReferencesCounter.countReferencesExpression(allocator, expression);
        defer references.deinit(allocator);
        for (0..8) |ssa_mask| {
            for (0..8) |scope_mask| {
                var ssa: NameCollector.NameSet = .{};
                defer ssa.deinit(allocator);
                var scoped: NameCollector.NameSet = .{};
                defer scoped.deinit(allocator);
                for (names, 0..) |name, index| {
                    const bit = @as(usize, 1) << @intCast(index);
                    if (ssa_mask & bit != 0) _ = try ssa.insert(allocator, name);
                    if (scope_mask & bit != 0) _ = try scoped.insert(allocator, name);
                }
                var expected = true;
                for (references.items()) |entry|
                    if (scoped.contains(entry.key) or !ssa.contains(entry.key)) {
                        expected = false;
                        break;
                    };
                try std.testing.expectEqual(expected, ReferenceAvailability.check(expression, &ssa, &scoped));
            }
        }
    }
}
