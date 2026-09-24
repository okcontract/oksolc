// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Removes assignments whose values are overwritten or leave scope unread.

const std = @import("std");
const AST = @import("../ast.zig");
const ControlFlowCollector = @import("../control_flow_side_effects_collector.zig").ControlFlowSideEffectsCollector;
const ControlFlowSideEffects = @import("../control_flow_side_effects.zig").ControlFlowSideEffects;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const OptimizerUtilities = @import("optimizer_utilities.zig");
const Semantics = @import("semantics.zig");
const UnusedStoreBaseModule = @import("unused_store_base.zig");
const Utilities = @import("../utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

const Base = UnusedStoreBaseModule.UnusedStoreBase(YulName);

pub const UnusedAssignEliminator = struct {
    allocator: std.mem.Allocator,
    base: Base,
    control_flow_side_effects: *const std.AutoHashMap(YulName, ControlFlowSideEffects),
    current_function: ?*const AST.FunctionDefinition = null,
    function_stack: std.ArrayList(?*const AST.FunctionDefinition) = .empty,

    pub const name = "UnusedAssignEliminator";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.scratchAllocator();
        var collector = try ControlFlowCollector.init(allocator, context.dialect, ast);
        defer collector.deinit();
        var named = try collector.functionSideEffectsNamed(allocator);
        defer named.deinit();

        var eliminator: UnusedAssignEliminator = .{
            .allocator = allocator,
            .base = Base.init(context.scratchBackingAllocator(), context.dialect),
            .control_flow_side_effects = &named,
        };
        defer eliminator.deinit();
        eliminator.base.hooks = .{
            .context = &eliminator,
            .identifier = visitIdentifier,
            .assignment = visitAssignment,
            .function_call = visitFunctionCall,
            .enter_function = enterFunction,
            .finalize_function = finalizeFunction,
            .leave_function = leaveFunction,
            .leave_statement = visitLeave,
            .after_block = afterBlock,
            .after_statement = afterStatement,
            .shortcut_nested_loop = shortcutNestedLoop,
        };
        try eliminator.base.run(ast);
        try eliminator.base.addCurrentUnusedStoresToRemoval();
        var to_remove = try eliminator.base.removalSet();
        defer to_remove.deinit();
        try OptimizerUtilities.StatementRemover.run(context.dispenser.allocator, ast, &to_remove);
    }

    fn deinit(self: *UnusedAssignEliminator) void {
        self.function_stack.deinit(self.allocator);
        self.base.deinit();
        self.* = undefined;
    }

    fn fromContext(context: ?*anyopaque) *UnusedAssignEliminator {
        return @ptrCast(@alignCast(context.?));
    }

    fn visitIdentifier(
        context: ?*anyopaque,
        base: *Base,
        identifier: *const AST.Identifier,
    ) anyerror!void {
        _ = context;
        try markUsed(base, identifier.name);
    }

    fn visitAssignment(
        _: ?*anyopaque,
        base: *Base,
        assignment: *const AST.Assignment,
    ) anyerror!bool {
        try base.visitExpression(assignment.value orelse return error.InvalidAst);
        return true;
    }

    fn visitFunctionCall(
        context: ?*anyopaque,
        base: *Base,
        call: *const AST.FunctionCall,
    ) anyerror!void {
        const self = fromContext(context);
        const effects = if (try Utilities.resolveBuiltinFunction(&call.function_name, base.dialect)) |builtin|
            builtin.control_flow_side_effects
        else switch (call.function_name) {
            .identifier => |identifier| self.control_flow_side_effects.get(identifier.name) orelse
                return error.UnknownFunction,
            .builtin => unreachable,
        };
        if (!effects.can_continue) base.clearAllActive();
    }

    fn enterFunction(
        context: ?*anyopaque,
        _: *Base,
        function: *const AST.FunctionDefinition,
    ) anyerror!void {
        const self = fromContext(context);
        try self.function_stack.append(self.allocator, self.current_function);
        self.current_function = function;
    }

    fn finalizeFunction(
        _: ?*anyopaque,
        base: *Base,
        function: *const AST.FunctionDefinition,
    ) anyerror!void {
        for (function.return_variables.items) |variable| try markUsed(base, variable.name);
    }

    fn leaveFunction(
        context: ?*anyopaque,
        _: *Base,
        _: *const AST.FunctionDefinition,
    ) anyerror!void {
        const self = fromContext(context);
        self.current_function = self.function_stack.pop().?;
    }

    fn visitLeave(
        context: ?*anyopaque,
        base: *Base,
        _: *const AST.Leave,
    ) anyerror!void {
        const self = fromContext(context);
        if (self.current_function) |function|
            for (function.return_variables.items) |variable| try markUsed(base, variable.name);
        base.clearAllActive();
    }

    fn afterBlock(
        _: ?*anyopaque,
        base: *Base,
        block: *const AST.Block,
    ) anyerror!void {
        for (block.statements.items) |*statement| switch (statement.*) {
            .variable_declaration => |*declaration| for (declaration.variables.items) |variable| {
                if (base.active_stores.fetchRemove(variable.name)) |removed| {
                    var stores = removed.value;
                    stores.deinit();
                }
            },
            else => {},
        };
    }

    fn afterStatement(
        _: ?*anyopaque,
        base: *Base,
        statement: *const AST.Statement,
    ) anyerror!void {
        const assignment = switch (statement.*) {
            .assignment => |*value| value,
            else => return,
        };
        var effects = try Semantics.SideEffectsCollector.collectExpression(
            base.dialect,
            assignment.value orelse return error.InvalidAst,
            null,
        );
        if (effects.movable()) {
            try base.all_stores.put(statement, {});
            for (assignment.variable_names.items) |variable|
                try base.replaceActiveWithStatement(variable.name, statement);
        } else {
            for (assignment.variable_names.items) |variable|
                try base.clearActiveKey(variable.name);
        }
    }

    fn shortcutNestedLoop(
        _: ?*anyopaque,
        base: *Base,
        zero_runs: *const Base.ActiveStores,
    ) anyerror!void {
        var active = base.active_stores.iterator();
        while (active.next()) |entry| {
            const before = zero_runs.get(entry.key_ptr.*);
            var stores = entry.value_ptr.keyIterator();
            while (stores.next()) |statement|
                if (before == null or !before.?.contains(statement.*))
                    try base.used_stores.put(statement.*, {});
        }
    }

    fn markUsed(base: *Base, variable: YulName) !void {
        try base.markKeyUsed(variable);
    }
};

test "unused assignment eliminator respects branch reads and overwrites" {
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
        "{ let a := 0 a := 1 a := 2 if a { a := 3 } a := 4 pop(a) }",
        "unused-assign.yul",
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
    try UnusedAssignEliminator.run(&context, &ast.root_block);
    try std.testing.expectEqual(@as(usize, 5), ast.root().statements.items.len);
}
