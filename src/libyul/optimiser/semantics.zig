// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Semantic fact collectors shared by the Yul optimizer.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const CallGraphModule = @import("call_graph_generator.zig");
const ControlFlowSideEffects = @import("../control_flow_side_effects.zig").ControlFlowSideEffects;
const NameCollectorModule = @import("name_collector.zig");
const Object = @import("../object.zig").Object;
const SideEffects = @import("../side_effects.zig").SideEffects;
const Utilities = @import("../utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

fn lessFunctionHandle(left: AST.FunctionHandle, right: AST.FunctionHandle) bool {
    const left_tag = @intFromEnum(left);
    const right_tag = @intFromEnum(right);
    if (left_tag != right_tag) return left_tag < right_tag;
    return switch (left) {
        .user => |name| name.lessThan(right.user),
        .builtin => |handle| handle.id < right.builtin.id,
    };
}

pub const FunctionSideEffects = ordered.OrderedMap(
    AST.FunctionHandle,
    SideEffects,
    lessFunctionHandle,
);
pub const NamedControlFlowSideEffects = std.AutoHashMap(YulName, ControlFlowSideEffects);

/// Returns only the effects introduced by the call itself. Argument effects
/// are deliberately excluded so post-order walkers can combine each child
/// exactly once.
pub fn functionCallSideEffects(
    dialect: AST.Dialect,
    function_side_effects: ?*const FunctionSideEffects,
    call: *const AST.FunctionCall,
) anyerror!SideEffects {
    if (try Utilities.resolveBuiltinFunction(&call.function_name, dialect)) |builtin|
        return builtin.side_effects;
    if (function_side_effects) |known| {
        const handle = Utilities.functionNameToHandle(&call.function_name);
        if (known.get(handle)) |effects| return effects.*;
    }
    return SideEffects.worst();
}

pub const SideEffectsCollector = struct {
    dialect: AST.Dialect,
    function_side_effects: ?*const FunctionSideEffects = null,
    effects: SideEffects = .{},

    pub fn init(
        dialect: AST.Dialect,
        function_side_effects: ?*const FunctionSideEffects,
    ) SideEffectsCollector {
        return .{ .dialect = dialect, .function_side_effects = function_side_effects };
    }

    pub fn collectExpression(
        dialect: AST.Dialect,
        expression: *const AST.Expression,
        function_side_effects: ?*const FunctionSideEffects,
    ) anyerror!SideEffectsCollector {
        var collector = init(dialect, function_side_effects);
        try collector.visitExpression(expression);
        return collector;
    }

    pub fn collectStatement(
        dialect: AST.Dialect,
        statement: *const AST.Statement,
    ) anyerror!SideEffectsCollector {
        var collector = init(dialect, null);
        try collector.visitStatement(statement);
        return collector;
    }

    pub fn collectBlock(
        dialect: AST.Dialect,
        block: *const AST.Block,
        function_side_effects: ?*const FunctionSideEffects,
    ) anyerror!SideEffectsCollector {
        var collector = init(dialect, function_side_effects);
        try collector.visitBlock(block);
        return collector;
    }

    pub fn collectForLoop(
        dialect: AST.Dialect,
        loop: *const AST.ForLoop,
        function_side_effects: ?*const FunctionSideEffects,
    ) anyerror!SideEffectsCollector {
        var collector = init(dialect, function_side_effects);
        try collector.visitForLoop(loop);
        return collector;
    }

    pub fn movable(self: *const SideEffectsCollector) bool {
        return self.effects.movable;
    }

    pub fn movableRelativeTo(
        self: *const SideEffectsCollector,
        other: SideEffects,
        code_contains_msize: bool,
    ) bool {
        if (!self.effects.cannot_loop) return false;
        if (self.effects.movable) return true;
        if (!self.effects.movable_apart_from_effects or
            self.effects.storage == .write or
            self.effects.other_state == .write or
            self.effects.memory == .write or
            self.effects.transient_storage == .write)
        {
            return false;
        }
        if (self.effects.other_state == .read and other.other_state == .write) return false;
        if (self.effects.storage == .read and other.storage == .write) return false;
        if (self.effects.memory == .read and (code_contains_msize or other.memory == .write)) return false;
        if (self.effects.transient_storage == .read and other.transient_storage == .write) return false;
        return true;
    }

    pub fn canBeRemoved(self: *const SideEffectsCollector, allow_msize_modification: bool) bool {
        return if (allow_msize_modification)
            self.effects.can_be_removed_if_no_msize
        else
            self.effects.can_be_removed;
    }

    pub fn cannotLoop(self: *const SideEffectsCollector) bool {
        return self.effects.cannot_loop;
    }

    pub fn invalidatesStorage(self: *const SideEffectsCollector) bool {
        return self.effects.storage == .write;
    }

    pub fn invalidatesMemory(self: *const SideEffectsCollector) bool {
        return self.effects.memory == .write;
    }

    pub fn sideEffects(self: *const SideEffectsCollector) SideEffects {
        return self.effects;
    }

    fn visitExpression(self: *SideEffectsCollector, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .literal, .identifier => {},
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
                self.effects.combineAssign(try functionCallSideEffects(
                    self.dialect,
                    self.function_side_effects,
                    call,
                ));
            },
        }
    }

    fn visitStatement(self: *SideEffectsCollector, statement: *const AST.Statement) anyerror!void {
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
            .for_loop => |*value| try self.visitForLoop(value),
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitBlock(self: *SideEffectsCollector, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitForLoop(self: *SideEffectsCollector, loop: *const AST.ForLoop) anyerror!void {
        try self.visitBlock(&loop.pre);
        try self.visitExpression(loop.condition orelse return error.InvalidAst);
        try self.visitBlock(&loop.body);
        try self.visitBlock(&loop.post);
    }
};

pub const SideEffectsPropagator = struct {
    pub fn sideEffects(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        graph: *const CallGraphModule.CallGraph,
    ) anyerror!FunctionSideEffects {
        var result: FunctionSideEffects = .{};
        errdefer result.deinit(allocator);

        for (0..graph.functions_with_loops.len()) |index|
            try markPossiblyLooping(allocator, &result, .{ .user = graph.functions_with_loops.at(index) });
        var recursive = try graph.recursiveFunctions();
        defer recursive.deinit(graph.allocator);
        for (0..recursive.len()) |index|
            try markPossiblyLooping(allocator, &result, recursive.at(index));

        for (graph.function_calls.items(), 0..) |entry, complete_before| {
            var effects: SideEffects = .{};
            var visited: CallGraphModule.FunctionHandleSet = .{};
            defer visited.deinit(allocator);
            for (entry.value.items) |callee|
                try collectTransitiveEffects(allocator, dialect, graph, &result, complete_before, &visited, callee, &effects);
            if (result.getPtr(entry.key)) |known|
                known.combineAssign(effects)
            else
                _ = try result.insert(allocator, entry.key, effects);
        }
        return result;
    }

    fn markPossiblyLooping(
        allocator: std.mem.Allocator,
        result: *FunctionSideEffects,
        handle: AST.FunctionHandle,
    ) !void {
        const effects = result.getPtr(handle) orelse blk: {
            _ = try result.insert(allocator, handle, .{});
            break :blk result.getPtr(handle).?;
        };
        effects.movable = false;
        effects.can_be_removed = false;
        effects.can_be_removed_if_no_msize = false;
        effects.cannot_loop = false;
    }

    fn collectTransitiveEffects(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        graph: *const CallGraphModule.CallGraph,
        known: *const FunctionSideEffects,
        complete_before: usize,
        visited: *CallGraphModule.FunctionHandleSet,
        handle: AST.FunctionHandle,
        effects: *SideEffects,
    ) anyerror!void {
        if (!(try visited.insert(allocator, handle))) return;
        if (effects.eql(SideEffects.worst())) return;
        switch (handle) {
            .builtin => |builtin| effects.combineAssign((try dialect.builtin(builtin)).side_effects),
            .user => {
                const position = graph.function_calls.search(handle);
                if (known.get(handle)) |function_effects| {
                    effects.combineAssign(function_effects.*);
                    // Earlier entries contain complete reachable effects;
                    // loop/recursion seeds alone are not complete summaries.
                    if (position.found and position.index < complete_before) return;
                }
                if (position.found)
                    for (graph.function_calls.items()[position.index].value.items) |callee|
                        try collectTransitiveEffects(
                            allocator,
                            dialect,
                            graph,
                            known,
                            complete_before,
                            visited,
                            callee,
                            effects,
                        );
            },
        }
    }
};

pub const MSizeFinder = struct {
    pub fn containsMSize(dialect: AST.Dialect, block: *const AST.Block) anyerror!bool {
        return findBlock(dialect, block);
    }

    pub fn containsMSizeObject(object: *const Object) anyerror!bool {
        const dialect = object.dialect() orelse return error.MissingDialect;
        const code = object.code() orelse return error.MissingCode;
        if (try findBlock(dialect.*, code.root())) return true;
        for (object.sub_objects.items) |*node| switch (node.*) {
            .object => |child| if (try containsMSizeObject(child)) return true,
            .data => {},
        };
        return false;
    }

    fn findBlock(dialect: AST.Dialect, block: *const AST.Block) anyerror!bool {
        for (block.statements.items) |*statement| if (try findStatement(dialect, statement)) return true;
        return false;
    }

    fn findStatement(dialect: AST.Dialect, statement: *const AST.Statement) anyerror!bool {
        return switch (statement.*) {
            .expression_statement => |*value| findExpression(dialect, &value.expression),
            .assignment => |*value| findExpression(dialect, value.value orelse return error.InvalidAst),
            .variable_declaration => |*value| if (value.value) |expression| findExpression(dialect, expression) else false,
            .function_definition => |*value| findBlock(dialect, &value.body),
            .if_statement => |*value| (try findExpression(dialect, value.condition orelse return error.InvalidAst)) or
                try findBlock(dialect, &value.body),
            .switch_statement => |*value| blk: {
                if (try findExpression(dialect, value.expression orelse return error.InvalidAst)) break :blk true;
                for (value.cases.items) |*case_value| if (try findBlock(dialect, &case_value.body)) break :blk true;
                break :blk false;
            },
            .for_loop => |*value| (try findBlock(dialect, &value.pre)) or
                (try findExpression(dialect, value.condition orelse return error.InvalidAst)) or
                (try findBlock(dialect, &value.body)) or
                try findBlock(dialect, &value.post),
            .block => |*value| findBlock(dialect, value),
            .break_statement, .continue_statement, .leave_statement => false,
        };
    }

    fn findExpression(dialect: AST.Dialect, expression: *const AST.Expression) anyerror!bool {
        return switch (expression.*) {
            .literal, .identifier => false,
            .function_call => |*call| blk: {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    if (try findExpression(dialect, &call.arguments.items[index])) break :blk true;
                }
                if (try Utilities.resolveBuiltinFunction(&call.function_name, dialect)) |builtin|
                    break :blk builtin.is_msize;
                break :blk false;
            },
        };
    }
};

pub const LeaveFinder = struct {
    pub fn containsLeave(function: *const AST.FunctionDefinition) bool {
        return findBlock(&function.body);
    }

    fn findBlock(block: *const AST.Block) bool {
        for (block.statements.items) |*statement| if (findStatement(statement)) return true;
        return false;
    }

    fn findStatement(statement: *const AST.Statement) bool {
        return switch (statement.*) {
            .leave_statement => true,
            .function_definition => |*value| findBlock(&value.body),
            .if_statement => |*value| findBlock(&value.body),
            .switch_statement => |*value| blk: {
                for (value.cases.items) |*case_value| if (findBlock(&case_value.body)) break :blk true;
                break :blk false;
            },
            .for_loop => |*value| findBlock(&value.pre) or findBlock(&value.body) or findBlock(&value.post),
            .block => |*value| findBlock(value),
            else => false,
        };
    }
};

pub const MovableChecker = struct {
    allocator: std.mem.Allocator,
    collector: SideEffectsCollector,
    variable_references: NameCollectorModule.NameSet = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        function_side_effects: ?*const FunctionSideEffects,
    ) MovableChecker {
        return .{
            .allocator = allocator,
            .collector = SideEffectsCollector.init(dialect, function_side_effects),
        };
    }

    pub fn collect(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        expression: *const AST.Expression,
    ) anyerror!MovableChecker {
        var checker = init(allocator, dialect, null);
        errdefer checker.deinit();
        try checker.visitExpression(expression);
        return checker;
    }

    pub fn deinit(self: *MovableChecker) void {
        self.variable_references.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn movable(self: *const MovableChecker) bool {
        return self.collector.movable();
    }

    pub fn sideEffects(self: *const MovableChecker) SideEffects {
        return self.collector.sideEffects();
    }

    pub fn referencedVariables(self: *const MovableChecker) *const NameCollectorModule.NameSet {
        return &self.variable_references;
    }

    pub fn visit(self: *MovableChecker, expression: *const AST.Expression) anyerror!void {
        try self.visitExpression(expression);
    }

    fn visitExpression(self: *MovableChecker, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .identifier => |identifier| _ = try self.variable_references.insert(self.allocator, identifier.name),
            .literal => {},
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
                const borrowed: AST.Expression = .{ .function_call = call.* };
                var direct = SideEffectsCollector.init(
                    self.collector.dialect,
                    self.collector.function_side_effects,
                );
                try direct.visitExpression(&borrowed);
                // Arguments were already visited above; only combine the call's
                // aggregate result. Recombining argument effects is idempotent.
                self.collector.effects.combineAssign(direct.effects);
            },
        }
    }
};

pub const TerminationFinder = struct {
    pub const ControlFlow = enum(c_int) {
        flow_out,
        break_flow,
        continue_flow,
        terminate,
        leave,
    };

    dialect: AST.Dialect,
    function_side_effects: ?*const NamedControlFlowSideEffects = null,

    pub fn init(
        dialect: AST.Dialect,
        function_side_effects: ?*const NamedControlFlowSideEffects,
    ) TerminationFinder {
        return .{ .dialect = dialect, .function_side_effects = function_side_effects };
    }

    pub fn firstUnconditionalControlFlowChange(
        self: *const TerminationFinder,
        statements: []const AST.Statement,
    ) anyerror!struct { control_flow: ControlFlow, index: usize } {
        for (statements, 0..) |*statement, index| {
            const control_flow = try self.controlFlowKind(statement);
            if (control_flow != .flow_out) return .{ .control_flow = control_flow, .index = index };
        }
        return .{ .control_flow = .flow_out, .index = std.math.maxInt(usize) };
    }

    pub fn controlFlowKind(
        self: *const TerminationFinder,
        statement: *const AST.Statement,
    ) anyerror!ControlFlow {
        return switch (statement.*) {
            .variable_declaration => |*value| if (value.value != null and
                try self.containsNonContinuingFunctionCall(value.value.?)) .terminate else .flow_out,
            .assignment => |*value| if (try self.containsNonContinuingFunctionCall(
                value.value orelse return error.InvalidAst,
            )) .terminate else .flow_out,
            .expression_statement => |*value| if (try self.containsNonContinuingFunctionCall(
                &value.expression,
            )) .terminate else .flow_out,
            .break_statement => .break_flow,
            .continue_statement => .continue_flow,
            .leave_statement => .leave,
            else => .flow_out,
        };
    }

    pub fn containsNonContinuingFunctionCall(
        self: *const TerminationFinder,
        expression: *const AST.Expression,
    ) anyerror!bool {
        const call = switch (expression.*) {
            .function_call => |*value| value,
            .identifier, .literal => return false,
        };
        for (call.arguments.items) |*argument|
            if (try self.containsNonContinuingFunctionCall(argument)) return true;
        if (try Utilities.resolveBuiltinFunction(&call.function_name, self.dialect)) |builtin|
            return !builtin.control_flow_side_effects.can_continue;
        const name = switch (call.function_name) {
            .identifier => |identifier| identifier.name,
            .builtin => unreachable,
        };
        if (self.function_side_effects) |known|
            if (known.get(name)) |effects| return !effects.can_continue;
        return false;
    }
};

test "semantic collectors recognize builtin side effects and irregular flow" {
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    const stop = dialect.dialect().findBuiltin("stop").?;
    var expression: AST.Expression = .{ .function_call = .{
        .function_name = .{ .builtin = .{ .handle = stop } },
    } };
    defer expression.deinit(allocator);
    const finder = TerminationFinder.init(dialect.dialect(), null);
    try std.testing.expect(try finder.containsNonContinuingFunctionCall(&expression));
    const effects = try SideEffectsCollector.collectExpression(dialect.dialect(), &expression, null);
    try std.testing.expect(!effects.canBeRemoved(false));
}

test "call graph effects match transitive closure for every three-node graph and loop seed" {
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const allocator = std.testing.allocator;
    var evm = try EVMDialect.init(allocator, .current(), false);
    defer evm.deinit();
    const dialect = evm.dialect();
    const names = [_]YulName{ try YulName.init("effects_a"), try YulName.init("effects_b"), try YulName.init("effects_c") };
    const looping: SideEffects = .{
        .movable = false,
        .can_be_removed = false,
        .can_be_removed_if_no_msize = false,
        .cannot_loop = false,
    };
    // Include distinct effect coordinates, pure calls, and a saturated result.
    for ([_][3][]const u8{ .{ "mload", "sstore", "tload" }, .{ "call", "add", "mstore" } }) |builtins| {
        for (0..512) |edges| {
            var reachable: [3][3]bool = @splat(@splat(false));
            for (0..3) |i| for (0..3) |j| {
                reachable[i][j] = edges & (@as(usize, 1) << @intCast(i * 3 + j)) != 0;
            };
            // This oracle uses transitive closure, not DFS or cached summaries.
            for (0..3) |k| for (0..3) |i| {
                for (0..3) |j| reachable[i][j] = reachable[i][j] or (reachable[i][k] and reachable[k][j]);
            };
            for (0..8) |loops| {
                var graph: CallGraphModule.CallGraph = .{ .allocator = allocator };
                defer graph.deinit();
                var local: [3]SideEffects = undefined;
                for (names, builtins, 0..) |name, builtin_name, i| {
                    const builtin = dialect.findBuiltin(builtin_name).?;
                    local[i] = (try dialect.builtin(builtin)).side_effects;
                    const has_loop = loops & (@as(usize, 1) << @intCast(i)) != 0;
                    if (has_loop) _ = try graph.functions_with_loops.insert(allocator, name);
                    if (has_loop or reachable[i][i]) local[i].combineAssign(looping);
                    _ = try graph.function_calls.insert(allocator, .{ .user = name }, .empty);
                    const callees = graph.function_calls.getPtr(.{ .user = name }).?;
                    try callees.append(allocator, .{ .builtin = builtin });
                    if (i == 0) {
                        const balance = dialect.findBuiltin("balance").?;
                        try callees.append(allocator, .{ .builtin = balance });
                        local[i].combineAssign((try dialect.builtin(balance)).side_effects);
                    }
                    for (names, 0..) |callee, j| {
                        if (edges & (@as(usize, 1) << @intCast(i * 3 + j)) != 0)
                            try callees.appendSlice(allocator, &.{ .{ .user = callee }, .{ .user = callee } });
                    }
                }
                var expected: FunctionSideEffects = .{};
                defer expected.deinit(allocator);
                for (names, 0..) |name, i| {
                    var effects = local[i];
                    for (local, 0..) |callee_effects, j| {
                        if (reachable[i][j]) effects.combineAssign(callee_effects);
                    }
                    _ = try expected.insert(allocator, .{ .user = name }, effects);
                }
                var actual = try SideEffectsPropagator.sideEffects(allocator, dialect, &graph);
                defer actual.deinit(allocator);
                try std.testing.expectEqualDeep(expected.items(), actual.items());
            }
        }
    }
}

test "call graph effects preserve seed-only nodes, builtin leaves and invalid handles" {
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const allocator = std.testing.allocator;
    var evm = try EVMDialect.init(allocator, .current(), false);
    defer evm.deinit();
    const dialect = evm.dialect();
    const caller: AST.FunctionHandle = .{ .user = try YulName.init("effects_caller") };
    const seeded: AST.FunctionHandle = .{ .user = try YulName.init("effects_seed_only") };
    const missing: AST.FunctionHandle = .{ .user = try YulName.init("effects_missing") };
    const builtin: AST.FunctionHandle = .{ .builtin = dialect.findBuiltin("add").? };
    var graph: CallGraphModule.CallGraph = .{ .allocator = allocator };
    defer graph.deinit();
    _ = try graph.functions_with_loops.insert(allocator, seeded.user);
    _ = try graph.function_calls.insert(allocator, caller, .empty);
    try graph.function_calls.getPtr(caller).?.appendSlice(allocator, &.{ seeded, missing, builtin });
    // A builtin remains a leaf when called, even if a manually built graph
    // gives it an adjacency entry. Its own published entry retains old behavior.
    _ = try graph.function_calls.insert(allocator, builtin, .empty);
    const store = dialect.findBuiltin("sstore").?;
    try graph.function_calls.getPtr(builtin).?.append(allocator, .{ .builtin = store });
    var actual = try SideEffectsPropagator.sideEffects(allocator, dialect, &graph);
    defer actual.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 3), actual.items().len);
    try std.testing.expect(!actual.contains(missing));
    try std.testing.expect(!actual.get(caller).?.cannot_loop);
    try std.testing.expectEqualDeep(actual.get(seeded).?.*, actual.get(caller).?.*);
    try std.testing.expectEqualDeep((try dialect.builtin(store)).side_effects, actual.get(builtin).?.*);

    try graph.function_calls.getPtr(caller).?.append(allocator, .{ .builtin = .{ .id = std.math.maxInt(usize) } });
    try std.testing.expectError(error.UnknownBuiltin, SideEffectsPropagator.sideEffects(allocator, dialect, &graph));
}
