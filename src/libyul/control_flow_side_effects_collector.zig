// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Reachability-based control-flow side-effect collection for user-defined Yul
//! functions, including the recursive-call fixed point used by optimized EVM
//! lowering.

const std = @import("std");
const AST = @import("ast.zig");
const ControlFlowSideEffects = @import("control_flow_side_effects.zig").ControlFlowSideEffects;
const FunctionReferenceResolverModule = @import("function_reference_resolver.zig");
const YulName = @import("yul_name.zig").YulName;

pub const ControlFlowNode = struct {
    successors: std.ArrayList(*const ControlFlowNode) = .empty,
    function_call: ?*const AST.FunctionCall = null,

    fn deinit(self: *ControlFlowNode, allocator: std.mem.Allocator) void {
        self.successors.deinit(allocator);
        self.* = undefined;
    }
};

pub const FunctionFlow = struct {
    entry: *const ControlFlowNode,
    exit: *const ControlFlowNode,
};

pub const ControlFlowBuilder = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*ControlFlowNode) = .empty,
    current_node: ?*ControlFlowNode = null,
    leave_node: ?*const ControlFlowNode = null,
    break_node: ?*const ControlFlowNode = null,
    continue_node: ?*const ControlFlowNode = null,
    function_flows: std.AutoHashMap(*const AST.FunctionDefinition, FunctionFlow),

    pub fn init(allocator: std.mem.Allocator, ast: *const AST.Block) !ControlFlowBuilder {
        var self: ControlFlowBuilder = .{
            .allocator = allocator,
            .function_flows = std.AutoHashMap(*const AST.FunctionDefinition, FunctionFlow).init(allocator),
        };
        errdefer self.deinit();
        self.current_node = try self.newNode();
        try self.visitBlock(ast);
        return self;
    }

    pub fn deinit(self: *ControlFlowBuilder) void {
        self.function_flows.deinit();
        for (self.nodes.items) |node| {
            node.deinit(self.allocator);
            self.allocator.destroy(node);
        }
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }

    fn newNode(self: *ControlFlowBuilder) !*ControlFlowNode {
        const node = try self.allocator.create(ControlFlowNode);
        errdefer self.allocator.destroy(node);
        node.* = .{};
        try self.nodes.append(self.allocator, node);
        return node;
    }

    fn connect(from: *ControlFlowNode, to: *const ControlFlowNode, allocator: std.mem.Allocator) !void {
        try from.successors.append(allocator, to);
    }

    fn newConnectedNode(self: *ControlFlowBuilder) !void {
        const node = try self.newNode();
        try connect(self.current_node orelse return error.InvalidControlFlow, node, self.allocator);
        self.current_node = node;
    }

    fn visitExpression(self: *ControlFlowBuilder, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .literal, .identifier => {},
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
                try self.newConnectedNode();
                self.current_node.?.function_call = call;
            },
        }
    }

    fn visitBlock(self: *ControlFlowBuilder, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *ControlFlowBuilder, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*node| try self.visitExpression(&node.expression),
            .assignment => |*node| try self.visitExpression(node.value orelse return error.InvalidAst),
            .variable_declaration => |*node| if (node.value) |value| try self.visitExpression(value),
            .function_definition => |*node| try self.visitFunctionDefinition(node),
            .if_statement => |*node| try self.visitIf(node),
            .switch_statement => |*node| try self.visitSwitch(node),
            .for_loop => |*node| try self.visitForLoop(node),
            .break_statement => try self.visitBreak(),
            .continue_statement => try self.visitContinue(),
            .leave_statement => try self.visitLeave(),
            .block => |*node| try self.visitBlock(node),
        }
    }

    fn visitIf(self: *ControlFlowBuilder, if_statement: *const AST.If) anyerror!void {
        try self.visitExpression(if_statement.condition orelse return error.InvalidAst);
        const branch_node = self.current_node orelse return error.InvalidControlFlow;
        const if_end = try self.newNode();
        try connect(branch_node, if_end, self.allocator);
        try self.newConnectedNode();
        try self.visitBlock(&if_statement.body);
        try connect(self.current_node orelse return error.InvalidControlFlow, if_end, self.allocator);
        self.current_node = if_end;
    }

    fn visitSwitch(self: *ControlFlowBuilder, switch_statement: *const AST.Switch) anyerror!void {
        try self.visitExpression(switch_statement.expression orelse return error.InvalidAst);
        if (switch_statement.cases.items.len == 0) return error.InvalidAst;
        const initial = self.current_node orelse return error.InvalidControlFlow;
        const final = try self.newNode();
        if (switch_statement.cases.items[switch_statement.cases.items.len - 1].value != null)
            try connect(initial, final, self.allocator);
        for (switch_statement.cases.items) |*case_value| {
            self.current_node = initial;
            try self.newConnectedNode();
            try self.visitBlock(&case_value.body);
            try connect(self.current_node orelse return error.InvalidControlFlow, final, self.allocator);
        }
        self.current_node = final;
    }

    fn visitFunctionDefinition(self: *ControlFlowBuilder, function: *const AST.FunctionDefinition) anyerror!void {
        const saved_current = self.current_node;
        const saved_leave = self.leave_node;
        const saved_break = self.break_node;
        const saved_continue = self.continue_node;
        defer {
            self.current_node = saved_current;
            self.leave_node = saved_leave;
            self.break_node = saved_break;
            self.continue_node = saved_continue;
        }

        const function_exit = try self.newNode();
        const function_entry = try self.newNode();
        self.current_node = function_entry;
        self.leave_node = function_exit;
        self.break_node = null;
        self.continue_node = null;
        try self.visitBlock(&function.body);
        try connect(self.current_node orelse return error.InvalidControlFlow, function_exit, self.allocator);
        try self.function_flows.putNoClobber(function, .{ .entry = function_entry, .exit = function_exit });
    }

    fn visitForLoop(self: *ControlFlowBuilder, loop: *const AST.ForLoop) anyerror!void {
        const saved_break = self.break_node;
        const saved_continue = self.continue_node;
        defer {
            self.break_node = saved_break;
            self.continue_node = saved_continue;
        }

        try self.visitBlock(&loop.pre);
        const break_target = try self.newNode();
        const continue_target = try self.newNode();
        self.break_node = break_target;
        self.continue_node = continue_target;

        try self.newConnectedNode();
        const loop_node = self.current_node orelse return error.InvalidControlFlow;
        try self.visitExpression(loop.condition orelse return error.InvalidAst);
        try connect(self.current_node orelse return error.InvalidControlFlow, break_target, self.allocator);
        try self.newConnectedNode();
        try self.visitBlock(&loop.body);
        try connect(self.current_node orelse return error.InvalidControlFlow, continue_target, self.allocator);
        self.current_node = continue_target;
        try self.visitBlock(&loop.post);
        try connect(self.current_node orelse return error.InvalidControlFlow, loop_node, self.allocator);
        self.current_node = break_target;
    }

    fn visitBreak(self: *ControlFlowBuilder) !void {
        try connect(
            self.current_node orelse return error.InvalidControlFlow,
            self.break_node orelse return error.InvalidControlFlow,
            self.allocator,
        );
        self.current_node = try self.newNode();
    }

    fn visitContinue(self: *ControlFlowBuilder) !void {
        try connect(
            self.current_node orelse return error.InvalidControlFlow,
            self.continue_node orelse return error.InvalidControlFlow,
            self.allocator,
        );
        self.current_node = try self.newNode();
    }

    fn visitLeave(self: *ControlFlowBuilder) !void {
        try connect(
            self.current_node orelse return error.InvalidControlFlow,
            self.leave_node orelse return error.InvalidControlFlow,
            self.allocator,
        );
        self.current_node = try self.newNode();
    }
};

const FunctionState = struct {
    function: *const AST.FunctionDefinition,
    flow: FunctionFlow,
    pending: std.ArrayList(*const ControlFlowNode) = .empty,
    processed: std.AutoHashMap(*const ControlFlowNode, void),
    calls: std.AutoHashMap(*const AST.FunctionCall, void),

    fn init(allocator: std.mem.Allocator, function: *const AST.FunctionDefinition, flow: FunctionFlow) FunctionState {
        return .{
            .function = function,
            .flow = flow,
            .processed = std.AutoHashMap(*const ControlFlowNode, void).init(allocator),
            .calls = std.AutoHashMap(*const AST.FunctionCall, void).init(allocator),
        };
    }

    fn deinit(self: *FunctionState, allocator: std.mem.Allocator) void {
        self.pending.deinit(allocator);
        self.processed.deinit();
        self.calls.deinit();
        self.* = undefined;
    }
};

pub const FunctionEffectsMap = std.AutoHashMap(*const AST.FunctionDefinition, ControlFlowSideEffects);

pub const ControlFlowSideEffectsCollector = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    cfg_builder: ControlFlowBuilder,
    function_references: std.AutoHashMap(*const AST.FunctionCall, *const AST.FunctionDefinition),
    function_side_effects: FunctionEffectsMap,
    state_index: std.AutoHashMap(*const AST.FunctionDefinition, usize),
    states: std.ArrayList(FunctionState) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *const AST.Block,
    ) !ControlFlowSideEffectsCollector {
        var self: ControlFlowSideEffectsCollector = .{
            .allocator = allocator,
            .dialect = dialect,
            .cfg_builder = try ControlFlowBuilder.init(allocator, ast),
            .function_references = std.AutoHashMap(*const AST.FunctionCall, *const AST.FunctionDefinition).init(allocator),
            .function_side_effects = FunctionEffectsMap.init(allocator),
            .state_index = std.AutoHashMap(*const AST.FunctionDefinition, usize).init(allocator),
        };
        errdefer self.deinit();
        try self.initialize(ast);
        try self.computeCanContinue();
        try self.computeTerminateAndRevert();
        return self;
    }

    pub fn deinit(self: *ControlFlowSideEffectsCollector) void {
        for (self.states.items) |*state| state.deinit(self.allocator);
        self.states.deinit(self.allocator);
        self.state_index.deinit();
        self.function_side_effects.deinit();
        self.function_references.deinit();
        self.cfg_builder.deinit();
        self.* = undefined;
    }

    pub fn functionSideEffects(self: *const ControlFlowSideEffectsCollector) *const FunctionEffectsMap {
        return &self.function_side_effects;
    }

    pub fn functionSideEffectsNamed(
        self: *const ControlFlowSideEffectsCollector,
        allocator: std.mem.Allocator,
    ) !std.AutoHashMap(YulName, ControlFlowSideEffects) {
        var result = std.AutoHashMap(YulName, ControlFlowSideEffects).init(allocator);
        errdefer result.deinit();
        var iterator = self.function_side_effects.iterator();
        while (iterator.next()) |entry| try result.putNoClobber(entry.key_ptr.*.name, entry.value_ptr.*);
        return result;
    }

    fn initialize(self: *ControlFlowSideEffectsCollector, ast: *const AST.Block) !void {
        var flows = self.cfg_builder.function_flows.iterator();
        while (flows.next()) |entry| {
            const function = entry.key_ptr.*;
            const state_index = self.states.items.len;
            var state = FunctionState.init(self.allocator, function, entry.value_ptr.*);
            errdefer state.deinit(self.allocator);
            try state.pending.append(self.allocator, entry.value_ptr.entry);
            try self.states.append(self.allocator, state);
            try self.state_index.put(function, state_index);
            try self.function_side_effects.put(function, .{
                .can_terminate = false,
                .can_revert = false,
                .can_continue = false,
            });
        }
        var function_references = try FunctionReferenceResolverModule.FunctionReferenceResolver.resolve(
            self.allocator,
            ast,
        );
        errdefer function_references.deinit();
        self.function_references.deinit();
        self.function_references = function_references;
    }

    fn computeCanContinue(self: *ControlFlowSideEffectsCollector) !void {
        var progress = true;
        while (progress) {
            progress = false;
            for (0..self.states.items.len) |index| {
                if (try self.processFunction(index)) progress = true;
            }
        }
    }

    fn processFunction(self: *ControlFlowSideEffectsCollector, state_index: usize) !bool {
        var progress = false;
        while (try self.nextProcessableNode(state_index)) |node| {
            const state = &self.states.items[state_index];
            if (node == state.flow.exit) {
                self.function_side_effects.getPtr(state.function).?.can_continue = true;
                return true;
            }
            for (node.successors.items) |successor|
                try self.recordReachabilityAndQueue(state_index, successor);
            progress = true;
        }
        return progress;
    }

    fn nextProcessableNode(
        self: *ControlFlowSideEffectsCollector,
        state_index: usize,
    ) !?*const ControlFlowNode {
        const state = &self.states.items[state_index];
        for (state.pending.items, 0..) |node, index| {
            if (node.function_call == null or (try self.sideEffects(node.function_call.?)).can_continue)
                return state.pending.orderedRemove(index);
        }
        return null;
    }

    fn sideEffects(self: *const ControlFlowSideEffectsCollector, call: *const AST.FunctionCall) !ControlFlowSideEffects {
        return switch (call.function_name) {
            .builtin => |builtin_name| (try self.dialect.builtin(builtin_name.handle)).control_flow_side_effects,
            .identifier => self.function_side_effects.get(
                self.function_references.get(call) orelse return error.UnresolvedFunctionReference,
            ) orelse return error.UnresolvedFunctionReference,
        };
    }

    fn recordReachabilityAndQueue(
        self: *ControlFlowSideEffectsCollector,
        state_index: usize,
        node: *const ControlFlowNode,
    ) anyerror!void {
        const state = &self.states.items[state_index];
        if (node.function_call) |call| try state.calls.put(call, {});
        const processed = try state.processed.getOrPut(node);
        if (!processed.found_existing) try state.pending.insert(self.allocator, 0, node);
    }

    fn computeTerminateAndRevert(self: *ControlFlowSideEffectsCollector) !void {
        for (self.states.items) |state| {
            var visited = std.AutoHashMap(*const AST.FunctionDefinition, void).init(self.allocator);
            defer visited.deinit();
            var result = self.function_side_effects.get(state.function).?;
            try self.collectCallEffects(state.function, &visited, &result);
            self.function_side_effects.getPtr(state.function).?.can_terminate = result.can_terminate;
            self.function_side_effects.getPtr(state.function).?.can_revert = result.can_revert;
        }
    }

    fn collectCallEffects(
        self: *const ControlFlowSideEffectsCollector,
        function: *const AST.FunctionDefinition,
        visited: *std.AutoHashMap(*const AST.FunctionDefinition, void),
        result: *ControlFlowSideEffects,
    ) anyerror!void {
        if (result.can_terminate and result.can_revert) return;
        const inserted = try visited.getOrPut(function);
        if (inserted.found_existing) return;
        const index = self.state_index.get(function) orelse return error.UnresolvedFunctionReference;
        var calls = self.states.items[index].calls.keyIterator();
        while (calls.next()) |call_pointer| {
            const call = call_pointer.*;
            const effects = try self.sideEffects(call);
            result.can_terminate = result.can_terminate or effects.can_terminate;
            result.can_revert = result.can_revert or effects.can_revert;
            if (self.function_references.get(call)) |callee|
                try self.collectCallEffects(callee, visited, result);
        }
    }
};

test "recursive control-flow effects distinguish returning and non-returning functions" {
    const Parser = @import("asm_parser.zig").Parser;
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("backends/evm/evm_dialect.zig");
    const allocator = std.testing.allocator;
    const dialect = try EVMDialect.strictAssemblyForEVM(EVMVersion.init(.Cancun));
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function forever() { forever() } function stopping() { stop() } function returning(x) { if x { leave } stopping() } }",
        "effects.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var collector = try ControlFlowSideEffectsCollector.init(allocator, dialect.dialect(), ast.root());
    defer collector.deinit();
    var named = try collector.functionSideEffectsNamed(allocator);
    defer named.deinit();
    const forever = named.get(try YulName.init("forever")).?;
    const stopping = named.get(try YulName.init("stopping")).?;
    const returning = named.get(try YulName.init("returning")).?;
    try std.testing.expect(!forever.can_continue);
    try std.testing.expect(!forever.can_terminate);
    try std.testing.expect(!stopping.can_continue and stopping.can_terminate);
    try std.testing.expect(returning.can_continue and returning.can_terminate);
}
