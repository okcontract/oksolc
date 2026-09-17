// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Resolves memory/storage loads and small known Keccak-256 expressions from
//! the forward data-flow environment.

const std = @import("std");
const AST = @import("../ast.zig");
const CallGraph = @import("call_graph_generator.zig");
const DataFlow = @import("data_flow_analyzer.zig");
const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
const EVMMetrics = @import("../backends/evm/evm_metrics.zig");
const Keccak = @import("../../libsolutil/keccak256.zig");
const Numeric = @import("../../libsolutil/numeric.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const LoadResolver = struct {
    const Self = @This();
    const Analyzer = DataFlow.DataFlowAnalyzer(Self, .analyze);

    allocator: std.mem.Allocator,
    analyzer: Analyzer,
    contains_msize: bool,
    expected_executions_per_deployment: ?usize,

    pub const name = "LoadResolver";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        const contains_msize = try Semantics.MSizeFinder.containsMSize(context.dialect, ast);
        var graph = try CallGraph.CallGraphGenerator.callGraph(allocator, ast);
        defer graph.deinit();
        var function_side_effects = try Semantics.SideEffectsPropagator.sideEffects(
            allocator,
            context.dialect,
            &graph,
        );
        defer function_side_effects.deinit(allocator);
        var resolver: LoadResolver = .{
            .allocator = allocator,
            .analyzer = Analyzer.init(
                allocator,
                context.dialect,
                &function_side_effects,
            ),
            .contains_msize = contains_msize,
            .expected_executions_per_deployment = context.expected_executions_per_deployment,
        };
        defer resolver.deinit();
        try resolver.analyzer.run(&resolver, ast);
    }

    fn deinit(self: *LoadResolver) void {
        self.analyzer.deinit();
        self.* = undefined;
    }

    pub fn visitExpression(
        self: *Self,
        analyzer: *Analyzer,
        expression: *AST.Expression,
    ) anyerror!DataFlow.ExpressionVisit {
        try analyzer.baseVisitExpression(expression);
        if (expression.* != .function_call) return .handled;
        const call = &expression.function_call;
        const handle = switch (call.function_name) {
            .builtin => |builtin| builtin.handle,
            .identifier => return .handled,
        };
        if (analyzer.load_function_handles[@intFromEnum(DataFlow.StoreLoadLocation.memory)]) |memory_load| {
            if (handle.id == memory_load.id) {
                if (!self.contains_msize and
                    try self.tryResolve(analyzer, expression, .memory, call.arguments.items))
                    return .modified;
                return .handled;
            }
        }
        if (analyzer.load_function_handles[@intFromEnum(DataFlow.StoreLoadLocation.storage)]) |storage_load| {
            if (handle.id == storage_load.id) {
                if (try self.tryResolve(analyzer, expression, .storage, call.arguments.items))
                    return .modified;
                return .handled;
            }
        }
        if (!self.contains_msize and
            analyzer.dialect.hashFunctionHandle() != null and
            analyzer.dialect.hashFunctionHandle().?.id == handle.id)
        {
            if (call.arguments.items.len == 2 and
                call.arguments.items[0] == .identifier and
                call.arguments.items[1] == .identifier)
            {
                const known = analyzer.keccakValue(
                    call.arguments.items[0].identifier.name,
                    call.arguments.items[1].identifier.name,
                );
                if (known) |value| if (analyzer.inScope(value)) {
                    replaceIdentifier(self.allocator, expression, value);
                    return .modified;
                };
            }
            if (try self.tryEvaluateKeccak(analyzer, expression, call.arguments.items))
                return .modified;
        }
        return .handled;
    }

    fn tryResolve(
        self: *LoadResolver,
        analyzer: *Analyzer,
        expression: *AST.Expression,
        location: DataFlow.StoreLoadLocation,
        arguments: []const AST.Expression,
    ) anyerror!bool {
        if (arguments.len == 0 or arguments[0] != .identifier) return false;
        const key = arguments[0].identifier.name;
        const value = switch (location) {
            .storage => analyzer.storageValue(key),
            .memory => analyzer.memoryValue(key),
        } orelse return false;
        if (!analyzer.inScope(value)) return false;
        replaceIdentifier(self.allocator, expression, value);
        return true;
    }

    fn tryEvaluateKeccak(
        self: *LoadResolver,
        analyzer: *Analyzer,
        expression: *AST.Expression,
        arguments: []const AST.Expression,
    ) anyerror!bool {
        if (arguments.len != 2 or arguments[0] != .identifier or arguments[1] != .identifier)
            return false;
        const evm_dialect: *const EVMDialect = @ptrCast(@alignCast(
            analyzer.dialect.context orelse return error.ExpectedEVMDialect,
        ));
        var meter = EVMMetrics.GasMeter.initUnsigned(
            evm_dialect,
            self.expected_executions_per_deployment == null,
            self.expected_executions_per_deployment orelse 1,
        );
        defer meter.deinit();
        var cost_of_keccak = try meter.costs(expression);
        defer cost_of_keccak.deinit();
        var maximum_literal: AST.Expression = .{ .literal = .{
            .kind = .Number,
            .value = .{ .numeric_value = std.math.maxInt(u256) },
        } };
        defer maximum_literal.deinit(self.allocator);
        var cost_of_literal = try meter.costs(&maximum_literal);
        defer cost_of_literal.deinit();
        if (cost_of_literal.compare(&cost_of_keccak) == .gt) return false;

        const memory_value_name = analyzer.memoryValue(arguments[0].identifier.name) orelse return false;
        if (!analyzer.inScope(memory_value_name)) return false;
        const memory_content = try analyzer.valueOfIdentifier(memory_value_name) orelse return false;
        const byte_length = try analyzer.valueOfIdentifier(arguments[1].identifier.name) orelse return false;
        if (byte_length > 32) return false;
        const bytes = Numeric.toBigEndian256(memory_content);
        const hash = Keccak.keccak256(bytes[0..@intCast(byte_length)]);
        const debug_data = if (expression.debugData()) |data| data.* else null;
        expression.deinit(self.allocator);
        expression.* = .{ .literal = .{
            .debug_data = debug_data,
            .kind = .Number,
            .value = .{ .numeric_value = hash.toInteger() },
        } };
        return true;
    }
};

fn replaceIdentifier(
    allocator: std.mem.Allocator,
    expression: *AST.Expression,
    name: YulName,
) void {
    const debug_data = if (expression.debugData()) |data| data.* else null;
    expression.deinit(allocator);
    expression.* = .{ .identifier = .{ .debug_data = debug_data, .name = name } };
}
