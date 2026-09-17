// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Reusable forward data-flow engine for Yul optimizer passes. It tracks
//! movable assignments, scope, loop depth, and simple memory/storage facts.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const BlockHasher = @import("block_hasher.zig");
const BuiltinHandle = @import("../builtins.zig").BuiltinHandle;
const KnowledgeBaseModule = @import("knowledge_base.zig");
const NameCollector = @import("name_collector.zig");
const Semantics = @import("semantics.zig");
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

pub const AssignedValue = struct {
    value: ?*const AST.Expression = null,
    loop_depth: usize = 0,
};

pub const MemoryAndStorage = enum {
    analyze,
    ignore,
};

pub const StoreLoadLocation = enum {
    memory,
    storage,
};

pub const ExpressionVisit = enum {
    descend,
    handled,
    modified,
};

pub const FunctionSideEffects = Semantics.FunctionSideEffects;
pub const NoObserver = struct {};
const NameMap = ordered.OrderedMap(YulName, YulName, lessYulName);

/// Function-frame-local dense identity for a disambiguated Yul variable.
/// `YulName` remains the public boundary; optimizer state uses this compact ID.
pub const VarId = enum(u32) { _ };

fn varIndex(id: VarId) usize {
    return @intFromEnum(id);
}

fn lessVarIdByName(names: []const YulName, left: VarId, right: VarId) bool {
    return names[varIndex(left)].lessThan(names[varIndex(right)]);
}

fn sortAndDeduplicateVarIds(state: anytype, ids: []VarId) []VarId {
    const names: []const YulName = state.variable_names.items;
    std.mem.sort(VarId, ids, names, lessVarIdByName);
    if (ids.len < 2) return ids;

    var unique_len: usize = 1;
    for (ids[1..]) |id| {
        if (id == ids[unique_len - 1]) continue;
        ids[unique_len] = id;
        unique_len += 1;
    }
    return ids[0..unique_len];
}

fn containsVarId(ids: []const VarId, needle: VarId) bool {
    for (ids) |id| if (id == needle) return true;
    return false;
}

pub const NamePair = struct {
    first: YulName,
    second: YulName,
};

pub const LoadFact = struct {
    location: StoreLoadLocation,
    key: YulName,
};

pub const ExpressionFacts = struct {
    fingerprint: u64,
    movable: bool = true,
    simple_load: ?LoadFact = null,
    keccak: ?NamePair = null,
};

pub const DependencyPoolStats = struct {
    forward_slots: usize,
    reverse_edges: usize,
    live_edges: usize,
    compactions: usize,
};

fn lessNamePair(left: NamePair, right: NamePair) bool {
    if (!left.first.eql(right.first)) return left.first.lessThan(right.first);
    return left.second.lessThan(right.second);
}

const KeccakMap = ordered.OrderedMap(NamePair, YulName, lessNamePair);

const Environment = struct {
    storage: NameMap = .{},
    memory: NameMap = .{},
    keccak: KeccakMap = .{},

    fn deinit(self: *Environment, allocator: std.mem.Allocator) void {
        self.storage.deinit(allocator);
        self.memory.deinit(allocator);
        self.keccak.deinit(allocator);
        self.* = undefined;
    }

    fn clone(self: *const Environment, allocator: std.mem.Allocator) !Environment {
        var result: Environment = .{};
        errdefer result.deinit(allocator);
        result.storage = try self.storage.clone(allocator);
        result.memory = try self.memory.clone(allocator);
        result.keccak = try self.keccak.clone(allocator);
        return result;
    }
};

const invalid_pool_index = std.math.maxInt(u32);
const dependency_compaction_min_edges: usize = 4_096;

const DependencyEdge = struct {
    referenced: VarId,
    owner: VarId,
    next: u32,
};

const DependencyEdgeList = std.MultiArrayList(DependencyEdge);

const VariableState = struct {
    /// Forward references retain upstream's sorted-name order in one edge
    /// pool. Reverse links validate against the owner's current pool slice.
    assigned: ?AssignedValue = null,
    reference_start: u32 = invalid_pool_index,
    reference_len: u32 = 0,
    reverse_head: u32 = invalid_pool_index,
    version: u64 = 0,
    active_scope_generation: u32 = 0,
    active_count: u32 = 0,
};

fn isCurrentDependencyEdge(owner: *const VariableState, edge_index: u32) bool {
    return owner.reference_start != invalid_pool_index and
        edge_index >= owner.reference_start and
        edge_index - owner.reference_start < owner.reference_len;
}

fn State(comptime memory_and_storage: MemoryAndStorage) type {
    return struct {
        const Self = @This();

        variable_ids: std.AutoHashMapUnmanaged(YulName, VarId) = .empty,
        variable_names: std.ArrayList(YulName) = .empty,
        variables: std.ArrayList(VariableState) = .empty,
        dependency_edges: DependencyEdgeList = .empty,
        live_dependency_edges: usize = 0,
        dependency_compactions: usize = 0,
        environment: if (memory_and_storage == .analyze) Environment else void =
            if (memory_and_storage == .analyze) .{} else {}, // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value rather than handling an error

        fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.variable_ids.deinit(allocator);
            self.variable_names.deinit(allocator);
            self.variables.deinit(allocator);
            self.dependency_edges.deinit(allocator);
            if (comptime memory_and_storage == .analyze)
                self.environment.deinit(allocator);
            self.* = undefined;
        }

        fn getId(self: *const Self, variable_name: YulName) ?VarId {
            return self.variable_ids.get(variable_name);
        }

        fn getOrCreateId(
            self: *Self,
            allocator: std.mem.Allocator,
            variable_name: YulName,
        ) !VarId {
            if (self.variable_ids.get(variable_name)) |id| return id;
            if (self.variables.items.len == std.math.maxInt(u32))
                return error.TooManyDataFlowVariables;
            try self.variable_names.ensureUnusedCapacity(allocator, 1);
            try self.variables.ensureUnusedCapacity(allocator, 1);
            const entry = try self.variable_ids.getOrPut(allocator, variable_name);
            if (entry.found_existing) return entry.value_ptr.*;
            const id: VarId = @enumFromInt(@as(u32, @intCast(self.variables.items.len)));
            entry.value_ptr.* = id;
            self.variable_names.appendAssumeCapacity(variable_name);
            self.variables.appendAssumeCapacity(.{});
            return id;
        }

        fn name(self: *const Self, id: VarId) YulName {
            return self.variable_names.items[varIndex(id)];
        }

        fn variable(self: *Self, id: VarId) *VariableState {
            return &self.variables.items[varIndex(id)];
        }

        fn variableConst(self: *const Self, id: VarId) *const VariableState {
            return &self.variables.items[varIndex(id)];
        }

        fn references(self: *const Self, id: VarId) ?[]const VarId {
            const variable_state = self.variableConst(id);
            if (variable_state.reference_start == invalid_pool_index) return null;
            const start: usize = variable_state.reference_start;
            return self.dependency_edges.items(.referenced)[start..][0..variable_state.reference_len];
        }
    };
}

const Scope = struct {
    declaration_mark: usize,
    generation: u32,
    is_function: bool,
};

const Declaration = struct {
    id: VarId,
    previous_scope_generation: u32,
};

const SparseVarSet = struct {
    dense: std.ArrayList(VarId) = .empty,
    sparse: std.ArrayList(u32) = .empty,

    fn deinit(self: *SparseVarSet, allocator: std.mem.Allocator) void {
        self.dense.deinit(allocator);
        self.sparse.deinit(allocator);
        self.* = undefined;
    }

    fn clearRetainingCapacity(self: *SparseVarSet) void {
        self.dense.clearRetainingCapacity();
    }

    fn ensureVariableCount(
        self: *SparseVarSet,
        allocator: std.mem.Allocator,
        count: usize,
    ) !void {
        const old_len = self.sparse.items.len;
        if (old_len >= count) return;
        try self.sparse.resize(allocator, count);
        @memset(self.sparse.items[old_len..], std.math.maxInt(u32));
    }

    fn contains(self: *const SparseVarSet, id: VarId) bool {
        const index = varIndex(id);
        if (index >= self.sparse.items.len) return false;
        const dense_index = self.sparse.items[index];
        return dense_index < self.dense.items.len and
            self.dense.items[dense_index] == id;
    }

    fn insert(
        self: *SparseVarSet,
        allocator: std.mem.Allocator,
        id: VarId,
    ) !void {
        try self.ensureVariableCount(allocator, varIndex(id) + 1);
        if (self.contains(id)) return;
        if (self.dense.items.len == std.math.maxInt(u32))
            return error.TooManyDataFlowVariables;
        try self.dense.append(allocator, id);
        self.sparse.items[varIndex(id)] = @intCast(self.dense.items.len - 1);
    }
};

pub const References = struct {
    names: []const YulName,
    ids: []const VarId,

    pub fn len(self: References) usize {
        return self.ids.len;
    }

    pub fn at(self: References, index: usize) YulName {
        return self.names[varIndex(self.ids[index])];
    }
};

pub fn DataFlowAnalyzer(
    comptime Observer: type,
    comptime memory_and_storage: MemoryAndStorage,
) type {
    return struct {
        const Self = @This();
        const EnvironmentSnapshot = if (memory_and_storage == .analyze) Environment else void;
        const has_observer = @hasDecl(Observer, "visitExpression") or
            @hasDecl(Observer, "assignValue") or
            @hasDecl(Observer, "visitFunction") or
            @hasDecl(Observer, "beforeStatement") or
            @hasDecl(Observer, "afterStatement");
        const tracks_expression_fingerprint = @hasDecl(
            Observer,
            "tracks_expression_fingerprint",
        ) and Observer.tracks_expression_fingerprint;

        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        function_side_effects: ?*const FunctionSideEffects,
        state: State(memory_and_storage) = .{},
        knowledge_base: KnowledgeBaseModule.KnowledgeBase,
        store_function_handles: if (memory_and_storage == .analyze) [2]?BuiltinHandle else void =
            if (memory_and_storage == .analyze) .{ null, null } else {}, // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value rather than handling an error
        load_function_handles: if (memory_and_storage == .analyze) [2]?BuiltinHandle else void =
            if (memory_and_storage == .analyze) .{ null, null } else {}, // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value rather than handling an error
        loop_depth: usize = 0,
        variable_scopes: std.ArrayList(Scope) = .empty,
        declared_variables: std.ArrayList(Declaration) = .empty,
        clear_scratch: SparseVarSet = .{},
        reference_scratch: std.ArrayList(VarId) = .empty,
        dependency_edge_scratch: DependencyEdgeList = .empty,
        expression_fact_sequence: u64 = 0,
        last_expression: ?*const AST.Expression = null,
        last_expression_facts: ExpressionFacts = undefined,
        next_scope_generation: u32 = 1,
        zero: AST.Expression = .{ .literal = .{
            .kind = .Number,
            .value = .{ .numeric_value = 0 },
        } },
        observer: if (has_observer) *Observer else void = if (has_observer) undefined else {}, // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value rather than handling an error

        pub fn init(
            allocator: std.mem.Allocator,
            dialect: AST.Dialect,
            function_side_effects: ?*const FunctionSideEffects,
        ) Self {
            var result: Self = .{
                .allocator = allocator,
                .dialect = dialect,
                .function_side_effects = function_side_effects,
                .knowledge_base = KnowledgeBaseModule.KnowledgeBase.init(
                    allocator,
                    .{ .context = null, .get_value = knowledgeValue },
                    dialect,
                    false,
                ),
            };
            if (comptime memory_and_storage == .analyze) {
                result.store_function_handles[@intFromEnum(StoreLoadLocation.memory)] =
                    dialect.memoryStoreFunctionHandle();
                result.load_function_handles[@intFromEnum(StoreLoadLocation.memory)] =
                    dialect.memoryLoadFunctionHandle();
                result.store_function_handles[@intFromEnum(StoreLoadLocation.storage)] =
                    dialect.storageStoreFunctionHandle();
                result.load_function_handles[@intFromEnum(StoreLoadLocation.storage)] =
                    dialect.storageLoadFunctionHandle();
            }
            return result;
        }

        pub fn deinit(self: *Self) void {
            self.state.deinit(self.allocator);
            self.knowledge_base.deinit();
            self.variable_scopes.deinit(self.allocator);
            self.declared_variables.deinit(self.allocator);
            self.clear_scratch.deinit(self.allocator);
            self.reference_scratch.deinit(self.allocator);
            self.dependency_edge_scratch.deinit(self.allocator);
            self.zero.deinit(self.allocator);
            self.* = undefined;
        }

        fn bind(self: *Self, observer: *Observer) void {
            if (comptime has_observer)
                self.observer = observer;
            self.knowledge_base.variable_values.context = self;
        }

        pub fn run(self: *Self, observer: *Observer, block: *AST.Block) anyerror!void {
            self.bind(observer);
            try self.visitBlock(block);
        }

        pub fn variableValue(self: *const Self, variable: YulName) ?*const AssignedValue {
            const id = self.state.getId(variable) orelse return null;
            return if (self.state.variableConst(id).assigned) |*value| value else null;
        }

        pub fn sortedReferences(self: *const Self, variable: YulName) ?References {
            const id = self.state.getId(variable) orelse return null;
            return .{
                .names = self.state.variable_names.items,
                .ids = self.state.references(id) orelse return null,
            };
        }

        pub fn dependencyPoolStats(self: *const Self) DependencyPoolStats {
            return .{
                .forward_slots = self.state.dependency_edges.len,
                .reverse_edges = self.state.dependency_edges.len,
                .live_edges = self.state.live_dependency_edges,
                .compactions = self.state.dependency_compactions,
            };
        }

        pub fn variableCount(self: *const Self) usize {
            return self.state.variable_names.items.len;
        }

        pub fn variableNameAt(self: *const Self, index: usize) YulName {
            return self.state.variable_names.items[index];
        }

        pub fn variableVersion(self: *const Self, variable: YulName) ?u64 {
            const id = self.state.getId(variable) orelse return null;
            return self.state.variableConst(id).version;
        }

        pub fn activeScopeGeneration(self: *const Self, variable: YulName) ?u32 {
            const id = self.state.getId(variable) orelse return null;
            const state = self.state.variableConst(id);
            return if (state.active_count == 0) null else state.active_scope_generation;
        }

        pub fn storageValue(self: *const Self, key: YulName) ?YulName {
            if (comptime memory_and_storage == .ignore) return null;
            return if (self.state.environment.storage.get(key)) |value| value.* else null;
        }

        pub fn memoryValue(self: *const Self, key: YulName) ?YulName {
            if (comptime memory_and_storage == .ignore) return null;
            return if (self.state.environment.memory.get(key)) |value| value.* else null;
        }

        pub fn keccakValue(self: *const Self, start: YulName, length: YulName) ?YulName {
            if (comptime memory_and_storage == .ignore) return null;
            return if (self.state.environment.keccak.get(.{ .first = start, .second = length })) |value|
                value.*
            else
                null;
        }

        pub fn knowledgeBase(self: *Self) *KnowledgeBaseModule.KnowledgeBase {
            return &self.knowledge_base;
        }

        pub fn currentLoopDepth(self: *const Self) usize {
            return self.loop_depth;
        }

        pub fn visitExpression(self: *Self, expression: *AST.Expression) anyerror!void {
            if (comptime @hasDecl(Observer, "visitExpression")) {
                const sequence_before_observer = self.expression_fact_sequence;
                switch (try self.observer.visitExpression(self, expression)) {
                    .descend => try self.baseVisitExpression(expression),
                    .handled => {
                        if (self.expression_fact_sequence == sequence_before_observer or
                            self.last_expression != expression)
                        {
                            self.setExpressionFacts(
                                expression,
                                try self.collectExpressionFacts(expression),
                            );
                        }
                    },
                    .modified => {
                        self.setExpressionFacts(
                            expression,
                            try self.collectExpressionFacts(expression),
                        );
                    },
                }
                return;
            }
            try self.baseVisitExpression(expression);
        }

        pub fn baseVisitExpression(self: *Self, expression: *AST.Expression) anyerror!void {
            const facts = switch (expression.*) {
                .literal => |*literal| ExpressionFacts{
                    .fingerprint = if (comptime tracks_expression_fingerprint)
                        try BlockHasher.ExpressionFingerprint.literal(literal)
                    else
                        0,
                },
                .identifier => |*identifier| ExpressionFacts{
                    .fingerprint = if (comptime tracks_expression_fingerprint)
                        BlockHasher.ExpressionFingerprint.identifier(identifier)
                    else
                        0,
                },
                .function_call => |*call| try self.visitFunctionCallFacts(expression, call, null),
            };
            self.setExpressionFacts(expression, facts);
        }

        /// CSE preserves upstream's rule that builtin literal arguments are not
        /// rewritten. Their facts still participate in the parent's bottom-up
        /// result without invoking the observer for those arguments.
        pub fn baseVisitExpressionSkippingLiteralArguments(
            self: *Self,
            expression: *AST.Expression,
            builtin: anytype,
        ) anyerror!void {
            const call = switch (expression.*) {
                .function_call => |*value| value,
                else => return self.baseVisitExpression(expression),
            };
            self.setExpressionFacts(
                expression,
                try self.visitFunctionCallFacts(expression, call, builtin),
            );
        }

        pub fn expressionFingerprint(
            self: *const Self,
            expression: *const AST.Expression,
        ) anyerror!u64 {
            if (comptime !tracks_expression_fingerprint)
                @compileError("observer did not request expression fingerprints");
            if (self.last_expression == expression)
                return self.last_expression_facts.fingerprint;
            return BlockHasher.ExpressionFingerprint.run(expression);
        }

        fn visitFunctionCallFacts(
            self: *Self,
            expression: *const AST.Expression,
            call: *AST.FunctionCall,
            literal_policy: anytype,
        ) anyerror!ExpressionFacts {
            var fingerprint: if (tracks_expression_fingerprint)
                BlockHasher.ExpressionFingerprint
            else
                void = if (tracks_expression_fingerprint) // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value rather than handling an error
                BlockHasher.ExpressionFingerprint.initFunctionCall(call)
            else {};
            var movable = true;
            var index = call.arguments.items.len;
            while (index != 0) {
                index -= 1;
                const argument = &call.arguments.items[index];
                const child_facts = if (comptime @TypeOf(literal_policy) == @TypeOf(null)) child: {
                    try self.visitExpression(argument);
                    break :child try self.currentExpressionFacts(argument);
                } else if (literal_policy.literalArgument(index) == null) child: {
                    try self.visitExpression(argument);
                    break :child try self.currentExpressionFacts(argument);
                } else try self.collectExpressionFacts(argument);
                if (comptime tracks_expression_fingerprint)
                    fingerprint.addChild(child_facts.fingerprint);
                movable = movable and child_facts.movable;
            }
            const call_movable = (try Semantics.functionCallSideEffects(
                self.dialect,
                self.function_side_effects,
                call,
            )).movable;
            movable = movable and call_movable;
            _ = expression;
            return .{
                .fingerprint = if (comptime tracks_expression_fingerprint)
                    fingerprint.finish()
                else
                    0,
                .movable = movable,
            };
        }

        fn collectExpressionFacts(
            self: *Self,
            expression: *const AST.Expression,
        ) anyerror!ExpressionFacts {
            return switch (expression.*) {
                .literal => |*literal| .{
                    .fingerprint = if (comptime tracks_expression_fingerprint)
                        try BlockHasher.ExpressionFingerprint.literal(literal)
                    else
                        0,
                },
                .identifier => |*identifier| .{
                    .fingerprint = if (comptime tracks_expression_fingerprint)
                        BlockHasher.ExpressionFingerprint.identifier(identifier)
                    else
                        0,
                },
                .function_call => |*call| facts: {
                    var fingerprint: if (tracks_expression_fingerprint)
                        BlockHasher.ExpressionFingerprint
                    else
                        void = if (tracks_expression_fingerprint) // zlinter-disable-current-line no_swallow_error - comptime branch constructs a void value rather than handling an error
                        BlockHasher.ExpressionFingerprint.initFunctionCall(call)
                    else {};
                    var movable = true;
                    var index = call.arguments.items.len;
                    while (index != 0) {
                        index -= 1;
                        const child_facts = try self.collectExpressionFacts(
                            &call.arguments.items[index],
                        );
                        if (comptime tracks_expression_fingerprint)
                            fingerprint.addChild(child_facts.fingerprint);
                        movable = movable and child_facts.movable;
                    }
                    const call_movable = (try Semantics.functionCallSideEffects(
                        self.dialect,
                        self.function_side_effects,
                        call,
                    )).movable;
                    movable = movable and call_movable;
                    break :facts .{
                        .fingerprint = if (comptime tracks_expression_fingerprint)
                            fingerprint.finish()
                        else
                            0,
                        .movable = movable,
                    };
                },
            };
        }

        fn classifyExpression(
            self: *const Self,
            expression: *const AST.Expression,
            initial: ExpressionFacts,
        ) ExpressionFacts {
            if (comptime memory_and_storage == .ignore) return initial;
            var result = initial;
            if (self.isSimpleLoad(.memory, expression)) |key|
                result.simple_load = .{ .location = .memory, .key = key }
            else if (self.isSimpleLoad(.storage, expression)) |key|
                result.simple_load = .{ .location = .storage, .key = key };
            result.keccak = self.isKeccak(expression);
            return result;
        }

        fn collectExpressionReferences(
            self: *Self,
            expression: *const AST.Expression,
        ) !void {
            switch (expression.*) {
                .literal => {},
                .identifier => |identifier| try self.reference_scratch.append(
                    self.allocator,
                    try self.state.getOrCreateId(self.allocator, identifier.name),
                ),
                .function_call => |*call| {
                    var index = call.arguments.items.len;
                    while (index != 0) {
                        index -= 1;
                        try self.collectExpressionReferences(&call.arguments.items[index]);
                    }
                },
            }
        }

        fn currentExpressionFacts(
            self: *const Self,
            expression: *const AST.Expression,
        ) !ExpressionFacts {
            if (self.last_expression != expression) return error.ExpressionFactsUnavailable;
            return self.last_expression_facts;
        }

        fn setExpressionFacts(
            self: *Self,
            expression: *const AST.Expression,
            facts: ExpressionFacts,
        ) void {
            self.last_expression = expression;
            self.last_expression_facts = facts;
            self.expression_fact_sequence +%= 1;
        }

        pub fn visitStatement(self: *Self, statement: *AST.Statement) anyerror!void {
            if (comptime @hasDecl(Observer, "beforeStatement"))
                try self.observer.beforeStatement(self, statement);
            switch (statement.*) {
                .expression_statement => |*value| try self.visitExpressionStatement(value),
                .assignment => |*value| try self.visitAssignment(value),
                .variable_declaration => |*value| try self.visitVariableDeclaration(value),
                .function_definition => |*value| try self.visitFunction(value),
                .if_statement => |*value| try self.visitIf(value),
                .switch_statement => |*value| try self.visitSwitch(value),
                .for_loop => |*value| try self.visitForLoop(value),
                .block => |*value| try self.visitBlock(value),
                .break_statement, .continue_statement, .leave_statement => {},
            }
            if (comptime @hasDecl(Observer, "afterStatement"))
                try self.observer.afterStatement(self, statement);
        }

        pub fn visitBlock(self: *Self, block: *AST.Block) anyerror!void {
            const scope_checkpoint = self.variable_scopes.items.len;
            defer self.restoreScopes(scope_checkpoint);
            try self.pushScope(false);
            for (block.statements.items) |*statement| try self.visitStatement(statement);
            if (self.variable_scopes.items.len != scope_checkpoint + 1)
                return error.UnbalancedDataFlowScopes;
        }

        pub fn baseAssignValue(
            self: *Self,
            variable: YulName,
            value: ?*const AST.Expression,
        ) anyerror!void {
            const id = self.state.getId(variable) orelse return error.UnknownDataFlowVariable;
            const state = self.state.variable(id);
            state.version +%= 1;
            state.assigned = .{
                .value = value,
                .loop_depth = self.loop_depth,
            };
        }

        pub fn assignValue(
            self: *Self,
            variable: YulName,
            value: ?*const AST.Expression,
        ) anyerror!void {
            if (comptime @hasDecl(Observer, "assignValue"))
                if (try self.observer.assignValue(self, variable, value)) return;
            try self.baseAssignValue(variable, value);
        }

        pub fn inScope(self: *const Self, variable: YulName) bool {
            const id = self.state.getId(variable) orelse return false;
            return self.state.variableConst(id).active_count != 0;
        }

        pub fn valueOfIdentifier(self: *const Self, name: YulName) anyerror!?u256 {
            const assigned = self.variableValue(name) orelse return null;
            const expression = assigned.value orelse return null;
            return switch (expression.*) {
                .literal => |*literal| @as(?u256, try literal.value.value()),
                else => null,
            };
        }

        fn visitExpressionStatement(
            self: *Self,
            statement: *AST.ExpressionStatement,
        ) anyerror!void {
            if (comptime memory_and_storage == .analyze) {
                if (self.isSimpleStore(.storage, statement)) |variables| {
                    try self.visitExpression(&statement.expression);
                    var index: usize = 0;
                    while (index < self.state.environment.storage.len()) {
                        const entry = self.state.environment.storage.items()[index];
                        if (!(try self.knowledge_base.knownToBeDifferent(variables.first, entry.key)) and
                            !variables.second.eql(entry.value))
                        {
                            _ = self.state.environment.storage.remove(entry.key);
                        } else index += 1;
                    }
                    try self.state.environment.storage.put(
                        self.allocator,
                        variables.first,
                        variables.second,
                    );
                    return;
                }
                if (self.isSimpleStore(.memory, statement)) |variables| {
                    try self.visitExpression(&statement.expression);
                    var index: usize = 0;
                    while (index < self.state.environment.memory.len()) {
                        const entry = self.state.environment.memory.items()[index];
                        if (!(try self.knowledge_base.knownToBeDifferentByAtLeast32(
                            variables.first,
                            entry.key,
                        ))) {
                            _ = self.state.environment.memory.remove(entry.key);
                        } else index += 1;
                    }
                    self.state.environment.keccak.clearRetainingCapacity();
                    try self.state.environment.memory.put(
                        self.allocator,
                        variables.first,
                        variables.second,
                    );
                    return;
                }
            }
            try self.clearKnowledgeIfInvalidatedExpression(&statement.expression);
            try self.visitExpression(&statement.expression);
        }

        fn visitAssignment(self: *Self, assignment: *AST.Assignment) anyerror!void {
            var stack_ids: [8]VarId = undefined;
            var heap_ids: ?[]VarId = null;
            defer if (heap_ids) |ids| self.allocator.free(ids);
            const ids = if (assignment.variable_names.items.len <= stack_ids.len)
                stack_ids[0..assignment.variable_names.items.len]
            else ids: {
                const allocated = try self.allocator.alloc(
                    VarId,
                    assignment.variable_names.items.len,
                );
                heap_ids = allocated;
                break :ids allocated;
            };
            for (assignment.variable_names.items, ids) |variable, *id|
                id.* = try self.state.getOrCreateId(self.allocator, variable.name);
            const unique_ids = sortAndDeduplicateVarIds(&self.state, ids);

            const value = assignment.value orelse return error.InvalidAst;
            try self.clearKnowledgeIfInvalidatedExpression(value);
            try self.visitExpression(value);
            try self.handleAssignmentIds(unique_ids, value, false);
        }

        fn visitVariableDeclaration(
            self: *Self,
            declaration: *AST.VariableDeclaration,
        ) anyerror!void {
            if (self.variable_scopes.items.len == 0) return error.MissingDataFlowScope;
            var stack_ids: [8]VarId = undefined;
            var heap_ids: ?[]VarId = null;
            defer if (heap_ids) |ids| self.allocator.free(ids);
            const ids = if (declaration.variables.items.len <= stack_ids.len)
                stack_ids[0..declaration.variables.items.len]
            else ids: {
                const allocated = try self.allocator.alloc(
                    VarId,
                    declaration.variables.items.len,
                );
                heap_ids = allocated;
                break :ids allocated;
            };
            for (declaration.variables.items, ids) |variable, *id|
                id.* = try self.declareVariable(variable.name);
            const unique_ids = sortAndDeduplicateVarIds(&self.state, ids);

            if (declaration.value) |value| {
                try self.clearKnowledgeIfInvalidatedExpression(value);
                try self.visitExpression(value);
            }
            try self.handleAssignmentIds(unique_ids, declaration.value, true);
        }

        fn visitIf(self: *Self, if_statement: *AST.If) anyerror!void {
            const condition = if_statement.condition orelse return error.InvalidAst;
            try self.clearKnowledgeIfInvalidatedExpression(condition);
            var pre_environment = try self.cloneEnvironment();
            defer self.deinitEnvironment(&pre_environment);
            try self.visitExpression(condition);
            try self.visitBlock(&if_statement.body);
            try self.joinKnowledge(&pre_environment);
            var assigned = try NameCollector.assignedVariableNames(self.allocator, &if_statement.body);
            defer assigned.deinit(self.allocator);
            try self.clearValues(&assigned);
        }

        fn visitSwitch(self: *Self, switch_statement: *AST.Switch) anyerror!void {
            const expression = switch_statement.expression orelse return error.InvalidAst;
            try self.clearKnowledgeIfInvalidatedExpression(expression);
            try self.visitExpression(expression);
            var assigned_variables: NameCollector.NameSet = .{};
            defer assigned_variables.deinit(self.allocator);
            for (switch_statement.cases.items) |*case_value| {
                var pre_environment = try self.cloneEnvironment();
                defer self.deinitEnvironment(&pre_environment);
                try self.visitBlock(&case_value.body);
                try self.joinKnowledge(&pre_environment);

                var assigned = try NameCollector.assignedVariableNames(self.allocator, &case_value.body);
                defer assigned.deinit(self.allocator);
                for (0..assigned.len()) |index|
                    _ = try assigned_variables.insert(self.allocator, assigned.at(index));
                try self.clearValues(&assigned);
                try self.clearKnowledgeIfInvalidatedBlock(&case_value.body);
            }
            for (switch_statement.cases.items) |*case_value|
                try self.clearKnowledgeIfInvalidatedBlock(&case_value.body);
            try self.clearValues(&assigned_variables);
        }

        fn visitFunction(self: *Self, function: *AST.FunctionDefinition) anyerror!void {
            if (comptime @hasDecl(Observer, "visitFunction"))
                if (try self.observer.visitFunction(self, function)) return;
            try self.baseVisitFunction(function);
        }

        pub fn baseVisitFunction(
            self: *Self,
            function: *AST.FunctionDefinition,
        ) anyerror!void {
            const saved_state = self.takeState();
            const saved_loop_depth = self.loop_depth;
            self.loop_depth = 0;
            defer {
                self.recycleDependencyEdges();
                self.state.deinit(self.allocator);
                self.state = saved_state;
                self.loop_depth = saved_loop_depth;
            }

            const scope_checkpoint = self.variable_scopes.items.len;
            defer self.restoreScopes(scope_checkpoint);
            try self.pushScope(true);
            for (function.parameters.items) |parameter|
                _ = try self.declareVariable(parameter.name);
            for (function.return_variables.items) |return_variable| {
                const id = try self.declareVariable(return_variable.name);
                try self.handleAssignmentIds(&.{id}, null, true);
            }
            try self.visitBlock(&function.body);
            if (self.variable_scopes.items.len != scope_checkpoint + 1)
                return error.UnbalancedDataFlowScopes;
        }

        fn visitForLoop(self: *Self, loop: *AST.ForLoop) anyerror!void {
            if (loop.pre.statements.items.len != 0) return error.ForLoopInitRewriterNotRun;
            self.loop_depth += 1;
            defer self.loop_depth -= 1;

            var assignments_since_continue = try NameCollector.AssignmentsSinceContinue.init(
                self.allocator,
                &loop.body,
            );
            defer assignments_since_continue.deinit();
            var assigned_variables = try NameCollector.assignedVariableNames(self.allocator, &loop.body);
            defer assigned_variables.deinit(self.allocator);
            var post_assigned = try NameCollector.assignedVariableNames(self.allocator, &loop.post);
            defer post_assigned.deinit(self.allocator);
            for (0..post_assigned.len()) |index|
                _ = try assigned_variables.insert(self.allocator, post_assigned.at(index));
            try self.clearValues(&assigned_variables);

            const condition = loop.condition orelse return error.InvalidAst;
            try self.clearKnowledgeIfInvalidatedExpression(condition);
            try self.clearKnowledgeIfInvalidatedBlock(&loop.post);
            try self.clearKnowledgeIfInvalidatedBlock(&loop.body);

            try self.visitExpression(condition);
            try self.visitBlock(&loop.body);
            try self.clearValues(assignments_since_continue.names());
            try self.clearKnowledgeIfInvalidatedBlock(&loop.body);
            try self.visitBlock(&loop.post);
            try self.clearValues(&assigned_variables);
            try self.clearKnowledgeIfInvalidatedExpression(condition);
            try self.clearKnowledgeIfInvalidatedBlock(&loop.post);
            try self.clearKnowledgeIfInvalidatedBlock(&loop.body);
        }

        fn handleAssignmentIds(
            self: *Self,
            variables: []const VarId,
            value: ?*AST.Expression,
            is_declaration: bool,
        ) anyerror!void {
            if (!is_declaration) try self.clearVariableIds(variables);

            self.reference_scratch.clearRetainingCapacity();
            const facts = if (value) |expression| facts: {
                try self.collectExpressionReferences(expression);
                break :facts self.classifyExpression(
                    expression,
                    try self.currentExpressionFacts(expression),
                );
            } else facts: {
                for (variables) |id|
                    try self.assignValue(self.state.name(id), &self.zero);
                break :facts null;
            };
            const referenced_variables = sortAndDeduplicateVarIds(
                &self.state,
                self.reference_scratch.items,
            );
            self.reference_scratch.items.len = referenced_variables.len;

            if (facts != null and variables.len == 1) {
                const variable = self.state.name(variables[0]);
                if (facts.?.movable and
                    !containsVarId(referenced_variables, variables[0]))
                    try self.assignValue(variable, value.?);
            }

            try self.setReferences(variables, referenced_variables);
            for (variables) |variable_id| {
                const variable = self.state.name(variable_id);
                if (comptime memory_and_storage == .analyze) {
                    if (!is_declaration) {
                        _ = self.state.environment.storage.remove(variable);
                        removeNameMapValues(&self.state.environment.storage, variable);
                        _ = self.state.environment.memory.remove(variable);
                        removeKeccakReferences(&self.state.environment.keccak, variable);
                        removeNameMapValues(&self.state.environment.memory, variable);
                    }
                }
            }

            if (comptime memory_and_storage == .analyze) {
                if (facts != null and variables.len == 1) {
                    const variable = self.state.name(variables[0]);
                    if (!containsVarId(referenced_variables, variables[0])) {
                        if (facts.?.simple_load) |load|
                            switch (load.location) {
                                .memory => try self.state.environment.memory.put(
                                    self.allocator,
                                    load.key,
                                    variable,
                                ),
                                .storage => try self.state.environment.storage.put(
                                    self.allocator,
                                    load.key,
                                    variable,
                                ),
                            }
                        else if (facts.?.keccak) |arguments|
                            try self.state.environment.keccak.put(
                                self.allocator,
                                arguments,
                                variable,
                            );
                    }
                }
            }
        }

        fn pushScope(self: *Self, is_function: bool) !void {
            if (self.next_scope_generation == std.math.maxInt(u32))
                return error.TooManyDataFlowScopes;
            try self.variable_scopes.append(self.allocator, .{
                .declaration_mark = self.declared_variables.items.len,
                .generation = self.next_scope_generation,
                .is_function = is_function,
            });
            self.next_scope_generation += 1;
        }

        fn declareVariable(self: *Self, name: YulName) !VarId {
            if (self.variable_scopes.items.len == 0) return error.MissingDataFlowScope;
            try self.declared_variables.ensureUnusedCapacity(self.allocator, 1);
            const id = try self.state.getOrCreateId(self.allocator, name);
            const variable = self.state.variable(id);
            if (variable.active_count == std.math.maxInt(u32))
                return error.TooManyNestedVariableDeclarations;
            const scope = self.variable_scopes.items[self.variable_scopes.items.len - 1];
            self.declared_variables.appendAssumeCapacity(.{
                .id = id,
                .previous_scope_generation = variable.active_scope_generation,
            });
            variable.active_count += 1;
            variable.active_scope_generation = scope.generation;
            return id;
        }

        fn restoreScopes(self: *Self, checkpoint: usize) void {
            while (self.variable_scopes.items.len > checkpoint) self.popScope();
        }

        fn takeState(self: *Self) State(memory_and_storage) {
            const result = self.state;
            self.state = .{};
            self.state.dependency_edges = self.dependency_edge_scratch;
            self.dependency_edge_scratch = .empty;
            return result;
        }

        fn recycleDependencyEdges(self: *Self) void {
            var candidate = self.state.dependency_edges;
            self.state.dependency_edges = .empty;
            candidate.len = 0;
            if (candidate.capacity > self.dependency_edge_scratch.capacity) {
                self.dependency_edge_scratch.deinit(self.allocator);
                self.dependency_edge_scratch = candidate;
            } else {
                candidate.deinit(self.allocator);
            }
        }

        fn popScope(self: *Self) void {
            std.debug.assert(self.variable_scopes.items.len != 0);
            const scope = self.variable_scopes.pop().?;
            while (self.declared_variables.items.len > scope.declaration_mark) {
                const declaration = self.declared_variables.pop().?;
                self.removeValueById(declaration.id);
                const variable = self.state.variable(declaration.id);
                variable.reverse_head = invalid_pool_index;
                std.debug.assert(variable.active_count != 0);
                variable.active_count -= 1;
                variable.active_scope_generation = declaration.previous_scope_generation;
            }
        }

        fn clearVariableIds(self: *Self, ids: []const VarId) !void {
            if (comptime memory_and_storage == .analyze)
                for (ids) |id|
                    removeEnvironmentNameReferences(&self.state.environment, self.state.name(id));
            self.clear_scratch.clearRetainingCapacity();
            try self.clear_scratch.ensureVariableCount(
                self.allocator,
                self.state.variables.items.len,
            );
            for (ids) |id| {
                try self.clear_scratch.insert(self.allocator, id);
                try self.addDirectDependentsToClear(id);
            }
            for (self.clear_scratch.dense.items) |id| self.removeValueById(id);
        }

        fn clearValues(
            self: *Self,
            variables_to_clear: *const NameCollector.NameSet,
        ) anyerror!void {
            if (comptime memory_and_storage == .analyze)
                removeEnvironmentReferences(&self.state.environment, variables_to_clear);
            self.clear_scratch.clearRetainingCapacity();
            try self.clear_scratch.ensureVariableCount(
                self.allocator,
                self.state.variables.items.len,
            );
            for (0..variables_to_clear.len()) |index| {
                const id = self.state.getId(variables_to_clear.at(index)) orelse continue;
                try self.clear_scratch.insert(self.allocator, id);
                try self.addDirectDependentsToClear(id);
            }
            for (self.clear_scratch.dense.items) |id| self.removeValueById(id);
        }

        fn addDirectDependentsToClear(
            self: *Self,
            referenced_variable: VarId,
        ) !void {
            const edges = self.state.dependency_edges.slice();
            const owners = edges.items(.owner);
            const next_edges = edges.items(.next);
            var edge_index = self.state.variableConst(referenced_variable).reverse_head;
            var previous_edge: u32 = invalid_pool_index;
            while (edge_index != invalid_pool_index) {
                std.debug.assert(edge_index < self.state.dependency_edges.len);
                const next = next_edges[edge_index];
                const owner_id = owners[edge_index];
                const owner = self.state.variableConst(owner_id);
                if (isCurrentDependencyEdge(owner, edge_index)) {
                    try self.clear_scratch.insert(self.allocator, owner_id);
                    previous_edge = edge_index;
                } else if (previous_edge == invalid_pool_index) {
                    self.state.variable(referenced_variable).reverse_head = next;
                } else {
                    next_edges[previous_edge] = next;
                }
                edge_index = next;
            }
        }

        fn setReferences(
            self: *Self,
            owners: []const VarId,
            referenced_variables: []const VarId,
        ) !void {
            if (owners.len != 0 and
                referenced_variables.len > std.math.maxInt(usize) / owners.len)
            {
                return error.TooManyDataFlowReferences;
            }
            const edge_count = owners.len * referenced_variables.len;
            try self.maybeCompactDependencyPools(edge_count);
            if (self.state.dependency_edges.len >= invalid_pool_index or
                edge_count > invalid_pool_index - self.state.dependency_edges.len)
            {
                return error.TooManyDataFlowReferences;
            }
            try self.state.dependency_edges.ensureUnusedCapacity(
                self.allocator,
                edge_count,
            );

            for (owners) |owner_id| {
                self.invalidateReferences(owner_id);
                const start: u32 = @intCast(self.state.dependency_edges.len);
                const owner = self.state.variable(owner_id);
                owner.reference_start = start;
                owner.reference_len = @intCast(referenced_variables.len);

                for (referenced_variables) |referenced_variable| {
                    const edge_index: u32 = @intCast(self.state.dependency_edges.len);
                    const next = self.state.variableConst(referenced_variable).reverse_head;
                    self.state.dependency_edges.appendAssumeCapacity(.{
                        .referenced = referenced_variable,
                        .owner = owner_id,
                        .next = next,
                    });
                    self.state.variable(referenced_variable).reverse_head = edge_index;
                }
                self.state.live_dependency_edges += referenced_variables.len;
            }
        }

        fn maybeCompactDependencyPools(self: *Self, incoming_edges: usize) !void {
            const total_edges = self.state.dependency_edges.len +| incoming_edges;
            if (total_edges < dependency_compaction_min_edges) return;
            const stale_edges = self.state.dependency_edges.len -
                self.state.live_dependency_edges;
            if (stale_edges < total_edges / 2 + total_edges % 2) return;
            try self.compactDependencyPools();
        }

        fn compactDependencyPools(self: *Self) !void {
            var dependency_edges: DependencyEdgeList = .empty;
            errdefer dependency_edges.deinit(self.allocator);
            try dependency_edges.ensureTotalCapacity(
                self.allocator,
                self.state.live_dependency_edges,
            );

            const old_edges = self.state.dependency_edges.slice();
            const old_referenced_variables = old_edges.items(.referenced);
            const old_owners = old_edges.items(.owner);
            const old_next_edges = old_edges.items(.next);
            for (self.state.variables.items) |*referenced_variable| {
                var old_edge_index = referenced_variable.reverse_head;
                while (old_edge_index != invalid_pool_index) {
                    std.debug.assert(old_edge_index < self.state.dependency_edges.len);
                    const owner_id = old_owners[old_edge_index];
                    const owner = self.state.variableConst(owner_id);
                    if (isCurrentDependencyEdge(owner, old_edge_index))
                        old_owners[old_edge_index] = @enumFromInt(invalid_pool_index);
                    old_edge_index = old_next_edges[old_edge_index];
                }
                referenced_variable.reverse_head = invalid_pool_index;
            }

            var rebuilt_forward_edges: usize = 0;
            for (0..self.state.variables.items.len) |owner_index| {
                const owner_id: VarId = @enumFromInt(@as(u32, @intCast(owner_index)));
                const owner = self.state.variable(owner_id);
                if (owner.reference_start == invalid_pool_index) continue;
                const old_start: usize = owner.reference_start;
                const reference_start: u32 = @intCast(dependency_edges.len);
                for (old_start..old_start + owner.reference_len) |old_edge_index| {
                    const referenced_variable = old_referenced_variables[old_edge_index];
                    const is_linked = @intFromEnum(old_owners[old_edge_index]) ==
                        invalid_pool_index;
                    const next = if (is_linked)
                        self.state.variableConst(referenced_variable).reverse_head
                    else
                        invalid_pool_index;
                    const edge_index: u32 = @intCast(dependency_edges.len);
                    dependency_edges.appendAssumeCapacity(.{
                        .referenced = referenced_variable,
                        .owner = owner_id,
                        .next = next,
                    });
                    if (is_linked)
                        self.state.variable(referenced_variable).reverse_head = edge_index;
                }
                owner.reference_start = reference_start;
                rebuilt_forward_edges += owner.reference_len;
            }
            std.debug.assert(rebuilt_forward_edges == self.state.live_dependency_edges);

            self.state.dependency_edges.deinit(self.allocator);
            self.state.dependency_edges = dependency_edges;
            dependency_edges = .empty;
            self.state.dependency_compactions += 1;
        }

        fn invalidateReferences(self: *Self, id: VarId) void {
            const variable = self.state.variable(id);
            if (variable.reference_start == invalid_pool_index) return;
            std.debug.assert(self.state.live_dependency_edges >= variable.reference_len);
            self.state.live_dependency_edges -= variable.reference_len;
            variable.reference_start = invalid_pool_index;
            variable.reference_len = 0;
        }

        fn removeValueById(self: *Self, id: VarId) void {
            const variable = self.state.variable(id);
            variable.assigned = null;
            variable.version +%= 1;
            self.invalidateReferences(id);
        }

        fn clearKnowledgeIfInvalidatedBlock(
            self: *Self,
            block: *const AST.Block,
        ) anyerror!void {
            if (comptime memory_and_storage == .ignore) return;
            const collector = try Semantics.SideEffectsCollector.collectBlock(
                self.dialect,
                block,
                self.function_side_effects,
            );
            self.clearInvalidatedKnowledge(collector);
        }

        fn clearKnowledgeIfInvalidatedExpression(
            self: *Self,
            expression: *const AST.Expression,
        ) anyerror!void {
            if (comptime memory_and_storage == .ignore) return;
            const collector = try Semantics.SideEffectsCollector.collectExpression(
                self.dialect,
                expression,
                self.function_side_effects,
            );
            self.clearInvalidatedKnowledge(collector);
        }

        fn clearInvalidatedKnowledge(
            self: *Self,
            collector: Semantics.SideEffectsCollector,
        ) void {
            if (comptime memory_and_storage == .ignore) return;
            if (collector.invalidatesStorage()) self.state.environment.storage.clearRetainingCapacity();
            if (collector.invalidatesMemory()) {
                self.state.environment.memory.clearRetainingCapacity();
                self.state.environment.keccak.clearRetainingCapacity();
            }
        }

        pub fn isSimpleStore(
            self: *const Self,
            location: StoreLoadLocation,
            statement: *const AST.ExpressionStatement,
        ) ?NamePair {
            if (comptime memory_and_storage == .ignore) return null;
            const call = switch (statement.expression) {
                .function_call => |*value| value,
                else => return null,
            };
            const handle = switch (call.function_name) {
                .builtin => |builtin| builtin.handle,
                .identifier => return null,
            };
            if (!optionalHandleEqual(self.store_function_handles[@intFromEnum(location)], handle) or
                call.arguments.items.len != 2) return null;
            const key = switch (call.arguments.items[0]) {
                .identifier => |identifier| identifier.name,
                else => return null,
            };
            const value = switch (call.arguments.items[1]) {
                .identifier => |identifier| identifier.name,
                else => return null,
            };
            return .{ .first = key, .second = value };
        }

        pub fn isSimpleLoad(
            self: *const Self,
            location: StoreLoadLocation,
            expression: *const AST.Expression,
        ) ?YulName {
            if (comptime memory_and_storage == .ignore) return null;
            const call = switch (expression.*) {
                .function_call => |*value| value,
                else => return null,
            };
            const handle = switch (call.function_name) {
                .builtin => |builtin| builtin.handle,
                .identifier => return null,
            };
            if (!optionalHandleEqual(self.load_function_handles[@intFromEnum(location)], handle) or
                call.arguments.items.len != 1) return null;
            return switch (call.arguments.items[0]) {
                .identifier => |identifier| identifier.name,
                else => null,
            };
        }

        fn isKeccak(self: *const Self, expression: *const AST.Expression) ?NamePair {
            if (comptime memory_and_storage == .ignore) return null;
            const call = switch (expression.*) {
                .function_call => |*value| value,
                else => return null,
            };
            const handle = switch (call.function_name) {
                .builtin => |builtin| builtin.handle,
                .identifier => return null,
            };
            if (!optionalHandleEqual(self.dialect.hashFunctionHandle(), handle) or
                call.arguments.items.len != 2) return null;
            const start = switch (call.arguments.items[0]) {
                .identifier => |identifier| identifier.name,
                else => return null,
            };
            const length = switch (call.arguments.items[1]) {
                .identifier => |identifier| identifier.name,
                else => return null,
            };
            return .{ .first = start, .second = length };
        }

        fn joinKnowledge(self: *Self, older: *const EnvironmentSnapshot) !void {
            if (comptime memory_and_storage == .ignore) return;
            joinNameMap(&self.state.environment.storage, &older.storage);
            joinNameMap(&self.state.environment.memory, &older.memory);
            var index: usize = 0;
            while (index < self.state.environment.keccak.len()) {
                const entry = self.state.environment.keccak.items()[index];
                const old_value = older.keccak.get(entry.key);
                if (old_value == null or !old_value.?.eql(entry.value))
                    _ = self.state.environment.keccak.remove(entry.key)
                else
                    index += 1;
            }
        }

        fn cloneEnvironment(self: *const Self) !EnvironmentSnapshot {
            if (comptime memory_and_storage == .analyze)
                return self.state.environment.clone(self.allocator);
            return {};
        }

        fn deinitEnvironment(self: *Self, environment: *EnvironmentSnapshot) void {
            if (comptime memory_and_storage == .analyze)
                environment.deinit(self.allocator);
        }

        fn knowledgeValue(context: ?*const anyopaque, name: YulName) ?*const AST.Expression {
            const self: *const Self = @ptrCast(@alignCast(context orelse return null));
            const assigned = self.variableValue(name) orelse return null;
            return assigned.value;
        }
    };
}

fn optionalHandleEqual(handle: ?BuiltinHandle, expected: BuiltinHandle) bool {
    return if (handle) |value| value.eql(expected) else false;
}

fn removeNameMapValues(map: *NameMap, value: YulName) void {
    var index: usize = 0;
    while (index < map.len()) {
        const entry = map.items()[index];
        if (entry.value.eql(value))
            _ = map.remove(entry.key)
        else
            index += 1;
    }
}

fn removeKeccakReferences(map: *KeccakMap, name: YulName) void {
    var index: usize = 0;
    while (index < map.len()) {
        const entry = map.items()[index];
        if (entry.key.first.eql(name) or entry.key.second.eql(name) or entry.value.eql(name))
            _ = map.remove(entry.key)
        else
            index += 1;
    }
}

fn removeEnvironmentNameReferences(environment: *Environment, name: YulName) void {
    _ = environment.storage.remove(name);
    removeNameMapValues(&environment.storage, name);
    _ = environment.memory.remove(name);
    removeNameMapValues(&environment.memory, name);
    removeKeccakReferences(&environment.keccak, name);
}

fn removeEnvironmentReferences(
    environment: *Environment,
    names: *const NameCollector.NameSet,
) void {
    removeNameMapSetReferences(&environment.storage, names);
    removeNameMapSetReferences(&environment.memory, names);
    var index: usize = 0;
    while (index < environment.keccak.len()) {
        const entry = environment.keccak.items()[index];
        if (names.contains(entry.key.first) or names.contains(entry.key.second) or names.contains(entry.value))
            _ = environment.keccak.remove(entry.key)
        else
            index += 1;
    }
}

fn removeNameMapSetReferences(map: *NameMap, names: *const NameCollector.NameSet) void {
    var index: usize = 0;
    while (index < map.len()) {
        const entry = map.items()[index];
        if (names.contains(entry.key) or names.contains(entry.value))
            _ = map.remove(entry.key)
        else
            index += 1;
    }
}

fn joinNameMap(current: *NameMap, older: *const NameMap) void {
    var index: usize = 0;
    while (index < current.len()) {
        const entry = current.items()[index];
        const old_value = older.get(entry.key);
        if (old_value == null or !old_value.?.eql(entry.value))
            _ = current.remove(entry.key)
        else
            index += 1;
    }
}

test "dense variable IDs are stable within a function frame" {
    const allocator = std.testing.allocator;
    const first_name = try YulName.init("dense_first");
    const second_name = try YulName.init("dense_second");
    var state: State(.ignore) = .{};
    defer state.deinit(allocator);

    const first_id = try state.getOrCreateId(allocator, first_name);
    const second_id = try state.getOrCreateId(allocator, second_name);
    try std.testing.expectEqual(@as(u32, 0), @intFromEnum(first_id));
    try std.testing.expectEqual(@as(u32, 1), @intFromEnum(second_id));
    try std.testing.expectEqual(first_id, try state.getOrCreateId(allocator, first_name));
    try std.testing.expect(state.name(first_id).eql(first_name));
    try std.testing.expect(state.name(second_id).eql(second_name));
    try std.testing.expectEqual(@as(usize, 2), state.variables.items.len);
}

test "sparse variable scratch logically clears stale indices" {
    const allocator = std.testing.allocator;
    const first: VarId = @enumFromInt(1);
    const third: VarId = @enumFromInt(3);
    var set: SparseVarSet = .{};
    defer set.deinit(allocator);

    try set.insert(allocator, third);
    try set.insert(allocator, first);
    try set.insert(allocator, third);
    try std.testing.expectEqual(@as(usize, 2), set.dense.items.len);
    try std.testing.expect(set.contains(first));
    try std.testing.expect(set.contains(third));

    set.clearRetainingCapacity();
    try std.testing.expect(!set.contains(first));
    try std.testing.expect(!set.contains(third));
    try set.insert(allocator, first);
    try std.testing.expect(set.contains(first));
    try std.testing.expect(!set.contains(third));
}

test "scope generations restore while variable versions advance" {
    const allocator = std.testing.allocator;
    const name = try YulName.init("scoped");
    const Analyzer = DataFlowAnalyzer(NoObserver, .ignore);
    var analyzer = Analyzer.init(allocator, .{}, null);
    defer analyzer.deinit();

    try analyzer.pushScope(false);
    _ = try analyzer.declareVariable(name);
    const outer_generation = analyzer.activeScopeGeneration(name).?;
    try analyzer.baseAssignValue(name, null);
    try std.testing.expectEqual(@as(?u64, 1), analyzer.variableVersion(name));

    try analyzer.pushScope(false);
    _ = try analyzer.declareVariable(name);
    const inner_generation = analyzer.activeScopeGeneration(name).?;
    try std.testing.expect(inner_generation > outer_generation);
    analyzer.popScope();
    try std.testing.expectEqual(
        @as(?u32, outer_generation),
        analyzer.activeScopeGeneration(name),
    );
    try std.testing.expectEqual(@as(?u64, 2), analyzer.variableVersion(name));

    analyzer.popScope();
    try std.testing.expectEqual(@as(?u32, null), analyzer.activeScopeGeneration(name));
    try std.testing.expectEqual(@as(?u64, 3), analyzer.variableVersion(name));
}

test "versioned reverse edges ignore stale dependency generations" {
    const allocator = std.testing.allocator;
    const Analyzer = DataFlowAnalyzer(NoObserver, .ignore);
    var analyzer = Analyzer.init(allocator, .{}, null);
    defer analyzer.deinit();

    try analyzer.pushScope(false);
    const first = try analyzer.declareVariable(try YulName.init("first"));
    const second = try analyzer.declareVariable(try YulName.init("second"));
    const dependent = try analyzer.declareVariable(try YulName.init("dependent"));
    try analyzer.setReferences(&.{dependent}, &.{first});
    analyzer.invalidateReferences(dependent);
    try analyzer.setReferences(&.{dependent}, &.{second});

    try analyzer.clearVariableIds(&.{first});
    try std.testing.expectEqual(
        invalid_pool_index,
        analyzer.state.variableConst(first).reverse_head,
    );
    const current = analyzer.state.references(dependent) orelse
        return error.MissingCurrentReferences;
    try std.testing.expectEqualSlices(VarId, &.{second}, current);

    try analyzer.clearVariableIds(&.{second});
    try std.testing.expect(analyzer.state.references(dependent) == null);
}

test "dependency pool compaction does not restore scope-cleared reverse edges" {
    const allocator = std.testing.allocator;
    const Analyzer = DataFlowAnalyzer(NoObserver, .ignore);
    var analyzer = Analyzer.init(allocator, .{}, null);
    defer analyzer.deinit();

    try analyzer.pushScope(false);
    const source_name = try YulName.init("source");
    const source = try analyzer.declareVariable(source_name);
    const dependent = try analyzer.declareVariable(try YulName.init("dependent"));
    try analyzer.setReferences(&.{dependent}, &.{source});

    try analyzer.pushScope(false);
    _ = try analyzer.declareVariable(source_name);
    analyzer.popScope();
    try std.testing.expectEqual(
        invalid_pool_index,
        analyzer.state.variableConst(source).reverse_head,
    );

    try analyzer.compactDependencyPools();
    try std.testing.expectEqual(
        invalid_pool_index,
        analyzer.state.variableConst(source).reverse_head,
    );
    try std.testing.expectEqual(
        @as(usize, 1),
        analyzer.dependencyPoolStats().reverse_edges,
    );

    try analyzer.clearVariableIds(&.{source});
    try std.testing.expect(analyzer.state.references(dependent) != null);
}

test "dependency pool compaction preserves only current reverse edges" {
    const allocator = std.testing.allocator;
    const Analyzer = DataFlowAnalyzer(NoObserver, .ignore);
    var analyzer = Analyzer.init(allocator, .{}, null);
    defer analyzer.deinit();

    try analyzer.pushScope(false);
    const first = try analyzer.declareVariable(try YulName.init("first"));
    const second = try analyzer.declareVariable(try YulName.init("second"));
    const dependent = try analyzer.declareVariable(try YulName.init("dependent"));
    try analyzer.setReferences(&.{dependent}, &.{first});
    analyzer.invalidateReferences(dependent);
    try analyzer.setReferences(&.{dependent}, &.{second});
    try std.testing.expectEqual(@as(usize, 2), analyzer.state.dependency_edges.len);
    try std.testing.expectEqual(@as(usize, 1), analyzer.state.live_dependency_edges);

    try analyzer.compactDependencyPools();
    const stats = analyzer.dependencyPoolStats();
    try std.testing.expectEqual(@as(usize, 1), stats.forward_slots);
    try std.testing.expectEqual(@as(usize, 1), stats.reverse_edges);
    try std.testing.expectEqual(@as(usize, 1), stats.live_edges);
    try std.testing.expectEqual(@as(usize, 1), stats.compactions);

    try analyzer.clearVariableIds(&.{first});
    try std.testing.expect(analyzer.state.references(dependent) != null);
    try analyzer.clearVariableIds(&.{second});
    try std.testing.expect(analyzer.state.references(dependent) == null);
}

test "data-flow analyzer tracks movable declaration values during a walk" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := 1 let y := x pop(y) }",
        "flow.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    const y = try YulName.init("y");
    const Observer = struct {
        y_name: YulName,
        seen_y: bool = false,

        pub fn afterStatement(
            self: *@This(),
            analyzer: *DataFlowAnalyzer(@This(), .ignore),
            _: *const AST.Statement,
        ) anyerror!void {
            if (analyzer.variableValue(self.y_name) != null) self.seen_y = true;
        }
    };
    var observer: Observer = .{ .y_name = y };
    const Analyzer = DataFlowAnalyzer(Observer, .ignore);
    var analyzer = Analyzer.init(allocator, .{}, null);
    defer analyzer.deinit();
    try analyzer.run(&observer, &ast.root_block);
    try std.testing.expect(observer.seen_y);
}

test "function frames reuse an empty dependency-edge buffer" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ " ++
            "function first(a) -> r { let x := a r := x } " ++
            "function second(a) -> r { let x := a r := x } " ++
            "let output := add(first(1), second(2)) " ++
            "}",
        "dependency-edge-reuse.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();

    var observer: NoObserver = .{};
    const Analyzer = DataFlowAnalyzer(NoObserver, .ignore);
    var analyzer = Analyzer.init(allocator, .{}, null);
    defer analyzer.deinit();
    try analyzer.run(&observer, &ast.root_block);

    try std.testing.expect(analyzer.dependency_edge_scratch.capacity != 0);
    try std.testing.expectEqual(@as(usize, 0), analyzer.dependency_edge_scratch.len);
}

test "rewritten expressions retain only final data-flow references" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let old := 1 let replacement := old let target := add(old, old) }",
        "rewritten-references.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();

    const replacement = try YulName.init("replacement");
    const target = try YulName.init("target");
    const Observer = struct {
        allocator: std.mem.Allocator,
        replacement: YulName,
        target: YulName,
        checked: bool = false,

        pub fn visitExpression(
            self: *@This(),
            _: *DataFlowAnalyzer(@This(), .ignore),
            expression: *AST.Expression,
        ) anyerror!ExpressionVisit {
            if (expression.* != .function_call) return .descend;
            const debug_data = if (expression.debugData()) |data| data.* else null;
            expression.deinit(self.allocator);
            expression.* = .{ .identifier = .{
                .debug_data = debug_data,
                .name = self.replacement,
            } };
            return .modified;
        }

        pub fn afterStatement(
            self: *@This(),
            analyzer: *DataFlowAnalyzer(@This(), .ignore),
            statement: *const AST.Statement,
        ) anyerror!void {
            const declaration = switch (statement.*) {
                .variable_declaration => |*value| value,
                else => return,
            };
            if (declaration.variables.items.len != 1 or
                !declaration.variables.items[0].name.eql(self.target)) return;
            const references = analyzer.sortedReferences(self.target) orelse
                return error.MissingFinalExpressionReferences;
            try std.testing.expectEqual(@as(usize, 1), references.len());
            try std.testing.expect(references.at(0).eql(self.replacement));
            self.checked = true;
        }
    };
    var observer: Observer = .{
        .allocator = allocator,
        .replacement = replacement,
        .target = target,
    };
    const Analyzer = DataFlowAnalyzer(Observer, .ignore);
    var analyzer = Analyzer.init(allocator, .{}, null);
    defer analyzer.deinit();
    try analyzer.run(&observer, &ast.root_block);
    try std.testing.expect(observer.checked);
}

test "data-flow simple stores, loads, and hashes require exact builtin arity" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../asm_parser.zig").Parser;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ mstore(key, value) mstore(key, value, extra) " ++
            "let a := mload(key) let b := mload(key, extra) " ++
            "let c := keccak256(key, value) let d := keccak256(key, value, extra) }",
        "arity.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    const key = try YulName.init("key");
    const value = try YulName.init("value");
    const statements = ast.root().statements.items;
    try std.testing.expectEqual(@as(usize, 6), statements.len);

    const Analyzer = DataFlowAnalyzer(NoObserver, .analyze);
    var analyzer = Analyzer.init(allocator, dialect.dialect(), null);
    defer analyzer.deinit();
    const store = analyzer.isSimpleStore(.memory, &statements[0].expression_statement).?;
    try std.testing.expect(store.first.eql(key));
    try std.testing.expect(store.second.eql(value));
    try std.testing.expect(analyzer.isSimpleStore(.memory, &statements[1].expression_statement) == null);
    try std.testing.expect(analyzer.isSimpleLoad(
        .memory,
        statements[2].variable_declaration.value.?,
    ).?.eql(key));
    try std.testing.expect(analyzer.isSimpleLoad(
        .memory,
        statements[3].variable_declaration.value.?,
    ) == null);
    const hash = analyzer.isKeccak(statements[4].variable_declaration.value.?).?;
    try std.testing.expect(hash.first.eql(key));
    try std.testing.expect(hash.second.eql(value));
    try std.testing.expect(analyzer.isKeccak(statements[5].variable_declaration.value.?) == null);
}

test "ignore-only analyzer erases environment storage" {
    const IgnoreAnalyzer = DataFlowAnalyzer(NoObserver, .ignore);
    const AnalyzeAnalyzer = DataFlowAnalyzer(NoObserver, .analyze);
    try std.testing.expect(@sizeOf(IgnoreAnalyzer) < @sizeOf(AnalyzeAnalyzer));
}
