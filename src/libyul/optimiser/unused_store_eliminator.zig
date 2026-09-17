// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Removes memory and storage writes that are overwritten or never observed.

const std = @import("std");
const AST = @import("../ast.zig");
const CallGraph = @import("call_graph_generator.zig");
const ControlFlowCollector = @import("../control_flow_side_effects_collector.zig").ControlFlowSideEffectsCollector;
const ControlFlowSideEffects = @import("../control_flow_side_effects.zig").ControlFlowSideEffects;
const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
const Instruction = @import("../../libevmasm/instruction.zig").Instruction;
const KnowledgeBaseModule = @import("knowledge_base.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const OptimizerUtilities = @import("optimizer_utilities.zig");
const SemanticInformation = @import("../../libevmasm/semantic_information.zig");
const Semantics = @import("semantics.zig");
const SSAValueTrackerModule = @import("ssa_value_tracker.zig");
const UnusedStoreBaseModule = @import("unused_store_base.zig");
const Utilities = @import("../utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

const Key = UnusedStoreBaseModule.UnusedStoreEliminatorKey;
const Base = UnusedStoreBaseModule.UnusedStoreBase(Key);
const ValueMap = SSAValueTrackerModule.ValueMap;
const FunctionSideEffects = Semantics.FunctionSideEffects;
const Location = SemanticInformation.Location;
const Effect = SemanticInformation.Effect;

pub const OperationLength = union(enum) {
    name: YulName,
    value: u256,
};

pub const Operation = struct {
    location: Location,
    effect: Effect,
    start: ?YulName = null,
    length: ?OperationLength = null,
};

const OperationList = struct {
    items: [6]Operation = undefined,
    len: usize = 0,

    fn append(self: *OperationList, operation: Operation) !void {
        if (self.len == self.items.len) return error.TooManyOperations;
        self.items[self.len] = operation;
        self.len += 1;
    }

    fn slice(self: *const OperationList) []const Operation {
        return self.items[0..self.len];
    }
};

const StoreOperationMap = std.AutoHashMap(*const AST.Statement, Operation);

pub const UnusedStoreEliminator = struct {
    allocator: std.mem.Allocator,
    base: Base,
    ignore_memory: bool,
    function_side_effects: *const FunctionSideEffects,
    control_flow_side_effects: *const std.AutoHashMap(YulName, ControlFlowSideEffects),
    ssa_values: *const ValueMap,
    store_operations: StoreOperationMap,
    store_operation_stack: std.ArrayList(StoreOperationMap) = .empty,
    knowledge_base: KnowledgeBaseModule.KnowledgeBase,

    pub const name = "UnusedStoreEliminator";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        var graph = try CallGraph.CallGraphGenerator.callGraph(allocator, ast);
        defer graph.deinit();
        var function_side_effects = try Semantics.SideEffectsPropagator.sideEffects(
            allocator,
            context.dialect,
            &graph,
        );
        defer function_side_effects.deinit(allocator);

        var tracker = SSAValueTrackerModule.SSAValueTracker.init(allocator);
        defer tracker.deinit();
        try tracker.run(ast);

        const ignore_memory = try Semantics.MSizeFinder.containsMSize(context.dialect, ast);
        var control_collector = try ControlFlowCollector.init(allocator, context.dialect, ast);
        defer control_collector.deinit();
        var control_effects = try control_collector.functionSideEffectsNamed(allocator);
        defer control_effects.deinit();

        const provider: KnowledgeBaseModule.ValueProvider = .{
            .context = tracker.values(),
            .get_value = valueProvider,
        };
        var eliminator: UnusedStoreEliminator = .{
            .allocator = allocator,
            .base = Base.init(allocator, context.dialect),
            .ignore_memory = ignore_memory,
            .function_side_effects = &function_side_effects,
            .control_flow_side_effects = &control_effects,
            .ssa_values = tracker.values(),
            .store_operations = StoreOperationMap.init(allocator),
            .knowledge_base = KnowledgeBaseModule.KnowledgeBase.init(
                allocator,
                provider,
                context.dialect,
                true,
            ),
        };
        defer eliminator.deinit();
        eliminator.base.hooks = .{
            .context = &eliminator,
            .function_call = visitFunctionCall,
            .enter_function = enterFunction,
            .finalize_function = finalizeFunction,
            .leave_function = leaveFunction,
            .leave_statement = visitLeave,
            .after_statement = afterStatement,
            .shortcut_nested_loop = shortcutNestedLoop,
        };
        try eliminator.base.run(ast);

        if (EVMDialectModule.fromDialect(context.dialect)) |evm_dialect| {
            if (evm_dialect.providesObjectAccess())
                try eliminator.clearActive(.Memory)
            else
                try eliminator.markActiveAsUsed(.Memory);
        } else {
            try eliminator.markActiveAsUsed(.Memory);
        }
        try eliminator.markActiveAsUsed(.Storage);
        try eliminator.base.addCurrentUnusedStoresToRemoval();

        var to_remove = try eliminator.base.removalSet();
        defer to_remove.deinit();
        try OptimizerUtilities.StatementRemover.run(allocator, ast, &to_remove);
    }

    fn deinit(self: *UnusedStoreEliminator) void {
        self.knowledge_base.deinit();
        self.store_operations.deinit();
        for (self.store_operation_stack.items) |*operations| operations.deinit();
        self.store_operation_stack.deinit(self.allocator);
        self.base.deinit();
        self.* = undefined;
    }

    fn fromContext(context: ?*anyopaque) *UnusedStoreEliminator {
        return @ptrCast(@alignCast(context.?));
    }

    fn valueProvider(context: ?*const anyopaque, variable_name: YulName) ?*const AST.Expression {
        const values: *const ValueMap = @ptrCast(@alignCast(context.?));
        return values.get(variable_name);
    }

    fn visitFunctionCall(
        context: ?*anyopaque,
        _: *Base,
        call: *const AST.FunctionCall,
    ) anyerror!void {
        const self = fromContext(context);
        const operations = try self.operationsFromFunctionCall(call);
        for (operations.slice()) |operation| try self.applyOperation(operation);

        const effects = if (try Utilities.resolveBuiltinFunction(&call.function_name, self.base.dialect)) |builtin|
            builtin.control_flow_side_effects
        else switch (call.function_name) {
            .identifier => |identifier| self.control_flow_side_effects.get(identifier.name) orelse
                return error.UnknownFunction,
            .builtin => unreachable,
        };
        if (effects.can_terminate) try self.markActiveAsUsed(.Storage);
        if (!effects.can_continue) {
            try self.clearActive(.Memory);
            if (!effects.can_terminate) try self.clearActive(.Storage);
        }
    }

    fn enterFunction(
        context: ?*anyopaque,
        _: *Base,
        _: *const AST.FunctionDefinition,
    ) anyerror!void {
        const self = fromContext(context);
        try self.store_operation_stack.append(self.allocator, self.store_operations);
        self.store_operations = StoreOperationMap.init(self.allocator);
    }

    fn finalizeFunction(
        context: ?*anyopaque,
        _: *Base,
        _: *const AST.FunctionDefinition,
    ) anyerror!void {
        try fromContext(context).markActiveAsUsed(null);
    }

    fn leaveFunction(
        context: ?*anyopaque,
        _: *Base,
        _: *const AST.FunctionDefinition,
    ) anyerror!void {
        const self = fromContext(context);
        self.store_operations.deinit();
        self.store_operations = self.store_operation_stack.pop().?;
    }

    fn visitLeave(
        context: ?*anyopaque,
        _: *Base,
        _: *const AST.Leave,
    ) anyerror!void {
        try fromContext(context).markActiveAsUsed(null);
    }

    fn shortcutNestedLoop(
        context: ?*anyopaque,
        _: *Base,
        _: *const Base.ActiveStores,
    ) anyerror!void {
        try fromContext(context).markActiveAsUsed(null);
    }

    fn afterStatement(
        context: ?*anyopaque,
        _: *Base,
        statement: *const AST.Statement,
    ) anyerror!void {
        const self = fromContext(context);
        const expression_statement = switch (statement.*) {
            .expression_statement => |*value| value,
            else => return,
        };
        const call = switch (expression_statement.expression) {
            .function_call => |*value| value,
            else => return error.InvalidAst,
        };
        const instruction = OptimizerUtilities.toEVMInstruction(
            self.base.dialect,
            &call.function_name,
        ) orelse return;
        for (call.arguments.items) |argument| switch (argument) {
            .identifier, .literal => {},
            .function_call => return,
        };

        const is_storage_write = instruction == .SSTORE;
        const is_memory_write = switch (instruction) {
            .EXTCODECOPY,
            .CODECOPY,
            .CALLDATACOPY,
            .RETURNDATACOPY,
            .MSTORE,
            .MSTORE8,
            => true,
            else => false,
        };
        if (!is_storage_write and (self.ignore_memory or !is_memory_write)) return;

        if (instruction == .RETURNDATACOPY and !try self.safeReturndataCopy(call)) return;

        const operations = try self.operationsFromFunctionCall(call);
        if (operations.len != 1) return error.InvalidStoreOperation;
        const operation = operations.items[0];
        try self.base.all_stores.put(statement, {});
        switch (operation.location) {
            .Storage => try (try self.base.activeSet(.Storage)).put(statement, {}),
            .Memory => try (try self.base.activeSet(.Memory)).put(statement, {}),
            .TransientStorage => return error.InvalidStoreLocation,
        }
        try self.store_operations.put(statement, operation);
    }

    fn safeReturndataCopy(self: *UnusedStoreEliminator, call: *const AST.FunctionCall) anyerror!bool {
        if (call.arguments.items.len != 3) return false;
        const start_offset = self.identifierNameIfSSA(&call.arguments.items[1]) orelse return false;
        const length = self.identifierNameIfSSA(&call.arguments.items[2]) orelse return false;
        const length_expression = self.ssa_values.get(length) orelse return false;
        const length_call = switch (length_expression.*) {
            .function_call => |*value| value,
            else => return false,
        };
        return try self.knowledge_base.knownToBeZero(start_offset) and
            OptimizerUtilities.toEVMInstruction(self.base.dialect, &length_call.function_name) ==
                Instruction.RETURNDATASIZE;
    }

    fn operationsFromFunctionCall(
        self: *UnusedStoreEliminator,
        call: *const AST.FunctionCall,
    ) anyerror!OperationList {
        const side_effects = if (try Utilities.resolveBuiltinFunction(&call.function_name, self.base.dialect)) |builtin|
            builtin.side_effects
        else switch (call.function_name) {
            .identifier => |identifier| (self.function_side_effects.get(.{ .user = identifier.name }) orelse
                return error.UnknownFunction).*,
            .builtin => unreachable,
        };

        const instruction = OptimizerUtilities.toEVMInstruction(
            self.base.dialect,
            &call.function_name,
        ) orelse {
            var result: OperationList = .{};
            if (side_effects.memory != .none)
                try result.append(.{ .location = .Memory, .effect = .Read });
            if (side_effects.storage != .none)
                try result.append(.{ .location = .Storage, .effect = .Read });
            return result;
        };

        var result: OperationList = .{};
        const operations = try SemanticInformation.readWriteOperations(instruction);
        for (operations.slice()) |operation| {
            if (operation.location == .TransientStorage) continue;
            var translated: Operation = .{
                .location = operation.location,
                .effect = operation.effect,
            };
            if (operation.start_parameter) |index|
                translated.start = self.identifierNameIfSSA(&call.arguments.items[index]);
            if (operation.length_parameter) |index| {
                if (self.identifierNameIfSSA(&call.arguments.items[index])) |variable_name|
                    translated.length = .{ .name = variable_name };
            }
            if (operation.length_constant) |length|
                translated.length = .{ .value = @intCast(length) };
            try result.append(translated);
        }
        return result;
    }

    fn applyOperation(self: *UnusedStoreEliminator, operation: Operation) anyerror!void {
        const key: Key = switch (operation.location) {
            .Storage => .Storage,
            .Memory => .Memory,
            .TransientStorage => return,
        };
        const active = try self.base.activeSet(key);
        var to_remove: std.ArrayList(*const AST.Statement) = .empty;
        defer to_remove.deinit(self.allocator);
        var iterator = active.keyIterator();
        while (iterator.next()) |statement| {
            const store_operation = self.store_operations.get(statement.*) orelse
                return error.MissingStoreOperation;
            if (operation.effect == .Read and !try self.knownUnrelated(store_operation, operation)) {
                try self.base.used_stores.put(statement.*, {});
                try to_remove.append(self.allocator, statement.*);
            } else if (operation.effect == .Write and
                try self.knownCovered(store_operation, operation))
            {
                try to_remove.append(self.allocator, statement.*);
            }
        }
        for (to_remove.items) |statement| _ = active.remove(statement);
    }

    fn knownUnrelated(
        self: *UnusedStoreEliminator,
        first: Operation,
        second: Operation,
    ) anyerror!bool {
        if (first.location != second.location) return true;
        if (first.location == .Storage) {
            if (first.start != null and second.start != null)
                return self.knowledge_base.knownToBeDifferent(first.start.?, second.start.?);
            return false;
        }
        if (first.location != .Memory) return false;
        if ((try self.optionalLengthValue(first.length)) == 0 or
            (try self.optionalLengthValue(second.length)) == 0)
            return true;

        if (first.start != null and first.length != null and second.start != null) {
            const length = try self.lengthValue(first.length.?);
            const start_first = try self.knowledge_base.valueIfKnownConstant(first.start.?);
            const start_second = try self.knowledge_base.valueIfKnownConstant(second.start.?);
            if (length != null and start_first != null and start_second != null) {
                const end = start_first.? +% length.?;
                if (end >= start_first.? and end <= start_second.?) return true;
            }
        }
        if (second.start != null and second.length != null and first.start != null) {
            const length = try self.lengthValue(second.length.?);
            const start_second = try self.knowledge_base.valueIfKnownConstant(second.start.?);
            const start_first = try self.knowledge_base.valueIfKnownConstant(first.start.?);
            if (length != null and start_second != null and start_first != null) {
                const end = start_second.? +% length.?;
                if (end >= start_second.? and end <= start_first.?) return true;
            }
        }
        if (first.start != null and first.length != null and second.start != null and second.length != null) {
            const first_length = try self.lengthValue(first.length.?);
            const second_length = try self.lengthValue(second.length.?);
            if (first_length != null and first_length.? <= 32 and
                second_length != null and second_length.? <= 32 and
                try self.knowledge_base.knownToBeDifferentByAtLeast32(first.start.?, second.start.?))
                return true;
        }
        return false;
    }

    fn knownCovered(
        self: *UnusedStoreEliminator,
        covered: Operation,
        covering: Operation,
    ) anyerror!bool {
        if (covered.location != covering.location) return false;
        if (optionalNameEqual(covered.start, covering.start) and
            optionalLengthEqual(covered.length, covering.length) and
            covered.start != null and covered.length != null)
            return true;
        if (covered.location != .Memory) return false;
        if ((try self.optionalLengthValue(covered.length)) == 0) return true;
        if (covered.start == null or covering.start == null or
            covered.length == null or covering.length == null)
            return false;

        const covered_length = try self.lengthValue(covered.length.?);
        const covering_length = try self.lengthValue(covering.length.?);
        if (covered.start.?.eql(covering.start.?))
            if (covered_length != null and covering_length != null and
                covered_length.? <= covering_length.?)
                return true;

        const covered_start = try self.knowledge_base.valueIfKnownConstant(covered.start.?);
        const covering_start = try self.knowledge_base.valueIfKnownConstant(covering.start.?);
        if (covered_start != null and covering_start != null and
            covered_length != null and covering_length != null)
        {
            const covering_end = covering_start.? +% covering_length.?;
            const covered_end = covered_start.? +% covered_length.?;
            if (covering_start.? <= covered_start.? and
                covering_end >= covering_start.? and
                covered_end >= covered_start.? and
                covered_end <= covering_end)
                return true;
        }
        return false;
    }

    fn markActiveAsUsed(self: *UnusedStoreEliminator, only_location: ?Location) !void {
        if (only_location == null or only_location.? == .Memory)
            try self.markKeyActiveAsUsed(.Memory);
        if (only_location == null or only_location.? == .Storage)
            try self.markKeyActiveAsUsed(.Storage);
    }

    fn markKeyActiveAsUsed(self: *UnusedStoreEliminator, key: Key) !void {
        const active = try self.base.activeSet(key);
        var iterator = active.keyIterator();
        while (iterator.next()) |statement| try self.base.used_stores.put(statement.*, {});
        active.clearRetainingCapacity();
    }

    fn clearActive(self: *UnusedStoreEliminator, only_location: ?Location) !void {
        if (only_location == null or only_location.? == .Memory)
            try self.base.clearActiveKey(.Memory);
        if (only_location == null or only_location.? == .Storage)
            try self.base.clearActiveKey(.Storage);
    }

    fn identifierNameIfSSA(self: *const UnusedStoreEliminator, expression: *const AST.Expression) ?YulName {
        return switch (expression.*) {
            .identifier => |identifier| if (self.ssa_values.contains(identifier.name)) identifier.name else null,
            else => null,
        };
    }

    fn lengthValue(self: *UnusedStoreEliminator, length: OperationLength) anyerror!?u256 {
        return switch (length) {
            .name => |variable_name| self.knowledge_base.valueIfKnownConstant(variable_name),
            .value => |value| value,
        };
    }

    fn optionalLengthValue(
        self: *UnusedStoreEliminator,
        length: ?OperationLength,
    ) anyerror!?u256 {
        return if (length) |value| self.lengthValue(value) else null;
    }
};

fn optionalNameEqual(first: ?YulName, second: ?YulName) bool {
    if (first == null or second == null) return first == null and second == null;
    return first.?.eql(second.?);
}

fn optionalLengthEqual(first: ?OperationLength, second: ?OperationLength) bool {
    if (first == null or second == null) return first == null and second == null;
    return switch (first.?) {
        .name => |name| switch (second.?) {
            .name => |other| name.eql(other),
            .value => false,
        },
        .value => |value| switch (second.?) {
            .name => false,
            .value => |other| value == other,
        },
    };
}

test "unused store eliminator removes an overwritten memory write" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = EVMDialectModule.EVMDialect;
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
        "{ let p := 0 let a := 1 let b := 2 mstore(p, a) mstore(p, b) pop(mload(p)) }",
        "unused-store.yul",
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
    try UnusedStoreEliminator.run(&context, &ast.root_block);
    try std.testing.expectEqual(@as(usize, 5), ast.root().statements.items.len);
}
