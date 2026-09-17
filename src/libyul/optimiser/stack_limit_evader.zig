// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Assigns path-reusable fixed memory slots to stack-unreachable variables,
//! invokes StackToMemoryMover, and advances matching `memoryguard` calls.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const ASTCopier = @import("ast_copier.zig").ASTCopier;
const AsmAnalysis = @import("../asm_analysis.zig");
const CallGraphModule = @import("call_graph_generator.zig");
const Compilability = @import("../compilability_checker.zig");
const ControlFlowGraphBuilder = @import("../backends/evm/control_flow_graph_builder.zig").ControlFlowGraphBuilder;
const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
const FunctionCallFinder = @import("function_call_finder.zig");
const NameCollector = @import("name_collector.zig");
const Numeric = @import("../../libsolutil/numeric.zig");
const Object = @import("../object.zig").Object;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const StackLayout = @import("../backends/evm/stack_layout_generator.zig");
const StackToMemory = @import("stack_to_memory_mover.zig");
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

const SlotsRequiredMap = ordered.OrderedMap(AST.FunctionHandle, u64, lessFunctionHandle);

pub const MemoryOffsetAllocator = struct {
    allocator: std.mem.Allocator,
    unreachable_variables: *const Compilability.UnreachableVariables,
    call_graph: *const CallGraphModule.FunctionCalls,
    function_definitions: *const NameCollector.FunctionDefinitionMap,
    reachable_stack_depth: usize,
    slot_allocations: StackToMemory.MemorySlotMap = .{},
    slots_required_for_function: SlotsRequiredMap = .{},

    pub fn deinit(self: *MemoryOffsetAllocator) void {
        self.slot_allocations.deinit(self.allocator);
        self.slots_required_for_function.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn run(self: *MemoryOffsetAllocator, function: AST.FunctionHandle) !u64 {
        if (self.slots_required_for_function.get(function)) |required| return required.*;
        _ = try self.slots_required_for_function.insert(self.allocator, function, 0);

        const function_name = switch (function) {
            .builtin => return 0,
            .user => |name| name,
        };
        var required_slots: u64 = 0;
        if (self.call_graph.get(function)) |children| {
            for (children.items) |child|
                required_slots = @max(required_slots, try self.run(child));
        }

        if (self.unreachable_variables.get(function_name)) |unreachables| {
            if (self.function_definitions.get(function_name)) |definition_pointer| {
                const definition = definition_pointer.*;
                const total_arg_count = definition.parameters.items.len +
                    definition.return_variables.items.len;
                if (total_arg_count > self.reachable_stack_depth) {
                    var remaining = total_arg_count - self.reachable_stack_depth;
                    for (definition.parameters.items) |parameter| {
                        if (remaining == 0) break;
                        try self.allocate(parameter.name, &required_slots);
                        remaining -= 1;
                    }
                    for (definition.return_variables.items) |return_variable| {
                        if (remaining == 0) break;
                        try self.allocate(return_variable.name, &required_slots);
                        remaining -= 1;
                    }
                }
            }
            for (unreachables.items) |variable| {
                if (!variable.empty() and !self.slot_allocations.contains(variable))
                    try self.allocate(variable, &required_slots);
            }
        }

        _ = try self.slots_required_for_function.fetchPut(
            self.allocator,
            function,
            required_slots,
        );
        return required_slots;
    }

    fn allocate(self: *MemoryOffsetAllocator, variable: YulName, next_slot: *u64) !void {
        _ = try self.slot_allocations.fetchPut(self.allocator, variable, next_slot.*);
        next_slot.* = std.math.add(u64, next_slot.*, 1) catch
            return error.TooManyMemorySlots;
    }
};

pub const StackLimitEvader = struct {
    pub fn runObject(
        context: *OptimiserStepContext,
        object: *const Object,
    ) !AST.Block {
        const code = object.code() orelse return error.MissingObjectCode;
        const evm_dialect = try requireObjectDialect(context.dialect);
        var copier = ASTCopier.init(context.dispenser.allocator);
        var ast_root = try copier.translateBlock(code.root());
        errdefer ast_root.deinit(context.dispenser.allocator);

        if (evm_dialect.evmVersion().canOverchargeGasForCall()) {
            var structure = try object.summarizeStructure();
            defer structure.deinit();
            var analysis_info = try AsmAnalysis.analyzeStrictBlock(
                context.dispenser.allocator,
                context.dialect,
                &ast_root,
                &structure,
                AsmAnalysis.instructionValidatorForEVMDialect(evm_dialect),
            );
            defer analysis_info.deinit();
            var cfg = try ControlFlowGraphBuilder.build(
                context.dispenser.allocator,
                &analysis_info,
                context.dialect,
                &ast_root,
            );
            defer cfg.deinit();
            var stack_errors = try StackLayout.StackLayoutGenerator.reportStackTooDeepAll(
                context.dispenser.allocator,
                &cfg,
                evm_dialect,
            );
            defer StackLayout.deinitStackTooDeepByFunction(
                context.dispenser.allocator,
                &stack_errors,
            );
            try runWithStackTooDeep(context, &ast_root, &stack_errors);
        } else {
            var checker = try Compilability.CompilabilityChecker.init(
                context.dispenser.allocator,
                object,
                true,
            );
            defer checker.deinit();
            try runWithUnreachableVariables(
                context,
                &ast_root,
                checker.unreachableVariables(),
            );
        }
        return ast_root;
    }

    pub fn runWithStackTooDeep(
        context: *OptimiserStepContext,
        ast_root: *AST.Block,
        stack_too_deep_errors: *const StackLayout.StackTooDeepByFunction,
    ) !void {
        _ = try requireObjectDialect(context.dialect);
        const allocator = context.dispenser.allocator;
        var unreachable_variables: Compilability.UnreachableVariables = .{};
        defer deinitUnreachableVariables(allocator, &unreachable_variables);

        var errors_iterator = stack_too_deep_errors.iterator();
        while (errors_iterator.next()) |entry| {
            var unreachables: std.ArrayList(YulName) = .empty;
            errdefer unreachables.deinit(allocator);
            for (entry.value_ptr.items) |stack_error| {
                const count = @min(stack_error.deficit, stack_error.variable_choices.items.len);
                for (stack_error.variable_choices.items[0..count]) |variable| {
                    if (!containsName(unreachables.items, variable))
                        try unreachables.append(allocator, variable);
                }
            }
            _ = try unreachable_variables.insert(allocator, entry.key_ptr.*, unreachables);
            unreachables = .empty;
        }
        try runWithUnreachableVariables(context, ast_root, &unreachable_variables);
    }

    pub fn runWithUnreachableVariables(
        context: *OptimiserStepContext,
        ast_root: *AST.Block,
        unreachable_variables: *const Compilability.UnreachableVariables,
    ) !void {
        const evm_dialect = try requireObjectDialect(context.dialect);
        const allocator = context.dispenser.allocator;
        const memory_guard_handle = context.dialect.findBuiltin("memoryguard") orelse
            return error.MissingMemoryGuardBuiltin;
        var memory_guard_calls = try FunctionCallFinder.findFunctionCalls(
            allocator,
            ast_root,
            .{ .builtin = memory_guard_handle },
        );
        defer memory_guard_calls.deinit(allocator);
        if (memory_guard_calls.items.len == 0) return;

        const reserved_memory = try literalArgumentValue(memory_guard_calls.items[0]);
        const limit: u256 = (@as(u256, 1) << 32) - 1;
        if (reserved_memory >= limit) return error.ReservedMemoryTooLarge;
        for (memory_guard_calls.items) |call|
            if (try literalArgumentValue(call) != reserved_memory) return;

        var call_graph = try CallGraphModule.CallGraphGenerator.callGraph(allocator, ast_root);
        defer call_graph.deinit();
        var recursive_functions = try call_graph.recursiveFunctions();
        defer recursive_functions.deinit(allocator);
        for (0..recursive_functions.len()) |index| switch (recursive_functions.at(index)) {
            .builtin => return error.BuiltinCannotBeRecursive,
            .user => |function_name| if (unreachable_variables.contains(function_name)) return,
        };

        var function_definitions = try NameCollector.allFunctionDefinitions(allocator, ast_root);
        defer function_definitions.deinit(allocator);
        var memory_allocator: MemoryOffsetAllocator = .{
            .allocator = allocator,
            .unreachable_variables = unreachable_variables,
            .call_graph = &call_graph.function_calls,
            .function_definitions = &function_definitions,
            .reachable_stack_depth = evm_dialect.reachableStackDepth(),
        };
        defer memory_allocator.deinit();
        const required_slots = try memory_allocator.run(.{ .user = .{} });
        if (required_slots >= std.math.maxInt(u32)) return error.TooManyMemorySlots;

        memory_guard_calls.deinit(allocator);
        memory_guard_calls = .empty;
        try StackToMemory.StackToMemoryMover.run(
            context,
            reserved_memory,
            &memory_allocator.slot_allocations,
            required_slots,
            ast_root,
        );

        const final_reserved_memory = std.math.add(
            u256,
            reserved_memory,
            @as(u256, required_slots) * 32,
        ) catch return error.MemoryOffsetOverflow;
        var updated_calls = try FunctionCallFinder.findFunctionCalls(
            allocator,
            ast_root,
            .{ .builtin = memory_guard_handle },
        );
        defer updated_calls.deinit(allocator);
        for (updated_calls.items) |call| {
            if (call.arguments.items.len != 1 or call.arguments.items[0] != .literal)
                return error.InvalidMemoryGuardCall;
            const literal = &call.arguments.items[0].literal;
            if (literal.kind != .Number) return error.InvalidMemoryGuardCall;
            literal.value.deinit(allocator);
            literal.value = .{
                .numeric_value = final_reserved_memory,
                .string_value = try Numeric.toCompactHexWithPrefixAlloc(
                    u256,
                    allocator,
                    final_reserved_memory,
                ),
            };
        }
    }
};

fn requireObjectDialect(dialect: AST.Dialect) !*const EVMDialectModule.EVMDialect {
    const evm_dialect = EVMDialectModule.fromDialect(dialect) orelse
        return error.EVMDialectWithObjectAccessRequired;
    if (!evm_dialect.providesObjectAccess())
        return error.EVMDialectWithObjectAccessRequired;
    return evm_dialect;
}

fn literalArgumentValue(call: *const AST.FunctionCall) !u256 {
    if (call.arguments.items.len != 1 or call.arguments.items[0] != .literal)
        return error.InvalidMemoryGuardCall;
    const literal = &call.arguments.items[0].literal;
    if (literal.kind != .Number) return error.InvalidMemoryGuardCall;
    return literal.value.value() catch error.InvalidMemoryGuardCall;
}

fn containsName(names: []const YulName, needle: YulName) bool {
    for (names) |name| if (name.eql(needle)) return true;
    return false;
}

fn deinitUnreachableVariables(
    allocator: std.mem.Allocator,
    variables: *Compilability.UnreachableVariables,
) void {
    for (variables.mutableItems()) |*entry| entry.value.deinit(allocator);
    variables.deinit(allocator);
}

test "stack limit evader moves a top-level variable and advances memoryguard" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const DebugInfoSelection = @import("../../liblangutil/debug_info_selection.zig").DebugInfoSelection;
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;

    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, EVMVersion.current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ mstore(0x40, memoryguard(0x80)) let x := 42 sstore(0, x) }",
        "stack-limit.yul",
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
        &ast.root_block,
        &reserved,
    );
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = dialect.dialect(),
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    var unreachables: Compilability.UnreachableVariables = .{};
    defer deinitUnreachableVariables(allocator, &unreachables);
    var top_level: std.ArrayList(YulName) = .empty;
    try top_level.append(allocator, try YulName.init("x"));
    _ = try unreachables.insert(allocator, .{}, top_level);

    try StackLimitEvader.runWithUnreachableVariables(
        &context,
        &ast.root_block,
        &unreachables,
    );
    var printer = Printer.init(
        allocator,
        dialect.dialect(),
        &.{},
        DebugInfoSelection.defaultValue(),
        null,
    );
    const rendered = try printer.renderBlock(&ast.root_block);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "memoryguard(0xa0)") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "mstore(0x80, 42)") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "sstore(0, mload(0x80))") != null);

    var no_stack_errors = StackLayout.StackTooDeepByFunction.init(allocator);
    defer StackLayout.deinitStackTooDeepByFunction(allocator, &no_stack_errors);
    try StackLimitEvader.runWithStackTooDeep(
        &context,
        &ast.root_block,
        &no_stack_errors,
    );
}

test "object-driven stack limit evasion selects and runs the backend" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../asm_parser.zig").Parser;
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;

    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, EVMVersion.current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const parsed = (try Parser.parseSource(
        allocator,
        "{ mstore(0x40, memoryguard(0x80)) let x := 1 pop(x) }",
        "stack-limit-object.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    const object = try Object.create(allocator, "");
    defer object.destroy();
    object.setCode(parsed, null);
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(
        allocator,
        dialect.dialect(),
        object.code().?.root(),
        &reserved,
    );
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = dialect.dialect(),
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    var transformed = try StackLimitEvader.runObject(&context, object);
    defer transformed.deinit(allocator);
    try std.testing.expect(transformed.statements.items.len != 0);
}
