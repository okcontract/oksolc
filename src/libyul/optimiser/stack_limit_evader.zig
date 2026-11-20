// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Assigns path-reusable fixed memory slots to stack-unreachable variables,
//! invokes StackToMemoryMover, and advances matching `memoryguard` calls.

const std = @import("std");
const AST = @import("../ast.zig");
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

const MemoryOffsetAllocator = struct {
    allocator: std.mem.Allocator,
    unreachable_variables: *const Compilability.UnreachableVariables,
    call_graph: *const CallGraphModule.FunctionCalls,
    components: *const CallGraphModule.Components,
    function_definitions: *const NameCollector.FunctionDefinitionMap,
    reachable_stack_depth: usize,
    slot_allocations: StackToMemory.MemorySlotMap = .{},

    fn deinit(self: *MemoryOffsetAllocator) void {
        self.slot_allocations.deinit(self.allocator);
        self.* = undefined;
    }

    const Requirement = struct {
        reachable: bool = false,
        slots: u64 = 0,
    };

    fn run(self: *MemoryOffsetAllocator, function: AST.FunctionHandle) !u64 {
        const components = self.components;
        const root = components.component_of.get(function) orelse return error.MissingCallGraphNode;
        const requirements = try self.allocator.alloc(Requirement, root + 1);
        defer self.allocator.free(requirements);
        @memset(requirements, .{});

        // Tarjan emits callees before callers. Walk backwards to mark the
        // closure of the entry point so uncalled functions receive no slots.
        requirements[root].reachable = true;
        var remaining = requirements.len;
        while (remaining != 0) {
            remaining -= 1;
            if (!requirements[remaining].reachable) continue;
            for (components.groups.items[remaining]) |node| {
                const children = self.call_graph.get(components.handles[node]) orelse continue;
                for (children.items) |child| {
                    const child_id = components.component_of.get(child) orelse return error.MissingCallGraphNode;
                    if (child_id > remaining) return error.InvalidComponentOrder;
                    requirements[child_id].reachable = true;
                }
            }
        }

        // Every member of a recursive component has the same reachable
        // callees. Propagate their completed slot requirements as one value.
        for (requirements, 0..) |*requirement, component_id| {
            if (!requirement.reachable) continue;
            const members = components.groups.items[component_id];
            var required_slots: u64 = 0;
            for (members) |node| {
                const children = self.call_graph.get(components.handles[node]) orelse continue;
                for (children.items) |child| {
                    const child_id = components.component_of.get(child).?;
                    if (child_id != component_id)
                        required_slots = @max(required_slots, requirements[child_id].slots);
                }
            }
            if (!components.recursive[component_id]) switch (components.handles[members[0]]) {
                .user => |name| try self.allocateFunction(name, &required_slots),
                .builtin => {},
            };
            requirement.slots = required_slots;
        }
        return requirements[root].slots;
    }

    fn allocateFunction(self: *MemoryOffsetAllocator, function_name: YulName, required_slots: *u64) !void {
        if (self.unreachable_variables.get(function_name)) |unreachables| {
            if (self.function_definitions.get(function_name)) |definition_pointer| {
                const definition = definition_pointer.*;
                const total_arg_count = definition.parameters.items.len +
                    definition.return_variables.items.len;
                if (total_arg_count > self.reachable_stack_depth) {
                    var remaining = total_arg_count - self.reachable_stack_depth;
                    for (definition.parameters.items) |parameter| {
                        if (remaining == 0) break;
                        try self.allocate(parameter.name, required_slots);
                        remaining -= 1;
                    }
                    for (definition.return_variables.items) |return_variable| {
                        if (remaining == 0) break;
                        try self.allocate(return_variable.name, required_slots);
                        remaining -= 1;
                    }
                }
            }
            for (unreachables.items) |variable| {
                if (!variable.empty() and !self.slot_allocations.contains(variable))
                    try self.allocate(variable, required_slots);
            }
        }
    }

    fn allocate(self: *MemoryOffsetAllocator, variable: YulName, next_slot: *u64) !void {
        _ = try self.slot_allocations.fetchPut(self.allocator, variable, next_slot.*);
        next_slot.* = std.math.add(u64, next_slot.*, 1) catch
            return error.TooManyMemorySlots;
    }
};

pub const StackLimitEvader = struct {
    /// Consumes the object code, returning its storage after rewriting. The
    /// context must allocate AST nodes with the object allocator. Source names
    /// still borrow the object; on error the consumed tree is destroyed.
    pub fn runObject(
        context: *OptimiserStepContext,
        object: *Object,
    ) !AST.Block {
        try object.validateNames();
        return runObjectWithValidatedNames(context, object);
    }

    /// Consumes code as runObject() does; requires validated namespaces.
    pub fn runObjectWithValidatedNames(
        context: *OptimiserStepContext,
        object: *Object,
    ) !AST.Block {
        const evm_dialect = try requireObjectDialect(context.dialect);
        std.debug.assert(context.dispenser.allocator.ptr == object.allocator.ptr and
            context.dispenser.allocator.vtable == object.allocator.vtable);
        return runWithRoot(context, object, try object.takeCodeRoot(), evm_dialect, null);
    }

    /// Consumes the compressor's root and borrows its report until return.
    /// Call immediately after compression, without AST, dialect or structure
    /// changes. The caller must still deinitialize the compression result.
    /// A different analysis object must use the original owner's allocator;
    /// the context must use it too. The returned AST still borrows source names
    /// from compressed.owner, which must outlive it. Validation errors leave
    /// the root owned by compressed; after transfer it stays empty on error.
    pub fn runAfterCompression(
        context: *OptimiserStepContext,
        object: *Object,
        compressed: *@import("stack_compressor.zig").RunResult,
    ) !AST.Block {
        const evm_dialect = try requireObjectDialect(context.dialect);
        if (!std.meta.eql(context.dispenser.allocator, compressed.owner.allocator) or
            !std.meta.eql(object.allocator, compressed.owner.allocator))
            return error.IncompatibleAllocator;
        if (object != compressed.owner) try object.validateNames();
        const report: ?*const StackLayout.StackTooDeepByFunction = if (compressed.stack_report) |*prepared|
            if (compressed.owner == object and std.meta.eql(prepared.dialect, context.dialect))
                &prepared.errors
            else
                null
        else
            null;
        const root = compressed.ast;
        compressed.ast = .{};
        return runWithRoot(context, object, root, evm_dialect, report);
    }

    fn runWithRoot(
        context: *OptimiserStepContext,
        object: *Object,
        root: AST.Block,
        evm_dialect: *const EVMDialectModule.EVMDialect,
        prepared_report: ?*const StackLayout.StackTooDeepByFunction,
    ) !AST.Block {
        var ast_root = root;
        errdefer ast_root.deinit(context.dispenser.allocator);

        if (prepared_report) |report| {
            context.recordCounter("Stack deficit reports reused", 1);
            try runWithStackTooDeep(context, &ast_root, report);
            return ast_root;
        }
        if (evm_dialect.evmVersion().canOverchargeGasForCall()) {
            var structure = try object.summarizeStructureWithValidatedNames();
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
            var checker = try Compilability.CompilabilityChecker.initWithBlockAndValidatedNames(
                context.dispenser.allocator,
                object,
                &ast_root,
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
        var components = try call_graph.stronglyConnectedComponents();
        defer components.deinit();
        for (components.groups.items, components.recursive) |members, is_recursive| {
            if (!is_recursive) continue;
            // Each invocation of a recursive function needs its own locals.
            for (members) |node|
                if (unreachable_variables.contains(components.handles[node].user)) return;
        }

        var function_definitions = try NameCollector.allFunctionDefinitions(allocator, ast_root);
        defer function_definitions.deinit(allocator);
        var memory_allocator: MemoryOffsetAllocator = .{
            .allocator = allocator,
            .unreachable_variables = unreachable_variables,
            .call_graph = &call_graph.function_calls,
            .components = &components,
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
            const spelling = try Numeric.toCompactHexWithPrefixAlloc(u256, allocator, final_reserved_memory);
            literal.value.deinit(allocator);
            literal.value = .{
                .numeric_value = final_reserved_memory,
                .string_value = spelling,
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

test "stack limit evader propagates callee slots across a recursive component" {
    const allocator = std.testing.allocator;
    const first = try YulName.init("first");
    const second = try YulName.init("second");
    const callee = try YulName.init("callee");
    const caller = try YulName.init("caller");
    const callee_local = try YulName.init("callee_local");
    const caller_local = try YulName.init("caller_local");
    var graph: CallGraphModule.CallGraph = .{ .allocator = allocator };
    defer graph.deinit();
    for ([_]struct { name: YulName, children: []const AST.FunctionHandle }{
        .{ .name = .{}, .children = &.{ .{ .user = first }, .{ .user = caller } } },
        .{ .name = first, .children = &.{ .{ .user = second }, .{ .user = callee } } },
        .{ .name = second, .children = &.{.{ .user = first }} },
        .{ .name = caller, .children = &.{.{ .user = second }} },
    }) |entry| {
        var children: std.ArrayList(AST.FunctionHandle) = .empty;
        errdefer children.deinit(allocator);
        try children.appendSlice(allocator, entry.children);
        _ = try graph.function_calls.insert(allocator, .{ .user = entry.name }, children);
    }
    var unreachable_variables: Compilability.UnreachableVariables = .{};
    defer deinitUnreachableVariables(allocator, &unreachable_variables);
    for ([_]YulName{ callee, caller }, [_]YulName{ callee_local, caller_local }) |name, local| {
        var variables: std.ArrayList(YulName) = .empty;
        errdefer variables.deinit(allocator);
        try variables.append(allocator, local);
        _ = try unreachable_variables.insert(allocator, name, variables);
    }

    var components = try graph.stronglyConnectedComponents();
    defer components.deinit();
    const definitions: NameCollector.FunctionDefinitionMap = .{};
    var memory_allocator: MemoryOffsetAllocator = .{
        .allocator = allocator,
        .unreachable_variables = &unreachable_variables,
        .call_graph = &graph.function_calls,
        .components = &components,
        .function_definitions = &definitions,
        .reachable_stack_depth = 16,
    };
    defer memory_allocator.deinit();
    try std.testing.expectEqual(@as(u64, 2), try memory_allocator.run(.{ .user = .{} }));
    try std.testing.expectEqual(@as(u64, 0), memory_allocator.slot_allocations.get(callee_local).?.*);
    try std.testing.expectEqual(@as(u64, 1), memory_allocator.slot_allocations.get(caller_local).?.*);
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

test "stack limit evasion and stack compression transfer roots and release allocation failures" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Copier = @import("ast_copier.zig").ASTCopier;
    const Compressor = @import("stack_compressor.zig").StackCompressor;
    const Encoding = @import("../ast_encoding.zig");
    const allocator = std.testing.allocator;
    for ([_]@import("../../liblangutil/evm_version.zig").EVMVersion{ .current(), .init(.Homestead) }) |version| {
        var dialect = try EVMDialectModule.EVMDialect.init(allocator, version, true);
        defer dialect.deinit();
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var source = (try Parser.parseSource(allocator, "{ { mstore(0x40, memoryguard(0x80)) let x := 1 pop(x) } }", "transfer.yul", &reporter, dialect.dialect(), .{})).?;
        defer source.deinit();
        const Check = struct {
            fn run(failing: std.mem.Allocator, ast: *const AST.AST) !void {
                const object = try Object.create(failing, "Root");
                defer object.destroy();
                var copier = Copier.init(failing);
                object.setCode(try copier.translateAst(ast), null);
                const storage = object.code().?.root().statements.items.ptr;
                const value = object.code().?.root().statements.items[0].block.statements.items[1].variable_declaration.value;
                var compressed = try Compressor.run(object, true, 16);
                defer compressed.deinit();
                try std.testing.expectEqual(storage, compressed.ast.statements.items.ptr);
                try std.testing.expectEqualDeep(try Encoding.hashBlock(ast.root()), try Encoding.hashBlock(&compressed.ast));
                const evm = EVMDialectModule.fromDialect(ast.dialect().*).?;
                try std.testing.expectEqual(evm.evmVersion().canOverchargeGasForCall(), compressed.stack_report != null);
                if (compressed.stack_report) |*report| {
                    try std.testing.expectEqual(@as(usize, 1), report.errors.count());
                    try std.testing.expectEqual(@as(usize, 0), report.errors.get(.{}).?.items.len);
                }
                var reserved: NameCollector.NameSet = .{};
                defer reserved.deinit(failing);
                var dispenser = try NameDispenser.initFromAst(failing, ast.dialect().*, &compressed.ast, &reserved);
                defer dispenser.deinit();
                var context: OptimiserStepContext = .{
                    .dialect = ast.dialect().*,
                    .dispenser = &dispenser,
                    .reserved_identifiers = &reserved,
                };
                var transformed = try StackLimitEvader.runAfterCompression(&context, object, &compressed);
                defer transformed.deinit(failing);
                // The spill pass can rebuild statement containers. The owned
                // expression remains at its original address across both passes.
                try std.testing.expectEqual(value, transformed.statements.items[0].block.statements.items[1].variable_declaration.value);
                try std.testing.expectEqual(@as(usize, 0), object.code().?.root().statements.items.len);
                try std.testing.expectEqualDeep(try Encoding.hashBlock(ast.root()), try Encoding.hashBlock(&transformed));
            }
        };
        // Keep OOM replay counts independent of SafeAllocator bucket occupancy.
        var deterministic = std.testing.FailingAllocator.init(allocator, .{ .resize_fail_index = 0 });
        try std.testing.checkAllAllocationFailures(deterministic.allocator(), Check.run, .{&source});
    }
}

test "stack limit evasion reuses preparation without skipping guard updates or fallbacks" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Copier = @import("ast_copier.zig").ASTCopier;
    const Compressor = @import("stack_compressor.zig").StackCompressor;
    const Encoding = @import("../ast_encoding.zig");
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const Profiler = @import("../../libsolutil/profiler.zig").Profiler;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var other_dialect = try EVMDialectModule.EVMDialect.init(allocator, .current(), true);
    defer other_dialect.deinit();
    const Mode = enum { reuse, other_object, other_dialect, classic };
    const sources = [_][]const u8{
        "{ { mstore(0x40, memoryguard(128)) let x := 1 pop(x) } }",
        "{ { let x := 1 pop(x) } }",
        "{ { mstore(0x40, memoryguard(128)) pop(f(1)) } function f(a) -> r { if a { r := f(sub(a, 1)) } } }",
    };
    for (sources, 0..) |source, source_index| for (std.enums.values(Mode)) |mode| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        const object = try Object.create(allocator, "Root");
        defer object.destroy();
        const parsed = (try Parser.parseSource(allocator, source, "stack-reuse.yul", &reporter, dialect.dialect(), .{})).?;
        object.setCode(parsed, null);
        var compressed = try Compressor.run(object, mode != .classic, 16);
        defer compressed.deinit();
        try std.testing.expectEqual(mode != .classic, compressed.stack_report != null);

        const reference = try Object.create(allocator, "Root");
        defer reference.destroy();
        var copier = Copier.init(allocator);
        reference.setCode(AST.AST.init(allocator, dialect.dialect(), try copier.translateBlock(&compressed.ast)), null);
        const other_object = try Object.create(allocator, "Root");
        defer other_object.destroy();
        other_object.setCode(AST.AST.init(allocator, dialect.dialect(), .{}), null);
        const active_dialect = if (mode == .other_dialect) other_dialect.dialect() else dialect.dialect();
        var reserved: NameCollector.NameSet = .{};
        defer reserved.deinit(allocator);
        var fresh_dispenser = try NameDispenser.initFromAst(allocator, active_dialect, reference.code().?.root(), &reserved);
        defer fresh_dispenser.deinit();
        var fresh_context: OptimiserStepContext = .{
            .dialect = active_dialect,
            .dispenser = &fresh_dispenser,
            .reserved_identifiers = &reserved,
        };
        var expected = try StackLimitEvader.runObject(&fresh_context, reference);
        defer expected.deinit(allocator);
        var dispenser = try NameDispenser.initFromAst(allocator, active_dialect, &compressed.ast, &reserved);
        defer dispenser.deinit();
        var profiler = Profiler.init(allocator, std.testing.io);
        defer profiler.deinit();
        var context: OptimiserStepContext = .{
            .dialect = active_dialect,
            .dispenser = &dispenser,
            .reserved_identifiers = &reserved,
            .profiler = &profiler,
        };
        var actual = try StackLimitEvader.runAfterCompression(&context, if (mode == .other_object) other_object else object, &compressed);
        defer actual.deinit(allocator);
        try std.testing.expectEqualDeep(try Encoding.hashBlock(&expected), try Encoding.hashBlock(&actual));
        try std.testing.expectEqual(@as(usize, 0), compressed.ast.statements.items.len);
        const reuse_count = profiler.counterFor("Stack deficit reports reused");
        try std.testing.expectEqual(mode == .reuse, reuse_count != null);
        if (reuse_count) |count| try std.testing.expectEqual(@as(u64, 1), count.total);
        if (source_index == 0) {
            var printer = Printer.init(allocator, active_dialect, &.{}, .defaultValue(), null);
            const rendered = try printer.renderBlock(&actual);
            defer allocator.free(rendered);
            try std.testing.expect(std.mem.find(u8, rendered, "memoryguard(0x80)") != null);
        }
    };
}

test "stack limit evasion rejects foreign allocators before consuming compression results" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Compressor = @import("stack_compressor.zig").StackCompressor;
    const Encoding = @import("../ast_encoding.zig");
    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var owner_arena = std.heap.ArenaAllocator.init(allocator);
    defer owner_arena.deinit();
    const owner_allocator = owner_arena.allocator();
    var other_arena = std.heap.ArenaAllocator.init(allocator);
    defer other_arena.deinit();
    const other_allocator = other_arena.allocator();
    const other = try Object.create(other_allocator, "Other");
    defer other.destroy();
    for ([_]bool{ false, true }) |optimized| {
        const object = try Object.create(owner_allocator, "Root");
        defer object.destroy();
        var reporter = Diagnostics.ErrorReporter.init(owner_allocator);
        defer reporter.deinit();
        object.setCode((try Parser.parseSource(owner_allocator, "{ { mstore(0, memoryguard(128)) } }", "owner.yul", &reporter, dialect.dialect(), .{})).?, null);
        var compressed = try Compressor.run(object, optimized, 16);
        defer compressed.deinit();
        try std.testing.expectEqual(optimized, compressed.stack_report != null);
        try std.testing.expectEqual(object, compressed.owner);
        const storage = compressed.ast.statements.items.ptr;
        const hash = try Encoding.hashBlock(&compressed.ast);
        const cases = [_]struct { allocator: std.mem.Allocator, object: *Object }{
            .{ .allocator = other_allocator, .object = other },
            .{ .allocator = owner_allocator, .object = other },
            .{ .allocator = other_allocator, .object = object },
        };
        for (cases) |case| {
            var reserved: NameCollector.NameSet = .{};
            defer reserved.deinit(case.allocator);
            var dispenser = try NameDispenser.initFromAst(case.allocator, dialect.dialect(), &compressed.ast, &reserved);
            defer dispenser.deinit();
            var context: OptimiserStepContext = .{
                .dialect = dialect.dialect(),
                .dispenser = &dispenser,
                .reserved_identifiers = &reserved,
            };
            try std.testing.expectError(error.IncompatibleAllocator, StackLimitEvader.runAfterCompression(&context, case.object, &compressed));
            try std.testing.expectEqual(storage, compressed.ast.statements.items.ptr);
            try std.testing.expectEqualDeep(hash, try Encoding.hashBlock(&compressed.ast));
            try std.testing.expectEqual(optimized, compressed.stack_report != null);
        }
    }
}

test "stack limit evasion prepares a rewritten compressed AST and releases allocation failures" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Copier = @import("ast_copier.zig").ASTCopier;
    const Compressor = @import("stack_compressor.zig").StackCompressor;
    const Encoding = @import("../ast_encoding.zig");
    const Profiler = @import("../../libsolutil/profiler.zig").Profiler;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const source_text =
        \\{ { mstore(0x40, memoryguard(128)) mstore(0, f(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17)) }
        \\  function f(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17) -> r {
        \\    let unused := 42
        \\    r := add(a17, add(a16, add(a15, add(a14, add(a13, add(a12, add(a11, add(a10, add(a9, add(a8, add(a7, add(a6, add(a5, add(a4, add(a3, add(a2, add(a1, a0)))))))))))))))))
        \\    r := xor(r, xor(a17, xor(a16, xor(a15, xor(a14, xor(a13, xor(a12, xor(a11, xor(a10, xor(a9, xor(a8, xor(a7, xor(a6, xor(a5, xor(a4, xor(a3, xor(a2, xor(a1, a0))))))))))))))))))
        \\  }
        \\}
    ;
    var source = (try Parser.parseSource(allocator, source_text, "compressed.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    const Check = struct {
        fn run(failing: std.mem.Allocator, ast: *const AST.AST) !void {
            const object = try Object.create(failing, "Root");
            defer object.destroy();
            var copier = Copier.init(failing);
            object.setCode(try copier.translateAst(ast), null);
            var compressed = try Compressor.run(object, true, 16);
            defer compressed.deinit();
            try std.testing.expectEqual(false, compressed.stack_report != null);
            try std.testing.expect(!std.meta.eql(try Encoding.hashBlock(ast.root()), try Encoding.hashBlock(&compressed.ast)));
            // Keeping all parameters live across both expressions causes a real
            // deficit. Compression must prune the unused declaration.
            const body = &compressed.ast.statements.items[1].function_definition.body;
            try std.testing.expectEqual(@as(usize, 2), body.statements.items.len);
            for (body.statements.items) |statement| try std.testing.expect(statement == .assignment);

            const reference = try Object.create(failing, "Root");
            defer reference.destroy();
            reference.setCode(AST.AST.init(failing, ast.dialect().*, try copier.translateBlock(&compressed.ast)), null);
            var reserved: NameCollector.NameSet = .{};
            defer reserved.deinit(failing);
            var fresh_dispenser = try NameDispenser.initFromAst(failing, ast.dialect().*, reference.code().?.root(), &reserved);
            defer fresh_dispenser.deinit();
            var fresh_context: OptimiserStepContext = .{
                .dialect = ast.dialect().*,
                .dispenser = &fresh_dispenser,
                .reserved_identifiers = &reserved,
            };
            var expected = try StackLimitEvader.runObject(&fresh_context, reference);
            defer expected.deinit(failing);
            var dispenser = try NameDispenser.initFromAst(failing, ast.dialect().*, &compressed.ast, &reserved);
            defer dispenser.deinit();
            var profiler = Profiler.init(failing, std.testing.io);
            defer profiler.deinit();
            var context: OptimiserStepContext = .{
                .dialect = ast.dialect().*,
                .dispenser = &dispenser,
                .reserved_identifiers = &reserved,
                .profiler = &profiler,
            };
            var actual = try StackLimitEvader.runAfterCompression(&context, object, &compressed);
            defer actual.deinit(failing);
            try std.testing.expectEqualDeep(try Encoding.hashBlock(&expected), try Encoding.hashBlock(&actual));
            try std.testing.expectEqual(@as(usize, 0), compressed.ast.statements.items.len);
            try std.testing.expect(profiler.counterFor("Stack deficit reports reused") == null);
        }
    };
    try Check.run(allocator, &source);
    var deterministic = std.testing.FailingAllocator.init(allocator, .{ .resize_fail_index = 0 });
    try std.testing.checkAllAllocationFailures(deterministic.allocator(), Check.run, .{&source});
}
