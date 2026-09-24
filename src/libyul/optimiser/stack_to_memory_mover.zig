// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Moves selected disambiguated Yul variables from stack slots to fixed
//! memory offsets while preserving tuple-return evaluation order.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
const NameCollector = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const Numeric = @import("../../libsolutil/numeric.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

pub const MemorySlotMap = ordered.OrderedMap(YulName, u64, lessYulName);
const ReturnVariableMap = ordered.OrderedMap(
    YulName,
    std.ArrayList(AST.NameWithDebugData),
    lessYulName,
);
const NameTranslationMap = ordered.OrderedMap(YulName, YulName, lessYulName);

pub const VariableMemoryOffsetTracker = struct {
    reserved_memory: u256,
    memory_slots: *const MemorySlotMap,
    num_required_slots: u64,

    pub fn offset(self: *const VariableMemoryOffsetTracker, variable: YulName) !?u256 {
        const slot = self.memory_slots.get(variable) orelse return null;
        if (slot.* >= self.num_required_slots) return error.InvalidMemorySlot;
        const reverse_slot = self.num_required_slots - slot.* - 1;
        return std.math.add(
            u256,
            self.reserved_memory,
            @as(u256, reverse_slot) * 32,
        ) catch error.MemoryOffsetOverflow;
    }

    pub fn contains(self: *const VariableMemoryOffsetTracker, variable: YulName) bool {
        return self.memory_slots.contains(variable);
    }
};

pub const StackToMemoryMover = struct {
    allocator: std.mem.Allocator,
    context: *OptimiserStepContext,
    memory_offset_tracker: VariableMemoryOffsetTracker,
    name_dispenser: *NameDispenser,
    function_return_variables: ReturnVariableMap = .{},
    new_function_definitions: std.ArrayList(AST.Statement) = .empty,

    pub fn run(
        context: *OptimiserStepContext,
        reserved_memory: u256,
        memory_slots: *const MemorySlotMap,
        num_required_slots: u64,
        block: *AST.Block,
    ) !void {
        const allocator = context.dispenser.allocator;
        const evm_dialect = EVMDialectModule.fromDialect(context.dialect) orelse
            return error.EVMDialectWithObjectAccessRequired;
        if (!evm_dialect.providesObjectAccess())
            return error.EVMDialectWithObjectAccessRequired;

        var mover: StackToMemoryMover = .{
            .allocator = allocator,
            .context = context,
            .memory_offset_tracker = .{
                .reserved_memory = reserved_memory,
                .memory_slots = memory_slots,
                .num_required_slots = num_required_slots,
            },
            .name_dispenser = context.dispenser,
        };
        defer mover.deinit();
        try mover.collectFunctionReturnVariables(block);
        try mover.visitBlock(block);

        try block.statements.ensureUnusedCapacity(
            allocator,
            mover.new_function_definitions.items.len,
        );
        for (mover.new_function_definitions.items) |*statement| {
            block.statements.appendAssumeCapacity(statement.*);
            statement.* = emptyStatement();
        }
        mover.new_function_definitions.clearRetainingCapacity();
    }

    fn deinit(self: *StackToMemoryMover) void {
        for (self.function_return_variables.mutableItems()) |*entry|
            entry.value.deinit(self.allocator);
        self.function_return_variables.deinit(self.allocator);
        deinitStatements(self.allocator, &self.new_function_definitions);
        self.* = undefined;
    }

    fn collectFunctionReturnVariables(self: *StackToMemoryMover, block: *const AST.Block) !void {
        var definitions = try NameCollector.allFunctionDefinitions(self.allocator, block);
        defer definitions.deinit(self.allocator);
        for (definitions.items()) |entry| {
            var returns: std.ArrayList(AST.NameWithDebugData) = .empty;
            errdefer returns.deinit(self.allocator);
            try returns.appendSlice(self.allocator, entry.value.return_variables.items);
            if (!(try self.function_return_variables.insert(
                self.allocator,
                entry.key,
                returns,
            ))) return error.InputNotDisambiguated;
            returns = .empty;
        }
    }

    fn visitBlock(self: *StackToMemoryMover, block: *AST.Block) anyerror!void {
        var old_statements = block.statements;
        block.statements = .empty;
        errdefer deinitStatements(self.allocator, &old_statements);

        var replacement: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(self.allocator, &replacement);
        for (old_statements.items) |*statement| {
            try self.visitStatement(statement);
            var rewritten = switch (statement.*) {
                .assignment => |*assignment| try self.rewriteLeftHandSide(
                    false,
                    assignment.debug_data,
                    assignment.variable_names.items,
                    &assignment.value,
                ),
                .variable_declaration => |*declaration| try self.rewriteLeftHandSide(
                    true,
                    declaration.debug_data,
                    declaration.variables.items,
                    &declaration.value,
                ),
                else => null,
            };
            if (rewritten) |*statements| {
                errdefer deinitStatements(self.allocator, statements);
                statement.deinit(self.allocator);
                statement.* = emptyStatement();
                try replacement.ensureUnusedCapacity(self.allocator, statements.items.len);
                for (statements.items) |*new_statement| {
                    replacement.appendAssumeCapacity(new_statement.*);
                    new_statement.* = emptyStatement();
                }
                statements.deinit(self.allocator);
            } else {
                try replacement.append(self.allocator, statement.*);
                statement.* = emptyStatement();
            }
        }
        old_statements.deinit(self.allocator);
        old_statements = .empty;
        block.statements = replacement;
        replacement = .empty;
    }

    fn visitStatement(self: *StackToMemoryMover, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitFunctionDefinition(value),
            .if_statement => |*value| {
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression| try self.visitExpression(expression);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *StackToMemoryMover, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
            .identifier => |identifier| {
                const offset = try self.memory_offset_tracker.offset(identifier.name) orelse return;
                expression.* = try self.generateMemoryLoad(identifier.debug_data, offset);
            },
            .literal => {},
        }
    }

    fn visitFunctionDefinition(
        self: *StackToMemoryMover,
        function: *AST.FunctionDefinition,
    ) anyerror!void {
        // Generated parameter and return initialization must not itself be
        // rewritten, so process the original body first.
        try self.visitBlock(&function.body);

        var memory_variable_inits: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(self.allocator, &memory_variable_inits);
        for (function.parameters.items) |parameter| {
            const offset = try self.memory_offset_tracker.offset(parameter.name) orelse continue;
            try self.appendMemoryStore(
                &memory_variable_inits,
                parameter.debug_data,
                offset,
                .{ .identifier = .{ .debug_data = parameter.debug_data, .name = parameter.name } },
            );
        }
        for (function.return_variables.items) |return_variable| {
            const offset = try self.memory_offset_tracker.offset(return_variable.name) orelse continue;
            try self.appendMemoryStore(
                &memory_variable_inits,
                return_variable.debug_data,
                offset,
                .{ .literal = .{
                    .debug_data = return_variable.debug_data,
                    .kind = .Number,
                    .value = .{ .numeric_value = 0 },
                } },
            );
        }

        if (function.return_variables.items.len == 1 and
            self.memory_offset_tracker.contains(function.return_variables.items[0].name))
        {
            try self.wrapSingleMemoryReturn(function, &memory_variable_inits);
            return;
        }

        if (memory_variable_inits.items.len != 0) {
            var combined: std.ArrayList(AST.Statement) = .empty;
            errdefer deinitStatements(self.allocator, &combined);
            try combined.ensureTotalCapacity(
                self.allocator,
                memory_variable_inits.items.len + function.body.statements.items.len,
            );
            combined.appendSliceAssumeCapacity(memory_variable_inits.items);
            combined.appendSliceAssumeCapacity(function.body.statements.items);
            memory_variable_inits.clearRetainingCapacity();
            function.body.statements.clearRetainingCapacity();
            memory_variable_inits.deinit(self.allocator);
            memory_variable_inits = .empty;
            function.body.statements.deinit(self.allocator);
            function.body.statements = combined;
            combined = .empty;
        }

        var stack_returns: std.ArrayList(AST.NameWithDebugData) = .empty;
        errdefer stack_returns.deinit(self.allocator);
        for (function.return_variables.items) |return_variable|
            if (!self.memory_offset_tracker.contains(return_variable.name))
                try stack_returns.append(self.allocator, return_variable);
        function.return_variables.deinit(self.allocator);
        function.return_variables = stack_returns;
        stack_returns = .empty;
    }

    fn wrapSingleMemoryReturn(
        self: *StackToMemoryMover,
        function: *AST.FunctionDefinition,
        memory_variable_inits: *std.ArrayList(AST.Statement),
    ) !void {
        const new_function_name = try self.name_dispenser.newName(function.name);
        var stack_parameters: std.ArrayList(AST.NameWithDebugData) = .empty;
        errdefer stack_parameters.deinit(self.allocator);
        for (function.parameters.items) |parameter|
            if (!self.memory_offset_tracker.contains(parameter.name))
                try stack_parameters.append(self.allocator, parameter);

        var new_argument_names: NameTranslationMap = .{};
        defer new_argument_names.deinit(self.allocator);
        for (stack_parameters.items) |parameter| {
            const new_name = try self.name_dispenser.newName(parameter.name);
            _ = try new_argument_names.insert(self.allocator, parameter.name, new_name);
        }

        var call_arguments: std.ArrayList(AST.Expression) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitExpressions(self.allocator, &call_arguments);
        for (stack_parameters.items) |parameter| try call_arguments.append(
            self.allocator,
            .{ .identifier = .{
                .debug_data = parameter.debug_data,
                .name = new_argument_names.get(parameter.name).?.*,
            } },
        );
        var call_statement: AST.Statement = .{ .expression_statement = .{
            .debug_data = function.debug_data,
            .expression = .{ .function_call = .{
                .debug_data = function.debug_data,
                .function_name = .{ .identifier = .{
                    .debug_data = function.debug_data,
                    .name = new_function_name,
                } },
                .arguments = call_arguments,
            } },
        } };
        call_arguments = .empty;
        errdefer call_statement.deinit(self.allocator);

        const return_variable = function.return_variables.items[0];
        const return_offset = (try self.memory_offset_tracker.offset(return_variable.name)).?;
        var return_assignment: AST.Statement = .{ .assignment = .{ .debug_data = function.debug_data } };
        errdefer return_assignment.deinit(self.allocator);
        try return_assignment.assignment.variable_names.append(self.allocator, .{
            .debug_data = function.debug_data,
            .name = return_variable.name,
        });
        var load = try self.generateMemoryLoad(function.debug_data, return_offset);
        errdefer load.deinit(self.allocator);
        return_assignment.assignment.value = try AST.createExpression(self.allocator, load);
        load = .{ .identifier = .{} };

        var wrapper_body: AST.Block = .{ .debug_data = function.debug_data };
        errdefer wrapper_body.deinit(self.allocator);
        try wrapper_body.statements.ensureTotalCapacity(
            self.allocator,
            memory_variable_inits.items.len + 2,
        );
        wrapper_body.statements.appendSliceAssumeCapacity(memory_variable_inits.items);
        memory_variable_inits.clearRetainingCapacity();
        memory_variable_inits.deinit(self.allocator);
        memory_variable_inits.* = .empty;
        wrapper_body.statements.appendAssumeCapacity(call_statement);
        call_statement = emptyStatement();
        wrapper_body.statements.appendAssumeCapacity(return_assignment);
        return_assignment = emptyStatement();

        try self.new_function_definitions.ensureUnusedCapacity(self.allocator, 1);
        const original_body = function.body;
        function.body = wrapper_body;
        wrapper_body = .{};
        self.new_function_definitions.appendAssumeCapacity(.{ .function_definition = .{
            .debug_data = function.debug_data,
            .name = new_function_name,
            .parameters = stack_parameters,
            .body = original_body,
        } });
        stack_parameters = .empty;

        for (function.parameters.items) |*parameter| {
            if (new_argument_names.get(parameter.name)) |new_name|
                parameter.name = new_name.*;
        }
    }

    fn rewriteLeftHandSide(
        self: *StackToMemoryMover,
        comptime is_declaration: bool,
        debug_data: @TypeOf(@as(AST.Assignment, undefined).debug_data),
        lhs_variables: if (is_declaration) []AST.NameWithDebugData else []AST.Identifier,
        value: *?*AST.Expression,
    ) !?std.ArrayList(AST.Statement) {
        if (lhs_variables.len == 1) {
            const offset = try self.memory_offset_tracker.offset(lhs_variables[0].name) orelse return null;
            const expression = if (value.*) |rhs| blk: {
                const moved = rhs.*;
                self.allocator.destroy(rhs);
                value.* = null;
                break :blk moved;
            } else AST.Expression{ .literal = .{
                .debug_data = debug_data,
                .kind = .Number,
                .value = .{ .numeric_value = 0 },
            } };
            var result: std.ArrayList(AST.Statement) = .empty;
            errdefer deinitStatements(self.allocator, &result);
            try self.appendMemoryStore(&result, debug_data, offset, expression);
            return result;
        }

        var rhs_memory_slots: std.ArrayList(?u256) = .empty;
        defer rhs_memory_slots.deinit(self.allocator);
        if (value.*) |rhs| {
            const call = switch (rhs.*) {
                .function_call => |*function_call| function_call,
                else => return error.MultiAssignmentRequiresFunctionCall,
            };
            switch (call.function_name) {
                .builtin => try rhs_memory_slots.appendNTimes(self.allocator, null, lhs_variables.len),
                .identifier => |identifier| {
                    const returns = self.function_return_variables.get(identifier.name) orelse
                        return error.UnknownFunctionReturnShape;
                    for (returns.items) |return_variable|
                        try rhs_memory_slots.append(
                            self.allocator,
                            try self.memory_offset_tracker.offset(return_variable.name),
                        );
                },
            }
        } else try rhs_memory_slots.appendNTimes(self.allocator, null, lhs_variables.len);
        if (rhs_memory_slots.items.len != lhs_variables.len)
            return error.ReturnArityMismatch;

        var any_rhs_memory = false;
        var any_lhs_memory = false;
        for (rhs_memory_slots.items) |slot| any_rhs_memory = any_rhs_memory or slot != null;
        for (lhs_variables) |lhs| any_lhs_memory = any_lhs_memory or
            self.memory_offset_tracker.contains(lhs.name);
        if (!any_rhs_memory and !any_lhs_memory) return null;

        var temp_declaration: AST.VariableDeclaration = .{
            .debug_data = debug_data,
            .value = value.*,
        };
        value.* = null;
        errdefer temp_declaration.deinit(self.allocator);
        var memory_assignments: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(self.allocator, &memory_assignments);
        var variable_assignments: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(self.allocator, &variable_assignments);

        for (lhs_variables, rhs_memory_slots.items) |lhs, rhs_slot| {
            var rhs = if (rhs_slot) |slot|
                try self.generateMemoryLoad(debug_data, slot)
            else blk: {
                const temp_name = try self.name_dispenser.newName(lhs.name);
                try temp_declaration.variables.append(self.allocator, .{
                    .debug_data = lhs.debug_data,
                    .name = temp_name,
                });
                break :blk AST.Expression{ .identifier = .{
                    .debug_data = debug_data,
                    .name = temp_name,
                } };
            };
            errdefer rhs.deinit(self.allocator);

            if (try self.memory_offset_tracker.offset(lhs.name)) |offset| {
                const moved = rhs;
                rhs = .{ .identifier = .{} };
                try self.appendMemoryStore(&memory_assignments, debug_data, offset, moved);
            } else {
                var statement: AST.Statement = if (is_declaration)
                    .{ .variable_declaration = .{ .debug_data = debug_data } }
                else
                    .{ .assignment = .{ .debug_data = debug_data } };
                errdefer statement.deinit(self.allocator);
                const owned_value = try AST.createExpression(self.allocator, rhs);
                rhs = .{ .identifier = .{} };
                if (is_declaration) {
                    statement.variable_declaration.value = owned_value;
                    try statement.variable_declaration.variables.append(self.allocator, lhs);
                } else {
                    statement.assignment.value = owned_value;
                    try statement.assignment.variable_names.append(self.allocator, lhs);
                }
                try variable_assignments.append(self.allocator, statement);
                statement = emptyStatement();
            }
        }

        var result: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(self.allocator, &result);
        try result.ensureTotalCapacity(
            self.allocator,
            1 + memory_assignments.items.len + variable_assignments.items.len,
        );
        if (temp_declaration.variables.items.len == 0) {
            const expression_pointer = temp_declaration.value orelse return error.MissingCallExpression;
            const expression = expression_pointer.*;
            self.allocator.destroy(expression_pointer);
            temp_declaration.value = null;
            temp_declaration.deinit(self.allocator);
            temp_declaration = .{};
            result.appendAssumeCapacity(.{ .expression_statement = .{
                .debug_data = debug_data,
                .expression = expression,
            } });
        } else {
            result.appendAssumeCapacity(.{ .variable_declaration = temp_declaration });
            temp_declaration = .{};
        }
        std.mem.reverse(AST.Statement, memory_assignments.items);
        result.appendSliceAssumeCapacity(memory_assignments.items);
        memory_assignments.clearRetainingCapacity();
        memory_assignments.deinit(self.allocator);
        memory_assignments = .empty;
        std.mem.reverse(AST.Statement, variable_assignments.items);
        result.appendSliceAssumeCapacity(variable_assignments.items);
        variable_assignments.clearRetainingCapacity();
        variable_assignments.deinit(self.allocator);
        variable_assignments = .empty;
        return result;
    }

    /// Consumes value on both success and failure.
    fn appendMemoryStore(
        self: *StackToMemoryMover,
        statements: *std.ArrayList(AST.Statement),
        debug_data: @TypeOf(@as(AST.ExpressionStatement, undefined).debug_data),
        offset: u256,
        value: AST.Expression,
    ) !void {
        var owned_value = value;
        errdefer owned_value.deinit(self.allocator);
        const memory_store_handle = self.context.dialect.memoryStoreFunctionHandle() orelse
            return error.MissingMemoryStoreBuiltin;
        try statements.ensureUnusedCapacity(self.allocator, 1);
        var arguments: std.ArrayList(AST.Expression) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitExpressions(self.allocator, &arguments);
        try arguments.ensureTotalCapacity(self.allocator, 2);
        arguments.appendAssumeCapacity(.{ .literal = try self.memoryOffsetLiteral(debug_data, offset) });
        arguments.appendAssumeCapacity(owned_value);
        statements.appendAssumeCapacity(.{ .expression_statement = .{
            .debug_data = debug_data,
            .expression = .{ .function_call = .{
                .debug_data = debug_data,
                .function_name = .{ .builtin = .{
                    .debug_data = debug_data,
                    .handle = memory_store_handle,
                } },
                .arguments = arguments,
            } },
        } });
        arguments = .empty;
    }

    fn generateMemoryLoad(
        self: *StackToMemoryMover,
        debug_data: @TypeOf(@as(AST.ExpressionStatement, undefined).debug_data),
        offset: u256,
    ) !AST.Expression {
        const memory_load_handle = self.context.dialect.memoryLoadFunctionHandle() orelse
            return error.MissingMemoryLoadBuiltin;
        var arguments: std.ArrayList(AST.Expression) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitExpressions(self.allocator, &arguments);
        try arguments.ensureTotalCapacity(self.allocator, 1);
        arguments.appendAssumeCapacity(.{ .literal = try self.memoryOffsetLiteral(debug_data, offset) });
        const result: AST.Expression = .{ .function_call = .{
            .debug_data = debug_data,
            .function_name = .{ .builtin = .{
                .debug_data = debug_data,
                .handle = memory_load_handle,
            } },
            .arguments = arguments,
        } };
        arguments = .empty;
        return result;
    }

    fn memoryOffsetLiteral(
        self: *StackToMemoryMover,
        debug_data: @TypeOf(@as(AST.Literal, undefined).debug_data),
        offset: u256,
    ) !AST.Literal {
        return .{
            .debug_data = debug_data,
            .kind = .Number,
            .value = .{
                .numeric_value = offset,
                .string_value = try Numeric.toCompactHexWithPrefixAlloc(
                    u256,
                    self.allocator,
                    offset,
                ),
            },
        };
    }
};

fn emptyStatement() AST.Statement {
    return .{ .block = .{} };
}

fn deinitStatements(allocator: std.mem.Allocator, statements: *std.ArrayList(AST.Statement)) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(allocator);
}

fn deinitExpressions(allocator: std.mem.Allocator, expressions: *std.ArrayList(AST.Expression)) void {
    for (expressions.items) |*expression| expression.deinit(allocator);
    expressions.deinit(allocator);
}

test "stack limit evader spill rewrites move expressions and clean up every allocation failure" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Copier = @import("ast_copier.zig").ASTCopier;
    const Analysis = @import("../asm_analysis.zig");
    const Objects = @import("../object.zig");
    const Finder = @import("function_call_finder.zig");
    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ function pair(a) -> r, s { r := a s := add(a, 1) }
        \\  function one(p) -> q { q := add(p, 2) }
        \\  let x := add(1, 2) x := add(x, 3)
        \\  let u, v := pair(x) u, v := pair(u) let w := one(v) pop(w)
        \\}
    , "spills.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    const Check = struct {
        fn run(failing: std.mem.Allocator, ast: *const AST.AST, evm: *const EVMDialectModule.EVMDialect) !void {
            var copier = Copier.init(failing);
            var result = try copier.translateBlock(ast.root());
            defer result.deinit(failing);
            const rhs_arguments = result.statements.items[2].variable_declaration.value.?.function_call.arguments.items.ptr;
            var reserved: NameCollector.NameSet = .{};
            defer reserved.deinit(failing);
            var dispenser = try NameDispenser.initFromAst(failing, ast.dialect().*, &result, &reserved);
            defer dispenser.deinit();
            var context: OptimiserStepContext = .{
                .dialect = ast.dialect().*,
                .dispenser = &dispenser,
                .reserved_identifiers = &reserved,
            };
            var slots: MemorySlotMap = .{};
            defer slots.deinit(failing);
            for ([_][]const u8{ "x", "u", "a", "r", "p", "q" }, 0..) |name, index|
                _ = try slots.insert(failing, try YulName.init(name), @intCast(index));
            try StackToMemoryMover.run(&context, 0x80, &slots, 6, &result);
            var definitions = try NameCollector.allFunctionDefinitions(failing, &result);
            defer definitions.deinit(failing);
            try std.testing.expectEqual(@as(usize, 3), definitions.len());
            var calls = try Finder.findFunctionCalls(failing, &result, .{ .builtin = ast.dialect().memoryStoreFunctionHandle().? });
            defer calls.deinit(failing);
            var retained = false;
            for (calls.items) |call| {
                const value = &call.arguments.items[1];
                if (value.* == .function_call and value.function_call.arguments.items.ptr == rhs_arguments) retained = true;
            }
            try std.testing.expect(retained);
            var structure = try Objects.Structure.init(failing, "");
            defer structure.deinit();
            var info = try Analysis.analyzeStrictBlock(failing, ast.dialect().*, &result, &structure, Analysis.instructionValidatorForEVMDialect(evm));
            defer info.deinit();
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ &source, &dialect });
}
