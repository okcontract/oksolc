// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Classic stack-based lowering from analyzed Yul ASTs to the EVM abstract
//! assembly interface.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../../ast.zig");
const AsmAnalysisInfo = @import("../../asm_analysis_info.zig").AsmAnalysisInfo;
const AbstractModule = @import("abstract_assembly.zig");
const AbstractAssembly = AbstractModule.AbstractAssembly;
const Builtins = @import("evm_builtins.zig");
const BuiltinContext = Builtins.BuiltinContext;
const DebugData = @import("../../../liblangutil/debug_data.zig").DebugData;
const EVMDialect = @import("evm_dialect.zig").EVMDialect;
const Exceptions = @import("../../exceptions.zig");
const ExternalIdentifierAccess = AbstractModule.ExternalIdentifierAccess;
const InstructionModule = @import("../../../libevmasm/instruction.zig");
const Instruction = InstructionModule.Instruction;
const NoOutputEVMDialect = @import("no_output_assembly.zig").NoOutputEVMDialect;
const ScopeModule = @import("../../scope.zig");
const Scope = ScopeModule.Scope;
const SourceLocation = @import("../../../liblangutil/source_location.zig").SourceLocation;
const StackTooDeepError = Exceptions.StackTooDeepError;
const Utilities = @import("../../utilities.zig");
const VariableReferenceCounterModule = @import("variable_reference_counter.zig");
const YulName = @import("../../yul_name.zig").YulName;

pub const UseNamedLabels = enum(c_int) {
    yes_and_force_unique,
    never,
    for_first_function_of_each_name,
};

pub const JumpInfo = struct {
    label: AbstractModule.LabelID,
    target_stack_height: i32,
};

pub const ForLoopLabels = struct {
    post: JumpInfo,
    done: JumpInfo,
};

pub const CodeTransformContext = struct {
    allocator: std.mem.Allocator,
    function_entry_ids: std.AutoHashMap(*const ScopeModule.Function, AbstractModule.LabelID),
    variable_stack_heights: std.AutoHashMap(*const ScopeModule.Variable, usize),
    variable_references: VariableReferenceCounterModule.ReferenceMap,
    for_loop_stack: std.ArrayList(ForLoopLabels) = .empty,
    assigned_named_labels: std.AutoHashMap(YulName, void),

    pub fn init(allocator: std.mem.Allocator) CodeTransformContext {
        return .{
            .allocator = allocator,
            .function_entry_ids = std.AutoHashMap(
                *const ScopeModule.Function,
                AbstractModule.LabelID,
            ).init(allocator),
            .variable_stack_heights = std.AutoHashMap(
                *const ScopeModule.Variable,
                usize,
            ).init(allocator),
            .variable_references = VariableReferenceCounterModule.ReferenceMap.init(allocator),
            .assigned_named_labels = std.AutoHashMap(YulName, void).init(allocator),
        };
    }

    pub fn deinit(self: *CodeTransformContext) void {
        self.function_entry_ids.deinit();
        self.variable_stack_heights.deinit();
        self.variable_references.deinit();
        self.for_loop_stack.deinit(self.allocator);
        self.assigned_named_labels.deinit();
        self.* = undefined;
    }
};

fn lessI32(left: i32, right: i32) bool {
    return left < right;
}

const StackSlotSet = ordered.OrderedSet(i32, lessI32);

pub const CodeTransform = struct {
    allocator: std.mem.Allocator,
    assembly: AbstractAssembly,
    info: *AsmAnalysisInfo,
    scope: ?*Scope = null,
    dialect: *const EVMDialect,
    no_output_dialect: ?*const NoOutputEVMDialect = null,
    builtin_context: *BuiltinContext,
    allow_stack_opt: bool,
    use_named_labels: UseNamedLabels,
    identifier_access: ExternalIdentifierAccess,
    context: *CodeTransformContext,
    owns_context: bool,
    variables_scheduled_for_deletion: std.AutoHashMap(*const ScopeModule.Variable, void),
    unused_stack_slots: StackSlotSet = .{},
    delayed_return_variables: []const AST.NameWithDebugData = &.{},
    function_exit_label: ?AbstractModule.LabelID = null,
    function_exit_stack_height: ?i32 = null,
    stack_errors: std.ArrayList(StackTooDeepError) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        assembly: AbstractAssembly,
        analysis_info: *AsmAnalysisInfo,
        block: *const AST.Block,
        dialect: *const EVMDialect,
        builtin_context: *BuiltinContext,
        allow_stack_opt: bool,
        identifier_access: ExternalIdentifierAccess,
        use_named_labels: UseNamedLabels,
    ) !CodeTransform {
        const context = try allocator.create(CodeTransformContext);
        errdefer allocator.destroy(context);
        context.* = CodeTransformContext.init(allocator);
        errdefer context.deinit();
        if (allow_stack_opt) {
            context.variable_references.deinit();
            context.variable_references = try VariableReferenceCounterModule.VariableReferenceCounter.run(
                allocator,
                analysis_info,
                block,
            );
        }
        return initWithContext(
            allocator,
            assembly,
            analysis_info,
            dialect,
            null,
            builtin_context,
            allow_stack_opt,
            identifier_access,
            use_named_labels,
            context,
            true,
            &.{},
            null,
        );
    }

    /// Constructs the classic transform with the dry-run builtin dispatcher
    /// used by `CompilabilityChecker`. Literal builtin arguments remain
    /// compile-time-only; every other argument is consumed and each return is
    /// represented by a zero constant.
    pub fn initNoOutput(
        allocator: std.mem.Allocator,
        assembly: AbstractAssembly,
        analysis_info: *AsmAnalysisInfo,
        block: *const AST.Block,
        dialect: *const NoOutputEVMDialect,
        builtin_context: *BuiltinContext,
        allow_stack_opt: bool,
    ) !CodeTransform {
        const context = try allocator.create(CodeTransformContext);
        errdefer allocator.destroy(context);
        context.* = CodeTransformContext.init(allocator);
        errdefer context.deinit();
        if (allow_stack_opt) {
            context.variable_references.deinit();
            context.variable_references = try VariableReferenceCounterModule.VariableReferenceCounter.run(
                allocator,
                analysis_info,
                block,
            );
        }
        return initWithContext(
            allocator,
            assembly,
            analysis_info,
            dialect.base,
            dialect,
            builtin_context,
            allow_stack_opt,
            .{},
            .never,
            context,
            true,
            &.{},
            null,
        );
    }

    fn initWithContext(
        allocator: std.mem.Allocator,
        assembly: AbstractAssembly,
        analysis_info: *AsmAnalysisInfo,
        dialect: *const EVMDialect,
        no_output_dialect: ?*const NoOutputEVMDialect,
        builtin_context: *BuiltinContext,
        allow_stack_opt: bool,
        identifier_access: ExternalIdentifierAccess,
        use_named_labels: UseNamedLabels,
        context: *CodeTransformContext,
        owns_context: bool,
        delayed_return_variables: []const AST.NameWithDebugData,
        function_exit_label: ?AbstractModule.LabelID,
    ) CodeTransform {
        return .{
            .allocator = allocator,
            .assembly = assembly,
            .info = analysis_info,
            .dialect = dialect,
            .no_output_dialect = no_output_dialect,
            .builtin_context = builtin_context,
            .allow_stack_opt = allow_stack_opt,
            .use_named_labels = use_named_labels,
            .identifier_access = identifier_access,
            .context = context,
            .owns_context = owns_context,
            .variables_scheduled_for_deletion = std.AutoHashMap(
                *const ScopeModule.Variable,
                void,
            ).init(allocator),
            .delayed_return_variables = delayed_return_variables,
            .function_exit_label = function_exit_label,
        };
    }

    pub fn deinit(self: *CodeTransform) void {
        for (self.stack_errors.items) |*stack_error| stack_error.deinit();
        self.stack_errors.deinit(self.allocator);
        self.variables_scheduled_for_deletion.deinit();
        self.unused_stack_slots.deinit(self.allocator);
        if (self.owns_context) {
            self.context.deinit();
            self.allocator.destroy(self.context);
        }
        self.* = undefined;
    }

    pub fn apply(self: *CodeTransform, block: *const AST.Block) anyerror!void {
        try self.visitBlock(block);
    }

    pub fn stackErrors(self: *const CodeTransform) []const StackTooDeepError {
        return self.stack_errors.items;
    }

    fn visitExpressionUnchecked(self: *CodeTransform, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .literal => |*literal| try self.visitLiteral(literal),
            .identifier => |*identifier| try self.visitIdentifier(identifier),
            .function_call => |*call| try self.visitFunctionCall(call),
        }
    }

    fn visitExpression(self: *CodeTransform, expression: *const AST.Expression) anyerror!void {
        const height = try self.assembly.stackHeight();
        try self.visitExpressionUnchecked(expression);
        try self.expectDeposit(1, height);
    }

    fn visitStatement(self: *CodeTransform, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*node| try self.visitExpressionStatement(node),
            .assignment => |*node| try self.visitAssignment(node),
            .variable_declaration => |*node| try self.visitVariableDeclaration(node),
            .function_definition => |*node| try self.visitFunctionDefinition(node),
            .if_statement => |*node| try self.visitIf(node),
            .switch_statement => |*node| try self.visitSwitch(node),
            .for_loop => |*node| try self.visitForLoop(node),
            .break_statement => |*node| try self.visitBreak(node),
            .continue_statement => |*node| try self.visitContinue(node),
            .leave_statement => |*node| try self.visitLeave(node),
            .block => |*node| try self.visitBlock(node),
        }
    }

    fn decreaseReference(self: *CodeTransform, variable: *const ScopeModule.Variable) !void {
        if (!self.allow_stack_opt) return;
        const reference = self.context.variable_references.getPtr(variable) orelse
            return error.InvalidReferenceState;
        if (reference.* == 0) return error.InvalidReferenceState;
        reference.* -= 1;
        if (reference.* == 0)
            try self.variables_scheduled_for_deletion.put(variable, {});
    }

    fn unreferenced(self: *const CodeTransform, variable: *const ScopeModule.Variable) bool {
        return (self.context.variable_references.get(variable) orelse 0) == 0;
    }

    fn freeUnusedVariables(self: *CodeTransform, pop_stack_top: bool) !void {
        if (!self.allow_stack_opt) return;
        const scope = self.scope orelse return error.InvalidAnalysisInfo;
        try self.deleteScheduledVariablesInScope(scope);
        if (!self.returnVariablesAndFunctionExitAreSetup() and
            !scope.function_scope and
            scope.super_scope != null and
            scope.super_scope.?.function_scope)
        {
            try self.deleteScheduledVariablesInScope(scope.super_scope.?);
        }
        if (pop_stack_top) {
            while (self.unused_stack_slots.contains((try self.assembly.stackHeight()) - 1)) {
                const slot = (try self.assembly.stackHeight()) - 1;
                if (!self.unused_stack_slots.remove(slot)) return error.InvalidStackState;
                try self.assembly.appendInstruction(.POP);
            }
        }
    }

    fn deleteScheduledVariablesInScope(self: *CodeTransform, scope: *Scope) !void {
        var iterator = scope.identifiers.valueIterator();
        while (iterator.next()) |identifier| switch (identifier.*) {
            .function => {},
            .variable => |*variable| {
                if (self.variables_scheduled_for_deletion.contains(variable))
                    try self.deleteVariable(variable);
            },
        };
    }

    fn deleteVariable(self: *CodeTransform, variable: *const ScopeModule.Variable) !void {
        if (!self.allow_stack_opt) return error.InvalidStackOptimizationState;
        const height = self.context.variable_stack_heights.get(variable) orelse
            return error.InvalidStackState;
        _ = try self.unused_stack_slots.insert(self.allocator, @intCast(height));
        if (!self.context.variable_stack_heights.remove(variable)) return error.InvalidStackState;
        if (!self.context.variable_references.remove(variable)) return error.InvalidReferenceState;
        if (!self.variables_scheduled_for_deletion.remove(variable)) return error.InvalidReferenceState;
    }

    fn visitVariableDeclaration(self: *CodeTransform, declaration: *const AST.VariableDeclaration) !void {
        const variable_count = declaration.variables.items.len;
        const raw_height = try self.assembly.stackHeight();
        if (raw_height < 0) return error.InvalidStackState;
        const height_at_start: usize = @intCast(raw_height);
        if (declaration.value) |value| {
            try self.visitExpressionUnchecked(value);
            try self.expectDeposit(@intCast(variable_count), @intCast(height_at_start));
            try self.freeUnusedVariables(false);
        } else {
            try self.assembly.setSourceLocation(originLocation(declaration.debug_data));
            for (0..variable_count) |_| try self.assembly.appendConstant(0);
        }
        try self.assembly.setSourceLocation(originLocation(declaration.debug_data));
        var at_top_of_stack = true;
        var variable_index: usize = 0;
        while (variable_index < variable_count) : (variable_index += 1) {
            const reverse_index = variable_count - 1 - variable_index;
            const variable_name = declaration.variables.items[reverse_index].name;
            const variable = try currentScopeVariable(self.scope, variable_name);
            try self.context.variable_stack_heights.put(variable, height_at_start + reverse_index);
            if (!self.allow_stack_opt) continue;
            if (self.unreferenced(variable)) {
                if (at_top_of_stack) {
                    if (!self.context.variable_stack_heights.remove(variable))
                        return error.InvalidStackState;
                    try self.assembly.appendInstruction(.POP);
                } else {
                    try self.variables_scheduled_for_deletion.put(variable, {});
                }
            } else {
                var found_unused_slot = false;
                var slot_index: usize = 0;
                while (slot_index < self.unused_stack_slots.len()) : (slot_index += 1) {
                    const slot = self.unused_stack_slots.at(slot_index);
                    if ((try self.assembly.stackHeight()) - slot >
                        @as(i32, @intCast(self.dialect.reachableStackDepth() + 1))) continue;
                    found_unused_slot = true;
                    if (!self.unused_stack_slots.remove(slot)) return error.InvalidStackState;
                    try self.context.variable_stack_heights.put(variable, @intCast(slot));
                    const height_difference = try self.variableHeightDiff(variable, variable_name, true);
                    if (height_difference != 0)
                        try self.assembly.appendInstruction(InstructionModule.swapInstruction(
                            @intCast(height_difference - 1),
                        ));
                    try self.assembly.appendInstruction(.POP);
                    break;
                }
                if (!found_unused_slot) at_top_of_stack = false;
            }
        }
    }

    fn visitAssignment(self: *CodeTransform, assignment: *const AST.Assignment) !void {
        const height = try self.assembly.stackHeight();
        try self.visitExpressionUnchecked(assignment.value orelse return error.InvalidAst);
        try self.expectDeposit(@intCast(assignment.variable_names.items.len), height);
        try self.assembly.setSourceLocation(originLocation(assignment.debug_data));
        var index = assignment.variable_names.items.len;
        while (index != 0) {
            index -= 1;
            try self.generateAssignment(&assignment.variable_names.items[index]);
        }
    }

    fn visitExpressionStatement(
        self: *CodeTransform,
        statement: *const AST.ExpressionStatement,
    ) !void {
        try self.assembly.setSourceLocation(originLocation(statement.debug_data));
        try self.visitExpressionUnchecked(&statement.expression);
    }

    fn visitFunctionCall(self: *CodeTransform, call: *const AST.FunctionCall) anyerror!void {
        const scope = self.scope orelse return error.InvalidAnalysisInfo;
        try self.assembly.setSourceLocation(originLocation(call.debug_data));
        if (try Utilities.resolveBuiltinFunctionForEVM(&call.function_name, self.dialect)) |builtin| {
            var index = call.arguments.items.len;
            while (index != 0) {
                index -= 1;
                if (builtin.base.literalArgument(index) == null)
                    try self.visitExpression(&call.arguments.items[index]);
            }
            try self.assembly.setSourceLocation(originLocation(call.debug_data));
            if (self.no_output_dialect) |dialect|
                try dialect.generateBuiltinCode(builtin, call, self.assembly, self.builtin_context)
            else
                try builtin.generateCode(call, self.assembly, self.builtin_context);
            return;
        }
        const function_identifier = switch (call.function_name) {
            .identifier => |identifier| identifier,
            .builtin => return error.UnknownBuiltin,
        };
        const return_label = try self.assembly.newLabelId();
        try self.assembly.appendLabelReference(return_label);
        const resolved = scope.lookup(function_identifier.name) orelse return error.FunctionNotFound;
        const function = switch (resolved.*) {
            .variable => return error.ExpectedFunction,
            .function => |*value| value,
        };
        if (function.num_arguments != call.arguments.items.len) return error.InvalidFunctionCall;
        var index = call.arguments.items.len;
        while (index != 0) {
            index -= 1;
            try self.visitExpression(&call.arguments.items[index]);
        }
        try self.assembly.setSourceLocation(originLocation(call.debug_data));
        try self.assembly.appendJumpTo(
            try self.functionEntryID(function),
            @as(i32, @intCast(function.num_returns)) -
                @as(i32, @intCast(function.num_arguments)) - 1,
            .into_function,
        );
        try self.assembly.appendLabel(return_label);
    }

    fn visitIdentifier(self: *CodeTransform, identifier: *const AST.Identifier) !void {
        try self.assembly.setSourceLocation(originLocation(identifier.debug_data));
        const scope = self.scope orelse return error.InvalidAnalysisInfo;
        if (scope.lookup(identifier.name)) |resolved| {
            switch (resolved.*) {
                .function => return error.ExpectedVariable,
                .variable => |*variable| {
                    const height_difference = try self.variableHeightDiff(variable, identifier.name, false);
                    if (height_difference != 0)
                        try self.assembly.appendInstruction(InstructionModule.dupInstruction(
                            @intCast(height_difference),
                        ))
                    else
                        try self.assembly.appendConstant(0);
                    try self.decreaseReference(variable);
                },
            }
            return;
        }
        try self.identifier_access.generateCode(identifier, .r_value, self.assembly);
    }

    fn visitLiteral(self: *CodeTransform, literal: *const AST.Literal) !void {
        try self.assembly.setSourceLocation(originLocation(literal.debug_data));
        try self.assembly.appendConstant(literal.value.value() catch return error.InvalidLiteral);
    }

    fn visitIf(self: *CodeTransform, if_statement: *const AST.If) anyerror!void {
        try self.visitExpression(if_statement.condition orelse return error.InvalidAst);
        try self.assembly.setSourceLocation(originLocation(if_statement.debug_data));
        try self.assembly.appendInstruction(.ISZERO);
        const end = try self.assembly.newLabelId();
        try self.assembly.appendJumpToIf(end, .ordinary);
        try self.visitBlock(&if_statement.body);
        try self.assembly.setSourceLocation(originLocation(if_statement.debug_data));
        try self.assembly.appendLabel(end);
    }

    fn visitSwitch(self: *CodeTransform, switch_statement: *const AST.Switch) anyerror!void {
        try self.visitExpression(switch_statement.expression orelse return error.InvalidAst);
        const expression_height = try self.assembly.stackHeight();
        const CaseBody = struct { case_value: *const AST.Case, label: AbstractModule.LabelID };
        var case_bodies: std.ArrayList(CaseBody) = .empty;
        defer case_bodies.deinit(self.allocator);
        const end = try self.assembly.newLabelId();
        for (switch_statement.cases.items) |*case_value| {
            if (case_value.value) |value| {
                try self.visitLiteral(value);
                try self.assembly.setSourceLocation(originLocation(case_value.debug_data));
                const body_label = try self.assembly.newLabelId();
                try case_bodies.append(self.allocator, .{ .case_value = case_value, .label = body_label });
                if (try self.assembly.stackHeight() != expression_height + 1)
                    return error.InvalidStackDeposit;
                try self.assembly.appendInstruction(InstructionModule.dupInstruction(2));
                try self.assembly.appendInstruction(.EQ);
                try self.assembly.appendJumpToIf(body_label, .ordinary);
            } else {
                try self.visitBlock(&case_value.body);
            }
        }
        try self.assembly.setSourceLocation(originLocation(switch_statement.debug_data));
        try self.assembly.appendJumpTo(end, 0, .ordinary);
        for (case_bodies.items, 0..) |entry, index| {
            try self.assembly.setSourceLocation(originLocation(entry.case_value.debug_data));
            try self.assembly.appendLabel(entry.label);
            try self.visitBlock(&entry.case_value.body);
            if (index + 1 < case_bodies.items.len) {
                try self.assembly.setSourceLocation(originLocation(entry.case_value.debug_data));
                try self.assembly.appendJumpTo(end, 0, .ordinary);
            }
        }
        try self.assembly.setSourceLocation(originLocation(switch_statement.debug_data));
        try self.assembly.appendLabel(end);
        try self.assembly.appendInstruction(.POP);
    }

    fn visitFunctionDefinition(
        self: *CodeTransform,
        function_definition: *const AST.FunctionDefinition,
    ) anyerror!void {
        const scope = self.scope orelse return error.InvalidAnalysisInfo;
        const scope_function = try currentScopeFunction(scope, function_definition.name);
        const virtual_block = self.info.getVirtualBlock(function_definition) orelse
            return error.InvalidAnalysisInfo;
        const virtual_scope = self.info.getScope(virtual_block) orelse
            return error.InvalidAnalysisInfo;
        var height: usize = 1;
        var parameter_index = function_definition.parameters.items.len;
        while (parameter_index != 0) {
            parameter_index -= 1;
            const variable = try currentScopeVariable(
                virtual_scope,
                function_definition.parameters.items[parameter_index].name,
            );
            try self.context.variable_stack_heights.put(variable, height);
            height += 1;
        }
        try self.assembly.setSourceLocation(originLocation(function_definition.debug_data));
        const stack_height_before = try self.assembly.stackHeight();
        try self.assembly.appendLabel(try self.functionEntryID(scope_function));
        try self.assembly.setStackHeight(@intCast(height));
        var sub_transform = initWithContext(
            self.allocator,
            self.assembly,
            self.info,
            self.dialect,
            self.no_output_dialect,
            self.builtin_context,
            self.allow_stack_opt,
            self.identifier_access,
            self.use_named_labels,
            self.context,
            false,
            function_definition.return_variables.items,
            try self.assembly.newLabelId(),
        );
        defer sub_transform.deinit();
        sub_transform.scope = virtual_scope;
        if (self.allow_stack_opt) {
            parameter_index = function_definition.parameters.items.len;
            while (parameter_index != 0) {
                parameter_index -= 1;
                const variable = try currentScopeVariable(
                    virtual_scope,
                    function_definition.parameters.items[parameter_index].name,
                );
                if ((self.context.variable_references.get(variable) orelse 0) == 0) {
                    try sub_transform.variables_scheduled_for_deletion.put(variable, {});
                    try sub_transform.deleteVariable(variable);
                }
            }
        } else {
            try sub_transform.setupReturnVariablesAndFunctionExit();
        }
        try sub_transform.visitBlock(&function_definition.body);
        try self.assembly.setSourceLocation(originLocation(function_definition.debug_data));
        if (sub_transform.stack_errors.items.len != 0) {
            try self.assembly.markAsInvalid();
            try self.stack_errors.ensureUnusedCapacity(
                self.allocator,
                sub_transform.stack_errors.items.len,
            );
            for (sub_transform.stack_errors.items) |*stack_error| {
                if (stack_error.function_name.empty())
                    stack_error.function_name = function_definition.name;
                self.stack_errors.appendAssumeCapacity(stack_error.*);
            }
            sub_transform.stack_errors.clearRetainingCapacity();
        }
        if (!sub_transform.returnVariablesAndFunctionExitAreSetup())
            try sub_transform.setupReturnVariablesAndFunctionExit();
        _ = try self.appendPopUntil(sub_transform.function_exit_stack_height.?);
        if (try self.assembly.stackHeight() != sub_transform.function_exit_stack_height.?)
            return error.InvalidFunctionExitStack;
        try self.assembly.appendLabel(sub_transform.function_exit_label.?);

        var stack_layout: std.ArrayList(i32) = .empty;
        defer stack_layout.deinit(self.allocator);
        const current_height = try self.assembly.stackHeight();
        if (current_height < 0) return error.InvalidStackState;
        try stack_layout.appendNTimes(self.allocator, -1, @intCast(current_height));
        if (stack_layout.items.len == 0) return error.InvalidFunctionExitStack;
        stack_layout.items[0] = @intCast(function_definition.return_variables.items.len);
        for (function_definition.return_variables.items, 0..) |return_variable, index| {
            const variable = try currentScopeVariable(virtual_scope, return_variable.name);
            const slot = self.context.variable_stack_heights.get(variable) orelse
                return error.InvalidStackState;
            if (slot >= stack_layout.items.len) return error.InvalidStackState;
            stack_layout.items[slot] = @intCast(index);
        }
        if (stack_layout.items.len > self.dialect.reachableStackDepth() + 1) {
            const unreachable_slots = stack_layout.items.len - (self.dialect.reachableStackDepth() + 1);
            const function_name = try function_definition.name.str();
            const message = try std.fmt.allocPrint(
                self.allocator,
                "The function {s} has {d} parameters or return variables too many to fit the stack size.",
                .{ function_name, unreachable_slots },
            );
            defer self.allocator.free(message);
            const stack_error = try StackTooDeepError.initInFunction(
                self.allocator,
                function_definition.name,
                .{},
                @intCast(unreachable_slots),
                message,
            );
            try self.stackError(
                stack_error,
                (try self.assembly.stackHeight()) -
                    @as(i32, @intCast(function_definition.parameters.items.len)),
            );
        } else {
            while (stack_layout.items.len != 0 and
                stack_layout.items[stack_layout.items.len - 1] !=
                    @as(i32, @intCast(stack_layout.items.len - 1)))
            {
                const target = stack_layout.items[stack_layout.items.len - 1];
                if (target < 0) {
                    try self.assembly.appendInstruction(.POP);
                    _ = stack_layout.pop();
                } else {
                    const target_index: usize = @intCast(target);
                    if (target_index >= stack_layout.items.len) return error.InvalidStackLayout;
                    const swap_depth = stack_layout.items.len - target_index - 1;
                    try self.assembly.appendInstruction(InstructionModule.swapInstruction(
                        @intCast(swap_depth),
                    ));
                    std.mem.swap(
                        i32,
                        &stack_layout.items[target_index],
                        &stack_layout.items[stack_layout.items.len - 1],
                    );
                }
            }
            for (stack_layout.items, 0..) |target, index|
                if (target != @as(i32, @intCast(index))) return error.InvalidStackLayout;
        }
        try self.assembly.appendJump(
            stack_height_before - @as(i32, @intCast(function_definition.return_variables.items.len)),
            .out_of_function,
        );
        try self.assembly.setStackHeight(stack_height_before);
    }

    fn visitForLoop(self: *CodeTransform, loop: *const AST.ForLoop) anyerror!void {
        const original_scope = self.scope;
        defer self.scope = original_scope;
        self.scope = self.info.getScope(&loop.pre) orelse return error.InvalidAnalysisInfo;
        const stack_start_height = try self.assembly.stackHeight();
        try self.visitStatements(loop.pre.statements.items);
        const loop_start = try self.assembly.newLabelId();
        const post_part = try self.assembly.newLabelId();
        const loop_end = try self.assembly.newLabelId();
        try self.assembly.setSourceLocation(originLocation(loop.debug_data));
        try self.assembly.appendLabel(loop_start);
        try self.visitExpression(loop.condition orelse return error.InvalidAst);
        try self.assembly.setSourceLocation(originLocation(loop.debug_data));
        try self.assembly.appendInstruction(.ISZERO);
        try self.assembly.appendJumpToIf(loop_end, .ordinary);
        const body_height = try self.assembly.stackHeight();
        try self.context.for_loop_stack.append(self.allocator, .{
            .post = .{ .label = post_part, .target_stack_height = body_height },
            .done = .{ .label = loop_end, .target_stack_height = body_height },
        });
        defer _ = self.context.for_loop_stack.pop();
        try self.visitBlock(&loop.body);
        try self.assembly.setSourceLocation(originLocation(loop.debug_data));
        try self.assembly.appendLabel(post_part);
        try self.visitBlock(&loop.post);
        try self.assembly.setSourceLocation(originLocation(loop.debug_data));
        try self.assembly.appendJumpTo(loop_start, 0, .ordinary);
        try self.assembly.appendLabel(loop_end);
        try self.finalizeBlock(&loop.pre, stack_start_height);
    }

    fn appendPopUntil(self: *CodeTransform, target_depth: i32) !i32 {
        const difference = (try self.assembly.stackHeight()) - target_depth;
        var index: i32 = 0;
        while (index < difference) : (index += 1) try self.assembly.appendInstruction(.POP);
        return difference;
    }

    fn visitBreak(self: *CodeTransform, node: *const AST.Break) !void {
        if (self.context.for_loop_stack.items.len == 0) return error.BreakOutsideLoop;
        try self.assembly.setSourceLocation(originLocation(node.debug_data));
        const jump = self.context.for_loop_stack.items[self.context.for_loop_stack.items.len - 1].done;
        try self.assembly.appendJumpTo(
            jump.label,
            try self.appendPopUntil(jump.target_stack_height),
            .ordinary,
        );
    }

    fn visitContinue(self: *CodeTransform, node: *const AST.Continue) !void {
        if (self.context.for_loop_stack.items.len == 0) return error.ContinueOutsideLoop;
        try self.assembly.setSourceLocation(originLocation(node.debug_data));
        const jump = self.context.for_loop_stack.items[self.context.for_loop_stack.items.len - 1].post;
        try self.assembly.appendJumpTo(
            jump.label,
            try self.appendPopUntil(jump.target_stack_height),
            .ordinary,
        );
    }

    fn visitLeave(self: *CodeTransform, node: *const AST.Leave) !void {
        const label = self.function_exit_label orelse return error.LeaveOutsideFunction;
        const height = self.function_exit_stack_height orelse return error.InvalidFunctionExitStack;
        try self.assembly.setSourceLocation(originLocation(node.debug_data));
        try self.assembly.appendJumpTo(label, try self.appendPopUntil(height), .ordinary);
    }

    fn visitBlock(self: *CodeTransform, block: *const AST.Block) anyerror!void {
        const original_scope = self.scope;
        defer self.scope = original_scope;
        self.scope = self.info.getScope(block) orelse return error.InvalidAnalysisInfo;
        for (block.statements.items) |*statement| {
            if (statement.* == .function_definition)
                try self.createFunctionEntryID(&statement.function_definition);
        }
        const block_start_height = try self.assembly.stackHeight();
        try self.visitStatements(block.statements.items);
        const scope = self.scope.?;
        const outermost_function_body = scope.super_scope != null and
            scope.super_scope.?.function_scope;
        const validate_height: ?i32 = if (!self.allow_stack_opt or !outermost_function_body)
            block_start_height
        else
            null;
        try self.finalizeBlock(block, validate_height);
    }

    fn createFunctionEntryID(
        self: *CodeTransform,
        function_definition: *const AST.FunctionDefinition,
    ) !void {
        const scope = self.scope orelse return error.InvalidAnalysisInfo;
        const function = try currentScopeFunction(scope, function_definition.name);
        if (self.context.function_entry_ids.contains(function)) return error.DuplicateFunctionEntry;
        const name_already_seen = self.context.assigned_named_labels.contains(function_definition.name);
        try self.context.assigned_named_labels.put(function_definition.name, {});
        if (self.use_named_labels == .yes_and_force_unique and name_already_seen)
            return error.DuplicateNamedLabel;
        const use_named = self.use_named_labels != .never and !name_already_seen;
        const label = if (use_named) try self.assembly.namedLabel(
            try function_definition.name.str(),
            function_definition.parameters.items.len,
            function_definition.return_variables.items.len,
            try astId(function_definition.debug_data),
        ) else try self.assembly.newLabelId();
        try self.context.function_entry_ids.put(function, label);
    }

    fn functionEntryID(
        self: *const CodeTransform,
        function: *const ScopeModule.Function,
    ) !AbstractModule.LabelID {
        return self.context.function_entry_ids.get(function) orelse error.FunctionEntryNotFound;
    }

    fn setupReturnVariablesAndFunctionExit(self: *CodeTransform) !void {
        if (self.function_exit_label == null or self.function_exit_stack_height != null)
            return error.InvalidFunctionExitStack;
        const original_scope = self.scope;
        defer self.scope = original_scope;
        var scope = self.scope orelse return error.InvalidAnalysisInfo;
        if (!scope.function_scope) {
            if (scope.super_scope == null or !scope.super_scope.?.function_scope)
                return error.InvalidAnalysisInfo;
            scope = scope.super_scope.?;
            self.scope = scope;
        }
        self.unused_stack_slots.map.clearRetainingCapacity();
        if (self.delayed_return_variables.len == 0) {
            self.function_exit_stack_height = 1;
            return;
        }
        for (self.delayed_return_variables) |return_variable| {
            const raw_height = try self.assembly.stackHeight();
            if (raw_height < 0) return error.InvalidStackState;
            try self.assembly.setSourceLocation(originLocation(return_variable.debug_data));
            try self.assembly.appendConstant(0);
            try self.assembly.setSourceLocation(originLocation(return_variable.debug_data));
            const variable = try currentScopeVariable(scope, return_variable.name);
            try self.context.variable_stack_heights.put(variable, @intCast(raw_height));
        }
        var maximum_height: usize = 0;
        for (self.delayed_return_variables) |return_variable| {
            maximum_height = @max(maximum_height, try self.variableStackHeight(return_variable.name));
        }
        self.function_exit_stack_height = @intCast(maximum_height + 1);
        self.delayed_return_variables = &.{};
    }

    fn returnVariablesAndFunctionExitAreSetup(self: *const CodeTransform) bool {
        return self.function_exit_stack_height != null;
    }

    fn visitStatements(self: *CodeTransform, statements: []const AST.Statement) anyerror!void {
        var jump_target: ?AbstractModule.LabelID = null;
        for (statements) |*statement| {
            try self.freeUnusedVariables(true);
            if (self.function_exit_label != null and
                !self.returnVariablesAndFunctionExitAreSetup() and
                statementNeedsReturnVariableSetup(statement, self.delayed_return_variables))
            {
                try self.setupReturnVariablesAndFunctionExit();
            }
            const is_function = statement.* == .function_definition;
            if (is_function and jump_target == null) {
                try self.assembly.setSourceLocation(AST.originLocationOfStatement(statement));
                jump_target = try self.assembly.newLabelId();
                try self.assembly.appendJumpTo(jump_target.?, 0, .ordinary);
            } else if (!is_function and jump_target != null) {
                try self.assembly.appendLabel(jump_target.?);
                jump_target = null;
            }
            try self.visitStatement(statement);
        }
        if (jump_target) |label| try self.assembly.appendLabel(label);
        try self.freeUnusedVariables(true);
    }

    fn finalizeBlock(self: *CodeTransform, block: *const AST.Block, start_height: ?i32) !void {
        try self.assembly.setSourceLocation(originLocation(block.debug_data));
        try self.freeUnusedVariables(true);
        const scope = self.scope orelse return error.InvalidAnalysisInfo;
        if (self.info.getScope(block) != scope) return error.InvalidAnalysisInfo;
        var iterator = scope.identifiers.valueIterator();
        while (iterator.next()) |identifier| switch (identifier.*) {
            .function => {},
            .variable => |*variable| {
                if (self.allow_stack_opt) {
                    if (self.context.variable_stack_heights.contains(variable) or
                        self.context.variable_references.contains(variable))
                        return error.InvalidStackOptimizationState;
                } else {
                    try self.assembly.appendInstruction(.POP);
                }
            },
        };
        if (start_height) |expected_height| {
            if ((try self.assembly.stackHeight()) - expected_height != 0)
                return error.InvalidStackDeposit;
        }
    }

    fn generateAssignment(self: *CodeTransform, identifier: *const AST.Identifier) !void {
        const scope = self.scope orelse return error.InvalidAnalysisInfo;
        if (scope.lookup(identifier.name)) |resolved| {
            const variable = switch (resolved.*) {
                .function => return error.ExpectedVariable,
                .variable => |*value| value,
            };
            const height_difference = try self.variableHeightDiff(variable, identifier.name, true);
            if (height_difference != 0)
                try self.assembly.appendInstruction(InstructionModule.swapInstruction(
                    @intCast(height_difference - 1),
                ));
            try self.assembly.appendInstruction(.POP);
            try self.decreaseReference(variable);
            return;
        }
        try self.identifier_access.generateCode(identifier, .l_value, self.assembly);
    }

    fn variableHeightDiff(
        self: *CodeTransform,
        variable: *const ScopeModule.Variable,
        variable_name: YulName,
        for_swap: bool,
    ) !usize {
        const stack_height = try self.assembly.stackHeight();
        if (stack_height < 0) return error.InvalidStackState;
        const variable_height = self.context.variable_stack_heights.get(variable) orelse
            return error.VariableNotOnStack;
        if (@as(usize, @intCast(stack_height)) < variable_height)
            return error.InvalidStackState;
        const height_difference = @as(usize, @intCast(stack_height)) - variable_height;
        if (height_difference <= @intFromBool(for_swap)) return error.InvalidStackDifference;
        const limit = self.dialect.reachableStackDepth() + @intFromBool(for_swap);
        if (height_difference > limit) {
            const excess = height_difference - limit;
            const variable_text = try variable_name.str();
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Variable {s} is {d} slot(s) too deep inside the stack. {s}",
                .{
                    variable_text,
                    excess,
                    @import("../../../libsolutil/stack_too_deep_string.zig").stack_too_deep_string,
                },
            );
            defer self.allocator.free(message);
            try self.stack_errors.append(
                self.allocator,
                try StackTooDeepError.init(
                    self.allocator,
                    variable_name,
                    @intCast(excess),
                    message,
                ),
            );
            try self.assembly.markAsInvalid();
            return if (for_swap) 2 else 1;
        }
        return height_difference;
    }

    fn variableStackHeight(self: *const CodeTransform, name: YulName) !usize {
        const scope = self.scope orelse return error.InvalidAnalysisInfo;
        const variable = try lookupVariable(scope, name);
        return self.context.variable_stack_heights.get(variable) orelse error.VariableNotOnStack;
    }

    fn expectDeposit(self: *const CodeTransform, deposit: i32, old_height: i32) !void {
        if (try self.assembly.stackHeight() != old_height + deposit)
            return error.InvalidStackDeposit;
    }

    fn stackError(self: *CodeTransform, stack_error: StackTooDeepError, target_height: i32) !void {
        errdefer {
            var owned_error = stack_error;
            owned_error.deinit();
        }
        try self.assembly.appendInstruction(.INVALID);
        while (try self.assembly.stackHeight() > target_height)
            try self.assembly.appendInstruction(.POP);
        while (try self.assembly.stackHeight() < target_height)
            try self.assembly.appendConstant(0);
        try self.stack_errors.append(self.allocator, stack_error);
        try self.assembly.markAsInvalid();
    }
};

fn currentScopeVariable(scope: ?*Scope, name: YulName) !*const ScopeModule.Variable {
    const current = scope orelse return error.InvalidAnalysisInfo;
    const identifier = current.identifiers.getPtr(name) orelse return error.VariableNotFound;
    return switch (identifier.*) {
        .function => error.ExpectedVariable,
        .variable => |*variable| variable,
    };
}

fn currentScopeFunction(scope: *Scope, name: YulName) !*const ScopeModule.Function {
    const identifier = scope.identifiers.getPtr(name) orelse return error.FunctionNotFound;
    return switch (identifier.*) {
        .variable => error.ExpectedFunction,
        .function => |*function| function,
    };
}

fn lookupVariable(scope: *Scope, name: YulName) !*const ScopeModule.Variable {
    const identifier = scope.lookup(name) orelse return error.VariableNotFound;
    return switch (identifier.*) {
        .function => error.ExpectedVariable,
        .variable => |*variable| variable,
    };
}

fn originLocation(debug_data: ?DebugData) SourceLocation {
    return if (debug_data) |debug| debug.origin_location else .{};
}

fn astId(debug_data: ?DebugData) !?usize {
    const raw = if (debug_data) |debug| debug.ast_id else null;
    if (raw) |value| {
        if (value < 0) return error.InvalidAstId;
        return @intCast(value);
    }
    return null;
}

fn statementNeedsReturnVariableSetup(
    statement: *const AST.Statement,
    return_variables: []const AST.NameWithDebugData,
) bool {
    if (statement.* == .function_definition) return true;
    if (statement.* == .expression_statement or statement.* == .assignment) {
        for (return_variables) |return_variable|
            if (statementReferencesName(statement, return_variable.name)) return true;
        return false;
    }
    return true;
}

fn statementReferencesName(statement: *const AST.Statement, name: YulName) bool {
    return switch (statement.*) {
        .expression_statement => |*node| expressionReferencesName(&node.expression, name),
        .assignment => |*node| blk: {
            for (node.variable_names.items) |identifier|
                if (identifier.name.eql(name)) break :blk true;
            break :blk if (node.value) |value| expressionReferencesName(value, name) else false;
        },
        else => false,
    };
}

fn expressionReferencesName(expression: *const AST.Expression, name: YulName) bool {
    return switch (expression.*) {
        .literal => false,
        .identifier => |identifier| identifier.name.eql(name),
        .function_call => |call| blk: {
            for (call.arguments.items) |*argument|
                if (expressionReferencesName(argument, name)) break :blk true;
            break :blk false;
        },
    };
}

test "classic transform emits the expected stack program for a local value" {
    const Parser = @import("../../asm_parser.zig").Parser;
    const AsmAnalysis = @import("../../asm_analysis.zig");
    const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
    const Assembly = @import("../../../libevmasm/assembly.zig").Assembly;
    const Adapter = @import("eth_assembly_adapter.zig").EthAssemblyAdapter;
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.init(.Cancun), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := add(1, 2) pop(x) }",
        "codegen.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    defer info.deinit();
    var analyzer = AsmAnalysis.AsmAnalyzer.init(
        allocator,
        &info,
        &reporter,
        dialect.dialect(),
        .{},
        .{},
        AsmAnalysis.instructionValidatorForEVMDialect(&dialect),
    );
    defer analyzer.deinit();
    try std.testing.expect(try analyzer.analyze(ast.root()));
    var assembly = try Assembly.init(allocator, EVMVersion.init(.Cancun), false, "codegen");
    defer assembly.deinit();
    var adapter = Adapter.init(allocator, &assembly);
    defer adapter.deinit();
    var builtin_context = BuiltinContext.init(allocator);
    defer builtin_context.deinit();
    var transform = try CodeTransform.init(
        allocator,
        adapter.abstractAssembly(),
        &info,
        ast.root(),
        &dialect,
        &builtin_context,
        false,
        .{},
        .never,
    );
    defer transform.deinit();
    try transform.apply(ast.root());
    try std.testing.expectEqual(@as(usize, 0), transform.stackErrors().len);
    try std.testing.expectEqual(@as(i32, 0), try adapter.abstractAssembly().stackHeight());
    const object = try assembly.assemble();
    try std.testing.expectEqualSlices(
        u8,
        &.{ 0x60, 0x02, 0x60, 0x01, 0x01, 0x80, 0x50, 0x50 },
        object.bytecode.items,
    );
}
