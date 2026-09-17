// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Three-phase conversion of reassigned Yul variables to explicit SSA values.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const DebugData = @import("../../liblangutil/debug_data.zig").DebugData;
const NameCollector = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const YulName = @import("../yul_name.zig").YulName;

pub const SSATransform = struct {
    pub const name = "SSATransform";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        const scratch_allocator = context.scratchAllocator();
        var assigned_variables = try NameCollector.assignedVariableNames(scratch_allocator, ast);
        defer assigned_variables.deinit(scratch_allocator);

        var introduce_ssa: IntroduceSSA = .{
            .allocator = allocator,
            .name_dispenser = context.dispenser,
            .variables_to_replace = &assigned_variables,
        };
        try introduce_ssa.visitBlock(ast);

        var introduce_control_flow: IntroduceControlFlowSSA = .{
            .allocator = allocator,
            .scratch_allocator = scratch_allocator,
            .name_dispenser = context.dispenser,
            .variables_to_replace = &assigned_variables,
        };
        defer introduce_control_flow.deinit();
        try introduce_control_flow.visitBlock(ast);

        var propagate: PropagateValues = .{
            .allocator = scratch_allocator,
            .variables_to_replace = &assigned_variables,
        };
        defer propagate.deinit();
        try propagate.visitBlock(ast);
    }
};

const IntroduceSSA = struct {
    allocator: std.mem.Allocator,
    name_dispenser: *NameDispenser,
    variables_to_replace: *const NameCollector.NameSet,

    fn visitBlock(self: *IntroduceSSA, block: *AST.Block) anyerror!void {
        var index: usize = 0;
        while (index < block.statements.items.len) {
            if (try self.replacementFor(&block.statements.items[index])) |replacement_value| {
                var replacement = replacement_value;
                defer deinitStatements(self.allocator, &replacement);
                std.debug.assert(replacement.items.len != 0);
                try block.statements.ensureUnusedCapacity(self.allocator, replacement.items.len - 1);

                switch (block.statements.items[index]) {
                    .variable_declaration => |*declaration| {
                        replacement.items[0].variable_declaration.value = declaration.value;
                        declaration.value = null;
                        declaration.variables.deinit(self.allocator);
                        declaration.variables = .empty;
                    },
                    .assignment => |*assignment| {
                        replacement.items[0].variable_declaration.value = assignment.value;
                        assignment.value = null;
                        assignment.variable_names.deinit(self.allocator);
                        assignment.variable_names = .empty;
                    },
                    else => unreachable,
                }

                block.statements.items[index] = replacement.items[0];
                if (replacement.items.len > 1) block.statements.insertSliceAssumeCapacity(
                    index + 1,
                    replacement.items[1..],
                );
                const inserted = replacement.items.len;
                replacement.clearRetainingCapacity();
                index += inserted;
            } else {
                try self.visitStatement(&block.statements.items[index]);
                index += 1;
            }
        }
    }

    fn replacementFor(
        self: *IntroduceSSA,
        statement: *AST.Statement,
    ) anyerror!?std.ArrayList(AST.Statement) {
        switch (statement.*) {
            .variable_declaration => |*declaration| {
                var replace = false;
                for (declaration.variables.items) |variable| {
                    if (self.variables_to_replace.contains(variable.name)) {
                        replace = true;
                        break;
                    }
                }
                if (!replace) return null;

                var result: std.ArrayList(AST.Statement) = .empty;
                errdefer deinitStatements(self.allocator, &result);
                try result.append(self.allocator, .{ .variable_declaration = .{
                    .debug_data = declaration.debug_data,
                } });
                for (declaration.variables.items) |variable| {
                    const new_name = try self.name_dispenser.newName(variable.name);
                    try result.items[0].variable_declaration.variables.append(
                        self.allocator,
                        .{ .debug_data = declaration.debug_data, .name = new_name },
                    );
                    var old_declaration = try variableCopyDeclaration(
                        self.allocator,
                        declaration.debug_data,
                        variable.name,
                        new_name,
                    );
                    errdefer old_declaration.deinit(self.allocator);
                    try result.append(self.allocator, old_declaration);
                }
                return result;
            },
            .assignment => |*assignment| {
                for (assignment.variable_names.items) |variable|
                    if (!self.variables_to_replace.contains(variable.name)) return error.InvalidAst;

                var result: std.ArrayList(AST.Statement) = .empty;
                errdefer deinitStatements(self.allocator, &result);
                try result.append(self.allocator, .{ .variable_declaration = .{
                    .debug_data = assignment.debug_data,
                } });
                for (assignment.variable_names.items) |variable| {
                    const new_name = try self.name_dispenser.newName(variable.name);
                    try result.items[0].variable_declaration.variables.append(
                        self.allocator,
                        .{ .debug_data = assignment.debug_data, .name = new_name },
                    );
                    var old_assignment = try variableCopyAssignment(
                        self.allocator,
                        assignment.debug_data,
                        variable.name,
                        new_name,
                    );
                    errdefer old_assignment.deinit(self.allocator);
                    try result.append(self.allocator, old_assignment);
                }
                return result;
            },
            else => return null,
        }
    }

    fn visitStatement(self: *IntroduceSSA, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*function| try self.visitBlock(&function.body),
            .if_statement => |*if_statement| try self.visitBlock(&if_statement.body),
            .switch_statement => |*switch_statement| for (switch_statement.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*loop| {
                // Matches ASTModifier's ordering, which is significant for generated names.
                try self.visitBlock(&loop.pre);
                try self.visitBlock(&loop.post);
                try self.visitBlock(&loop.body);
            },
            .block => |*nested| try self.visitBlock(nested),
            else => {},
        }
    }
};

const UniqueNameList = struct {
    items: std.ArrayList(YulName) = .empty,

    fn deinit(self: *UniqueNameList, allocator: std.mem.Allocator) void {
        self.items.deinit(allocator);
        self.* = undefined;
    }

    fn clearRetainingCapacity(self: *UniqueNameList) void {
        self.items.clearRetainingCapacity();
    }

    fn contains(self: *const UniqueNameList, name: YulName) bool {
        for (self.items.items) |candidate| if (candidate.eql(name)) return true;
        return false;
    }

    fn append(self: *UniqueNameList, allocator: std.mem.Allocator, name: YulName) !void {
        if (!self.contains(name)) try self.items.append(allocator, name);
    }

    fn appendAll(
        self: *UniqueNameList,
        allocator: std.mem.Allocator,
        other: *const UniqueNameList,
    ) !void {
        for (other.items.items) |name| try self.append(allocator, name);
    }

    fn removeAll(self: *UniqueNameList, names: *const UniqueNameList) void {
        for (names.items.items) |name| {
            var index: usize = 0;
            while (index < self.items.items.len) : (index += 1) {
                if (self.items.items[index].eql(name)) {
                    _ = self.items.orderedRemove(index);
                    break;
                }
            }
        }
    }
};

const IntroduceControlFlowSSA = struct {
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    name_dispenser: *NameDispenser,
    variables_to_replace: *const NameCollector.NameSet,
    variables_in_scope: NameCollector.NameSet = .{},
    variables_to_reassign: UniqueNameList = .{},

    fn deinit(self: *IntroduceControlFlowSSA) void {
        self.variables_in_scope.deinit(self.scratch_allocator);
        self.variables_to_reassign.deinit(self.scratch_allocator);
        self.* = undefined;
    }

    fn visitFunction(self: *IntroduceControlFlowSSA, function: *AST.FunctionDefinition) anyerror!void {
        const parent_scope = self.variables_in_scope;
        const parent_reassign = self.variables_to_reassign;
        self.variables_in_scope = .{};
        self.variables_to_reassign = .{};
        defer {
            self.variables_in_scope.deinit(self.scratch_allocator);
            self.variables_to_reassign.deinit(self.scratch_allocator);
            self.variables_in_scope = parent_scope;
            self.variables_to_reassign = parent_reassign;
        }

        for (function.parameters.items) |parameter| {
            if (self.variables_to_replace.contains(parameter.name)) {
                _ = try self.variables_in_scope.insert(self.scratch_allocator, parameter.name);
                try self.variables_to_reassign.append(self.scratch_allocator, parameter.name);
            }
        }
        try self.visitBlock(&function.body);
    }

    fn visitForLoop(self: *IntroduceControlFlowSSA, loop: *AST.ForLoop) anyerror!void {
        if (loop.pre.statements.items.len != 0) return error.ForLoopInitRewriterNotRun;
        var assigned = try NameCollector.assignedVariableNames(self.scratch_allocator, &loop.body);
        defer assigned.deinit(self.scratch_allocator);
        var post_assigned = try NameCollector.assignedVariableNames(self.scratch_allocator, &loop.post);
        defer post_assigned.deinit(self.scratch_allocator);
        for (0..post_assigned.len()) |index|
            _ = try assigned.insert(self.scratch_allocator, post_assigned.at(index));
        for (0..assigned.len()) |index| {
            const variable = assigned.at(index);
            if (self.variables_in_scope.contains(variable))
                try self.variables_to_reassign.append(self.scratch_allocator, variable);
        }
        try self.visitBlock(&loop.body);
        try self.visitBlock(&loop.post);
    }

    fn visitSwitch(self: *IntroduceControlFlowSSA, switch_statement: *AST.Switch) anyerror!void {
        if (self.variables_to_reassign.items.items.len != 0) return error.InvalidControlFlowSSAState;
        var to_reassign: UniqueNameList = .{};
        defer to_reassign.deinit(self.scratch_allocator);
        for (switch_statement.cases.items) |*case_value| {
            try self.visitBlock(&case_value.body);
            try to_reassign.appendAll(self.scratch_allocator, &self.variables_to_reassign);
        }
        try self.variables_to_reassign.appendAll(self.scratch_allocator, &to_reassign);
    }

    fn visitBlock(self: *IntroduceControlFlowSSA, block: *AST.Block) anyerror!void {
        var variables_declared_here: UniqueNameList = .{};
        defer variables_declared_here.deinit(self.scratch_allocator);
        var assigned_variables: UniqueNameList = .{};
        defer assigned_variables.deinit(self.scratch_allocator);

        var index: usize = 0;
        while (index < block.statements.items.len) {
            var to_prepend: std.ArrayList(AST.Statement) = .empty;
            defer deinitStatements(self.allocator, &to_prepend);
            const debug_data = debugDataOfStatement(&block.statements.items[index]);
            for (self.variables_to_reassign.items.items) |variable| {
                const new_name = try self.name_dispenser.newName(variable);
                var declaration = try variableCopyDeclaration(
                    self.allocator,
                    debug_data,
                    new_name,
                    variable,
                );
                errdefer declaration.deinit(self.allocator);
                try to_prepend.append(self.allocator, declaration);
                try assigned_variables.append(self.scratch_allocator, variable);
            }
            self.variables_to_reassign.clearRetainingCapacity();

            switch (block.statements.items[index]) {
                .variable_declaration => |*declaration| for (declaration.variables.items) |variable| {
                    if (self.variables_to_replace.contains(variable.name)) {
                        try variables_declared_here.append(self.scratch_allocator, variable.name);
                        _ = try self.variables_in_scope.insert(self.scratch_allocator, variable.name);
                    }
                },
                .assignment => |*assignment| for (assignment.variable_names.items) |variable| {
                    if (self.variables_to_replace.contains(variable.name))
                        try assigned_variables.append(self.scratch_allocator, variable.name);
                },
                else => try self.visitStatement(&block.statements.items[index]),
            }

            if (to_prepend.items.len != 0) {
                const count = to_prepend.items.len;
                try block.statements.insertSlice(self.allocator, index, to_prepend.items);
                to_prepend.clearRetainingCapacity();
                index += count;
            }
            index += 1;
        }

        for (assigned_variables.items.items) |variable|
            try self.variables_to_reassign.append(self.scratch_allocator, variable);
        for (variables_declared_here.items.items) |variable|
            _ = self.variables_in_scope.remove(variable);
        self.variables_to_reassign.removeAll(&variables_declared_here);
    }

    fn visitStatement(self: *IntroduceControlFlowSSA, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*function| try self.visitFunction(function),
            .if_statement => |*if_statement| try self.visitBlock(&if_statement.body),
            .switch_statement => |*switch_statement| try self.visitSwitch(switch_statement),
            .for_loop => |*loop| try self.visitForLoop(loop),
            .block => |*nested| try self.visitBlock(nested),
            else => {},
        }
    }
};

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

const CurrentValueMap = ordered.OrderedMap(YulName, YulName, lessYulName);

const PropagateValues = struct {
    allocator: std.mem.Allocator,
    variables_to_replace: *const NameCollector.NameSet,
    current_variable_values: CurrentValueMap = .{},
    clear_at_end_of_block: NameCollector.NameSet = .{},

    fn deinit(self: *PropagateValues) void {
        self.current_variable_values.deinit(self.allocator);
        self.clear_at_end_of_block.deinit(self.allocator);
        self.* = undefined;
    }

    fn visitIdentifier(self: *PropagateValues, identifier: *AST.Identifier) void {
        if (self.current_variable_values.get(identifier.name)) |current|
            identifier.name = current.*;
    }

    fn visitExpression(self: *PropagateValues, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .identifier => |*identifier| self.visitIdentifier(identifier),
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
            .literal => {},
        }
    }

    fn visitVariableDeclaration(
        self: *PropagateValues,
        declaration: *AST.VariableDeclaration,
    ) anyerror!void {
        if (declaration.value) |value| try self.visitExpression(value);
        if (declaration.variables.items.len != 1) return;

        const variable = declaration.variables.items[0].name;
        if (self.variables_to_replace.contains(variable)) {
            const value = declaration.value orelse return error.InvalidAst;
            if (value.* != .identifier) return error.InvalidAst;
            _ = try self.current_variable_values.fetchPut(
                self.allocator,
                variable,
                value.identifier.name,
            );
            _ = try self.clear_at_end_of_block.insert(self.allocator, variable);
        } else if (declaration.value) |value| {
            if (value.* == .identifier and self.variables_to_replace.contains(value.identifier.name)) {
                _ = try self.current_variable_values.fetchPut(
                    self.allocator,
                    value.identifier.name,
                    variable,
                );
                _ = try self.clear_at_end_of_block.insert(self.allocator, value.identifier.name);
            }
        }
    }

    fn visitAssignment(self: *PropagateValues, assignment: *AST.Assignment) anyerror!void {
        try self.visitExpression(assignment.value orelse return error.InvalidAst);
        if (assignment.variable_names.items.len != 1) return;
        const variable = assignment.variable_names.items[0].name;
        if (!self.variables_to_replace.contains(variable)) return;
        const value = assignment.value.?;
        if (value.* != .identifier) return error.InvalidAst;
        _ = try self.current_variable_values.fetchPut(
            self.allocator,
            variable,
            value.identifier.name,
        );
        _ = try self.clear_at_end_of_block.insert(self.allocator, variable);
    }

    fn visitForLoop(self: *PropagateValues, loop: *AST.ForLoop) anyerror!void {
        if (loop.pre.statements.items.len != 0) return error.ForLoopInitRewriterNotRun;
        var assigned = try NameCollector.assignedVariableNames(self.allocator, &loop.body);
        defer assigned.deinit(self.allocator);
        var post_assigned = try NameCollector.assignedVariableNames(self.allocator, &loop.post);
        defer post_assigned.deinit(self.allocator);
        for (0..post_assigned.len()) |index|
            _ = try assigned.insert(self.allocator, post_assigned.at(index));
        for (0..assigned.len()) |index|
            _ = self.current_variable_values.remove(assigned.at(index));

        try self.visitExpression(loop.condition orelse return error.InvalidAst);
        try self.visitBlock(&loop.body);
        try self.visitBlock(&loop.post);
    }

    fn visitBlock(self: *PropagateValues, block: *AST.Block) anyerror!void {
        const parent_clear = self.clear_at_end_of_block;
        self.clear_at_end_of_block = .{};
        defer {
            self.clear_at_end_of_block.deinit(self.allocator);
            self.clear_at_end_of_block = parent_clear;
        }

        for (block.statements.items) |*statement| try self.visitStatement(statement);
        for (0..self.clear_at_end_of_block.len()) |index|
            _ = self.current_variable_values.remove(self.clear_at_end_of_block.at(index));
    }

    fn visitStatement(self: *PropagateValues, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| try self.visitAssignment(value),
            .variable_declaration => |*value| try self.visitVariableDeclaration(value),
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
};

fn variableCopyDeclaration(
    allocator: std.mem.Allocator,
    debug_data: anytype,
    declared_name: YulName,
    value_name: YulName,
) !AST.Statement {
    var declaration: AST.VariableDeclaration = .{ .debug_data = debug_data };
    errdefer declaration.deinit(allocator);
    try declaration.variables.append(allocator, .{ .debug_data = debug_data, .name = declared_name });
    declaration.value = try AST.createExpression(allocator, .{ .identifier = .{
        .debug_data = debug_data,
        .name = value_name,
    } });
    return .{ .variable_declaration = declaration };
}

fn variableCopyAssignment(
    allocator: std.mem.Allocator,
    debug_data: anytype,
    assigned_name: YulName,
    value_name: YulName,
) !AST.Statement {
    var assignment: AST.Assignment = .{ .debug_data = debug_data };
    errdefer assignment.deinit(allocator);
    try assignment.variable_names.append(allocator, .{
        .debug_data = debug_data,
        .name = assigned_name,
    });
    assignment.value = try AST.createExpression(allocator, .{ .identifier = .{
        .debug_data = debug_data,
        .name = value_name,
    } });
    return .{ .assignment = assignment };
}

fn debugDataOfStatement(statement: *const AST.Statement) ?DebugData {
    return if (statement.debugData()) |debug_data| debug_data.* else null;
}

fn deinitStatements(allocator: std.mem.Allocator, statements: *std.ArrayList(AST.Statement)) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(allocator);
}

test "SSA transform introduces and propagates assignment values" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := 1 pop(x) x := 2 pop(x) }",
        "ssa.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = .{},
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    try SSATransform.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "let x_1 := 1") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "pop(x_1)") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "pop(x_2)") != null);
}
