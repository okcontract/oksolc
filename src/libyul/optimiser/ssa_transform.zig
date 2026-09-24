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
        const old_len = block.statements.items.len;
        var expanded_len = old_len;
        // Cache the first 64 original decisions in one word, without allocating
        // width metadata or modifying annotations. Larger indices use the set.
        var replacements: std.StaticBitSet(64) = .empty;
        for (block.statements.items, 0..) |*statement, source_index| {
            const extra = self.additionalStatements(statement, null);
            expanded_len = std.math.add(usize, expanded_len, extra) catch return error.OutOfMemory;
            if (extra != 0 and source_index < replacements.capacity()) replacements.set(source_index);
        }

        if (expanded_len != old_len) {
            try block.statements.ensureTotalCapacityPrecise(self.allocator, expanded_len);
            block.statements.items.len = expanded_len;
            var source_index = old_len;
            var destination_index = expanded_len;
            // Destinations are at or after their sources. Complete the backwards
            // move without fallible work, leaving valid empty blocks in every gap.
            while (source_index != 0) {
                source_index -= 1;
                const statement = block.statements.items[source_index];
                const extra = self.additionalStatements(&statement, if (source_index < replacements.capacity()) replacements.isSet(source_index) else null);
                block.statements.items[source_index] = .{ .block = .{} };
                destination_index -= extra + 1;
                block.statements.items[destination_index] = statement;
                @memset(block.statements.items[destination_index + 1 ..][0..extra], .{ .block = .{} });
            }
            std.debug.assert(destination_index == 0);
        }

        // Name generation and recursive visits retain their original lexical
        // order. Only complete statements replace live gaps, so OOM anywhere
        // leaves every retained owner destructible by the block allocator.
        var index: usize = 0;
        for (0..old_len) |source_index| {
            const extra = self.additionalStatements(&block.statements.items[index], if (source_index < replacements.capacity()) replacements.isSet(source_index) else null);
            const slots = block.statements.items[index..][0 .. extra + 1];
            switch (slots[0]) {
                .variable_declaration => |*declaration| if (extra != 0) {
                    for (declaration.variables.items, slots[1..]) |*variable, *destination| {
                        const new_name = try self.name_dispenser.newName(variable.name);
                        const copy = try variableCopyDeclaration(self.allocator, declaration.debug_data, variable.name, new_name);
                        destination.* = copy;
                        variable.* = .{ .debug_data = declaration.debug_data, .name = new_name };
                    }
                },
                .assignment => try self.replaceAssignment(slots),
                else => try self.visitStatement(&slots[0]),
            }
            index += slots.len;
        }
        std.debug.assert(index == expanded_len);
    }

    fn additionalStatements(self: *const IntroduceSSA, statement: *const AST.Statement, known_replacement: ?bool) usize {
        return switch (statement.*) {
            .variable_declaration => |*declaration| blk: {
                if (known_replacement) |replace| break :blk if (replace) declaration.variables.items.len else 0;
                for (declaration.variables.items) |variable|
                    if (self.variables_to_replace.contains(variable.name)) break :blk declaration.variables.items.len;
                break :blk 0;
            },
            .assignment => |*assignment| assignment.variable_names.items.len,
            else => 0,
        };
    }

    fn replaceAssignment(self: *IntroduceSSA, slots: []AST.Statement) !void {
        const assignment = &slots[0].assignment;
        for (assignment.variable_names.items) |variable|
            if (!self.variables_to_replace.contains(variable.name)) return error.InvalidAst;

        var declaration: AST.VariableDeclaration = .{
            .debug_data = assignment.debug_data,
            .variables = try .initCapacity(self.allocator, assignment.variable_names.items.len),
        };
        errdefer declaration.deinit(self.allocator);
        for (assignment.variable_names.items, slots[1..]) |variable, *destination| {
            const new_name = try self.name_dispenser.newName(variable.name);
            declaration.variables.appendAssumeCapacity(.{ .debug_data = assignment.debug_data, .name = new_name });
            const copy = try variableCopyAssignment(self.allocator, assignment.debug_data, variable.name, new_name);
            destination.* = copy;
        }
        // The expression stays with its old owner until all fallible work ends.
        // Identifier and NameWithDebugData arrays have different element types.
        declaration.value = assignment.value;
        assignment.value = null;
        assignment.variable_names.deinit(self.allocator);
        assignment.variable_names = .empty;
        slots[0] = .{ .variable_declaration = declaration };
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
            const count = self.variables_to_reassign.items.items.len;
            if (count != 0) {
                const debug_data = debugDataOfStatement(&block.statements.items[index]);
                const slots = try block.statements.addManyAt(self.allocator, index, count);
                // addManyAt checks growth and moves the suffix. Initialize every
                // gap before fallible construction so the block always owns
                // valid statements, including after a partial failure.
                @memset(slots, .{ .block = .{} });
                for (self.variables_to_reassign.items.items, slots) |variable, *destination| {
                    const new_name = try self.name_dispenser.newName(variable);
                    var declaration = try variableCopyDeclaration(
                        self.allocator,
                        debug_data,
                        new_name,
                        variable,
                    );
                    errdefer declaration.deinit(self.allocator);
                    try assigned_variables.append(self.scratch_allocator, variable);
                    destination.* = declaration;
                }
                // Skip generated declarations and reacquire the original node
                // after growth. Recursive visits retain their original order.
                index += count;
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
    var declaration: AST.VariableDeclaration = .{
        .debug_data = debug_data,
        .variables = try .initCapacity(allocator, 1),
    };
    errdefer declaration.deinit(allocator);
    declaration.variables.appendAssumeCapacity(.{ .debug_data = debug_data, .name = declared_name });
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
    var assignment: AST.Assignment = .{
        .debug_data = debug_data,
        .variable_names = try .initCapacity(allocator, 1),
    };
    errdefer assignment.deinit(allocator);
    assignment.variable_names.appendAssumeCapacity(.{
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

test "SSA transform reuses declaration storage and expression owners" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator, "{ let x, y := pair() pop(y) x := 1 pop(x) function pair() -> a, b { a := 2 b := 3 } }", "ssa-move.yul", &reporter, .{}, .{})).?;
    defer ast.deinit();
    const original = ast.root().statements.items;
    const names = original[0].variable_declaration.variables.items.ptr;
    const declaration_value = original[0].variable_declaration.value.?;
    const assignment_value = original[2].assignment.value.?;
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{ .dialect = .{}, .dispenser = &dispenser, .reserved_identifiers = &reserved };
    try SSATransform.run(&context, &ast.root_block);
    const after = ast.root().statements.items;
    try std.testing.expect(names == after[0].variable_declaration.variables.items.ptr);
    try std.testing.expect(declaration_value == after[0].variable_declaration.value.?);
    try std.testing.expect(assignment_value == after[4].variable_declaration.value.?);
    try std.testing.expectEqualStrings("x_1", try after[0].variable_declaration.variables.items[0].name.str());
    try std.testing.expectEqualStrings("y_2", try after[0].variable_declaration.variables.items[1].name.str());
    try std.testing.expectEqualStrings("x", try after[1].variable_declaration.variables.items[0].name.str());
    try std.testing.expectEqualStrings("y", try after[2].variable_declaration.variables.items[0].name.str());
}

test "SSA transform preserves first-phase tuple order and all annotations" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Converter = @import("../asm_json_converter.zig").AsmJsonConverter;
    const JSON = @import("../../libsolutil/json.zig");
    const allocator = std.testing.allocator;
    const cases = .{
        .{ "wide", "{ let x, y := pair() " ++ "x, y := pair() " ** 32 ++ "pop(x) pop(y) function pair() -> a, b { a := 1 b := 2 } }", "85a90ee29f0f905de511c249775c28c3cb4155c230dcf59fb25337bfbaf012e7" },
        .{ "nested", "{ let x, y := pair() let z let stable := 0 x, y := pair() if x { z := 1 x := 2 } switch y case 0 { y := 3 } default { x := 4 } for { let i := 0 } lt(i, 3) { i := add(i, 1) x := add(x, 1) } { y := add(y, 1) } { let nested := 0 nested := 1 } function pair() -> a, b { a := 1 b := 2 } }", "f08b6f8aa6a72f1f358494c2434523ce3631baaaecc6992783e0fd163efb28fa" },
    };
    inline for (cases) |case| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, case[1], "ssa-storage.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        const original_declaration = &ast.root_block.statements.items[0].variable_declaration;
        original_declaration.debug_data.?.ast_id = 42;
        original_declaration.variables.items[0].debug_data = null;
        const declaration_debug = original_declaration.debug_data;
        const original_expression = original_declaration.value.?;
        original_expression.function_call.debug_data.?.ast_id = 73;
        const expression_debug = original_expression.debugData().?.*;
        const original_assignment = for (ast.root().statements.items) |*statement| {
            if (statement.* == .assignment) break &statement.assignment;
        } else unreachable;
        original_assignment.debug_data.?.ast_id = 54;
        const assignment_debug = original_assignment.debug_data;
        const assignment_expression = original_assignment.value.?;
        assignment_expression.function_call.debug_data.?.ast_id = 91;
        const assignment_expression_debug = assignment_expression.debugData().?.*;
        var reserved: NameCollector.NameSet = .{};
        defer reserved.deinit(allocator);
        var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
        defer dispenser.deinit();
        var assigned = try NameCollector.assignedVariableNames(allocator, ast.root());
        defer assigned.deinit(allocator);
        var pass: IntroduceSSA = .{ .allocator = allocator, .name_dispenser = &dispenser, .variables_to_replace = &assigned };
        try pass.visitBlock(&ast.root_block);
        const retained = &ast.root().statements.items[0].variable_declaration;
        try std.testing.expect(retained.value.? == original_expression);
        try std.testing.expectEqualDeep(expression_debug, retained.value.?.debugData().?.*);
        // Exported AST JSON omits AST IDs. Check the full annotation on the
        // retained declaration, renamed variables and both generated copies.
        for (ast.root().statements.items[0..3], 0..) |*statement, index| {
            const declaration = &statement.variable_declaration;
            try std.testing.expectEqualDeep(declaration_debug, declaration.debug_data);
            for (declaration.variables.items) |variable|
                try std.testing.expectEqualDeep(declaration_debug, variable.debug_data);
            if (index != 0)
                try std.testing.expectEqualDeep(declaration_debug, declaration.value.?.identifier.debug_data);
        }
        const assignment_index = for (ast.root().statements.items, 0..) |*statement, index| {
            if (statement.* == .variable_declaration and statement.variable_declaration.value == assignment_expression) break index;
        } else return error.MissingAssignmentExpressionOwner;
        const replacement = &ast.root().statements.items[assignment_index].variable_declaration;
        try std.testing.expectEqualDeep(assignment_debug, replacement.debug_data);
        try std.testing.expectEqualDeep(assignment_expression_debug, replacement.value.?.debugData().?.*);
        for (replacement.variables.items) |variable|
            try std.testing.expectEqualDeep(assignment_debug, variable.debug_data);
        for (ast.root().statements.items[assignment_index + 1 ..][0..2]) |*statement| {
            const assignment = &statement.assignment;
            try std.testing.expectEqualDeep(assignment_debug, assignment.debug_data);
            for (assignment.variable_names.items) |variable|
                try std.testing.expectEqualDeep(assignment_debug, variable.debug_data);
            try std.testing.expectEqualDeep(assignment_debug, assignment.value.?.identifier.debug_data);
        }
        var json = try Converter.convertAlloc(allocator, &ast, 7);
        defer json.deinit();
        const bytes = try JSON.jsonCompactPrintAlloc(allocator, &json.value);
        defer allocator.free(bytes);
        var hash: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(bytes, &hash, .{});
        const encoded = std.fmt.bytesToHex(hash, .lower);
        try std.testing.expectEqualStrings(case[2], &encoded);
    }
}

test "SSA transform preserves unchanged blocks and leaves reserve failure untouched" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Encoding = @import("../ast_encoding.zig");
    const allocator = std.testing.allocator;
    const cases = .{
        .{ "{ let stable := 1 pop(stable) { let inner := 2 pop(inner) } }", false },
        .{ "{ let x := 1 x := 2 }", true },
    };
    inline for (cases) |case| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, case[0], "ssa-reserve.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        // Remove parser spare capacity before testing the first reserve failure.
        const items = try ast.root_block.statements.toOwnedSlice(allocator);
        ast.root_block.statements = .{ .items = items, .capacity = items.len };
        const hash = try Encoding.hashBlock(ast.root());
        var reserved: NameCollector.NameSet = .{};
        defer reserved.deinit(allocator);
        var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
        defer dispenser.deinit();
        var assigned = try NameCollector.assignedVariableNames(allocator, ast.root());
        defer assigned.deinit(allocator);
        var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
        var pass: IntroduceSSA = .{ .allocator = rejecting.allocator(), .name_dispenser = &dispenser, .variables_to_replace = &assigned };
        if (case[1]) {
            try std.testing.expectError(error.OutOfMemory, pass.visitBlock(&ast.root_block));
            try std.testing.expect(rejecting.has_induced_failure);
        } else {
            try pass.visitBlock(&ast.root_block);
            try std.testing.expect(!rejecting.has_induced_failure);
        }
        try std.testing.expect(items.ptr == ast.root().statements.items.ptr);
        try std.testing.expectEqual(items.len, ast.root().statements.items.len);
        try std.testing.expectEqualDeep(hash, try Encoding.hashBlock(ast.root()));
    }
}

test "SSA transform first phase retains zero-arity assignment values" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator, "{ x := 1 }", "ssa-empty.yul", &reporter, .{}, .{})).?;
    defer ast.deinit();
    const assignment = &ast.root_block.statements.items[0].assignment;
    const value = assignment.value.?;
    const debug = assignment.debug_data;
    // A synthetic private-phase boundary: zero extra slots still replaces the
    // assignment with a declaration and transfers its original expression.
    assignment.variable_names.clearRetainingCapacity();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
    defer dispenser.deinit();
    const assigned: NameCollector.NameSet = .{};
    var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
    var pass: IntroduceSSA = .{ .allocator = rejecting.allocator(), .name_dispenser = &dispenser, .variables_to_replace = &assigned };
    try pass.visitBlock(&ast.root_block);
    try std.testing.expect(!rejecting.has_induced_failure);
    try std.testing.expectEqual(@as(usize, 1), ast.root().statements.items.len);
    const declaration = &ast.root().statements.items[0].variable_declaration;
    try std.testing.expect(declaration.value.? == value);
    try std.testing.expectEqual(@as(usize, 0), declaration.variables.items.len);
    try std.testing.expectEqualDeep(debug, declaration.debug_data);
}

test "SSA transform preserves original statement decisions across cache boundaries" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Converter = @import("../asm_json_converter.zig").AsmJsonConverter;
    const JSON = @import("../../libsolutil/json.zig");
    const Encoding = @import("../ast_encoding.zig");
    const cases = .{
        .{ 63, "4cce5ff729f4d0e2d0efefaa2b701aca9be18c99531ba3fd3aed68dd61eefdf5", "7e68529b470c6ffb27030d0f942464185199af3ce9d3388f3ae568e57c9605f0" },
        .{ 64, "7697affeecb3c8f9bc0f82df9ad3e7866aacc3b501e2470a799db2705309d0a7", "036149a21f22d8d946d5f717747c2b15bc025521fc684be0097145ea2f8aba4d" },
        .{ 65, "db4ac6008821d2a916c349d173cf4544c51ed54da991b1c1d2116352c4202faf", "ef19dee1eaadd5f829e94d9087a520c4938b7a94ddba3fabdb951995a872d396" },
        .{ 66, "77bc1ea40c15791862647bf42d84a42907deb6cd3588f2e13f1a2e86aa3a0bb6", "287f2fa7b61749eface141491c0fdfa3f1f3cfe59b3c449596d2b2fe41563229" },
        .{ 130, "0ba03a69727803206aab7d1dbfefe0443a58072157ae990325315b7dd1cb170d", "39c11e8505f899c1e598008735734aaefe0656195ab587840ca171f67b40d2d5" },
    };
    inline for (cases) |case| {
        var source = std.Io.Writer.Allocating.init(std.testing.allocator);
        defer source.deinit();
        try source.writer.writeAll("{ ");
        for (0..case[0]) |index| {
            if (index == 63) {
                try source.writer.writeAll("let v_63, stable_63 := pair() ");
            } else {
                try source.writer.print("let v_{d} := {d} ", .{ index, index });
            }
        }
        for (0..case[0]) |index| {
            if (index % 3 != 1) try source.writer.print("v_{d} := {d} ", .{ index, index + 1000 });
        }
        try source.writer.writeAll("{ let nested := 0 nested := 1 } function pair() -> first, second { first := 1 second := 2 } }");
        const allocator = std.testing.allocator;
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, source.writer.buffered(), "ssa-width.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        // Canonical encoding covers AST IDs; exported JSON separately covers
        // native positions. Include distinct IDs around the cached boundary.
        for (ast.root_block.statements.items[0..case[0]], 0..) |*statement, index| {
            statement.variable_declaration.debug_data.?.ast_id = @intCast(index + 50);
            if (index % 2 == 0) statement.variable_declaration.variables.items[0].debug_data = null;
        }
        var reserved: NameCollector.NameSet = .{};
        defer reserved.deinit(allocator);
        var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
        defer dispenser.deinit();
        var assigned = try NameCollector.assignedVariableNames(allocator, ast.root());
        defer assigned.deinit(allocator);
        var pass: IntroduceSSA = .{ .allocator = allocator, .name_dispenser = &dispenser, .variables_to_replace = &assigned };
        try pass.visitBlock(&ast.root_block);
        var json = try Converter.convertAlloc(allocator, &ast, 7);
        defer json.deinit();
        const bytes = try JSON.jsonCompactPrintAlloc(allocator, &json.value);
        defer allocator.free(bytes);
        var json_hash: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(bytes, &json_hash, .{});
        const encoded = std.fmt.bytesToHex(json_hash, .lower);
        const canonical = (try Encoding.hashBlock(ast.root())).hex();
        try std.testing.expectEqualStrings(case[1], &encoded);
        try std.testing.expectEqualStrings(case[2], &canonical);
    }
}

test "SSA transform preserves control-flow order and complete annotations" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Converter = @import("../asm_json_converter.zig").AsmJsonConverter;
    const Encoding = @import("../ast_encoding.zig");
    const JSON = @import("../../libsolutil/json.zig");
    const allocator = std.testing.allocator;
    const source =
        \\{ let x := 1 let y := 2
        \\  if x { y := 3 { x := 4 } }
        \\  switch y case 0 { x := 5 } default { y := 6 }
        \\  for {} lt(x, 10) { x := add(x, 1) } {
        \\    if y { y := add(y, 1) continue } break
        \\  }
        \\  pop(f(x, y))
        \\  function f(a, b) -> r {
        \\    a := add(a, b)
        \\    switch b case 0 { b := a } default { a := b }
        \\    { if a { b := 2 } a := add(a, b) }
        \\    r := a
        \\  }
        \\}
    ;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator, source, "control-ssa.yul", &reporter, .{}, .{})).?;
    defer ast.deinit();
    const original_expression = ast.root().statements.items[0].variable_declaration.value.?;
    const statements = ast.root_block.statements.items;
    statements[2].if_statement.debug_data.?.ast_id = 113;
    statements[2].if_statement.body.statements.items[0].assignment.debug_data.?.ast_id = 199;
    statements[3].switch_statement.debug_data = null;
    statements[4].for_loop.debug_data.?.ast_id = 217;
    statements[4].for_loop.post.statements.items[0].assignment.debug_data.?.ast_id = 233;
    statements[6].function_definition.debug_data.?.ast_id = 313;
    statements[6].function_definition.parameters.items[0].debug_data = null;
    statements[6].function_definition.body.statements.items[0].assignment.debug_data.?.ast_id = 337;
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
    defer dispenser.deinit();
    var assigned = try NameCollector.assignedVariableNames(allocator, ast.root());
    defer assigned.deinit(allocator);
    var first: IntroduceSSA = .{ .allocator = allocator, .name_dispenser = &dispenser, .variables_to_replace = &assigned };
    try first.visitBlock(&ast.root_block);
    var control: IntroduceControlFlowSSA = .{ .allocator = allocator, .scratch_allocator = allocator, .name_dispenser = &dispenser, .variables_to_replace = &assigned };
    defer control.deinit();
    try control.visitBlock(&ast.root_block);
    try std.testing.expect(original_expression == ast.root().statements.items[0].variable_declaration.value.?);
    var json = try Converter.convertAlloc(allocator, &ast, 7);
    defer json.deinit();
    const bytes = try JSON.jsonCompactPrintAlloc(allocator, &json.value);
    defer allocator.free(bytes);
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &digest, .{});
    const encoded = std.fmt.bytesToHex(digest, .lower);
    const canonical = (try Encoding.hashBlock(ast.root())).hex();
    try std.testing.expectEqualStrings("34bce9bdaf02bfd87e614a23467c8fbc3db93c4a8917d63a67a239df21a7fe92", &encoded);
    try std.testing.expectEqualStrings("ddd350892ff8981b7cc2bb2aa18e80e55378a97afa060edc0eec394be8a1b16f", &canonical);
}

test "SSA transform control-flow insertion skips empty work and preserves reserve failures" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Encoding = @import("../ast_encoding.zig");
    const allocator = std.testing.allocator;
    const cases = .{ .{ "{ pop(0) { pop(1) } }", false }, .{ "{ pop(x) }", true } };
    inline for (cases) |case| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, case[0], "control-reserve.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        const items = try ast.root_block.statements.toOwnedSlice(allocator);
        ast.root_block.statements = .{ .items = items, .capacity = items.len };
        const hash = try Encoding.hashBlock(ast.root());
        var reserved: NameCollector.NameSet = .{};
        defer reserved.deinit(allocator);
        var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
        defer dispenser.deinit();
        var assigned: NameCollector.NameSet = .{};
        defer assigned.deinit(allocator);
        var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
        var pass: IntroduceControlFlowSSA = .{
            .allocator = rejecting.allocator(),
            .scratch_allocator = if (case[1]) allocator else rejecting.allocator(),
            .name_dispenser = &dispenser,
            .variables_to_replace = &assigned,
        };
        defer pass.deinit();
        if (case[1]) {
            // A pending function parameter exists in the surrounding scope.
            const name = try YulName.init("x");
            _ = try assigned.insert(allocator, name);
            _ = try pass.variables_in_scope.insert(allocator, name);
            try pass.variables_to_reassign.append(allocator, name);
            try std.testing.expectError(error.OutOfMemory, pass.visitBlock(&ast.root_block));
        } else {
            try pass.visitBlock(&ast.root_block);
            try std.testing.expect(!rejecting.has_induced_failure);
        }
        try std.testing.expect(items.ptr == ast.root().statements.items.ptr);
        try std.testing.expectEqual(items.len, ast.root().statements.items.len);
        try std.testing.expectEqualDeep(hash, try Encoding.hashBlock(ast.root()));
    }
}
