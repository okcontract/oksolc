// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structured Solidity CFG construction translated from `ControlFlowBuilder.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Types = @import("../ast/types.zig");
const Graph = @import("control_flow_graph.zig");
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;
const YulAST = @import("../../libyul/ast.zig");

pub const BuildError = std.mem.Allocator.Error || error{InvalidAst};
const max_ast_depth = 4096;

pub fn createFunctionFlow(
    node_container: *Graph.NodeContainer,
    function: *const AST.Node,
    contract: ?*const AST.Node,
) BuildError!Graph.FunctionFlow {
    if (function.nodeKind() != .function_definition or
        !function.payload.function_definition.implemented())
        return error.InvalidAst;
    const flow: Graph.FunctionFlow = .{
        .entry = try node_container.newNode(),
        .exit = try node_container.newNode(),
        .revert = try node_container.newNode(),
        .transaction_return = try node_container.newNode(),
    };
    var builder = ControlFlowBuilder.init(node_container, flow, contract);
    try builder.appendFunction(function);
    return flow;
}

pub const ControlFlowBuilder = struct {
    node_container: *Graph.NodeContainer,
    current_node: ?*Graph.CFGNode,
    return_node: *Graph.CFGNode,
    revert_node: *Graph.CFGNode,
    transaction_return_node: *Graph.CFGNode,
    contract: ?*const AST.Node,
    break_jump: ?*Graph.CFGNode = null,
    continue_jump: ?*Graph.CFGNode = null,
    placeholder_entry: ?*Graph.CFGNode = null,
    placeholder_exit: ?*Graph.CFGNode = null,

    fn init(
        node_container: *Graph.NodeContainer,
        flow: Graph.FunctionFlow,
        contract: ?*const AST.Node,
    ) ControlFlowBuilder {
        return .{
            .node_container = node_container,
            .current_node = flow.entry,
            .return_node = flow.exit,
            .revert_node = flow.revert,
            .transaction_return_node = flow.transaction_return,
            .contract = contract,
        };
    }

    fn appendFunction(self: *ControlFlowBuilder, node: *const AST.Node) BuildError!void {
        const function = node.payload.function_definition;
        try self.appendParameterList(function.callable.parameters, true, false);
        if (function.callable.return_parameters) |parameters| {
            try self.appendParameterList(parameters, false, true);
            for (parameters.payload.parameter_list.parameters) |parameter|
                try self.return_node.variable_occurrences.append(
                    self.node_container.allocator,
                    .{ .declaration = parameter, .kind = .Return },
                );
        }
        for (function.modifiers) |modifier| try self.appendModifierInvocation(modifier);
        try self.append(function.body.?, 0);
        try self.connectCurrent(self.return_node);
        self.current_node = null;
    }

    fn appendParameterList(
        self: *ControlFlowBuilder,
        node: *const AST.Node,
        assigned: bool,
        is_return: bool,
    ) BuildError!void {
        if (node.nodeKind() != .parameter_list) return error.InvalidAst;
        for (node.payload.parameter_list.parameters) |parameter|
            try self.appendVariableDeclaration(parameter, assigned, is_return, 0);
    }

    fn append(
        self: *ControlFlowBuilder,
        node: *const AST.Node,
        depth: usize,
    ) BuildError!void {
        if (depth >= max_ast_depth or self.current_node == null)
            return error.InvalidAst;
        switch (node.payload) {
            .function_type_name => try self.cover(node.location),
            .block => |value| {
                try self.cover(node.location);
                for (value.statements) |statement| try self.append(statement, depth + 1);
            },
            .if_statement => try self.appendIf(node, depth),
            .try_statement => try self.appendTry(node, depth),
            .while_statement => try self.appendWhile(node, depth),
            .for_statement => try self.appendFor(node, depth),
            .continue_statement => try self.appendJump(node, self.continue_jump),
            .break_statement => try self.appendJump(node, self.break_jump),
            .throw_statement => try self.appendTerminal(node, self.revert_node),
            .revert_statement => try self.appendTerminal(node, self.revert_node),
            .return_statement => try self.appendReturn(node, depth),
            .placeholder_statement => try self.appendPlaceholder(),
            .variable_declaration => try self.appendVariableDeclaration(node, false, false, depth),
            .variable_declaration_statement => try self.appendVariableStatement(node, depth),
            .conditional => try self.appendConditional(node, depth),
            .binary_operation => try self.appendBinary(node, depth),
            .unary_operation => try self.appendUnary(node, depth),
            .function_call => try self.appendFunctionCall(node, depth),
            .modifier_invocation => try self.appendModifierInvocation(node),
            .inline_assembly => try self.appendInlineAssembly(node),
            .identifier => try self.appendIdentifier(node),
            .expression_statement => |value| {
                try self.cover(node.location);
                try self.append(value.expression, depth + 1);
            },
            .emit_statement => |value| {
                try self.cover(node.location);
                try self.append(value.event_call, depth + 1);
            },
            .assignment => |value| {
                try self.cover(node.location);
                try self.append(value.left_hand_side, depth + 1);
                try self.append(value.right_hand_side, depth + 1);
            },
            .tuple_expression => |value| {
                try self.cover(node.location);
                for (value.components) |component|
                    if (component) |child| try self.append(child, depth + 1);
            },
            .function_call_options => |value| {
                try self.cover(node.location);
                try self.append(value.expression, depth + 1);
                for (value.options) |child| try self.append(child, depth + 1);
            },
            .member_access => |value| {
                try self.cover(node.location);
                try self.append(value.expression, depth + 1);
            },
            .index_access => |value| {
                try self.cover(node.location);
                try self.append(value.base, depth + 1);
                if (value.index) |child| try self.append(child, depth + 1);
            },
            .index_range_access => |value| {
                try self.cover(node.location);
                try self.append(value.base, depth + 1);
                if (value.start) |child| try self.append(child, depth + 1);
                if (value.end) |child| try self.append(child, depth + 1);
            },
            .new_expression => |value| {
                try self.cover(node.location);
                try self.append(value.type_name, depth + 1);
            },
            .elementary_type_name_expression => |value| {
                try self.cover(node.location);
                // Upstream deliberately treats this expression as a visitor
                // leaf even though the parsed node retains its type name.
                _ = value;
            },
            else => try self.cover(node.location),
        }
    }

    fn appendIf(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        const value = node.payload.if_statement;
        try self.cover(node.location);
        try self.append(value.condition, depth + 1);
        var branches = try self.split(2);
        branches[0] = try self.createFlow(branches[0], value.true_body, depth + 1);
        if (value.false_body) |false_body| {
            branches[1] = try self.createFlow(branches[1], false_body, depth + 1);
            try self.merge(branches, null);
        } else try self.merge(branches, branches[1]);
    }

    fn appendTry(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        const value = node.payload.try_statement;
        try self.append(value.external_call, depth + 1);
        if (value.clauses.len == 0) return error.InvalidAst;
        var branches = try self.split(value.clauses.len);
        for (value.clauses, 0..) |clause_node, index| {
            if (clause_node.nodeKind() != .try_catch_clause) return error.InvalidAst;
            branches[index] = try self.createFlow(
                branches[index],
                clause_node.payload.try_catch_clause.block,
                depth + 1,
            );
        }
        try self.merge(branches, null);
    }

    fn appendWhile(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        const value = node.payload.while_statement;
        try self.cover(node.location);
        if (value.is_do_while) {
            const after_while = try self.newLabel();
            const while_body = try self.createLabelHere();
            const condition = try self.newLabel();
            const old_break = self.break_jump;
            const old_continue = self.continue_jump;
            self.break_jump = after_while;
            self.continue_jump = condition;
            try self.append(value.body, depth + 1);
            self.break_jump = old_break;
            self.continue_jump = old_continue;
            try self.placeAndConnect(condition);
            try self.append(value.condition, depth + 1);
            try connect(self.node_container.allocator, self.current_node.?, while_body);
            try self.placeAndConnect(after_while);
        } else {
            const while_condition = try self.createLabelHere();
            try self.append(value.condition, depth + 1);
            const branches = try self.split(2);
            defer self.node_container.allocator.free(branches);
            const while_body = branches[0];
            const after_while = branches[1];
            self.current_node = while_body;
            const old_break = self.break_jump;
            const old_continue = self.continue_jump;
            self.break_jump = after_while;
            self.continue_jump = while_condition;
            try self.append(value.body, depth + 1);
            self.break_jump = old_break;
            self.continue_jump = old_continue;
            try connect(self.node_container.allocator, self.current_node.?, while_condition);
            self.current_node = after_while;
        }
    }

    fn appendFor(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        const value = node.payload.for_statement;
        try self.cover(node.location);
        if (value.initialization_expression) |initialization|
            try self.append(initialization, depth + 1);
        const condition = try self.createLabelHere();
        if (value.condition) |condition_expression|
            try self.append(condition_expression, depth + 1);
        const post_part = try self.newLabel();
        const branches = try self.split(2);
        defer self.node_container.allocator.free(branches);
        const after_for = branches[1];
        self.current_node = branches[0];
        const old_break = self.break_jump;
        const old_continue = self.continue_jump;
        self.break_jump = after_for;
        self.continue_jump = post_part;
        try self.append(value.body, depth + 1);
        self.break_jump = old_break;
        self.continue_jump = old_continue;
        try self.placeAndConnect(post_part);
        if (value.loop_expression) |expression| try self.append(expression, depth + 1);
        try connect(self.node_container.allocator, self.current_node.?, condition);
        self.current_node = after_for;
    }

    fn appendConditional(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        const value = node.payload.conditional;
        try self.cover(node.location);
        try self.append(value.condition, depth + 1);
        var branches = try self.split(2);
        branches[0] = try self.createFlow(branches[0], value.true_expression, depth + 1);
        branches[1] = try self.createFlow(branches[1], value.false_expression, depth + 1);
        try self.merge(branches, null);
    }

    fn appendBinary(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        const value = node.payload.binary_operation;
        const user_function = try operationFunction(node);
        if ((value.operator == .Or or value.operator == .And) and user_function == null) {
            try self.cover(node.location);
            try self.append(value.left, depth + 1);
            var branches = try self.split(2);
            branches[0] = try self.createFlow(branches[0], value.right, depth + 1);
            try self.merge(branches, branches[1]);
            return;
        }
        try self.cover(node.location);
        try self.append(value.left, depth + 1);
        try self.append(value.right, depth + 1);
        if (user_function) |function| try self.appendCallNode(function);
    }

    fn appendUnary(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        try self.cover(node.location);
        try self.append(node.payload.unary_operation.sub_expression, depth + 1);
        if (try operationFunction(node)) |function| try self.appendCallNode(function);
    }

    fn appendFunctionCall(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        const value = node.payload.function_call;
        const function_type = (try expressionType(value.expression)).asFunction() orelse {
            try self.cover(node.location);
            try self.append(value.expression, depth + 1);
            for (value.arguments) |argument| try self.append(argument, depth + 1);
            return;
        };
        try self.cover(node.location);
        try self.append(value.expression, depth + 1);
        for (value.arguments) |argument| try self.append(argument, depth + 1);
        switch (function_type.kind) {
            .Revert => {
                try self.connectCurrent(self.revert_node);
                self.current_node = try self.newLabel();
            },
            .Require, .Assert => {
                try self.connectCurrent(self.revert_node);
                const next = try self.newLabel();
                try self.connectCurrent(next);
                self.current_node = next;
            },
            .Internal => if (try resolveInternalFunctionCall(
                value.expression,
                function_type.declaration,
                self.contract,
            )) |function| try self.appendCallNode(function),
            else => {},
        }
    }

    fn appendCallNode(self: *ControlFlowBuilder, function: *const AST.Node) BuildError!void {
        self.current_node.?.function_definition = function;
        const next = try self.newLabel();
        try self.connectCurrent(next);
        self.current_node = next;
    }

    fn appendReturn(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        try self.cover(node.location);
        if (node.payload.return_statement.expression) |expression| {
            try self.append(expression, depth + 1);
            const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
            const parameters_node = switch (annotation.*) {
                .return_statement => |value| value.function_return_parameters,
                else => return error.InvalidAst,
            } orelse return error.InvalidAst;
            for (parameters_node.payload.parameter_list.parameters) |parameter|
                try self.current_node.?.variable_occurrences.append(
                    self.node_container.allocator,
                    .{ .declaration = parameter, .kind = .Assignment, .occurrence = node.location },
                );
        }
        try self.connectCurrent(self.return_node);
        self.current_node = try self.newLabel();
    }

    fn appendVariableStatement(self: *ControlFlowBuilder, node: *const AST.Node, depth: usize) BuildError!void {
        const value = node.payload.variable_declaration_statement;
        try self.cover(node.location);
        for (value.declarations) |declaration|
            if (declaration) |variable|
                try self.appendVariableDeclaration(variable, false, false, depth + 1);
        if (value.initial_value) |initial| {
            try self.append(initial, depth + 1);
            for (value.declarations, 0..) |declaration, index|
                if (declaration) |variable|
                    try self.current_node.?.variable_occurrences.append(
                        self.node_container.allocator,
                        .{
                            .declaration = variable,
                            .kind = .Assignment,
                            .occurrence = try variableAssignmentLocation(initial, index),
                        },
                    );
        }
    }

    fn appendVariableDeclaration(
        self: *ControlFlowBuilder,
        node: *const AST.Node,
        externally_assigned: bool,
        _: bool,
        depth: usize,
    ) BuildError!void {
        if (node.nodeKind() != .variable_declaration) return error.InvalidAst;
        try self.cover(node.location);
        try self.current_node.?.variable_occurrences.append(
            self.node_container.allocator,
            .{ .declaration = node, .kind = .Declaration },
        );
        const value = node.payload.variable_declaration.value;
        if (value != null or externally_assigned)
            try self.current_node.?.variable_occurrences.append(
                self.node_container.allocator,
                .{
                    .declaration = node,
                    .kind = .Assignment,
                    .occurrence = if (value) |expression| expression.location else null,
                },
            );
        if (value) |expression| try self.append(expression, depth + 1);
    }

    fn appendIdentifier(self: *ControlFlowBuilder, node: *const AST.Node) BuildError!void {
        try self.cover(node.location);
        const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
        const identifier = switch (annotation.*) {
            .identifier => |value| value,
            else => return error.InvalidAst,
        };
        const declaration = identifier.referenced_declaration orelse return;
        if (declaration.nodeKind() != .variable_declaration) return;
        try self.current_node.?.variable_occurrences.append(
            self.node_container.allocator,
            .{
                .declaration = declaration,
                .kind = if (identifier.expression.will_be_written_to) .Assignment else .Access,
                .occurrence = node.location,
            },
        );
    }

    fn appendInlineAssembly(self: *ControlFlowBuilder, node: *const AST.Node) BuildError!void {
        const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
        const assembly_annotation = switch (annotation.*) {
            .inline_assembly => |*value| value,
            else => return error.InvalidAst,
        };
        const operations = node.payload.inline_assembly.operations orelse
            return error.InvalidAst;
        try self.appendYulBlock(
            operations.root(),
            operations.dialect().*,
            assembly_annotation,
            0,
        );
    }

    fn appendModifierInvocation(self: *ControlFlowBuilder, node: *const AST.Node) BuildError!void {
        if (node.nodeKind() != .modifier_invocation or self.contract == null)
            return error.InvalidAst;
        const value = node.payload.modifier_invocation;
        if (value.arguments) |arguments|
            for (arguments) |argument| try self.append(argument, 0);
        const referenced = try referencedDeclaration(value.modifier_name) orelse return;
        if (referenced.nodeKind() != .modifier_definition) return;
        const definition = switch (try requiredLookup(value.modifier_name)) {
            .Static => referenced,
            .Virtual => ASTImplementation.resolveModifierVirtual(
                referenced,
                self.contract.?,
                null,
            ) catch return error.InvalidAst,
            .Super => return error.InvalidAst,
        };
        if (!definition.payload.modifier_definition.implemented()) return;
        self.placeholder_entry = try self.newLabel();
        self.placeholder_exit = try self.newLabel();
        try self.appendModifierDefinition(definition);
        try self.connectCurrent(self.return_node);
        self.current_node = self.placeholder_entry;
        self.return_node = self.placeholder_exit.?;
        self.placeholder_entry = null;
        self.placeholder_exit = null;
    }

    fn appendModifierDefinition(self: *ControlFlowBuilder, node: *const AST.Node) BuildError!void {
        const modifier = node.payload.modifier_definition;
        try self.appendParameterList(modifier.callable.parameters, true, false);
        try self.append(modifier.body.?, 0);
    }

    fn appendPlaceholder(self: *ControlFlowBuilder) BuildError!void {
        const entry = self.placeholder_entry orelse return error.InvalidAst;
        const exit = self.placeholder_exit orelse return error.InvalidAst;
        try self.connectCurrent(entry);
        self.current_node = try self.newLabel();
        try connect(self.node_container.allocator, exit, self.current_node.?);
    }

    fn appendYulBlock(
        self: *ControlFlowBuilder,
        block: *const YulAST.Block,
        dialect: YulAST.Dialect,
        assembly: *const ASTAnnotations.InlineAssemblyAnnotation,
        depth: usize,
    ) BuildError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        for (block.statements.items) |*statement|
            try self.appendYulStatement(statement, dialect, assembly, depth + 1);
    }

    fn appendYulStatement(
        self: *ControlFlowBuilder,
        statement: *const YulAST.Statement,
        dialect: YulAST.Dialect,
        assembly: *const ASTAnnotations.InlineAssemblyAnnotation,
        depth: usize,
    ) BuildError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        const native_location = YulAST.nativeLocationOfStatement(statement);
        if (!native_location.eql(YulAST.originLocationOfStatement(statement)))
            return error.InvalidAst;
        try self.cover(native_location);
        switch (statement.*) {
            .expression_statement => |*value| try self.appendYulExpression(
                &value.expression,
                dialect,
                assembly,
                depth + 1,
            ),
            .assignment => |*value| {
                if (value.value) |expression|
                    try self.appendYulExpression(expression, dialect, assembly, depth + 1);
                for (value.variable_names.items) |*identifier|
                    try self.appendYulExternalReference(identifier, assembly, .Assignment);
            },
            .variable_declaration => |*value| if (value.value) |expression|
                try self.appendYulExpression(expression, dialect, assembly, depth + 1),
            .function_definition => {},
            .if_statement => |*value| {
                if (value.condition) |condition|
                    try self.appendYulExpression(condition, dialect, assembly, depth + 1);
                var branches = try self.split(2);
                errdefer self.node_container.allocator.free(branches);
                self.current_node = branches[0];
                try self.appendYulBlock(&value.body, dialect, assembly, depth + 1);
                branches[0] = self.current_node orelse return error.InvalidAst;
                try self.merge(branches, branches[1]);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression|
                    try self.appendYulExpression(expression, dialect, assembly, depth + 1);
                const before_switch = self.current_node orelse return error.InvalidAst;
                var branches = try self.split(value.cases.items.len);
                errdefer self.node_container.allocator.free(branches);
                for (value.cases.items, 0..) |*case_value, index| {
                    self.current_node = branches[index];
                    try self.appendYulBlock(&case_value.body, dialect, assembly, depth + 1);
                    branches[index] = self.current_node orelse return error.InvalidAst;
                }
                try self.merge(branches, null);
                if (!YulAST.hasDefaultCase(value))
                    try connect(
                        self.node_container.allocator,
                        before_switch,
                        self.current_node orelse return error.InvalidAst,
                    );
            },
            .for_loop => |*value| {
                try self.appendYulBlock(&value.pre, dialect, assembly, depth + 1);
                const condition = try self.createLabelHere();
                if (value.condition) |condition_expression|
                    try self.appendYulExpression(
                        condition_expression,
                        dialect,
                        assembly,
                        depth + 1,
                    );
                const post = try self.newLabel();
                const branches = try self.split(2);
                defer self.node_container.allocator.free(branches);
                const after_for = branches[1];
                self.current_node = branches[0];
                const old_break = self.break_jump;
                const old_continue = self.continue_jump;
                self.break_jump = after_for;
                self.continue_jump = post;
                try self.appendYulBlock(&value.body, dialect, assembly, depth + 1);
                self.break_jump = old_break;
                self.continue_jump = old_continue;
                try self.placeAndConnect(post);
                try self.appendYulBlock(&value.post, dialect, assembly, depth + 1);
                try connect(
                    self.node_container.allocator,
                    self.current_node orelse return error.InvalidAst,
                    condition,
                );
                self.current_node = after_for;
            },
            .break_statement => {
                try self.connectCurrent(self.break_jump orelse return error.InvalidAst);
                self.current_node = try self.newLabel();
            },
            .continue_statement => {
                try self.connectCurrent(self.continue_jump orelse return error.InvalidAst);
                self.current_node = try self.newLabel();
            },
            .leave_statement => return error.InvalidAst,
            .block => |*value| try self.appendYulBlock(value, dialect, assembly, depth + 1),
        }
    }

    fn appendYulExpression(
        self: *ControlFlowBuilder,
        expression: *const YulAST.Expression,
        dialect: YulAST.Dialect,
        assembly: *const ASTAnnotations.InlineAssemblyAnnotation,
        depth: usize,
    ) BuildError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        switch (expression.*) {
            .literal => {},
            .identifier => |*identifier| try self.appendYulExternalReference(
                identifier,
                assembly,
                .Access,
            ),
            .function_call => |*call| {
                // ASTWalker evaluates Yul call arguments in reverse order.
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.appendYulExpression(
                        &call.arguments.items[index],
                        dialect,
                        assembly,
                        depth + 1,
                    );
                }
                const builtin = switch (call.function_name) {
                    .identifier => null,
                    .builtin => |name| dialect.builtin(name.handle) catch
                        return error.InvalidAst,
                };
                if (builtin) |function| {
                    const effects = function.control_flow_side_effects;
                    const current = self.current_node orelse return error.InvalidAst;
                    if (effects.can_terminate)
                        try connect(
                            self.node_container.allocator,
                            current,
                            self.transaction_return_node,
                        );
                    if (effects.can_revert)
                        try connect(self.node_container.allocator, current, self.revert_node);
                    if (!effects.can_continue) self.current_node = try self.newLabel();
                }
            },
        }
    }

    fn appendYulExternalReference(
        self: *ControlFlowBuilder,
        identifier: *const YulAST.Identifier,
        assembly: *const ASTAnnotations.InlineAssemblyAnnotation,
        kind: Graph.VariableOccurrence.Kind,
    ) BuildError!void {
        const reference = yulExternalReference(assembly, identifier) orelse return;
        const declaration = reference.info.declaration orelse return;
        if (declaration.nodeKind() != .variable_declaration) return;
        const location = try yulIdentifierLocation(identifier);
        const current = self.current_node orelse return error.InvalidAst;
        try current.variable_occurrences.append(
            self.node_container.allocator,
            .{ .declaration = declaration, .kind = kind, .occurrence = location },
        );
    }

    fn appendJump(
        self: *ControlFlowBuilder,
        node: *const AST.Node,
        destination: ?*Graph.CFGNode,
    ) BuildError!void {
        try self.cover(node.location);
        try self.connectCurrent(destination orelse return error.InvalidAst);
        self.current_node = try self.newLabel();
    }

    fn appendTerminal(
        self: *ControlFlowBuilder,
        node: *const AST.Node,
        destination: *Graph.CFGNode,
    ) BuildError!void {
        try self.cover(node.location);
        try self.connectCurrent(destination);
        self.current_node = try self.newLabel();
    }

    fn split(self: *ControlFlowBuilder, count: usize) BuildError![]*Graph.CFGNode {
        const source = self.current_node orelse return error.InvalidAst;
        const nodes = try self.node_container.allocator.alloc(*Graph.CFGNode, count);
        errdefer self.node_container.allocator.free(nodes);
        for (nodes) |*node| {
            node.* = try self.newLabel();
            try connect(self.node_container.allocator, source, node.*);
        }
        self.current_node = null;
        return nodes;
    }

    fn merge(
        self: *ControlFlowBuilder,
        nodes: []const *Graph.CFGNode,
        end_node: ?*Graph.CFGNode,
    ) BuildError!void {
        const destination = end_node orelse try self.newLabel();
        for (nodes) |node| if (node != destination)
            try connect(self.node_container.allocator, node, destination);
        self.current_node = destination;
        self.node_container.allocator.free(@constCast(nodes));
    }

    fn createFlow(
        self: *ControlFlowBuilder,
        entry: *Graph.CFGNode,
        node: *const AST.Node,
        depth: usize,
    ) BuildError!*Graph.CFGNode {
        const old_current = self.current_node;
        self.current_node = entry;
        try self.append(node, depth);
        const result = self.current_node orelse return error.InvalidAst;
        self.current_node = old_current;
        return result;
    }

    fn cover(self: *ControlFlowBuilder, location: @import("../../liblangutil/source_location.zig").SourceLocation) BuildError!void {
        const node = self.current_node orelse return error.InvalidAst;
        node.location = @TypeOf(location).smallestCovering(node.location, location);
    }

    fn newLabel(self: *ControlFlowBuilder) std.mem.Allocator.Error!*Graph.CFGNode {
        return self.node_container.newNode();
    }

    fn createLabelHere(self: *ControlFlowBuilder) BuildError!*Graph.CFGNode {
        const label = try self.newLabel();
        try self.connectCurrent(label);
        self.current_node = label;
        return label;
    }

    fn placeAndConnect(self: *ControlFlowBuilder, label: *Graph.CFGNode) BuildError!void {
        try self.connectCurrent(label);
        self.current_node = label;
    }

    fn connectCurrent(self: *ControlFlowBuilder, to: *Graph.CFGNode) BuildError!void {
        try connect(
            self.node_container.allocator,
            self.current_node orelse return error.InvalidAst,
            to,
        );
    }
};

fn connect(
    allocator: std.mem.Allocator,
    from: *Graph.CFGNode,
    to: *Graph.CFGNode,
) std.mem.Allocator.Error!void {
    try from.exits.append(allocator, to);
    errdefer _ = from.exits.pop();
    try to.entries.append(allocator, from);
}

fn expressionType(node: *const AST.Node) BuildError!*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    const expression = switch (annotation.*) {
        .expression => |*value| value,
        .identifier => |*value| &value.expression,
        .member_access => |*value| &value.expression,
        .operation => |*value| &value.expression,
        .binary_operation => |*value| &value.operation.expression,
        .function_call => |*value| &value.expression,
        else => return error.InvalidAst,
    };
    return expression.type_ref orelse error.InvalidAst;
}

fn operationFunction(node: *const AST.Node) BuildError!?*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    const field = switch (annotation.*) {
        .operation => |*value| &value.user_defined_function,
        .binary_operation => |*value| &value.operation.user_defined_function,
        else => return error.InvalidAst,
    };
    return (field.get() catch return error.InvalidAst).*;
}

fn referencedDeclaration(node: *const AST.Node) BuildError!?*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier => |value| value.referenced_declaration,
        .identifier_path => |value| value.referenced_declaration,
        .member_access => |value| value.referenced_declaration,
        else => error.InvalidAst,
    };
}

fn requiredLookup(node: *const AST.Node) BuildError!AST.VirtualLookup {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    const lookup = switch (annotation.*) {
        .identifier => |value| value.required_lookup.value,
        .identifier_path => |value| value.required_lookup.value,
        .member_access => |value| value.required_lookup.value,
        else => return error.InvalidAst,
    };
    return lookup orelse error.InvalidAst;
}

fn resolveInternalFunctionCall(
    expression: *const AST.Node,
    declaration: ?*const AST.Node,
    most_derived_contract: ?*const AST.Node,
) BuildError!?*const AST.Node {
    const function = declaration orelse return null;
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    return switch (expression.payload) {
        .identifier => switch (try requiredLookup(expression)) {
            .Virtual => if (!ASTImplementation.functionVirtualSemantics(function))
                function
            else
                try resolveVirtualFunction(
                    function,
                    most_derived_contract orelse return error.InvalidAst,
                    null,
                ),
            .Static, .Super => error.InvalidAst,
        },
        .member_access => |member| switch (try requiredLookup(expression)) {
            .Static => function,
            .Super => blk: {
                const owner_type = try expressionType(member.expression);
                const type_type = owner_type.asTypeType() orelse return error.InvalidAst;
                const contract_type = switch (type_type.actual_type.payload) {
                    .Contract => |value| value,
                    else => return error.InvalidAst,
                };
                if (!contract_type.is_super) return error.InvalidAst;
                const derived = most_derived_contract orelse return error.InvalidAst;
                const search_start = (ASTImplementation.superContract(
                    contract_type.declaration,
                    derived,
                ) catch return error.InvalidAst) orelse return error.InvalidAst;
                break :blk try resolveVirtualFunction(function, derived, search_start);
            },
            .Virtual => error.InvalidAst,
        },
        else => function,
    };
}

fn resolveVirtualFunction(
    declaration: *const AST.Node,
    most_derived_contract: *const AST.Node,
    search_start: ?*const AST.Node,
) BuildError!*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(most_derived_contract) orelse
        return error.InvalidAst;
    const hierarchy = switch (annotation.*) {
        .contract_definition => |value| value.linearized_base_contracts,
        else => return error.InvalidAst,
    };
    var found_start = search_start == null;
    for (hierarchy) |contract| {
        if (!found_start and contract != search_start.?) continue;
        found_start = true;
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        for (contract.payload.contract_definition.sub_nodes) |candidate| {
            if (candidate.nodeKind() != .function_definition) continue;
            if (search_start != null and
                !candidate.payload.function_definition.implemented()) continue;
            if (candidate == declaration or callableOverrides(candidate, declaration, 0))
                return candidate;
        }
    }
    return error.InvalidAst;
}

fn callableOverrides(
    candidate: *const AST.Node,
    target: *const AST.Node,
    depth: usize,
) bool {
    if (depth >= 256) return false;
    const annotation = ASTAnnotations.annotationConst(candidate) orelse return false;
    const bases = switch (annotation.*) {
        .documented_callable => |value| value.callable.base_functions.items,
        else => return false,
    };
    for (bases) |base|
        if (base == target or callableOverrides(base, target, depth + 1)) return true;
    return false;
}

fn variableAssignmentLocation(
    initial: *const AST.Node,
    declaration_index: usize,
) BuildError!?SourceLocation {
    var expression: ?*const AST.Node = initial;
    switch (initial.payload) {
        .tuple_expression => |tuple| if (tuple.components.len > 1) {
            if (declaration_index >= tuple.components.len) return error.InvalidAst;
            expression = tuple.components[declaration_index];
        },
        else => {},
    }
    expression = resolveOuterUnaryTuples(expression);
    return if (expression) |value| value.location else null;
}

fn resolveOuterUnaryTuples(expression: ?*const AST.Node) ?*const AST.Node {
    var result = expression;
    while (result) |node| switch (node.payload) {
        .tuple_expression => |tuple| {
            if (tuple.components.len != 1) return result;
            result = tuple.components[0];
        },
        else => return result,
    };
    return null;
}

fn yulExternalReference(
    assembly: *const ASTAnnotations.InlineAssemblyAnnotation,
    identifier: *const YulAST.Identifier,
) ?*const ASTAnnotations.InlineAssemblyExternalReference {
    for (assembly.external_references.items) |*reference|
        if (reference.identifier == identifier) return reference;
    return null;
}

fn yulIdentifierLocation(identifier: *const YulAST.Identifier) BuildError!SourceLocation {
    const debug_data = identifier.debug_data orelse return .{};
    if (!debug_data.native_location.eql(debug_data.origin_location))
        return error.InvalidAst;
    return debug_data.native_location;
}
