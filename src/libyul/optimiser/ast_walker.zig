// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Generic const and mutable Yul AST traversal with overridable node hooks.

const AST = @import("../ast.zig");

pub const ConstCallbacks = struct {
    literal: ?*const fn (?*anyopaque, *ASTWalker, *const AST.Literal) void = null,
    identifier: ?*const fn (?*anyopaque, *ASTWalker, *const AST.Identifier) void = null,
    function_call: ?*const fn (?*anyopaque, *ASTWalker, *const AST.FunctionCall) void = null,
    expression_statement: ?*const fn (?*anyopaque, *ASTWalker, *const AST.ExpressionStatement) void = null,
    assignment: ?*const fn (?*anyopaque, *ASTWalker, *const AST.Assignment) void = null,
    variable_declaration: ?*const fn (?*anyopaque, *ASTWalker, *const AST.VariableDeclaration) void = null,
    if_statement: ?*const fn (?*anyopaque, *ASTWalker, *const AST.If) void = null,
    switch_statement: ?*const fn (?*anyopaque, *ASTWalker, *const AST.Switch) void = null,
    function_definition: ?*const fn (?*anyopaque, *ASTWalker, *const AST.FunctionDefinition) void = null,
    for_loop: ?*const fn (?*anyopaque, *ASTWalker, *const AST.ForLoop) void = null,
    break_statement: ?*const fn (?*anyopaque, *ASTWalker, *const AST.Break) void = null,
    continue_statement: ?*const fn (?*anyopaque, *ASTWalker, *const AST.Continue) void = null,
    leave_statement: ?*const fn (?*anyopaque, *ASTWalker, *const AST.Leave) void = null,
    block: ?*const fn (?*anyopaque, *ASTWalker, *const AST.Block) void = null,
};

pub const ASTWalker = struct {
    context: ?*anyopaque = null,
    callbacks: ConstCallbacks = .{},

    pub fn init(context: ?*anyopaque, callbacks: ConstCallbacks) ASTWalker {
        return .{ .context = context, .callbacks = callbacks };
    }

    pub fn visitExpression(self: *ASTWalker, expression: *const AST.Expression) void {
        switch (expression.*) {
            .literal => |*node| self.visitLiteral(node),
            .identifier => |*node| self.visitIdentifier(node),
            .function_call => |*node| self.visitFunctionCall(node),
        }
    }

    pub fn visitStatement(self: *ASTWalker, statement: *const AST.Statement) void {
        switch (statement.*) {
            .expression_statement => |*node| self.visitExpressionStatement(node),
            .assignment => |*node| self.visitAssignment(node),
            .variable_declaration => |*node| self.visitVariableDeclaration(node),
            .function_definition => |*node| self.visitFunctionDefinition(node),
            .if_statement => |*node| self.visitIf(node),
            .switch_statement => |*node| self.visitSwitch(node),
            .for_loop => |*node| self.visitForLoop(node),
            .break_statement => |*node| self.visitBreak(node),
            .continue_statement => |*node| self.visitContinue(node),
            .leave_statement => |*node| self.visitLeave(node),
            .block => |*node| self.visitBlock(node),
        }
    }

    pub fn visitLiteral(self: *ASTWalker, node: *const AST.Literal) void {
        if (self.callbacks.literal) |callback| callback(self.context, self, node) else self.walkLiteral(node);
    }

    pub fn visitIdentifier(self: *ASTWalker, node: *const AST.Identifier) void {
        if (self.callbacks.identifier) |callback| callback(self.context, self, node) else self.walkIdentifier(node);
    }

    pub fn visitFunctionCall(self: *ASTWalker, node: *const AST.FunctionCall) void {
        if (self.callbacks.function_call) |callback| callback(self.context, self, node) else self.walkFunctionCall(node);
    }

    pub fn visitExpressionStatement(self: *ASTWalker, node: *const AST.ExpressionStatement) void {
        if (self.callbacks.expression_statement) |callback| callback(self.context, self, node) else self.walkExpressionStatement(node);
    }

    pub fn visitAssignment(self: *ASTWalker, node: *const AST.Assignment) void {
        if (self.callbacks.assignment) |callback| callback(self.context, self, node) else self.walkAssignment(node);
    }

    pub fn visitVariableDeclaration(self: *ASTWalker, node: *const AST.VariableDeclaration) void {
        if (self.callbacks.variable_declaration) |callback| callback(self.context, self, node) else self.walkVariableDeclaration(node);
    }

    pub fn visitIf(self: *ASTWalker, node: *const AST.If) void {
        if (self.callbacks.if_statement) |callback| callback(self.context, self, node) else self.walkIf(node);
    }

    pub fn visitSwitch(self: *ASTWalker, node: *const AST.Switch) void {
        if (self.callbacks.switch_statement) |callback| callback(self.context, self, node) else self.walkSwitch(node);
    }

    pub fn visitFunctionDefinition(self: *ASTWalker, node: *const AST.FunctionDefinition) void {
        if (self.callbacks.function_definition) |callback| callback(self.context, self, node) else self.walkFunctionDefinition(node);
    }

    pub fn visitForLoop(self: *ASTWalker, node: *const AST.ForLoop) void {
        if (self.callbacks.for_loop) |callback| callback(self.context, self, node) else self.walkForLoop(node);
    }

    pub fn visitBreak(self: *ASTWalker, node: *const AST.Break) void {
        if (self.callbacks.break_statement) |callback| callback(self.context, self, node) else self.walkBreak(node);
    }

    pub fn visitContinue(self: *ASTWalker, node: *const AST.Continue) void {
        if (self.callbacks.continue_statement) |callback| callback(self.context, self, node) else self.walkContinue(node);
    }

    pub fn visitLeave(self: *ASTWalker, node: *const AST.Leave) void {
        if (self.callbacks.leave_statement) |callback| callback(self.context, self, node) else self.walkLeave(node);
    }

    pub fn visitBlock(self: *ASTWalker, node: *const AST.Block) void {
        if (self.callbacks.block) |callback| callback(self.context, self, node) else self.walkBlock(node);
    }

    pub fn walkLiteral(_: *ASTWalker, _: *const AST.Literal) void {}
    pub fn walkIdentifier(_: *ASTWalker, _: *const AST.Identifier) void {}

    pub fn walkFunctionCall(self: *ASTWalker, node: *const AST.FunctionCall) void {
        var index = node.arguments.items.len;
        while (index != 0) {
            index -= 1;
            self.visitExpression(&node.arguments.items[index]);
        }
    }

    pub fn walkExpressionStatement(self: *ASTWalker, node: *const AST.ExpressionStatement) void {
        self.visitExpression(&node.expression);
    }

    pub fn walkAssignment(self: *ASTWalker, node: *const AST.Assignment) void {
        for (node.variable_names.items) |*name| self.visitIdentifier(name);
        if (node.value) |value| self.visitExpression(value);
    }

    pub fn walkVariableDeclaration(self: *ASTWalker, node: *const AST.VariableDeclaration) void {
        if (node.value) |value| self.visitExpression(value);
    }

    pub fn walkIf(self: *ASTWalker, node: *const AST.If) void {
        if (node.condition) |condition| self.visitExpression(condition);
        self.visitBlock(&node.body);
    }

    pub fn walkSwitch(self: *ASTWalker, node: *const AST.Switch) void {
        if (node.expression) |expression| self.visitExpression(expression);
        for (node.cases.items) |*case_value| {
            if (case_value.value) |value| self.visitLiteral(value);
            self.visitBlock(&case_value.body);
        }
    }

    pub fn walkFunctionDefinition(self: *ASTWalker, node: *const AST.FunctionDefinition) void {
        self.visitBlock(&node.body);
    }

    pub fn walkForLoop(self: *ASTWalker, node: *const AST.ForLoop) void {
        self.visitBlock(&node.pre);
        if (node.condition) |condition| self.visitExpression(condition);
        self.visitBlock(&node.body);
        self.visitBlock(&node.post);
    }

    pub fn walkBreak(_: *ASTWalker, _: *const AST.Break) void {}
    pub fn walkContinue(_: *ASTWalker, _: *const AST.Continue) void {}
    pub fn walkLeave(_: *ASTWalker, _: *const AST.Leave) void {}

    pub fn walkBlock(self: *ASTWalker, node: *const AST.Block) void {
        for (node.statements.items) |*statement| self.visitStatement(statement);
    }
};

pub const MutableCallbacks = struct {
    literal: ?*const fn (?*anyopaque, *ASTModifier, *AST.Literal) void = null,
    identifier: ?*const fn (?*anyopaque, *ASTModifier, *AST.Identifier) void = null,
    function_call: ?*const fn (?*anyopaque, *ASTModifier, *AST.FunctionCall) void = null,
    expression_statement: ?*const fn (?*anyopaque, *ASTModifier, *AST.ExpressionStatement) void = null,
    assignment: ?*const fn (?*anyopaque, *ASTModifier, *AST.Assignment) void = null,
    variable_declaration: ?*const fn (?*anyopaque, *ASTModifier, *AST.VariableDeclaration) void = null,
    if_statement: ?*const fn (?*anyopaque, *ASTModifier, *AST.If) void = null,
    switch_statement: ?*const fn (?*anyopaque, *ASTModifier, *AST.Switch) void = null,
    function_definition: ?*const fn (?*anyopaque, *ASTModifier, *AST.FunctionDefinition) void = null,
    for_loop: ?*const fn (?*anyopaque, *ASTModifier, *AST.ForLoop) void = null,
    break_statement: ?*const fn (?*anyopaque, *ASTModifier, *AST.Break) void = null,
    continue_statement: ?*const fn (?*anyopaque, *ASTModifier, *AST.Continue) void = null,
    leave_statement: ?*const fn (?*anyopaque, *ASTModifier, *AST.Leave) void = null,
    block: ?*const fn (?*anyopaque, *ASTModifier, *AST.Block) void = null,
};

pub const ASTModifier = struct {
    context: ?*anyopaque = null,
    callbacks: MutableCallbacks = .{},

    pub fn init(context: ?*anyopaque, callbacks: MutableCallbacks) ASTModifier {
        return .{ .context = context, .callbacks = callbacks };
    }

    pub fn visitExpression(self: *ASTModifier, expression: *AST.Expression) void {
        switch (expression.*) {
            .literal => |*node| self.visitLiteral(node),
            .identifier => |*node| self.visitIdentifier(node),
            .function_call => |*node| self.visitFunctionCall(node),
        }
    }

    pub fn visitStatement(self: *ASTModifier, statement: *AST.Statement) void {
        switch (statement.*) {
            .expression_statement => |*node| self.visitExpressionStatement(node),
            .assignment => |*node| self.visitAssignment(node),
            .variable_declaration => |*node| self.visitVariableDeclaration(node),
            .function_definition => |*node| self.visitFunctionDefinition(node),
            .if_statement => |*node| self.visitIf(node),
            .switch_statement => |*node| self.visitSwitch(node),
            .for_loop => |*node| self.visitForLoop(node),
            .break_statement => |*node| self.visitBreak(node),
            .continue_statement => |*node| self.visitContinue(node),
            .leave_statement => |*node| self.visitLeave(node),
            .block => |*node| self.visitBlock(node),
        }
    }

    pub fn visitLiteral(self: *ASTModifier, node: *AST.Literal) void {
        if (self.callbacks.literal) |callback| callback(self.context, self, node) else self.walkLiteral(node);
    }

    pub fn visitIdentifier(self: *ASTModifier, node: *AST.Identifier) void {
        if (self.callbacks.identifier) |callback| callback(self.context, self, node) else self.walkIdentifier(node);
    }

    pub fn visitFunctionCall(self: *ASTModifier, node: *AST.FunctionCall) void {
        if (self.callbacks.function_call) |callback| callback(self.context, self, node) else self.walkFunctionCall(node);
    }

    pub fn visitExpressionStatement(self: *ASTModifier, node: *AST.ExpressionStatement) void {
        if (self.callbacks.expression_statement) |callback| callback(self.context, self, node) else self.walkExpressionStatement(node);
    }

    pub fn visitAssignment(self: *ASTModifier, node: *AST.Assignment) void {
        if (self.callbacks.assignment) |callback| callback(self.context, self, node) else self.walkAssignment(node);
    }

    pub fn visitVariableDeclaration(self: *ASTModifier, node: *AST.VariableDeclaration) void {
        if (self.callbacks.variable_declaration) |callback| callback(self.context, self, node) else self.walkVariableDeclaration(node);
    }

    pub fn visitIf(self: *ASTModifier, node: *AST.If) void {
        if (self.callbacks.if_statement) |callback| callback(self.context, self, node) else self.walkIf(node);
    }

    pub fn visitSwitch(self: *ASTModifier, node: *AST.Switch) void {
        if (self.callbacks.switch_statement) |callback| callback(self.context, self, node) else self.walkSwitch(node);
    }

    pub fn visitFunctionDefinition(self: *ASTModifier, node: *AST.FunctionDefinition) void {
        if (self.callbacks.function_definition) |callback| callback(self.context, self, node) else self.walkFunctionDefinition(node);
    }

    pub fn visitForLoop(self: *ASTModifier, node: *AST.ForLoop) void {
        if (self.callbacks.for_loop) |callback| callback(self.context, self, node) else self.walkForLoop(node);
    }

    pub fn visitBreak(self: *ASTModifier, node: *AST.Break) void {
        if (self.callbacks.break_statement) |callback| callback(self.context, self, node) else self.walkBreak(node);
    }

    pub fn visitContinue(self: *ASTModifier, node: *AST.Continue) void {
        if (self.callbacks.continue_statement) |callback| callback(self.context, self, node) else self.walkContinue(node);
    }

    pub fn visitLeave(self: *ASTModifier, node: *AST.Leave) void {
        if (self.callbacks.leave_statement) |callback| callback(self.context, self, node) else self.walkLeave(node);
    }

    pub fn visitBlock(self: *ASTModifier, node: *AST.Block) void {
        if (self.callbacks.block) |callback| callback(self.context, self, node) else self.walkBlock(node);
    }

    pub fn walkLiteral(_: *ASTModifier, _: *AST.Literal) void {}
    pub fn walkIdentifier(_: *ASTModifier, _: *AST.Identifier) void {}

    pub fn walkFunctionCall(self: *ASTModifier, node: *AST.FunctionCall) void {
        var index = node.arguments.items.len;
        while (index != 0) {
            index -= 1;
            self.visitExpression(&node.arguments.items[index]);
        }
    }

    pub fn walkExpressionStatement(self: *ASTModifier, node: *AST.ExpressionStatement) void {
        self.visitExpression(&node.expression);
    }

    pub fn walkAssignment(self: *ASTModifier, node: *AST.Assignment) void {
        for (node.variable_names.items) |*name| self.visitIdentifier(name);
        if (node.value) |value| self.visitExpression(value);
    }

    pub fn walkVariableDeclaration(self: *ASTModifier, node: *AST.VariableDeclaration) void {
        if (node.value) |value| self.visitExpression(value);
    }

    pub fn walkIf(self: *ASTModifier, node: *AST.If) void {
        if (node.condition) |condition| self.visitExpression(condition);
        self.visitBlock(&node.body);
    }

    pub fn walkSwitch(self: *ASTModifier, node: *AST.Switch) void {
        if (node.expression) |expression| self.visitExpression(expression);
        for (node.cases.items) |*case_value| {
            if (case_value.value) |value| self.visitLiteral(value);
            self.visitBlock(&case_value.body);
        }
    }

    pub fn walkFunctionDefinition(self: *ASTModifier, node: *AST.FunctionDefinition) void {
        self.visitBlock(&node.body);
    }

    pub fn walkForLoop(self: *ASTModifier, node: *AST.ForLoop) void {
        self.visitBlock(&node.pre);
        if (node.condition) |condition| self.visitExpression(condition);
        self.visitBlock(&node.post);
        self.visitBlock(&node.body);
    }

    pub fn walkBreak(_: *ASTModifier, _: *AST.Break) void {}
    pub fn walkContinue(_: *ASTModifier, _: *AST.Continue) void {}
    pub fn walkLeave(_: *ASTModifier, _: *AST.Leave) void {}

    pub fn walkBlock(self: *ASTModifier, node: *AST.Block) void {
        for (node.statements.items) |*statement| self.visitStatement(statement);
    }
};

pub fn forEachConst(
    comptime Node: type,
    block: *const AST.Block,
    context: ?*anyopaque,
    visitor: *const fn (?*anyopaque, *const Node) void,
) void {
    const Adapter = struct {
        const State = struct {
            context: ?*anyopaque,
            visitor: *const fn (?*anyopaque, *const Node) void,
        };

        fn callback(raw_context: ?*anyopaque, walker: *ASTWalker, node: *const Node) void {
            const state: *State = @ptrCast(@alignCast(raw_context.?));
            state.visitor(state.context, node);
            continueConstWalk(Node, walker, node);
        }
    };
    var state: Adapter.State = .{ .context = context, .visitor = visitor };
    var callbacks: ConstCallbacks = .{};
    installConstCallback(Node, &callbacks, Adapter.callback);
    var walker = ASTWalker.init(&state, callbacks);
    walker.visitBlock(block);
}

pub fn forEachMutable(
    comptime Node: type,
    block: *AST.Block,
    context: ?*anyopaque,
    visitor: *const fn (?*anyopaque, *Node) void,
) void {
    const Adapter = struct {
        const State = struct {
            context: ?*anyopaque,
            visitor: *const fn (?*anyopaque, *Node) void,
        };

        fn callback(raw_context: ?*anyopaque, modifier: *ASTModifier, node: *Node) void {
            const state: *State = @ptrCast(@alignCast(raw_context.?));
            state.visitor(state.context, node);
            continueMutableWalk(Node, modifier, node);
        }
    };
    var state: Adapter.State = .{ .context = context, .visitor = visitor };
    var callbacks: MutableCallbacks = .{};
    installMutableCallback(Node, &callbacks, Adapter.callback);
    var modifier = ASTModifier.init(&state, callbacks);
    modifier.visitBlock(block);
}

fn installConstCallback(comptime Node: type, callbacks: *ConstCallbacks, callback: anytype) void {
    if (Node == AST.Literal) callbacks.literal = callback else if (Node == AST.Identifier) callbacks.identifier = callback else if (Node == AST.FunctionCall) callbacks.function_call = callback else if (Node == AST.ExpressionStatement) callbacks.expression_statement = callback else if (Node == AST.Assignment) callbacks.assignment = callback else if (Node == AST.VariableDeclaration) callbacks.variable_declaration = callback else if (Node == AST.If) callbacks.if_statement = callback else if (Node == AST.Switch) callbacks.switch_statement = callback else if (Node == AST.FunctionDefinition) callbacks.function_definition = callback else if (Node == AST.ForLoop) callbacks.for_loop = callback else if (Node == AST.Break) callbacks.break_statement = callback else if (Node == AST.Continue) callbacks.continue_statement = callback else if (Node == AST.Leave) callbacks.leave_statement = callback else if (Node == AST.Block) callbacks.block = callback else @compileError("unsupported Yul AST node type");
}

fn installMutableCallback(comptime Node: type, callbacks: *MutableCallbacks, callback: anytype) void {
    if (Node == AST.Literal) callbacks.literal = callback else if (Node == AST.Identifier) callbacks.identifier = callback else if (Node == AST.FunctionCall) callbacks.function_call = callback else if (Node == AST.ExpressionStatement) callbacks.expression_statement = callback else if (Node == AST.Assignment) callbacks.assignment = callback else if (Node == AST.VariableDeclaration) callbacks.variable_declaration = callback else if (Node == AST.If) callbacks.if_statement = callback else if (Node == AST.Switch) callbacks.switch_statement = callback else if (Node == AST.FunctionDefinition) callbacks.function_definition = callback else if (Node == AST.ForLoop) callbacks.for_loop = callback else if (Node == AST.Break) callbacks.break_statement = callback else if (Node == AST.Continue) callbacks.continue_statement = callback else if (Node == AST.Leave) callbacks.leave_statement = callback else if (Node == AST.Block) callbacks.block = callback else @compileError("unsupported Yul AST node type");
}

fn continueConstWalk(comptime Node: type, walker: *ASTWalker, node: *const Node) void {
    if (Node == AST.Literal) walker.walkLiteral(node) else if (Node == AST.Identifier) walker.walkIdentifier(node) else if (Node == AST.FunctionCall) walker.walkFunctionCall(node) else if (Node == AST.ExpressionStatement) walker.walkExpressionStatement(node) else if (Node == AST.Assignment) walker.walkAssignment(node) else if (Node == AST.VariableDeclaration) walker.walkVariableDeclaration(node) else if (Node == AST.If) walker.walkIf(node) else if (Node == AST.Switch) walker.walkSwitch(node) else if (Node == AST.FunctionDefinition) walker.walkFunctionDefinition(node) else if (Node == AST.ForLoop) walker.walkForLoop(node) else if (Node == AST.Break) walker.walkBreak(node) else if (Node == AST.Continue) walker.walkContinue(node) else if (Node == AST.Leave) walker.walkLeave(node) else if (Node == AST.Block) walker.walkBlock(node) else @compileError("unsupported Yul AST node type");
}

fn continueMutableWalk(comptime Node: type, modifier: *ASTModifier, node: *Node) void {
    if (Node == AST.Literal) modifier.walkLiteral(node) else if (Node == AST.Identifier) modifier.walkIdentifier(node) else if (Node == AST.FunctionCall) modifier.walkFunctionCall(node) else if (Node == AST.ExpressionStatement) modifier.walkExpressionStatement(node) else if (Node == AST.Assignment) modifier.walkAssignment(node) else if (Node == AST.VariableDeclaration) modifier.walkVariableDeclaration(node) else if (Node == AST.If) modifier.walkIf(node) else if (Node == AST.Switch) modifier.walkSwitch(node) else if (Node == AST.FunctionDefinition) modifier.walkFunctionDefinition(node) else if (Node == AST.ForLoop) modifier.walkForLoop(node) else if (Node == AST.Break) modifier.walkBreak(node) else if (Node == AST.Continue) modifier.walkContinue(node) else if (Node == AST.Leave) modifier.walkLeave(node) else if (Node == AST.Block) modifier.walkBlock(node) else @compileError("unsupported Yul AST node type");
}
