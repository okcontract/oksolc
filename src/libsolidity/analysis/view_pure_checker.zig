// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Function and modifier state-mutability inference translated from
//! `ViewPureChecker.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Enums = @import("../ast/ast_enums.zig");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const GlobalContext = @import("global_context.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;
const SemanticInformation = @import("../../libevmasm/semantic_information.zig");
const YulAST = @import("../../libyul/ast.zig");
const EVMDialect = @import("../../libyul/backends/evm/evm_dialect.zig");

pub const CheckError = std.mem.Allocator.Error ||
    Diagnostics.ReportError ||
    error{InvalidAst};

const max_ast_depth = 4096;

const MutabilityAndLocation = struct {
    mutability: AST.StateMutability,
    location: SourceLocation,
};

pub const ViewPureChecker = struct {
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    errors: bool = false,
    best: MutabilityAndLocation = .{ .mutability = .Payable, .location = .{} },
    current_function: ?*const AST.Node = null,
    inferred_modifiers: std.AutoHashMap(*const AST.Node, MutabilityAndLocation),
    modifiers_in_progress: std.AutoHashMap(*const AST.Node, void),

    pub fn init(
        allocator: std.mem.Allocator,
        reporter: *Diagnostics.ErrorReporter,
    ) ViewPureChecker {
        return .{
            .allocator = allocator,
            .reporter = reporter,
            .inferred_modifiers = std.AutoHashMap(
                *const AST.Node,
                MutabilityAndLocation,
            ).init(allocator),
            .modifiers_in_progress = std.AutoHashMap(*const AST.Node, void).init(allocator),
        };
    }

    pub fn deinit(self: *ViewPureChecker) void {
        self.modifiers_in_progress.deinit();
        self.inferred_modifiers.deinit();
        self.* = undefined;
    }

    pub fn check(
        self: *ViewPureChecker,
        source_units: []const *AST.Node,
    ) CheckError!bool {
        const watcher = self.reporter.errorWatcher();
        for (source_units) |source_unit| {
            if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
            try self.visitNode(@constCast(source_unit), 0);
        }
        if (self.current_function != null or self.modifiers_in_progress.count() != 0)
            return error.InvalidAst;
        return watcher.ok() and !self.errors;
    }

    fn visitNode(
        self: *ViewPureChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        var descend = true;
        switch (node.payload) {
            .import_directive => descend = false,
            .function_definition => try self.visitFunctionDefinition(node),
            .modifier_definition => try self.visitModifierDefinition(node),
            .member_access => descend = try self.visitMemberAccess(node),
            else => {},
        }

        if (descend) {
            var children: std.ArrayList(*const AST.Node) = .empty;
            defer children.deinit(self.allocator);
            try ASTImplementation.appendChildren(self.allocator, &children, node);
            for (children.items) |child| try self.visitNode(@constCast(child), depth + 1);
        }

        switch (node.payload) {
            .function_definition => try self.endFunctionDefinition(node),
            .modifier_definition => try self.endModifierDefinition(node),
            .identifier => try self.endIdentifier(node),
            .inline_assembly => try self.endInlineAssembly(node),
            .binary_operation => try self.endBinaryOperation(node),
            .unary_operation => try self.endUnaryOperation(node),
            .function_call => try self.endFunctionCall(node),
            .member_access => try self.endMemberAccess(node),
            .index_access => try self.endIndexAccess(node),
            .index_range_access => try self.endIndexRangeAccess(node),
            .modifier_invocation => try self.endModifierInvocation(node),
            else => {},
        }
    }

    fn visitFunctionDefinition(
        self: *ViewPureChecker,
        node: *const AST.Node,
    ) CheckError!void {
        if (self.current_function != null) return error.InvalidAst;
        self.current_function = node;
        self.best = .{ .mutability = .Pure, .location = node.location };
    }

    fn endFunctionDefinition(
        self: *ViewPureChecker,
        node: *const AST.Node,
    ) CheckError!void {
        if (self.current_function != node) return error.InvalidAst;
        const function = node.payload.function_definition;
        const body_nonempty = if (function.body) |body|
            body.nodeKind() == .block and body.payload.block.statements.len != 0
        else
            false;
        if (mutabilityLess(self.best.mutability, function.state_mutability) and
            function.state_mutability != .Payable and function.implemented() and
            body_nonempty and function.kind == .Function and
            !function.callable.marked_virtual)
        {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Function state mutability can be restricted to {s}",
                .{Enums.stateMutabilityToString(self.best.mutability)},
            );
            defer self.allocator.free(message);
            try self.reporter.warning(errorId(2018), node.location, message);
        }
        self.current_function = null;
    }

    fn visitModifierDefinition(
        self: *ViewPureChecker,
        node: *const AST.Node,
    ) CheckError!void {
        if (self.current_function != null) return error.InvalidAst;
        self.best = .{ .mutability = .Pure, .location = node.location };
    }

    fn endModifierDefinition(
        self: *ViewPureChecker,
        node: *const AST.Node,
    ) std.mem.Allocator.Error!void {
        if (self.current_function != null) return;
        try self.inferred_modifiers.put(node, self.best);
    }

    fn endIdentifier(self: *ViewPureChecker, node: *AST.Node) CheckError!void {
        const annotation = try identifierAnnotation(node);
        const declaration = annotation.referenced_declaration orelse return error.InvalidAst;
        var mutability: AST.StateMutability = .Pure;
        if (declaration.nodeKind() == .variable_declaration) {
            const variable = declaration.payload.variable_declaration;
            if (variable.mutability == .Immutable) {
                const assigned_literal = if (variable.value) |value|
                    if ((try expressionAnnotation(value)).type_ref) |type_ref|
                        type_ref.category() == .RationalNumber
                    else
                        false
                else
                    false;
                if (!assigned_literal) mutability = .View;
            } else if (ASTImplementation.isStateVariable(declaration) and
                variable.mutability != .Constant)
                mutability = if (annotation.expression.will_be_written_to)
                    .NonPayable
                else
                    .View;
        } else if (declaration.nodeKind() == .magic_variable_declaration) {
            const declaration_type = GlobalContext.declarationType(declaration) orelse
                return error.InvalidAst;
            if (declaration_type.category() == .Contract or
                declaration_type.category() == .Integer) mutability = .View;
        }
        try self.reportMutability(mutability, node.location, null);
    }

    fn endInlineAssembly(
        self: *ViewPureChecker,
        node: *const AST.Node,
    ) CheckError!void {
        const value = node.payload.inline_assembly;
        const operations = value.operations orelse return;
        try self.analyzeYulBlock(operations.dialect().*, operations.root());
    }

    fn analyzeYulBlock(
        self: *ViewPureChecker,
        dialect: YulAST.Dialect,
        block: *const YulAST.Block,
    ) CheckError!void {
        for (block.statements.items) |*statement|
            try self.analyzeYulStatement(dialect, statement);
    }

    fn analyzeYulStatement(
        self: *ViewPureChecker,
        dialect: YulAST.Dialect,
        statement: *const YulAST.Statement,
    ) CheckError!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.analyzeYulExpression(
                dialect,
                &value.expression,
            ),
            .assignment => |*value| if (value.value) |expression|
                try self.analyzeYulExpression(dialect, expression),
            .variable_declaration => |*value| if (value.value) |expression|
                try self.analyzeYulExpression(dialect, expression),
            .function_definition => |*value| try self.analyzeYulBlock(dialect, &value.body),
            .if_statement => |*value| {
                if (value.condition) |condition| try self.analyzeYulExpression(dialect, condition);
                try self.analyzeYulBlock(dialect, &value.body);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression| try self.analyzeYulExpression(dialect, expression);
                for (value.cases.items) |*case_value|
                    try self.analyzeYulBlock(dialect, &case_value.body);
            },
            .for_loop => |*value| {
                try self.analyzeYulBlock(dialect, &value.pre);
                if (value.condition) |condition| try self.analyzeYulExpression(dialect, condition);
                try self.analyzeYulBlock(dialect, &value.body);
                try self.analyzeYulBlock(dialect, &value.post);
            },
            .block => |*value| try self.analyzeYulBlock(dialect, value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn analyzeYulExpression(
        self: *ViewPureChecker,
        dialect: YulAST.Dialect,
        expression: *const YulAST.Expression,
    ) CheckError!void {
        switch (expression.*) {
            .function_call => |*call| {
                if (call.function_name == .builtin)
                    if (EVMDialect.fromDialect(dialect)) |evm_dialect|
                        if (evm_dialect.builtin(call.function_name.builtin.handle)) |builtin|
                            if (builtin.instruction) |instruction| {
                                const location = if (call.debug_data) |debug_data|
                                    debug_data.native_location
                                else
                                    SourceLocation{};
                                if (SemanticInformation.invalidInViewFunctions(instruction))
                                    try self.reportMutability(.NonPayable, location, null)
                                else if (SemanticInformation.invalidInPureFunctions(instruction))
                                    try self.reportMutability(.View, location, null);
                            };
                for (call.arguments.items) |*argument|
                    try self.analyzeYulExpression(dialect, argument);
            },
            .identifier, .literal => {},
        }
    }

    fn endBinaryOperation(
        self: *ViewPureChecker,
        node: *AST.Node,
    ) CheckError!void {
        const declaration = (try binaryOperationAnnotation(
            node,
        )).operation.user_defined_function.get() catch return error.InvalidAst;
        if (declaration.*) |function|
            try self.reportFunctionCallMutability(
                functionMutability(function),
                node.location,
            );
    }

    fn endUnaryOperation(
        self: *ViewPureChecker,
        node: *AST.Node,
    ) CheckError!void {
        const declaration = (try operationAnnotation(
            node,
        )).user_defined_function.get() catch return error.InvalidAst;
        if (declaration.*) |function|
            try self.reportFunctionCallMutability(
                functionMutability(function),
                node.location,
            );
    }

    fn endFunctionCall(self: *ViewPureChecker, node: *AST.Node) CheckError!void {
        const annotation = try functionCallAnnotation(node);
        if ((annotation.kind.get() catch return error.InvalidAst).* != .FunctionCall) return;
        const function_type = (try expressionAnnotation(
            node.payload.function_call.expression,
        )).type_ref orelse return error.InvalidAst;
        const function = function_type.asFunction() orelse return error.InvalidAst;
        try self.reportFunctionCallMutability(function.state_mutability, node.location);
    }

    fn visitMemberAccess(
        _: *ViewPureChecker,
        node: *const AST.Node,
    ) CheckError!bool {
        const value = node.payload.member_access;
        if (!std.mem.eql(u8, value.member_name, "selector")) return true;
        const expression_type = (try expressionAnnotation(value.expression)).type_ref orelse
            return error.InvalidAst;
        if (expression_type.category() != .Function or
            value.expression.nodeKind() != .member_access) return true;
        const base = value.expression.payload.member_access.expression;
        return !(base.nodeKind() == .identifier and
            std.mem.eql(u8, base.payload.identifier.name, "this"));
    }

    fn endMemberAccess(self: *ViewPureChecker, node: *AST.Node) CheckError!void {
        const value = node.payload.member_access;
        const owner_type = (try expressionAnnotation(value.expression)).type_ref orelse
            return error.InvalidAst;
        const annotation = try memberAccessAnnotation(node);
        var mutability: AST.StateMutability = .Pure;
        switch (owner_type.payload) {
            .Address => if (std.mem.eql(u8, value.member_name, "balance") or
                std.mem.eql(u8, value.member_name, "code") or
                std.mem.eql(u8, value.member_name, "codehash"))
            {
                mutability = .View;
            },
            .Magic => |magic| {
                if (magicMemberPayable(magic.kind, value.member_name))
                    mutability = .Payable
                else if (!magicMemberPure(magic.kind, value.member_name))
                    mutability = .View;
            },
            .Struct => if (TypeBehavior.dataStoredIn(owner_type, .Storage)) {
                mutability = if (annotation.expression.will_be_written_to)
                    .NonPayable
                else
                    .View;
            },
            .Array => |array| if (std.mem.eql(u8, value.member_name, "length") and
                array.isDynamicallySized() and
                TypeBehavior.dataStoredIn(owner_type, .Storage))
            {
                mutability = .View;
            },
            else => if (annotation.referenced_declaration) |declaration|
                if (declaration.nodeKind() == .variable_declaration and
                    ASTImplementation.isStateVariable(declaration) and
                    declaration.payload.variable_declaration.mutability != .Constant)
                {
                    mutability = if (annotation.expression.will_be_written_to)
                        .NonPayable
                    else
                        .View;
                },
        }
        try self.reportMutability(mutability, node.location, null);
    }

    fn endIndexAccess(self: *ViewPureChecker, node: *AST.Node) CheckError!void {
        const value = node.payload.index_access;
        if (value.index == null) return;
        const base_type = (try expressionAnnotation(value.base)).type_ref orelse
            return error.InvalidAst;
        if (!TypeBehavior.dataStoredIn(base_type, .Storage)) return;
        const writes = (try expressionAnnotation(node)).will_be_written_to;
        try self.reportMutability(if (writes) .NonPayable else .View, node.location, null);
    }

    fn endIndexRangeAccess(
        self: *ViewPureChecker,
        node: *AST.Node,
    ) CheckError!void {
        const base_type = (try expressionAnnotation(
            node.payload.index_range_access.base,
        )).type_ref orelse return error.InvalidAst;
        if (!TypeBehavior.dataStoredIn(base_type, .Storage)) return;
        const writes = (try expressionAnnotation(node)).will_be_written_to;
        try self.reportMutability(if (writes) .NonPayable else .View, node.location, null);
    }

    fn endModifierInvocation(
        self: *ViewPureChecker,
        node: *AST.Node,
    ) CheckError!void {
        const name = node.payload.modifier_invocation.modifier_name;
        const declaration = (try identifierPathOrIdentifierDeclaration(name)) orelse
            return error.InvalidAst;
        if (declaration.nodeKind() == .contract_definition) return;
        if (declaration.nodeKind() != .modifier_definition) return error.InvalidAst;
        const inferred = try self.modifierMutability(declaration);
        try self.reportMutability(inferred.mutability, node.location, inferred.location);
    }

    fn modifierMutability(
        self: *ViewPureChecker,
        modifier: *const AST.Node,
    ) CheckError!MutabilityAndLocation {
        if (self.inferred_modifiers.get(modifier)) |inferred| return inferred;
        if (self.modifiers_in_progress.contains(modifier)) return error.InvalidAst;
        try self.modifiers_in_progress.put(modifier, {});
        defer _ = self.modifiers_in_progress.remove(modifier);

        const saved_best = self.best;
        const saved_function = self.current_function;
        self.best = .{ .mutability = .Pure, .location = modifier.location };
        self.current_function = null;
        try self.visitNode(@constCast(modifier), 0);
        const inferred = self.inferred_modifiers.get(modifier) orelse return error.InvalidAst;
        self.best = saved_best;
        self.current_function = saved_function;
        return inferred;
    }

    fn reportFunctionCallMutability(
        self: *ViewPureChecker,
        mutability: AST.StateMutability,
        location: SourceLocation,
    ) CheckError!void {
        try self.reportMutability(
            if (mutability == .Payable) .NonPayable else mutability,
            location,
            null,
        );
    }

    fn reportMutability(
        self: *ViewPureChecker,
        mutability: AST.StateMutability,
        location: SourceLocation,
        nested_location: ?SourceLocation,
    ) CheckError!void {
        if (mutabilityLess(self.best.mutability, mutability))
            self.best = .{ .mutability = mutability, .location = location };
        const current = self.current_function orelse return;
        const declared = current.payload.function_definition.state_mutability;
        if (!mutabilityLess(declared, mutability)) return;

        if (mutability == .View or (mutability == .Payable and declared == .Pure)) {
            try self.reporter.typeError(
                errorId(2527),
                location,
                "Function declared as pure, but this expression (potentially) reads from the environment or state and thus requires \"view\".",
            );
            self.errors = true;
        } else if (mutability == .NonPayable) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Function cannot be declared as {s} because this expression (potentially) modifies the state.",
                .{Enums.stateMutabilityToString(declared)},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(8961), location, message);
            self.errors = true;
        } else if (mutability == .Payable and functionRequiresPayable(current)) {
            const constructor = current.payload.function_definition.kind == .Constructor;
            if (nested_location) |nested| {
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(
                    self.allocator,
                    "\"msg.value\" or \"callvalue()\" appear here inside the modifier.",
                    nested,
                );
                try self.reporter.reportWithSecondary(
                    errorId(4006),
                    .TypeError,
                    location,
                    &secondary,
                    if (constructor)
                        "This modifier uses \"msg.value\" or \"callvalue()\" and thus the constructor has to be payable."
                    else
                        "This modifier uses \"msg.value\" or \"callvalue()\" and thus the function has to be payable or internal.",
                );
            } else try self.reporter.typeError(
                errorId(5887),
                location,
                if (constructor)
                    "\"msg.value\" and \"callvalue()\" can only be used in payable constructors. Make the constructor \"payable\" to avoid this error."
                else
                    "\"msg.value\" and \"callvalue()\" can only be used in payable public functions. Make the function \"payable\" or use an internal function to avoid this error.",
            );
            self.errors = true;
        }
    }
};

fn mutabilityLess(left: AST.StateMutability, right: AST.StateMutability) bool {
    return @intFromEnum(left) < @intFromEnum(right);
}

fn functionMutability(node: *const AST.Node) AST.StateMutability {
    return switch (node.payload) {
        .function_definition => |value| value.state_mutability,
        else => .NonPayable,
    };
}

fn functionRequiresPayable(function: *const AST.Node) bool {
    const definition = function.payload.function_definition;
    const externally_callable = definition.kind == .Constructor or
        ASTImplementation.isPublic(function);
    if (!externally_callable) return false;
    const scope = ASTImplementation.scope(function) orelse return true;
    return scope.nodeKind() != .contract_definition or
        scope.payload.contract_definition.contract_kind != .Library;
}

fn magicMemberPayable(kind: Types.MagicKind, member: []const u8) bool {
    return kind == .Message and std.mem.eql(u8, member, "value");
}

fn magicMemberPure(kind: Types.MagicKind, member: []const u8) bool {
    return switch (kind) {
        .ABI => std.mem.eql(u8, member, "decode") or
            std.mem.eql(u8, member, "encode") or
            std.mem.eql(u8, member, "encodePacked") or
            std.mem.eql(u8, member, "encodeWithSelector") or
            std.mem.eql(u8, member, "encodeCall") or
            std.mem.eql(u8, member, "encodeWithSignature"),
        .Message => std.mem.eql(u8, member, "data") or std.mem.eql(u8, member, "sig"),
        .MetaType => std.mem.eql(u8, member, "creationCode") or
            std.mem.eql(u8, member, "runtimeCode") or
            std.mem.eql(u8, member, "name") or
            std.mem.eql(u8, member, "interfaceId") or
            std.mem.eql(u8, member, "min") or
            std.mem.eql(u8, member, "max"),
        else => false,
    };
}

fn expressionAnnotation(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.ExpressionAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .expression => |*value| value,
        .identifier => |*value| &value.expression,
        .member_access => |*value| &value.expression,
        .operation => |*value| &value.expression,
        .binary_operation => |*value| &value.operation.expression,
        .function_call => |*value| &value.expression,
        else => error.InvalidAst,
    };
}

fn identifierAnnotation(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.IdentifierAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier => |*value| value,
        else => error.InvalidAst,
    };
}

fn memberAccessAnnotation(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.MemberAccessAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .member_access => |*value| value,
        else => error.InvalidAst,
    };
}

fn binaryOperationAnnotation(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.BinaryOperationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .binary_operation => |*value| value,
        else => error.InvalidAst,
    };
}

fn operationAnnotation(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.OperationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .operation => |*value| value,
        else => error.InvalidAst,
    };
}

fn functionCallAnnotation(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.FunctionCallAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .function_call => |*value| value,
        else => error.InvalidAst,
    };
}

fn identifierPathOrIdentifierDeclaration(
    node: *const AST.Node,
) CheckError!?*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier_path => |value| value.referenced_declaration,
        .identifier => |value| value.referenced_declaration,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
