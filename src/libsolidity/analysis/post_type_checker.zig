// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Checks that require every Solidity expression to have a resolved type.
//!
//! The checker persists across source units so constant dependency cycles are
//! finalized in deterministic declaration order, matching the upstream pass.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const FunctionSelector = @import("../../libsolutil/function_selector.zig");
const SetOnce = @import("../../libsolutil/set_once.zig");
const YulAST = @import("../../libyul/ast.zig");

pub const CheckError = TypeProviderModule.ProviderError ||
    Diagnostics.ReportError ||
    SetOnce.SetOnceError ||
    error{InvalidAst};

const max_ast_depth = 4096;
const max_cycle_depth = 256;

const Dependency = struct {
    from: *const AST.Node,
    to: *const AST.Node,
};

pub const PostTypeChecker = struct {
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    type_provider: *TypeProviderModule.TypeProvider,
    current_tree: ?*AST.Tree = null,
    current_constant: ?*const AST.Node = null,
    current_contract: ?*const AST.Node = null,
    current_statement: ?*const AST.Node = null,
    inside_modifier_invocation: bool = false,
    inside_struct: usize = 0,
    inside_require: bool = false,
    constant_variables: std.ArrayList(*const AST.Node) = .empty,
    dependencies: std.ArrayList(Dependency) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        reporter: *Diagnostics.ErrorReporter,
        type_provider: *TypeProviderModule.TypeProvider,
    ) PostTypeChecker {
        return .{
            .allocator = allocator,
            .reporter = reporter,
            .type_provider = type_provider,
        };
    }

    pub fn deinit(self: *PostTypeChecker) void {
        self.dependencies.deinit(self.allocator);
        self.constant_variables.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn check(
        self: *PostTypeChecker,
        tree: *AST.Tree,
        root: *AST.Node,
    ) CheckError!bool {
        if (self.current_tree != null or root.nodeKind() != .source_unit)
            return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        self.current_tree = tree;
        defer self.current_tree = null;
        try self.visitNode(root, 0);
        if (self.current_constant != null or self.current_contract != null or
            self.current_statement != null or self.inside_modifier_invocation or
            self.inside_struct != 0 or self.inside_require)
            return error.InvalidAst;
        return watcher.ok();
    }

    pub fn finalize(self: *PostTypeChecker) CheckError!bool {
        if (self.current_tree != null) return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        for (self.constant_variables.items) |declaration|
            if (try self.findCycle(declaration)) |via| {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "The value of the constant {s} has a cyclic dependency via {s}.",
                    .{ declarationName(declaration), declarationName(via) },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(6161), declaration.location, message);
            };
        return watcher.ok();
    }

    fn visitNode(
        self: *PostTypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;

        switch (node.payload) {
            .contract_definition => {
                if (self.current_contract != null) return error.InvalidAst;
                self.current_contract = node;
            },
            .struct_definition => self.inside_struct += 1,
            .modifier_invocation => {
                if (self.inside_modifier_invocation) return error.InvalidAst;
                self.inside_modifier_invocation = true;
            },
            .emit_statement, .revert_statement => {
                if (self.current_statement != null) return error.InvalidAst;
                self.current_statement = node;
            },
            .variable_declaration => try self.visitVariableDeclaration(node),
            .identifier => try self.visitIdentifier(node),
            .member_access => try self.visitMemberAccess(node),
            .function_call => try self.visitFunctionCall(node),
            .for_statement => try self.visitForStatement(node),
            else => {},
        }

        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.allocator);
        try ASTImplementation.appendChildren(self.allocator, &children, node);
        for (children.items) |child| try self.visitNode(@constCast(child), depth + 1);

        switch (node.payload) {
            .variable_declaration => self.endVariableDeclaration(node),
            .contract_definition => self.current_contract = null,
            .struct_definition => self.inside_struct -= 1,
            .modifier_invocation => self.inside_modifier_invocation = false,
            .emit_statement, .revert_statement => self.current_statement = null,
            .function_call => try self.endFunctionCall(node),
            .override_specifier => try self.endOverrideSpecifier(node),
            .error_definition => try self.endErrorDefinition(node),
            else => {},
        }
    }

    fn visitVariableDeclaration(
        self: *PostTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const variable = node.payload.variable_declaration;
        if (variable.mutability == .Constant) {
            if (self.current_constant != null) return error.InvalidAst;
            self.current_constant = node;
            try self.constant_variables.append(self.allocator, node);
        }
        const contract = self.current_contract orelse return;
        if (contract.payload.contract_definition.contract_kind != .Interface or
            self.inside_struct != 0 or isCallableOrCatchParameter(node)) return;
        try self.reporter.typeError(
            errorId(8274),
            node.location,
            "Variables cannot be declared in interfaces.",
        );
    }

    fn endVariableDeclaration(self: *PostTypeChecker, node: *const AST.Node) void {
        if (node.payload.variable_declaration.mutability != .Constant) return;
        std.debug.assert(self.current_constant == node);
        self.current_constant = null;
    }

    fn visitIdentifier(self: *PostTypeChecker, node: *AST.Node) CheckError!void {
        const annotation = try identifierAnnotation(node);
        if (self.current_constant) |current|
            if (annotation.referenced_declaration) |declaration|
                try self.recordConstantDependency(current, declaration);
        if (self.inside_modifier_invocation) return;
        if (annotation.expression.type_ref) |type_ref|
            if (type_ref.category() == .Modifier)
                try self.reporter.typeError(
                    errorId(3112),
                    node.location,
                    "Modifier can only be referenced in function headers.",
                );
    }

    fn visitMemberAccess(self: *PostTypeChecker, node: *AST.Node) CheckError!void {
        if (self.current_constant == null) return;
        const annotation = try memberAccessAnnotation(node);
        if (annotation.referenced_declaration) |declaration|
            try self.recordConstantDependency(self.current_constant.?, declaration);
    }

    fn recordConstantDependency(
        self: *PostTypeChecker,
        from: *const AST.Node,
        to: *const AST.Node,
    ) std.mem.Allocator.Error!void {
        if (to.nodeKind() != .variable_declaration or
            to.payload.variable_declaration.mutability != .Constant) return;
        for (self.dependencies.items) |dependency|
            if (dependency.from == from and dependency.to == to) return;
        try self.dependencies.append(self.allocator, .{ .from = from, .to = to });
    }

    fn visitFunctionCall(self: *PostTypeChecker, node: *AST.Node) CheckError!void {
        const call_annotation = try functionCallAnnotation(node);
        if ((try call_annotation.kind.get()).* != .FunctionCall) return;
        const expression = node.payload.function_call.expression;
        const callee_type = (try expressionAnnotation(expression)).type_ref orelse
            return error.InvalidAst;
        const function = callee_type.asFunction() orelse return;
        if (function.kind == .Require) {
            if (self.inside_require) return error.InvalidAst;
            self.inside_require = true;
        }
        if (function.kind == .Event and
            (self.current_statement == null or
                self.current_statement.?.nodeKind() != .emit_statement))
            try self.reporter.typeError(
                errorId(3132),
                node.location,
                "Event invocations have to be prefixed by \"emit\".",
            )
        else if (function.kind == .Error and !self.inside_require and
            (self.current_statement == null or
                self.current_statement.?.nodeKind() != .revert_statement))
            try self.reporter.typeError(
                errorId(7757),
                node.location,
                "Errors can only be used with revert statements: \"revert MyError(args);\", or require functions: \"require(condition, MyError(args))\".",
            );
        self.current_statement = null;
    }

    fn endFunctionCall(self: *PostTypeChecker, node: *AST.Node) CheckError!void {
        const call_annotation = try functionCallAnnotation(node);
        if ((try call_annotation.kind.get()).* != .FunctionCall) return;
        const callee_type = (try expressionAnnotation(
            node.payload.function_call.expression,
        )).type_ref orelse return error.InvalidAst;
        if (callee_type.asFunction()) |function|
            if (function.kind == .Require) {
                if (!self.inside_require) return error.InvalidAst;
                self.inside_require = false;
            };
    }

    fn endOverrideSpecifier(
        self: *PostTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        for (node.payload.override_specifier.overrides) |path| {
            const declaration = (try identifierPathAnnotation(path)).referenced_declaration orelse
                return error.InvalidAst;
            if (declaration.nodeKind() == .contract_definition) continue;
            const type_name = try self.declarationTypeNameAlloc(declaration);
            defer self.allocator.free(type_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Expected contract but got {s}.",
                .{type_name},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(9301), path.location, message);
        }
    }

    fn declarationTypeNameAlloc(
        self: *PostTypeChecker,
        declaration: *const AST.Node,
    ) CheckError![]u8 {
        const type_ref: ?*const Types.Type = switch (declaration.payload) {
            .variable_declaration => (try variableAnnotation(declaration)).type_ref,
            .function_definition => try self.type_provider.functionFromDefinition(
                declaration,
                .Internal,
            ),
            .modifier_definition => |value| blk: {
                const parameters = value.callable.parameters.payload.parameter_list.parameters;
                const parameter_types = try self.allocator.alloc(*const Types.Type, parameters.len);
                defer self.allocator.free(parameter_types);
                for (parameters, parameter_types) |parameter, *target|
                    target.* = (try variableAnnotation(parameter)).type_ref orelse
                        return error.InvalidAst;
                break :blk try self.type_provider.modifier(parameter_types);
            },
            .event_definition => try self.type_provider.functionFromEvent(declaration),
            .error_definition => try self.type_provider.functionFromError(declaration),
            .struct_definition => try self.type_provider.structType(declaration, .Storage),
            .enum_definition => try self.type_provider.enumType(declaration),
            .user_defined_value_type_definition => try self.type_provider.userDefinedValueType(
                declaration,
                null,
            ),
            else => null,
        };
        if (type_ref) |present|
            return TypeBehavior.toStringAlloc(self.allocator, present, true);
        return self.allocator.dupe(u8, declarationName(declaration));
    }

    fn endErrorDefinition(
        self: *PostTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const name = node.payload.error_definition.callable.declaration.name;
        if (std.mem.eql(u8, name, "Error") or std.mem.eql(u8, name, "Panic")) {
            try self.reporter.syntaxError(
                errorId(1855),
                node.location,
                "The built-in errors \"Error\" and \"Panic\" cannot be re-defined.",
            );
            return;
        }
        const signature = try errorSignatureAlloc(self.allocator, node);
        defer self.allocator.free(signature);
        const selector = FunctionSelector.selectorFromSignatureU32(signature);
        if (selector != 0 and selector != std.math.maxInt(u32)) return;
        const selector_hash = FunctionSelector.selectorFromSignatureH32(signature);
        const hex = selector_hash.hex();
        const message = try std.fmt.allocPrint(
            self.allocator,
            "The selector 0x{s} is reserved. Please rename the error to avoid the collision.",
            .{&hex},
        );
        defer self.allocator.free(message);
        try self.reporter.syntaxError(errorId(2855), node.location, message);
    }

    fn visitForStatement(
        self: *PostTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const annotation = try forStatementAnnotation(self.current_tree orelse
            return error.InvalidAst, node);
        try annotation.is_simple_counter_loop.assign(try self.isSimpleCounterLoop(node));
    }

    fn isSimpleCounterLoop(
        self: *PostTypeChecker,
        node: *AST.Node,
    ) CheckError!bool {
        const statement = node.payload.for_statement;
        const condition = statement.condition orelse return false;
        if (condition.nodeKind() != .binary_operation or
            condition.payload.binary_operation.operator != .LessThan) return false;
        const binary_annotation = try binaryOperationAnnotation(condition);
        if ((try binary_annotation.operation.user_defined_function.get()).* != null)
            return false;
        const loop_statement = statement.loop_expression orelse return false;
        if (loop_statement.nodeKind() != .expression_statement) return false;
        const post_expression = loop_statement.payload.expression_statement.expression;
        if (post_expression.nodeKind() != .unary_operation or
            post_expression.payload.unary_operation.operator != .Inc) return false;
        const unary_annotation = try operationAnnotation(post_expression);
        if ((try unary_annotation.user_defined_function.get()).* != null) return false;

        const left = condition.payload.binary_operation.left;
        if (left.nodeKind() != .identifier) return false;
        const left_type = (try expressionAnnotation(left)).type_ref orelse
            return error.InvalidAst;
        const common_type = binary_annotation.common_type orelse return error.InvalidAst;
        if (left_type.category() != .Integer or common_type.category() != .Integer or
            !TypeBehavior.equals(left_type, common_type)) return false;

        const incremented = post_expression.payload.unary_operation.sub_expression;
        if (incremented.nodeKind() != .identifier) return false;
        const declaration = (try identifierAnnotation(left)).referenced_declaration orelse
            return error.InvalidAst;
        if ((try identifierAnnotation(incremented)).referenced_declaration != declaration)
            return false;
        if (declaration.nodeKind() == .variable_declaration and
            !ASTImplementation.isLocalVariable(declaration)) return false;
        if (try subtreeWritesDeclaration(
            self.allocator,
            condition.payload.binary_operation.right,
            declaration,
        ))
            return false;
        return !(try subtreeWritesDeclaration(self.allocator, statement.body, declaration));
    }

    fn findCycle(
        self: *PostTypeChecker,
        start: *const AST.Node,
    ) CheckError!?*const AST.Node {
        var active = std.AutoHashMap(*const AST.Node, void).init(self.allocator);
        defer active.deinit();
        var complete = std.AutoHashMap(*const AST.Node, void).init(self.allocator);
        defer complete.deinit();
        try active.put(start, {});
        var next = try self.sortedDependencies(start);
        defer next.deinit(self.allocator);
        for (next.items) |dependency|
            if (try self.hasCycleFrom(dependency, 2, &active, &complete))
                return dependency;
        return null;
    }

    fn hasCycleFrom(
        self: *PostTypeChecker,
        declaration: *const AST.Node,
        depth: usize,
        active: *std.AutoHashMap(*const AST.Node, void),
        complete: *std.AutoHashMap(*const AST.Node, void),
    ) CheckError!bool {
        if (active.contains(declaration)) return true;
        if (complete.contains(declaration)) return false;
        if (depth >= max_cycle_depth) {
            try self.reporter.fatal(
                errorId(7380),
                .DeclarationError,
                declaration.location,
                null,
                "Variable definition exhausting cyclic dependency validator.",
            );
            unreachable;
        }
        try active.put(declaration, {});
        defer _ = active.remove(declaration);

        var next = try self.sortedDependencies(declaration);
        defer next.deinit(self.allocator);
        for (next.items) |dependency|
            if (try self.hasCycleFrom(dependency, depth + 1, active, complete)) return true;
        try complete.put(declaration, {});
        return false;
    }

    fn sortedDependencies(
        self: *PostTypeChecker,
        declaration: *const AST.Node,
    ) std.mem.Allocator.Error!std.ArrayList(*const AST.Node) {
        var next: std.ArrayList(*const AST.Node) = .empty;
        errdefer next.deinit(self.allocator);
        for (self.dependencies.items) |dependency|
            if (dependency.from == declaration) try next.append(self.allocator, dependency.to);
        std.sort.insertion(*const AST.Node, next.items, {}, struct {
            fn lessThan(_: void, left: *const AST.Node, right: *const AST.Node) bool {
                return ASTAnnotations.compatibilityId(left) <
                    ASTAnnotations.compatibilityId(right);
            }
        }.lessThan);
        return next;
    }
};

fn subtreeWritesDeclaration(
    allocator: std.mem.Allocator,
    root: *const AST.Node,
    declaration: *const AST.Node,
) CheckError!bool {
    if (root.nodeKind() == .identifier) {
        const annotation = try identifierAnnotation(root);
        if (annotation.referenced_declaration == declaration and
            annotation.expression.will_be_written_to) return true;
    } else if (root.nodeKind() == .inline_assembly) {
        const operations = root.payload.inline_assembly.operations orelse
            return error.InvalidAst;
        if (try yulBlockWritesName(operations.root(), declarationName(declaration), 0))
            return true;
    }
    var children: std.ArrayList(*const AST.Node) = .empty;
    defer children.deinit(allocator);
    try ASTImplementation.appendChildren(allocator, &children, root);
    for (children.items) |child|
        if (try subtreeWritesDeclaration(allocator, child, declaration)) return true;
    return false;
}

fn yulBlockWritesName(
    block: *const YulAST.Block,
    declaration_name: []const u8,
    depth: usize,
) CheckError!bool {
    if (depth >= max_ast_depth) return error.InvalidAst;
    for (block.statements.items) |*statement| switch (statement.*) {
        .assignment => |*assignment| {
            for (assignment.variable_names.items) |identifier| {
                const name = identifier.name.str() catch return error.InvalidAst;
                if (std.mem.eql(u8, name, declaration_name)) return true;
            }
        },
        .function_definition => |*function| {
            if (try yulBlockWritesName(&function.body, declaration_name, depth + 1))
                return true;
        },
        .if_statement => |*if_statement| {
            if (try yulBlockWritesName(&if_statement.body, declaration_name, depth + 1))
                return true;
        },
        .switch_statement => |*switch_statement| {
            for (switch_statement.cases.items) |*case_value|
                if (try yulBlockWritesName(&case_value.body, declaration_name, depth + 1))
                    return true;
        },
        .for_loop => |*for_loop| {
            if (try yulBlockWritesName(&for_loop.pre, declaration_name, depth + 1) or
                try yulBlockWritesName(&for_loop.body, declaration_name, depth + 1) or
                try yulBlockWritesName(&for_loop.post, declaration_name, depth + 1))
                return true;
        },
        .block => |*nested| {
            if (try yulBlockWritesName(nested, declaration_name, depth + 1)) return true;
        },
        .expression_statement,
        .variable_declaration,
        .break_statement,
        .continue_statement,
        .leave_statement,
        => {},
    };
    return false;
}

fn isCallableOrCatchParameter(node: *const AST.Node) bool {
    const enclosing = ASTImplementation.scope(node) orelse return false;
    return switch (enclosing.nodeKind()) {
        .function_type_name,
        .function_definition,
        .modifier_definition,
        .event_definition,
        .error_definition,
        .try_catch_clause,
        => true,
        else => false,
    };
}

fn errorSignatureAlloc(
    allocator: std.mem.Allocator,
    definition: *const AST.Node,
) CheckError![]u8 {
    const value = definition.payload.error_definition;
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try output.appendSlice(allocator, value.callable.declaration.name);
    try output.append(allocator, '(');
    const parameters = value.callable.parameters.payload.parameter_list.parameters;
    for (parameters, 0..) |parameter, index| {
        if (index != 0) try output.append(allocator, ',');
        const type_ref = (try variableAnnotation(parameter)).type_ref orelse
            return error.InvalidAst;
        try appendAbiSignatureType(allocator, &output, type_ref, 0);
    }
    try output.append(allocator, ')');
    return output.toOwnedSlice(allocator);
}

fn appendAbiSignatureType(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    type_ref: *const Types.Type,
    depth: usize,
) CheckError!void {
    if (depth >= 64) return error.InvalidAst;
    switch (type_ref.payload) {
        .Address, .Contract => try output.appendSlice(allocator, "address"),
        .Enum => try output.appendSlice(allocator, "uint8"),
        .UserDefinedValueType => |value| try appendAbiSignatureType(
            allocator,
            output,
            value.underlying_type orelse return error.InvalidAst,
            depth + 1,
        ),
        .Array => |value| switch (value.kind) {
            .String => try output.appendSlice(allocator, "string"),
            .Bytes => try output.appendSlice(allocator, "bytes"),
            .Ordinary => {
                try appendAbiSignatureType(allocator, output, value.base_type, depth + 1);
                try output.append(allocator, '[');
                if (value.length) |length| try appendDecimal(allocator, output, length);
                try output.append(allocator, ']');
            },
        },
        .Struct => |value| {
            try output.append(allocator, '(');
            for (value.declaration.payload.struct_definition.members, 0..) |member, index| {
                if (index != 0) try output.append(allocator, ',');
                const member_type = (try variableAnnotation(member)).type_ref orelse
                    return error.InvalidAst;
                try appendAbiSignatureType(allocator, output, member_type, depth + 1);
            }
            try output.append(allocator, ')');
        },
        else => {
            const name = try TypeBehavior.canonicalNameAlloc(allocator, type_ref);
            defer allocator.free(name);
            try output.appendSlice(allocator, name);
        },
    }
}

fn appendDecimal(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    value: anytype,
) std.mem.Allocator.Error!void {
    const rendered = try std.fmt.allocPrint(allocator, "{d}", .{value});
    defer allocator.free(rendered);
    try output.appendSlice(allocator, rendered);
}

fn declarationName(node: *const AST.Node) []const u8 {
    const declaration = node.declarationConst() orelse return "";
    return declaration.name;
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

fn identifierPathAnnotation(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.IdentifierPathAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier_path => |*value| value,
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

fn variableAnnotation(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.VariableDeclarationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .variable_declaration => |*value| value,
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

fn forStatementAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.ForStatementAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .for_statement => |*value| value,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
