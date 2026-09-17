// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Reachable Solidity function-call graph construction translated from
//! `FunctionCallGraph.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const CallGraphModule = @import("../ast/call_graph.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const SetOnce = @import("../../libsolutil/set_once.zig");

pub const BuildError = ASTImplementation.AstError ||
    SetOnce.SetOnceError ||
    error{InvalidAst};

const max_ast_depth = 4096;
const Node = CallGraphModule.Node;
const CallGraph = CallGraphModule.CallGraph;

pub const FunctionCallGraphBuilder = struct {
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    contract: *const AST.Node,
    graph: CallGraph,
    current_node: Node = .{ .special = .Entry },
    visit_queue: std.ArrayList(*const AST.Node) = .empty,
    queue_index: usize = 0,
    visited_constants: std.AutoHashMap(*const AST.Node, void),

    fn init(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        contract: *const AST.Node,
        compatibility_ids: CompatibilityIdResolver,
    ) FunctionCallGraphBuilder {
        return .{
            .allocator = allocator,
            .type_provider = type_provider,
            .contract = contract,
            .graph = CallGraph.init(allocator, compatibility_ids),
            .visited_constants = std.AutoHashMap(*const AST.Node, void).init(allocator),
        };
    }

    fn deinitAuxiliary(self: *FunctionCallGraphBuilder) void {
        self.visited_constants.deinit();
        self.visit_queue.deinit(self.allocator);
    }

    pub fn buildCreationGraph(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        contract: *const AST.Node,
        compatibility_ids: CompatibilityIdResolver,
    ) BuildError!CallGraph {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        var builder = FunctionCallGraphBuilder.init(
            allocator,
            type_provider,
            contract,
            compatibility_ids,
        );
        defer builder.deinitAuxiliary();
        errdefer builder.graph.deinit();
        const annotation = try contractAnnotation(contract);
        var base_index = annotation.linearized_base_contracts.len;
        while (base_index != 0) {
            base_index -= 1;
            const base = annotation.linearized_base_contracts[base_index];
            builder.current_node = .{ .special = .Entry };
            for (base.payload.contract_definition.sub_nodes) |member|
                if (member.nodeKind() == .variable_declaration and
                    ASTImplementation.isStateVariable(member) and
                    member.payload.variable_declaration.mutability != .Constant)
                    try builder.visitNode(@constCast(member), 0);

            if (findFunctionKind(base, .Constructor)) |constructor| {
                try builder.functionReferenced(constructor, true);
                builder.current_node = .{ .callable = constructor };
            }
            for (base.payload.contract_definition.base_contracts) |inheritance|
                try builder.visitNode(@constCast(inheritance), 0);
        }
        builder.current_node = .{ .special = .Entry };
        try builder.processQueue();
        return builder.graph;
    }

    pub fn buildDeployedGraph(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        contract: *const AST.Node,
        creation_graph: *const CallGraph,
        compatibility_ids: CompatibilityIdResolver,
    ) BuildError!CallGraph {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        var builder = FunctionCallGraphBuilder.init(
            allocator,
            type_provider,
            contract,
            compatibility_ids,
        );
        defer builder.deinitAuxiliary();
        errdefer builder.graph.deinit();
        const annotation = try contractAnnotation(contract);
        const interface_functions = try ASTImplementation.contractInterfaceFunctionListAlloc(
            type_provider,
            allocator,
            contract,
            true,
        );
        defer allocator.free(interface_functions);
        for (interface_functions) |entry| {
            const declaration = entry.function_type.payload.Function.declaration orelse
                return error.InvalidAst;
            if (declaration.nodeKind() == .function_definition)
                try builder.functionReferenced(declaration, true)
            else if (declaration.nodeKind() != .variable_declaration)
                return error.InvalidAst;
        }
        if (findFirstFunctionKind(annotation.linearized_base_contracts, .Fallback)) |fallback|
            try builder.functionReferenced(fallback, true);
        if (findFirstFunctionKind(annotation.linearized_base_contracts, .Receive)) |receive|
            try builder.functionReferenced(receive, true);

        builder.current_node = .{ .special = .InternalDispatch };
        for (creation_graph.edges.items) |edge| {
            if (!Node.eql(edge.caller, .{ .special = .InternalDispatch })) continue;
            switch (edge.callee) {
                .callable => |callable| try builder.functionReferenced(callable, false),
                .special => return error.InvalidAst,
            }
        }
        builder.current_node = .{ .special = .Entry };
        try builder.processQueue();
        return builder.graph;
    }

    /// Builds the transitive callable graph induced by explicit semantic roots.
    /// The synthetic entry edges identify roots in the returned graph only;
    /// consumers decide whether those roots are executable entry points.
    pub fn buildRootedGraph(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        contract: *const AST.Node,
        roots: []const *const AST.Node,
        compatibility_ids: CompatibilityIdResolver,
    ) BuildError!CallGraph {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        var builder = FunctionCallGraphBuilder.init(
            allocator,
            type_provider,
            contract,
            compatibility_ids,
        );
        defer builder.deinitAuxiliary();
        errdefer builder.graph.deinit();
        for (roots) |root| try builder.functionReferenced(root, true);
        try builder.processQueue();
        return builder.graph;
    }

    fn processQueue(self: *FunctionCallGraphBuilder) BuildError!void {
        if (!Node.eql(self.current_node, .{ .special = .Entry })) return error.InvalidAst;
        while (self.queue_index < self.visit_queue.items.len) {
            const callable = self.visit_queue.items[self.queue_index];
            self.queue_index += 1;
            self.current_node = .{ .callable = callable };
            try self.visitNode(@constCast(callable), 0);
        }
        self.current_node = .{ .special = .Entry };
    }

    fn visitNode(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
        depth: usize,
    ) BuildError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        switch (node.payload) {
            .function_call => try self.visitFunctionCall(node),
            .emit_statement => try self.visitEmitStatement(node),
            .identifier => try self.visitIdentifier(node),
            .member_access => try self.visitMemberAccess(node),
            .binary_operation => try self.visitBinaryOperation(node),
            .unary_operation => try self.visitUnaryOperation(node),
            .modifier_invocation => try self.visitModifierInvocation(node),
            .new_expression => try self.visitNewExpression(node),
            else => {},
        }
        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.allocator);
        try ASTImplementation.appendChildren(self.allocator, &children, node);
        for (children.items) |child| try self.visitNode(@constCast(child), depth + 1);
    }

    fn visitFunctionCall(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
    ) BuildError!void {
        const annotation = try functionCallAnnotation(node);
        if ((try annotation.kind.get()).* != .FunctionCall) return;
        const callee_annotation = try expressionAnnotation(
            node.payload.function_call.expression,
        );
        const type_ref = callee_annotation.type_ref orelse return error.InvalidAst;
        const function = type_ref.asFunction() orelse return error.InvalidAst;
        if (function.kind == .Internal and !callee_annotation.called_directly)
            try self.graph.addEdge(
                self.current_node,
                .{ .special = .InternalDispatch },
            )
        else if (function.kind == .Error) {
            const declaration = function.declaration orelse return error.InvalidAst;
            if (declaration.nodeKind() != .error_definition) return error.InvalidAst;
            try self.graph.addUsedError(declaration);
        }
    }

    fn visitEmitStatement(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
    ) BuildError!void {
        const call = node.payload.emit_statement.event_call;
        if (call.nodeKind() != .function_call) return error.InvalidAst;
        const type_ref = (try expressionAnnotation(
            call.payload.function_call.expression,
        )).type_ref orelse return error.InvalidAst;
        const function = type_ref.asFunction() orelse return error.InvalidAst;
        const declaration = function.declaration orelse return error.InvalidAst;
        if (function.kind != .Event or declaration.nodeKind() != .event_definition)
            return error.InvalidAst;
        try self.graph.addEmittedEvent(declaration);
    }

    fn visitIdentifier(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
    ) BuildError!void {
        const annotation = try identifierAnnotation(node);
        const declaration = annotation.referenced_declaration orelse return error.InvalidAst;
        if (declaration.nodeKind() == .variable_declaration and
            declaration.payload.variable_declaration.mutability == .Constant)
        {
            if (!self.visited_constants.contains(declaration)) {
                try self.visited_constants.put(declaration, {});
                try self.visitNode(@constCast(declaration), 0);
            }
            return;
        }
        if (!isCallable(declaration)) return;
        const function_type = annotation.expression.type_ref orelse return error.InvalidAst;
        const function = function_type.asFunction() orelse return;
        if (function.kind != .Internal) return;
        const lookup = (try annotation.required_lookup.get()).*;
        if (lookup != .Virtual) return error.InvalidAst;
        try self.functionReferenced(
            try ASTImplementation.resolveCallableVirtual(
                self.type_provider,
                declaration,
                self.contract,
                null,
            ),
            annotation.expression.called_directly,
        );
    }

    fn visitMemberAccess(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
    ) BuildError!void {
        const value = node.payload.member_access;
        const owner_type = (try expressionAnnotation(value.expression)).type_ref orelse
            return error.InvalidAst;
        if (owner_type.asMagic()) |magic|
            if (magic.kind == .MetaType and
                (std.mem.eql(u8, value.member_name, "creationCode") or
                    std.mem.eql(u8, value.member_name, "runtimeCode")))
            {
                const argument = magic.type_argument orelse return error.InvalidAst;
                const contract_type = switch (argument.payload) {
                    .Contract => |contract| contract,
                    else => return error.InvalidAst,
                };
                try self.graph.addBytecodeDependency(
                    contract_type.declaration,
                    node,
                    self.current_node,
                );
            };

        const annotation = try memberAccessAnnotation(node);
        const declaration = annotation.referenced_declaration orelse return;
        if (declaration.nodeKind() != .function_definition) return;
        const member_type = annotation.expression.type_ref orelse return error.InvalidAst;
        const function = member_type.asFunction() orelse return;
        if (function.kind != .Internal) return;
        const lookup = (try annotation.required_lookup.get()).*;
        const resolved = switch (lookup) {
            .Static => declaration,
            .Super => blk: {
                const type_type = owner_type.asTypeType() orelse return error.InvalidAst;
                const contract_type = switch (type_type.actual_type.payload) {
                    .Contract => |contract| contract,
                    else => return error.InvalidAst,
                };
                if (!contract_type.is_super) return error.InvalidAst;
                const search_start = (try ASTImplementation.superContract(
                    contract_type.declaration,
                    self.contract,
                )) orelse return error.InvalidAst;
                break :blk try ASTImplementation.resolveCallableVirtual(
                    self.type_provider,
                    declaration,
                    self.contract,
                    search_start,
                );
            },
            .Virtual => return error.InvalidAst,
        };
        try self.functionReferenced(resolved, annotation.expression.called_directly);
    }

    fn visitBinaryOperation(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
    ) BuildError!void {
        if ((try (try binaryOperationAnnotation(
            node,
        )).operation.user_defined_function.get()).*) |function|
            try self.functionReferenced(function, true);
    }

    fn visitUnaryOperation(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
    ) BuildError!void {
        if ((try (try operationAnnotation(node)).user_defined_function.get()).*) |function|
            try self.functionReferenced(function, true);
    }

    fn visitModifierInvocation(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
    ) BuildError!void {
        const name = node.payload.modifier_invocation.modifier_name;
        const declaration = (try identifierPathOrIdentifierDeclaration(name)) orelse
            return error.InvalidAst;
        if (declaration.nodeKind() != .modifier_definition) return;
        const lookup = try identifierPathOrIdentifierLookup(name);
        try self.functionReferenced(
            if (lookup == .Virtual)
                try ASTImplementation.resolveCallableVirtual(
                    self.type_provider,
                    declaration,
                    self.contract,
                    null,
                )
            else if (lookup == .Static)
                declaration
            else
                return error.InvalidAst,
            true,
        );
    }

    fn visitNewExpression(
        self: *FunctionCallGraphBuilder,
        node: *AST.Node,
    ) BuildError!void {
        const type_ref = (try typeNameAnnotation(
            node.payload.new_expression.type_name,
        )).type_ref orelse return error.InvalidAst;
        if (type_ref.category() == .Contract)
            try self.graph.addBytecodeDependency(
                type_ref.payload.Contract.declaration,
                node,
                self.current_node,
            );
    }

    fn functionReferenced(
        self: *FunctionCallGraphBuilder,
        callable: *const AST.Node,
        called_directly: bool,
    ) BuildError!void {
        if (!isCallable(callable)) return error.InvalidAst;
        if (called_directly)
            try self.graph.addEdge(self.current_node, .{ .callable = callable })
        else
            try self.graph.addEdge(
                .{ .special = .InternalDispatch },
                .{ .callable = callable },
            );
        if (!self.graph.hasCaller(.{ .callable = callable })) {
            try self.graph.ensureCaller(.{ .callable = callable });
            try self.visit_queue.append(self.allocator, callable);
        }
    }
};

fn isCallable(node: *const AST.Node) bool {
    return node.nodeKind() == .function_definition or
        node.nodeKind() == .modifier_definition;
}

fn findFunctionKind(contract: *const AST.Node, kind: AST.Token) ?*const AST.Node {
    for (contract.payload.contract_definition.sub_nodes) |member|
        if (member.nodeKind() == .function_definition and
            member.payload.function_definition.kind == kind) return member;
    return null;
}

fn findFirstFunctionKind(
    contracts: AST.NodeList,
    kind: AST.Token,
) ?*const AST.Node {
    for (contracts) |contract|
        if (findFunctionKind(contract, kind)) |function| return function;
    return null;
}

fn contractAnnotation(
    node: *const AST.Node,
) BuildError!*const ASTAnnotations.ContractDefinitionAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => error.InvalidAst,
    };
}

/// Zig equivalent of the diagnostic-only `operator<<(CallGraph::Node)` from
/// the upstream pair. The returned string is owned by `allocator`.
pub fn formatNodeAlloc(
    allocator: std.mem.Allocator,
    node: Node,
) BuildError![]u8 {
    return switch (node) {
        .special => |special| allocator.dupe(
            u8,
            switch (special) {
                .InternalDispatch => "InternalDispatch",
                .Entry => "Entry",
            },
        ),
        .callable => |callable| formatCallableNodeAlloc(allocator, callable),
    };
}

fn formatCallableNodeAlloc(
    allocator: std.mem.Allocator,
    callable: *const AST.Node,
) BuildError![]u8 {
    const callable_data = switch (callable.payload) {
        .function_definition => |*function| &function.callable,
        .modifier_definition => |*modifier| &modifier.callable,
        else => return error.InvalidAst,
    };
    var parameters: std.ArrayList(u8) = .empty;
    defer parameters.deinit(allocator);
    for (callable_data.parameters, 0..) |parameter, index| {
        if (index != 0) try parameters.append(allocator, ',');
        const parameter_type = try TypeBehavior.variableDeclarationType(parameter);
        const rendered = try TypeBehavior.toStringAlloc(allocator, parameter_type, true);
        defer allocator.free(rendered);
        try parameters.appendSlice(allocator, rendered);
    }

    if (callable.nodeKind() == .function_definition and
        callable.payload.function_definition.free)
        return std.fmt.allocPrint(
            allocator,
            "function {s}({s})",
            .{ callable_data.declaration.name, parameters.items },
        );

    const scope = ASTImplementation.scope(callable) orelse return error.InvalidAst;
    if (scope.nodeKind() != .contract_definition) return error.InvalidAst;
    const scope_name = scope.payload.contract_definition.declaration.name;
    return switch (callable.payload) {
        .function_definition => |function| switch (function.kind) {
            .Constructor => std.fmt.allocPrint(allocator, "constructor of {s}", .{scope_name}),
            .Fallback => std.fmt.allocPrint(allocator, "fallback of {s}", .{scope_name}),
            .Receive => std.fmt.allocPrint(allocator, "receive of {s}", .{scope_name}),
            else => std.fmt.allocPrint(
                allocator,
                "function {s}.{s}({s})",
                .{ scope_name, callable_data.declaration.name, parameters.items },
            ),
        },
        .modifier_definition => std.fmt.allocPrint(
            allocator,
            "modifier {s}.{s}",
            .{ scope_name, callable_data.declaration.name },
        ),
        else => error.InvalidAst,
    };
}

fn expressionAnnotation(
    node: *const AST.Node,
) BuildError!*const ASTAnnotations.ExpressionAnnotation {
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
) BuildError!*const ASTAnnotations.IdentifierAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier => |*value| value,
        else => error.InvalidAst,
    };
}

fn memberAccessAnnotation(
    node: *const AST.Node,
) BuildError!*const ASTAnnotations.MemberAccessAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .member_access => |*value| value,
        else => error.InvalidAst,
    };
}

fn binaryOperationAnnotation(
    node: *const AST.Node,
) BuildError!*const ASTAnnotations.BinaryOperationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .binary_operation => |*value| value,
        else => error.InvalidAst,
    };
}

fn operationAnnotation(
    node: *const AST.Node,
) BuildError!*const ASTAnnotations.OperationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .operation => |*value| value,
        else => error.InvalidAst,
    };
}

fn functionCallAnnotation(
    node: *const AST.Node,
) BuildError!*const ASTAnnotations.FunctionCallAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .function_call => |*value| value,
        else => error.InvalidAst,
    };
}

fn typeNameAnnotation(
    node: *const AST.Node,
) BuildError!*const ASTAnnotations.TypeNameAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .type_name => |*value| value,
        else => error.InvalidAst,
    };
}

fn identifierPathOrIdentifierDeclaration(
    node: *const AST.Node,
) BuildError!?*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier_path => |value| value.referenced_declaration,
        .identifier => |value| value.referenced_declaration,
        else => error.InvalidAst,
    };
}

fn identifierPathOrIdentifierLookup(node: *const AST.Node) BuildError!AST.VirtualLookup {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier_path => |value| (try value.required_lookup.get()).*,
        .identifier => |value| (try value.required_lookup.get()).*,
        else => error.InvalidAst,
    };
}
