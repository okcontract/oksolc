// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Post-typing static diagnostics translated from `StaticAnalyzer.cpp`.
//!
//! The analyzer owns no AST data. It walks a fully annotated tree, keeps a
//! deterministic source-order use ledger for locals, and emits diagnostics
//! whose semantics do not belong in expression type construction.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const ConstantEvaluator = @import("constant_evaluator.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const SetOnce = @import("../../libsolutil/set_once.zig");

pub const AnalyzeError = ConstantEvaluator.EvaluateError ||
    std.mem.Allocator.Error ||
    Diagnostics.ReportError ||
    SetOnce.SetOnceError ||
    error{InvalidAst};

const max_ast_depth = 4096;

const LocalUse = struct {
    declaration: *const AST.Node,
    count: usize = 0,
};

pub const StaticAnalyzer = struct {
    allocator: std.mem.Allocator,
    tree: *AST.Tree,
    reporter: *Diagnostics.ErrorReporter,
    type_provider: *TypeProviderModule.TypeProvider,
    current_contract: ?*const AST.Node = null,
    current_function: ?*const AST.Node = null,
    constructor: bool = false,
    local_uses: std.ArrayList(LocalUse) = .empty,
    constructor_uses_assembly: std.AutoHashMap(*const AST.Node, bool),

    pub fn init(
        allocator: std.mem.Allocator,
        tree: *AST.Tree,
        reporter: *Diagnostics.ErrorReporter,
        type_provider: *TypeProviderModule.TypeProvider,
    ) StaticAnalyzer {
        return .{
            .allocator = allocator,
            .tree = tree,
            .reporter = reporter,
            .type_provider = type_provider,
            .constructor_uses_assembly = std.AutoHashMap(*const AST.Node, bool).init(allocator),
        };
    }

    pub fn deinit(self: *StaticAnalyzer) void {
        self.constructor_uses_assembly.deinit();
        self.local_uses.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn analyze(self: *StaticAnalyzer, source_unit: *AST.Node) AnalyzeError!bool {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        try self.visitNode(source_unit, 0);
        return watcher.ok();
    }

    fn visitNode(
        self: *StaticAnalyzer,
        node: *AST.Node,
        depth: usize,
    ) AnalyzeError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        const previous_contract = self.current_contract;
        const previous_function = self.current_function;
        const previous_constructor = self.constructor;
        if (node.nodeKind() == .contract_definition) self.current_contract = node;
        if (node.nodeKind() == .function_definition) {
            if (self.current_function != null or self.local_uses.items.len != 0)
                return error.InvalidAst;
            self.current_function = node;
            self.constructor = node.payload.function_definition.kind == .Constructor;
        }

        switch (node.payload) {
            .assignment => try self.visitAssignment(node),
            .variable_declaration => try self.visitVariableDeclaration(node),
            .identifier => try self.visitIdentifier(node),
            .return_statement => try self.visitReturn(node),
            .expression_statement => try self.visitExpressionStatement(node),
            .member_access => try self.visitMemberAccess(node),
            .inline_assembly => try self.visitInlineAssembly(node),
            .binary_operation => try self.visitBinaryOperation(node),
            .function_call => try self.visitFunctionCall(node),
            else => {},
        }

        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.allocator);
        try ASTImplementation.appendChildren(self.allocator, &children, node);
        for (children.items) |child| try self.visitNode(@constCast(child), depth + 1);

        switch (node.payload) {
            .function_definition => try self.endFunctionDefinition(node),
            else => {},
        }

        self.current_contract = previous_contract;
        self.current_function = previous_function;
        self.constructor = previous_constructor;
    }

    fn visitAssignment(self: *StaticAnalyzer, node: *AST.Node) AnalyzeError!void {
        const assignment = node.payload.assignment;
        const lhs_type = (try expressionAnnotation(
            self.tree,
            assignment.left_hand_side,
        )).type_ref orelse return error.InvalidAst;
        const rhs_type = (try expressionAnnotation(
            self.tree,
            assignment.right_hand_side,
        )).type_ref orelse return error.InvalidAst;
        if (lhs_type.asTuple() != null and rhs_type.asTuple() != null)
            try self.checkDoubleStorageAssignment(node, lhs_type, rhs_type);
    }

    fn visitVariableDeclaration(
        self: *StaticAnalyzer,
        node: *AST.Node,
    ) AnalyzeError!void {
        if (self.current_function != null and
            ASTImplementation.isLocalVariable(node) and
            node.payload.variable_declaration.declaration.name.len != 0)
        {
            if (self.findLocalUse(node) == null)
                try self.local_uses.append(self.allocator, .{ .declaration = node });
        }
        const variable = node.payload.variable_declaration;
        if (!ASTImplementation.isStateVariable(node) and
            variable.reference_location != .Storage) return;
        const type_ref = (try variableAnnotation(self.tree, node)).type_ref orelse
            return error.InvalidAst;
        const decomposition = try TypeBehavior.fullDecompositionAlloc(
            self.type_provider,
            self.allocator,
            type_ref,
        );
        defer self.allocator.free(decomposition);
        for (decomposition) |component_type| {
            const bound = TypeBehavior.storageSizeUpperBound(component_type) catch |err| switch (err) {
                error.Overflow => std.math.maxInt(u256),
                else => return error.InvalidAst,
            };
            if (bound < (@as(u256, 1) << 64)) continue;
            const type_name = try TypeBehavior.toStringAlloc(
                self.allocator,
                component_type,
                true,
            );
            defer self.allocator.free(type_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Type {s} covers a large part of storage and thus makes collisions likely. Either use mappings or dynamic arrays and allow their size to be increased only in small quantities per transaction.",
                .{type_name},
            );
            defer self.allocator.free(message);
            try self.reporter.warning(
                errorId(7325),
                if (variable.type_name) |type_node| type_node.location else node.location,
                message,
            );
        }
    }

    fn visitIdentifier(self: *StaticAnalyzer, node: *AST.Node) AnalyzeError!void {
        if (self.current_function == null) return;
        const declaration = (try identifierAnnotation(
            self.tree,
            node,
        )).referenced_declaration orelse return error.InvalidAst;
        self.markUse(declaration);
    }

    fn visitMemberAccess(self: *StaticAnalyzer, node: *AST.Node) AnalyzeError!void {
        const value = node.payload.member_access;
        const owner_type = (try expressionAnnotation(
            self.tree,
            value.expression,
        )).type_ref orelse return error.InvalidAst;
        if (owner_type.asMagic()) |magic| {
            if (magic.kind == .Message and std.mem.eql(u8, value.member_name, "gas"))
                try self.reporter.typeError(
                    errorId(1400),
                    node.location,
                    "\"msg.gas\" has been deprecated in favor of \"gasleft()\"",
                )
            else if (magic.kind == .Block and std.mem.eql(u8, value.member_name, "blockhash"))
                try self.reporter.typeError(
                    errorId(8113),
                    node.location,
                    "\"block.blockhash()\" has been deprecated in favor of \"blockhash()\"",
                )
            else if (magic.kind == .MetaType and
                std.mem.eql(u8, value.member_name, "runtimeCode"))
            {
                const argument = magic.type_argument orelse return error.InvalidAst;
                const contract_type = switch (argument.payload) {
                    .Contract => |contract| contract,
                    else => return error.InvalidAst,
                };
                if (try self.constructorUsesAssembly(contract_type.declaration))
                    try self.reporter.warning(
                        errorId(6417),
                        node.location,
                        "The constructor of the contract (or its base) uses inline assembly. Because of that, it might be that the deployed bytecode is different from type(...).runtimeCode.",
                    );
            } else if (self.current_function != null and
                self.current_function.?.payload.function_definition.kind == .Receive and
                magic.kind == .Message and std.mem.eql(u8, value.member_name, "data"))
                try self.reporter.typeError(
                    errorId(7139),
                    node.location,
                    "\"msg.data\" cannot be used inside of \"receive\" function.",
                );
        }
        const member_type = (try expressionAnnotation(self.tree, node)).type_ref orelse
            return error.InvalidAst;
        if (std.mem.eql(u8, value.member_name, "callcode") and
            member_type.asFunction() != null and
            member_type.asFunction().?.kind == .BareCallCode)
            try self.reporter.typeError(
                errorId(2256),
                node.location,
                "\"callcode\" has been deprecated in favour of \"delegatecall\".",
            );
        if (self.constructor)
            if (resolveOuterUnaryTuples(value.expression)) |expression|
                if (expression.nodeKind() == .identifier and
                    std.mem.eql(u8, expression.payload.identifier.name, "this"))
                    try self.reporter.warning(
                        errorId(5805),
                        expression.location,
                        "\"this\" used in constructor. Note that external functions of a contract cannot be called while it is being constructed.",
                    );
    }

    fn visitInlineAssembly(self: *StaticAnalyzer, node: *AST.Node) AnalyzeError!void {
        if (self.current_function == null) return;
        const annotation = ASTAnnotations.annotation(node) orelse return error.InvalidAst;
        const assembly = switch (annotation.*) {
            .inline_assembly => |*value| value,
            else => return error.InvalidAst,
        };
        for (assembly.external_references.items) |reference|
            if (reference.info.declaration) |declaration| self.markUse(declaration);
    }

    fn endFunctionDefinition(
        self: *StaticAnalyzer,
        node: *const AST.Node,
    ) AnalyzeError!void {
        const function = node.payload.function_definition;
        const body_has_statements = if (function.body) |body|
            body.payload.block.statements.len != 0
        else
            false;
        if (body_has_statements) {
            std.mem.sort(LocalUse, self.local_uses.items, {}, localUseLessThan);
            for (self.local_uses.items) |use| {
                if (use.count != 0) continue;
                const scope = ASTImplementation.scope(use.declaration);
                const parameter = scope != null and
                    (scope.? == node or scope.?.nodeKind() == .try_catch_clause);
                try self.reporter.warning(
                    if (parameter) errorId(5667) else errorId(2072),
                    use.declaration.location,
                    if (parameter)
                        if (scope.?.nodeKind() == .try_catch_clause)
                            "Unused try/catch parameter. Remove or comment out the variable name to silence this warning."
                        else
                            "Unused function parameter. Remove or comment out the variable name to silence this warning."
                    else
                        "Unused local variable.",
                );
            }
        }
        self.local_uses.clearRetainingCapacity();
    }

    fn visitReturn(self: *StaticAnalyzer, node: *const AST.Node) AnalyzeError!void {
        if (node.payload.return_statement.expression == null) return;
        const function = self.current_function orelse return;
        const returns = function.payload.function_definition.callable.return_parameters orelse
            return;
        for (returns.payload.parameter_list.parameters) |parameter| self.markUse(parameter);
    }

    fn visitExpressionStatement(
        self: *StaticAnalyzer,
        node: *AST.Node,
    ) AnalyzeError!void {
        const expression = node.payload.expression_statement.expression;
        if ((try (try expressionAnnotation(self.tree, expression)).is_pure.get()).*)
            try self.reporter.warning(
                errorId(6133),
                node.location,
                "Statement has no effect.",
            );
    }

    fn visitBinaryOperation(self: *StaticAnalyzer, node: *AST.Node) AnalyzeError!void {
        const value = node.payload.binary_operation;
        if (value.operator != .Div and value.operator != .Mod) return;
        const right = try expressionAnnotation(self.tree, value.right);
        if (!(try right.is_pure.get()).*) return;
        var left_value = try ConstantEvaluator.evaluate(
            self.allocator,
            self.reporter,
            self.type_provider,
            value.left,
        );
        defer left_value.deinit();
        if (left_value.type_ref == null) return;
        var right_value = try ConstantEvaluator.evaluate(
            self.allocator,
            self.reporter,
            self.type_provider,
            value.right,
        );
        defer right_value.deinit();
        const rational = right_value.rationalValue() orelse return;
        if (!rational.numerator.isZero()) return;
        try self.reporter.typeError(
            errorId(1211),
            node.location,
            if (value.operator == .Div) "Division by zero." else "Modulo zero.",
        );
    }

    fn visitFunctionCall(self: *StaticAnalyzer, node: *AST.Node) AnalyzeError!void {
        const value = node.payload.function_call;
        const callee_annotation = try expressionAnnotation(self.tree, value.expression);
        const callee_type = callee_annotation.type_ref orelse return error.InvalidAst;
        const function_type = callee_type.asFunction() orelse return;
        if ((function_type.kind == .AddMod or function_type.kind == .MulMod) and
            value.arguments.len == 3)
        {
            const modulus = try expressionAnnotation(self.tree, value.arguments[2]);
            if ((try modulus.is_pure.get()).*) {
                var evaluated = try ConstantEvaluator.evaluate(
                    self.allocator,
                    self.reporter,
                    self.type_provider,
                    value.arguments[2],
                );
                defer evaluated.deinit();
                const rational = evaluated.rationalValue();
                if (rational != null and rational.?.numerator.isZero())
                    try self.reporter.typeError(
                        errorId(4195),
                        node.location,
                        "Arithmetic modulo zero.",
                    );
            }
        }
        if (self.current_contract) |contract| {
            if (contract.payload.contract_definition.contract_kind == .Library and
                function_type.kind == .DelegateCall and function_type.declaration != null and
                ASTImplementation.scope(function_type.declaration.?) == contract)
            {
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(
                    self.allocator,
                    "The function declaration is here:",
                    contract.location,
                );
                try self.reporter.reportWithSecondary(
                    errorId(6700),
                    .TypeError,
                    node.location,
                    &secondary,
                    "Libraries cannot call their own functions externally.",
                );
            }
        }
    }

    fn checkDoubleStorageAssignment(
        self: *StaticAnalyzer,
        assignment_node: *const AST.Node,
        lhs_type: *const Types.Type,
        rhs_type: *const Types.Type,
    ) AnalyzeError!void {
        const lhs = assignment_node.payload.assignment.left_hand_side;
        if (lhs.nodeKind() != .tuple_expression) {
            if (!self.reporter.hasErrors()) return error.InvalidAst;
            return;
        }
        var counts: StorageAssignmentCounts = .{};
        try self.countStorageAssignments(
            lhs,
            lhs_type.asTuple() orelse return error.InvalidAst,
            rhs_type.asTuple() orelse return error.InvalidAst,
            &counts,
            0,
        );
        if (counts.storage_to_storage_copies >= 1 and counts.to_storage_copies >= 2)
            try self.reporter.warning(
                errorId(7238),
                assignment_node.location,
                "This assignment performs two copies to storage. Since storage copies do not first copy to a temporary location, one of them might be overwritten before the second is executed and thus may have unexpected effects. It is safer to perform the copies separately or assign to storage pointers first.",
            );
        if (counts.storage_byte_array_pushes >= 1 and counts.storage_byte_accesses >= 2)
            try self.reporter.warning(
                errorId(7239),
                assignment_node.location,
                "This assignment involves multiple accesses to a bytes array in storage while simultaneously enlarging it. When a bytes array is enlarged, it may transition from short storage layout to long storage layout, which invalidates all references to its elements. It is safer to only enlarge byte arrays in a single operation, one element at a time.",
            );
    }

    fn countStorageAssignments(
        self: *StaticAnalyzer,
        lhs_expression: *const AST.Node,
        lhs_tuple_type: *const Types.TupleType,
        rhs_tuple_type: *const Types.TupleType,
        counts: *StorageAssignmentCounts,
        depth: usize,
    ) AnalyzeError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        const lhs_node = resolveOuterUnaryTuples(lhs_expression) orelse
            return error.InvalidAst;
        const lhs = switch (lhs_node.payload) {
            .tuple_expression => |*tuple| tuple,
            else => return error.InvalidAst,
        };
        if (lhs.components.len != lhs_tuple_type.components.len)
            return error.InvalidAst;
        if (lhs_tuple_type.components.len != rhs_tuple_type.components.len) {
            if (!self.reporter.hasErrors()) return error.InvalidAst;
            return;
        }
        for (lhs_tuple_type.components, 0..) |maybe_component_type, index| {
            const component_type = maybe_component_type orelse continue;
            if (component_type.asReference()) |reference| {
                if (TypeBehavior.dataStoredIn(component_type, .Storage) and
                    !reference.isPointer())
                {
                    counts.to_storage_copies += 1;
                    if (rhs_tuple_type.components[index]) |rhs_component| {
                        if (TypeBehavior.dataStoredIn(rhs_component, .Storage))
                            counts.storage_to_storage_copies += 1;
                    }
                }
                continue;
            }
            if (component_type.asFixedBytes()) |bytes_type| {
                if (bytes_type.bytes != 1) continue;
                const component = resolveOuterUnaryTuples(lhs.components[index]) orelse continue;
                switch (component.payload) {
                    .function_call => |call| {
                        const call_type = (try expressionAnnotation(
                            self.tree,
                            call.expression,
                        )).type_ref orelse return error.InvalidAst;
                        const function = call_type.asFunction() orelse continue;
                        if (function.kind != .ArrayPush) continue;
                        const array_type = (function.selfType() orelse continue).asArray() orelse
                            continue;
                        if (array_type.isByteArray() and
                            TypeBehavior.dataStoredIn(function.selfType().?, .Storage))
                        {
                            counts.storage_byte_accesses += 1;
                            counts.storage_byte_array_pushes += 1;
                        }
                    },
                    .index_access => |access| {
                        const base_type = (try expressionAnnotation(
                            self.tree,
                            access.base,
                        )).type_ref orelse return error.InvalidAst;
                        const array_type = base_type.asArray() orelse continue;
                        if (array_type.isByteArray() and
                            TypeBehavior.dataStoredIn(base_type, .Storage))
                            counts.storage_byte_accesses += 1;
                    },
                    else => {},
                }
                continue;
            }
            const nested_lhs_type = component_type.asTuple() orelse continue;
            const component_node = lhs.components[index] orelse continue;
            if (component_node.nodeKind() != .tuple_expression) continue;
            const rhs_component = rhs_tuple_type.components[index] orelse continue;
            const nested_rhs_type = rhs_component.asTuple() orelse continue;
            try self.countStorageAssignments(
                component_node,
                nested_lhs_type,
                nested_rhs_type,
                counts,
                depth + 1,
            );
        }
    }

    fn constructorUsesAssembly(
        self: *StaticAnalyzer,
        contract: *const AST.Node,
    ) AnalyzeError!bool {
        const annotation = ASTAnnotations.annotationConst(contract) orelse
            return error.InvalidAst;
        const hierarchy = switch (annotation.*) {
            .contract_definition => |value| value.linearized_base_contracts,
            else => return error.InvalidAst,
        };
        for (hierarchy) |base|
            if (try self.constructorDirectlyUsesAssembly(base)) return true;
        return false;
    }

    fn constructorDirectlyUsesAssembly(
        self: *StaticAnalyzer,
        contract: *const AST.Node,
    ) AnalyzeError!bool {
        const entry = try self.constructor_uses_assembly.getOrPut(contract);
        if (entry.found_existing) return entry.value_ptr.*;
        entry.value_ptr.* = false;
        const constructor = ASTImplementation.contractConstructor(contract) orelse return false;
        var pending: std.ArrayList(*const AST.Node) = .empty;
        defer pending.deinit(self.allocator);
        try pending.append(self.allocator, constructor);
        while (pending.pop()) |node| {
            if (node.nodeKind() == .inline_assembly) {
                entry.value_ptr.* = true;
                return true;
            }
            var children: std.ArrayList(*const AST.Node) = .empty;
            defer children.deinit(self.allocator);
            try ASTImplementation.appendChildren(self.allocator, &children, node);
            try pending.appendSlice(self.allocator, children.items);
        }
        return false;
    }

    fn markUse(self: *StaticAnalyzer, declaration: *const AST.Node) void {
        if (self.findLocalUse(declaration)) |use| use.count += 1;
    }

    fn findLocalUse(
        self: *StaticAnalyzer,
        declaration: *const AST.Node,
    ) ?*LocalUse {
        for (self.local_uses.items) |*use|
            if (use.declaration == declaration) return use;
        return null;
    }
};

const StorageAssignmentCounts = struct {
    storage_to_storage_copies: usize = 0,
    to_storage_copies: usize = 0,
    storage_byte_array_pushes: usize = 0,
    storage_byte_accesses: usize = 0,
};

fn localUseLessThan(_: void, lhs: LocalUse, rhs: LocalUse) bool {
    return ASTAnnotations.compatibilityId(lhs.declaration) <
        ASTAnnotations.compatibilityId(rhs.declaration);
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

fn expressionAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) AnalyzeError!*ASTAnnotations.ExpressionAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
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
    tree: *AST.Tree,
    node: *AST.Node,
) AnalyzeError!*ASTAnnotations.IdentifierAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .identifier => |*value| value,
        else => error.InvalidAst,
    };
}

fn variableAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) AnalyzeError!*ASTAnnotations.VariableDeclarationAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .variable_declaration => |*value| value,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
