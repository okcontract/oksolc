// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Immutable write-context validation translated from `ImmutableValidator.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");

pub const AnalyzeError = std.mem.Allocator.Error ||
    Diagnostics.ReportError ||
    error{InvalidAst};

const max_ast_depth = 4096;

pub const ImmutableValidator = struct {
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    most_derived_contract: *const AST.Node,

    pub fn init(
        allocator: std.mem.Allocator,
        reporter: *Diagnostics.ErrorReporter,
        most_derived_contract: *const AST.Node,
    ) ImmutableValidator {
        return .{
            .allocator = allocator,
            .reporter = reporter,
            .most_derived_contract = most_derived_contract,
        };
    }

    pub fn analyze(self: *ImmutableValidator) AnalyzeError!bool {
        if (self.most_derived_contract.nodeKind() != .contract_definition)
            return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        const annotation = try contractAnnotation(self.most_derived_contract);
        var base_index = annotation.linearized_base_contracts.len;
        while (base_index != 0) {
            base_index -= 1;
            const contract = annotation.linearized_base_contracts[base_index];
            for (contract.payload.contract_definition.sub_nodes) |member|
                switch (member.nodeKind()) {
                    .function_definition => {
                        if (member.payload.function_definition.kind != .Constructor)
                            try self.visitNode(@constCast(member), 0);
                    },
                    .modifier_definition => try self.visitNode(@constCast(member), 0),
                    else => {},
                };
        }
        return watcher.ok();
    }

    fn visitNode(
        self: *ImmutableValidator,
        node: *AST.Node,
        depth: usize,
    ) AnalyzeError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.allocator);
        try ASTImplementation.appendChildren(self.allocator, &children, node);
        for (children.items) |child| try self.visitNode(@constCast(child), depth + 1);
        switch (node.nodeKind()) {
            .identifier => try self.analyzeVariableReference(
                (try identifierAnnotation(node)).referenced_declaration,
                node,
                (try identifierAnnotation(node)).expression.will_be_written_to,
            ),
            .member_access => try self.analyzeVariableReference(
                (try memberAccessAnnotation(node)).referenced_declaration,
                node,
                (try memberAccessAnnotation(node)).expression.will_be_written_to,
            ),
            else => {},
        }
    }

    fn analyzeVariableReference(
        self: *ImmutableValidator,
        reference: ?*const AST.Node,
        expression: *const AST.Node,
        will_be_written_to: bool,
    ) Diagnostics.ReportError!void {
        const variable = reference orelse return;
        if (variable.nodeKind() != .variable_declaration or
            !ASTImplementation.isStateVariable(variable) or
            variable.payload.variable_declaration.mutability != .Immutable or
            !will_be_written_to) return;
        try self.reporter.typeError(
            errorId(1581),
            expression.location,
            "Cannot write to immutable here: Immutable variables can only be initialized inline or assigned directly in the constructor.",
        );
    }
};

fn contractAnnotation(
    node: *const AST.Node,
) AnalyzeError!*const ASTAnnotations.ContractDefinitionAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => error.InvalidAst,
    };
}

fn identifierAnnotation(
    node: *const AST.Node,
) AnalyzeError!*const ASTAnnotations.IdentifierAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier => |*value| value,
        else => error.InvalidAst,
    };
}

fn memberAccessAnnotation(
    node: *const AST.Node,
) AnalyzeError!*const ASTAnnotations.MemberAccessAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .member_access => |*value| value,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
