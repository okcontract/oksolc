// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! NatSpec inheritance analysis translated from `DocStringAnalyser.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Types = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");

pub const AnalyseError = TypeProviderModule.ProviderError ||
    Diagnostics.ReportError ||
    error{InvalidAst};

const max_ast_depth = 4096;

pub const DocStringAnalyser = struct {
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    type_provider: *TypeProviderModule.TypeProvider,

    pub fn init(
        allocator: std.mem.Allocator,
        reporter: *Diagnostics.ErrorReporter,
        type_provider: *TypeProviderModule.TypeProvider,
    ) DocStringAnalyser {
        return .{
            .allocator = allocator,
            .reporter = reporter,
            .type_provider = type_provider,
        };
    }

    pub fn analyseDocStrings(
        self: *DocStringAnalyser,
        tree: *AST.Tree,
        source_unit: *AST.Node,
    ) AnalyseError!bool {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        try self.visitNode(tree, source_unit, 0);
        return watcher.ok();
    }

    fn visitNode(
        self: *DocStringAnalyser,
        tree: *AST.Tree,
        node: *AST.Node,
        depth: usize,
    ) AnalyseError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        const visit_children = switch (node.payload) {
            .function_definition => |function| blk: {
                if (function.kind != .Constructor) {
                    const function_type = try self.type_provider.functionFromDefinition(
                        node,
                        .Internal,
                    );
                    try self.handleCallable(tree, node, &function_type.payload.Function);
                }
                break :blk true;
            },
            .variable_declaration => blk: {
                if (!ASTImplementation.isStateVariable(node) and
                    !ASTImplementation.isFileLevelVariable(node)) break :blk false;
                const getter_type = try self.type_provider.functionFromVariable(node);
                const annotation = try documentedAnnotation(node);
                const bases = try baseFunctions(node);
                if (try self.resolveInheritDoc(node, annotation, bases)) |base|
                    try copyMissingTags(
                        tree,
                        &.{base},
                        annotation,
                        &getter_type.payload.Function,
                    )
                else if (annotation.doc_tags.items.len == 0)
                    try copyMissingTags(
                        tree,
                        bases,
                        annotation,
                        &getter_type.payload.Function,
                    );
                break :blk false;
            },
            .modifier_definition, .event_definition, .error_definition => blk: {
                try self.handleCallable(tree, node, null);
                break :blk true;
            },
            else => true,
        };
        if (!visit_children) return;
        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.allocator);
        try ASTImplementation.appendChildren(self.allocator, &children, node);
        for (children.items) |child| try self.visitNode(tree, @constCast(child), depth + 1);
    }

    fn handleCallable(
        self: *DocStringAnalyser,
        tree: *AST.Tree,
        node: *AST.Node,
        function_type: ?*const Types.FunctionType,
    ) AnalyseError!void {
        const annotation = try documentedAnnotation(node);
        const bases = try baseFunctions(node);
        if (try self.resolveInheritDoc(node, annotation, bases)) |base| {
            try copyMissingTags(tree, &.{base}, annotation, function_type);
        } else if (annotation.doc_tags.items.len == 0 and
            bases.len == 1 and parameterNamesEqual(node, bases[0]))
        {
            try copyMissingTags(tree, bases, annotation, function_type);
        }
    }

    fn resolveInheritDoc(
        self: *DocStringAnalyser,
        node: *const AST.Node,
        annotation: *ASTAnnotations.StructurallyDocumentedAnnotation,
        bases: []const *const AST.Node,
    ) AnalyseError!?*const AST.Node {
        const reference = annotation.inheritdoc_reference orelse return null;
        if (try findBaseCallable(bases, reference, 0)) |callable| return callable;
        const documentation = documentationNode(node) orelse return error.InvalidAst;
        const contract_name = (reference.declarationConst() orelse return error.InvalidAst).name;
        const message = try std.fmt.allocPrint(
            self.allocator,
            "Documentation tag @inheritdoc references contract \"{s}\", but the contract does not contain a function that is overridden by this function.",
            .{contract_name},
        );
        defer self.allocator.free(message);
        try self.reporter.docstringParsingError(
            errorId(4682),
            documentation.location,
            message,
        );
        return null;
    }
};

fn copyMissingTags(
    tree: *AST.Tree,
    base_functions: []const *const AST.Node,
    target: *ASTAnnotations.StructurallyDocumentedAnnotation,
    function_type: ?*const Types.FunctionType,
) AnalyseError!void {
    if (base_functions.len != 1) return;
    const base_function = base_functions[0];
    const source = try documentedAnnotationConst(base_function);
    var index: usize = 0;
    while (index != source.doc_tags.items.len) {
        const tag = source.doc_tags.items[index].name;
        var group_end = index + 1;
        while (group_end != source.doc_tags.items.len and
            std.mem.eql(u8, source.doc_tags.items[group_end].name, tag)) : (group_end += 1)
        {}
        if (std.mem.eql(u8, tag, "inheritdoc") or
            std.mem.startsWith(u8, tag, "custom") or
            hasTag(target.doc_tags.items, tag))
        {
            index = group_end;
            continue;
        }
        for (source.doc_tags.items[index..group_end], 0..) |entry, ordinal| {
            var content = entry.tag.content;
            if (function_type != null and std.mem.eql(u8, tag, "return")) {
                const return_names = function_type.?.return_parameter_names;
                const name_end = firstWhitespace(entry.tag.content);
                const documented_name = if (name_end) |end|
                    entry.tag.content[0..end]
                else
                    entry.tag.content;
                if (return_names.len > ordinal and
                    !std.mem.eql(u8, documented_name, return_names[ordinal]))
                {
                    const base_has_no_name = if (callableReturnParameters(base_function)) |returns|
                        returns.len > ordinal and variableName(returns[ordinal]).len == 0
                    else
                        false;
                    const target_name = return_names[ordinal];
                    const remainder = if (name_end == null or base_has_no_name)
                        entry.tag.content
                    else
                        entry.tag.content[name_end.? + 1 ..];
                    content = if (target_name.len == 0)
                        try tree.ownString(remainder)
                    else
                        try std.fmt.allocPrint(
                            tree.allocator(),
                            "{s} {s}",
                            .{ target_name, remainder },
                        );
                }
            }
            try target.doc_tags.append(tree.allocator(), .{
                .name = entry.name,
                .tag = .{
                    .content = content,
                    .parameter_name = entry.tag.parameter_name,
                },
            });
        }
        index = group_end;
    }
    std.sort.insertion(
        ASTAnnotations.DocTagEntry,
        target.doc_tags.items,
        {},
        docTagLessThan,
    );
}

fn findBaseCallable(
    base_functions: []const *const AST.Node,
    contract_reference: *const AST.Node,
    depth: usize,
) AnalyseError!?*const AST.Node {
    if (depth >= 256) return error.InvalidAst;
    for (base_functions) |candidate| {
        const annotation = try callableAnnotationConst(candidate);
        const contract = annotation.declaration.scopable.contract orelse return error.InvalidAst;
        if (contract == contract_reference) return candidate;
        if (try findBaseCallable(
            annotation.base_functions.items,
            contract_reference,
            depth + 1,
        )) |found|
            return found;
    }
    return null;
}

fn parameterNamesEqual(left: *const AST.Node, right: *const AST.Node) bool {
    const left_parameters = callableParameters(left) orelse return false;
    const right_parameters = callableParameters(right) orelse return false;
    if (left_parameters.len != right_parameters.len) return false;
    for (left_parameters, right_parameters) |left_parameter, right_parameter|
        if (!std.mem.eql(
            u8,
            variableName(left_parameter),
            variableName(right_parameter),
        )) return false;
    return true;
}

fn baseFunctions(node: *const AST.Node) AnalyseError![]const *const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .documented_callable => |*value| value.callable.base_functions.items,
        .variable_declaration => |*value| value.base_functions.items,
        else => error.InvalidAst,
    };
}

fn callableAnnotationConst(
    node: *const AST.Node,
) AnalyseError!*const ASTAnnotations.CallableDeclarationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .documented_callable => |*value| &value.callable,
        else => error.InvalidAst,
    };
}

fn documentedAnnotation(
    node: *AST.Node,
) AnalyseError!*ASTAnnotations.StructurallyDocumentedAnnotation {
    return @constCast(try documentedAnnotationConst(node));
}

fn documentedAnnotationConst(
    node: *const AST.Node,
) AnalyseError!*const ASTAnnotations.StructurallyDocumentedAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .contract_definition => |*value| &value.documented,
        .documented_callable => |*value| &value.documented,
        .variable_declaration => |*value| &value.documented,
        .type_class_definition => |*value| &value.documented,
        else => error.InvalidAst,
    };
}

fn documentationNode(node: *const AST.Node) ?*const AST.Node {
    return switch (node.payload) {
        .contract_definition => |value| value.documentation,
        .function_definition => |value| value.documentation,
        .variable_declaration => |value| value.documentation,
        .modifier_definition => |value| value.documentation,
        .event_definition => |value| value.documentation,
        .error_definition => |value| value.documentation,
        .type_class_definition => |value| value.documentation,
        else => null,
    };
}

fn callableParameters(node: *const AST.Node) ?AST.NodeList {
    const parameters = switch (node.payload) {
        .function_definition => |value| value.callable.parameters,
        .modifier_definition => |value| value.callable.parameters,
        .event_definition => |value| value.callable.parameters,
        .error_definition => |value| value.callable.parameters,
        else => return null,
    };
    if (parameters.nodeKind() != .parameter_list) return null;
    return parameters.payload.parameter_list.parameters;
}

fn callableReturnParameters(node: *const AST.Node) ?AST.NodeList {
    const returns = switch (node.payload) {
        .function_definition => |value| value.callable.return_parameters orelse return null,
        .modifier_definition => |value| value.callable.return_parameters orelse return null,
        .event_definition => |value| value.callable.return_parameters orelse return null,
        .error_definition => |value| value.callable.return_parameters orelse return null,
        else => return null,
    };
    if (returns.nodeKind() != .parameter_list) return null;
    return returns.payload.parameter_list.parameters;
}

fn variableName(node: *const AST.Node) []const u8 {
    return switch (node.payload) {
        .variable_declaration => |value| value.declaration.name,
        else => "",
    };
}

fn hasTag(tags: []const ASTAnnotations.DocTagEntry, name: []const u8) bool {
    for (tags) |entry| if (std.mem.eql(u8, entry.name, name)) return true;
    return false;
}

fn firstWhitespace(content: []const u8) ?usize {
    for (content, 0..) |byte, index|
        if (byte == ' ' or byte == '\t') return index;
    return null;
}

fn docTagLessThan(
    _: void,
    left: ASTAnnotations.DocTagEntry,
    right: ASTAnnotations.DocTagEntry,
) bool {
    return std.mem.order(u8, left.name, right.name) == .lt;
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
