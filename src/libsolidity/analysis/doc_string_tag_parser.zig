// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! NatSpec tag validation translated from `DocStringTagParser.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const DocStringParser = @import("../parsing/doc_string_parser.zig");
const Common = @import("../../liblangutil/common.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");

pub const ParseError = TypeProviderModule.ProviderError ||
    DocStringParser.ParseError ||
    error{InvalidAst};

const max_ast_depth = 4096;

pub const DocStringTagParser = struct {
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    type_provider: *TypeProviderModule.TypeProvider,

    pub fn init(
        allocator: std.mem.Allocator,
        reporter: *Diagnostics.ErrorReporter,
        type_provider: *TypeProviderModule.TypeProvider,
    ) DocStringTagParser {
        return .{
            .allocator = allocator,
            .reporter = reporter,
            .type_provider = type_provider,
        };
    }

    pub fn parseDocStrings(
        self: *DocStringTagParser,
        tree: *AST.Tree,
        source_unit: *AST.Node,
    ) ParseError!bool {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        try self.visitNode(tree, source_unit, 0);
        return watcher.ok();
    }

    pub fn validateDocStringsUsingTypes(
        self: *DocStringTagParser,
        source_unit: *const AST.Node,
    ) ParseError!bool {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        try self.validateReturns(source_unit, 0);
        return watcher.ok();
    }

    fn visitNode(
        self: *DocStringTagParser,
        tree: *AST.Tree,
        node: *AST.Node,
        depth: usize,
    ) ParseError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        const visit_children = switch (node.payload) {
            .contract_definition => blk: {
                try self.parseNode(
                    tree,
                    node,
                    &.{ "author", "title", "dev", "notice" },
                    "contracts",
                );
                break :blk true;
            },
            .function_definition => |function| blk: {
                if (function.kind == .Constructor)
                    try self.handleConstructor(tree, node)
                else
                    try self.handleCallable(tree, node);
                break :blk true;
            },
            .variable_declaration => blk: {
                if (ASTImplementation.isStateVariable(node)) {
                    if (node.isPublic())
                        try self.parseNode(
                            tree,
                            node,
                            &.{ "dev", "notice", "return", "inheritdoc" },
                            "public state variables",
                        )
                    else
                        try self.parseNode(
                            tree,
                            node,
                            &.{ "dev", "notice", "inheritdoc" },
                            "non-public state variables",
                        );
                } else if (ASTImplementation.isFileLevelVariable(node))
                    try self.parseNode(tree, node, &.{"dev"}, "file-level variables");
                break :blk false;
            },
            .modifier_definition, .event_definition, .error_definition => blk: {
                try self.handleCallable(tree, node);
                break :blk true;
            },
            .inline_assembly => blk: {
                try self.visitInlineAssembly(tree, node);
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

    fn handleConstructor(
        self: *DocStringTagParser,
        tree: *AST.Tree,
        node: *AST.Node,
    ) ParseError!void {
        try self.parseNode(
            tree,
            node,
            &.{ "author", "dev", "notice", "param" },
            "constructor",
        );
        try self.checkParameters(node);
    }

    fn handleCallable(
        self: *DocStringTagParser,
        tree: *AST.Tree,
        node: *AST.Node,
    ) ParseError!void {
        switch (node.nodeKind()) {
            .event_definition => try self.parseNode(
                tree,
                node,
                &.{ "dev", "notice", "param" },
                "events",
            ),
            .error_definition => try self.parseNode(
                tree,
                node,
                &.{ "dev", "notice", "param" },
                "errors",
            ),
            .modifier_definition => try self.parseNode(
                tree,
                node,
                &.{ "dev", "notice", "param", "inheritdoc" },
                "modifiers",
            ),
            .function_definition => try self.parseNode(
                tree,
                node,
                &.{ "dev", "notice", "return", "param", "inheritdoc" },
                "functions",
            ),
            else => return error.InvalidAst,
        }
        try self.checkParameters(node);
    }

    fn parseNode(
        self: *DocStringTagParser,
        tree: *AST.Tree,
        node: *AST.Node,
        valid_tags: []const []const u8,
        node_name: []const u8,
    ) ParseError!void {
        const documentation = documentationNode(node) orelse return;
        const text = switch (documentation.payload) {
            .structured_documentation => |value| value.text,
            else => return error.InvalidAst,
        };
        const annotation = try documentedAnnotation(tree, node);
        annotation.doc_tags = try DocStringParser.parseDocString(
            tree.allocator(),
            text,
            documentation.location,
            self.reporter,
        );
        for (annotation.doc_tags.items) |entry| {
            if (std.mem.eql(u8, entry.name, "custom") or
                std.mem.eql(u8, entry.name, "custom:"))
            {
                try self.reporter.docstringParsingError(
                    errorId(6564),
                    documentation.location,
                    "Custom documentation tag must contain a chosen name, i.e. @custom:mytag.",
                );
            } else if (std.mem.startsWith(u8, entry.name, "custom:") and
                entry.name.len > "custom:".len)
            {
                if (!validCustomTag(entry.name)) {
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Invalid character in custom tag @{s}. Only lowercase letters and \"-\" are permitted.",
                        .{entry.name},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.docstringParsingError(
                        errorId(2968),
                        documentation.location,
                        message,
                    );
                }
            } else if (!containsString(valid_tags, entry.name)) {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Documentation tag @{s} not valid for {s}.",
                    .{ entry.name, node_name },
                );
                defer self.allocator.free(message);
                try self.reporter.docstringParsingError(
                    errorId(6546),
                    documentation.location,
                    message,
                );
            }
        }
    }

    fn checkParameters(
        self: *DocStringTagParser,
        node: *const AST.Node,
    ) ParseError!void {
        const documentation = documentationNode(node) orelse return;
        const annotation = try documentedAnnotationConst(node);
        for (annotation.doc_tags.items) |entry| {
            if (!std.mem.eql(u8, entry.name, "param")) continue;
            if (callableHasParameter(node, entry.tag.parameter_name)) continue;
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Documented parameter \"{s}\" not found in the parameter list of the function.",
                .{entry.tag.parameter_name},
            );
            defer self.allocator.free(message);
            try self.reporter.docstringParsingError(
                errorId(3881),
                documentation.location,
                message,
            );
        }
    }

    fn validateReturns(
        self: *DocStringTagParser,
        node: *const AST.Node,
        depth: usize,
    ) ParseError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        if (documentedAnnotationConstOptional(node)) |annotation| {
            var return_tags_visited: usize = 0;
            for (annotation.doc_tags.items) |entry| {
                if (!std.mem.eql(u8, entry.name, "return")) continue;
                return_tags_visited += 1;
                const return_names: []const []const u8 = switch (node.payload) {
                    .variable_declaration => if (node.isPublic()) blk: {
                        const function_type = try self.type_provider.functionFromVariable(node);
                        break :blk function_type.payload.Function.return_parameter_names;
                    } else continue,
                    .function_definition => blk: {
                        const function_type = try self.type_provider.functionFromDefinition(
                            node,
                            .Internal,
                        );
                        break :blk function_type.payload.Function.return_parameter_names;
                    },
                    else => continue,
                };
                const documentation = documentationNode(node) orelse return error.InvalidAst;
                if (return_tags_visited > return_names.len) {
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Documentation tag \"@return {s}\" exceeds the number of return parameters.",
                        .{entry.tag.content},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.docstringParsingError(
                        errorId(2604),
                        documentation.location,
                        message,
                    );
                } else {
                    const parameter = return_names[return_tags_visited - 1];
                    const first_word = firstWord(entry.tag.content);
                    if (parameter.len != 0 and !std.mem.eql(u8, parameter, first_word)) {
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "Documentation tag \"@return {s}\" does not contain the name of its return parameter.",
                            .{entry.tag.content},
                        );
                        defer self.allocator.free(message);
                        try self.reporter.docstringParsingError(
                            errorId(5856),
                            documentation.location,
                            message,
                        );
                    }
                }
            }
        }
        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.allocator);
        try ASTImplementation.appendChildren(self.allocator, &children, node);
        for (children.items) |child| try self.validateReturns(child, depth + 1);
    }

    fn visitInlineAssembly(
        self: *DocStringTagParser,
        tree: *AST.Tree,
        node: *AST.Node,
    ) ParseError!void {
        const documentation = node.payload.inline_assembly.statement.documentation orelse return;
        var temporary_arena = std.heap.ArenaAllocator.init(self.allocator);
        defer temporary_arena.deinit();
        var temporary_reporter = Diagnostics.ErrorReporter.init(self.allocator);
        defer temporary_reporter.deinit();
        const tags = try DocStringParser.parseDocString(
            temporary_arena.allocator(),
            documentation,
            node.location,
            &temporary_reporter,
        );
        if (temporary_reporter.diagnostics().len != 0) {
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            for (temporary_reporter.diagnostics()) |diagnostic|
                try secondary.append(self.allocator, diagnostic.description, node.location);
            try self.reporter.warningWithSecondary(
                errorId(7828),
                node.location,
                "Inline assembly has invalid NatSpec documentation.",
                &secondary,
            );
        }

        for (tags.items) |entry| {
            if (!std.mem.eql(u8, entry.name, "solidity")) {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Unexpected NatSpec tag \"{s}\" with value \"{s}\" in inline assembly.",
                    .{ entry.name, entry.tag.content },
                );
                defer self.allocator.free(message);
                try self.reporter.warning(errorId(6269), node.location, message);
                continue;
            }
            var seen: std.ArrayList([]const u8) = .empty;
            defer seen.deinit(self.allocator);
            var duplicate_warnings: std.ArrayList([]const u8) = .empty;
            defer duplicate_warnings.deinit(self.allocator);
            var position: usize = 0;
            while (nextWhitespaceSeparated(entry.tag.content, &position)) |word| {
                if (!containsString(seen.items, word)) {
                    try seen.append(self.allocator, word);
                    if (std.mem.eql(u8, word, "memory-safe-assembly")) {
                        const annotation = try inlineAssemblyAnnotation(tree, node);
                        if (annotation.marked_memory_safe)
                            try self.reporter.warning(
                                errorId(8544),
                                node.location,
                                "Inline assembly marked as memory safe using both a NatSpec tag and an assembly block annotation. If you are not concerned with backwards compatibility, only use the assembly block annotation, otherwise only use the NatSpec tag.",
                            );
                        annotation.marked_memory_safe = true;
                        try self.reporter.warning(
                            errorId(2424),
                            node.location,
                            "Natspec memory-safe-assembly special comment for inline assembly is deprecated and scheduled for removal. Use the memory-safe block annotation instead.",
                        );
                    } else {
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "Unexpected value for @solidity tag in inline assembly: {s}",
                            .{word},
                        );
                        defer self.allocator.free(message);
                        try self.reporter.warning(errorId(8787), node.location, message);
                    }
                } else if (!containsString(duplicate_warnings.items, word)) {
                    try duplicate_warnings.append(self.allocator, word);
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Value for @solidity tag in inline assembly specified multiple times: {s}",
                        .{word},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.warning(errorId(4377), node.location, message);
                }
            }
        }
    }
};

fn documentationNode(node: *const AST.Node) ?*AST.Node {
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

fn documentedAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ParseError!*ASTAnnotations.StructurallyDocumentedAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .contract_definition => |*value| &value.documented,
        .documented_callable => |*value| &value.documented,
        .variable_declaration => |*value| &value.documented,
        .type_class_definition => |*value| &value.documented,
        else => error.InvalidAst,
    };
}

fn documentedAnnotationConst(
    node: *const AST.Node,
) ParseError!*const ASTAnnotations.StructurallyDocumentedAnnotation {
    return documentedAnnotationConstOptional(node) orelse error.InvalidAst;
}

fn documentedAnnotationConstOptional(
    node: *const AST.Node,
) ?*const ASTAnnotations.StructurallyDocumentedAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .contract_definition => |*value| &value.documented,
        .documented_callable => |*value| &value.documented,
        .variable_declaration => |*value| &value.documented,
        .type_class_definition => |*value| &value.documented,
        else => null,
    };
}

fn inlineAssemblyAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ParseError!*ASTAnnotations.InlineAssemblyAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .inline_assembly => |*value| value,
        else => error.InvalidAst,
    };
}

fn callableHasParameter(node: *const AST.Node, name: []const u8) bool {
    const callable = switch (node.payload) {
        .function_definition => |value| value.callable,
        .modifier_definition => |value| value.callable,
        .event_definition => |value| value.callable,
        .error_definition => |value| value.callable,
        else => return false,
    };
    for (callable.parameters.payload.parameter_list.parameters) |parameter|
        if (std.mem.eql(
            u8,
            parameter.payload.variable_declaration.declaration.name,
            name,
        )) return true;
    if (callable.return_parameters) |returns|
        for (returns.payload.parameter_list.parameters) |parameter|
            if (std.mem.eql(
                u8,
                parameter.payload.variable_declaration.declaration.name,
                name,
            )) return true;
    return false;
}

fn validCustomTag(name: []const u8) bool {
    const suffix = name["custom:".len..];
    if (suffix.len == 0 or suffix[0] < 'a' or suffix[0] > 'z') return false;
    for (suffix[1..]) |byte|
        if ((byte < 'a' or byte > 'z') and byte != '-') return false;
    return true;
}

fn containsString(values: []const []const u8, needle: []const u8) bool {
    for (values) |value| if (std.mem.eql(u8, value, needle)) return true;
    return false;
}

fn firstWord(content: []const u8) []const u8 {
    for (content, 0..) |byte, index|
        if (byte == ' ' or byte == '\t') return content[0..index];
    return content;
}

fn nextWhitespaceSeparated(content: []const u8, position: *usize) ?[]const u8 {
    while (position.* != content.len and Common.isWhiteSpace(content[position.*]))
        position.* += 1;
    if (position.* == content.len) return null;
    const start = position.*;
    while (position.* != content.len and !Common.isWhiteSpace(content[position.*]))
        position.* += 1;
    return content[start..position.*];
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
