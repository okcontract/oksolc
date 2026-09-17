// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! NatSpec JSON generation translated from `Natspec.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const JSON = @import("../../libsolutil/json.zig");

const Json = JSON.Json;

pub const natspec_version: u32 = 1;
pub const NatspecError = ASTImplementation.AstError || error{InvalidAst};

pub const Natspec = struct {
    pub fn userDocumentation(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        compatibility_ids: CompatibilityIdResolver,
        contract: *const AST.Node,
    ) NatspecError!Json {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        var document: Json = .{ .object = .empty };
        try document.object.put(allocator, "version", .{ .integer = natspec_version });
        try putString(allocator, &document, "kind", "user");
        try document.object.put(allocator, "methods", .{ .object = .empty });

        if (ASTImplementation.contractConstructor(contract)) |constructor| {
            const notice = try extractDocAlloc(
                allocator,
                (try documentedAnnotationConst(constructor)).doc_tags.items,
                "notice",
            );
            if (notice.len != 0) {
                var constructor_doc: Json = .{ .object = .empty };
                try putString(allocator, &constructor_doc, "notice", notice);
                try document.object.getPtr("methods").?.object.put(
                    allocator,
                    "constructor",
                    constructor_doc,
                );
            }
        }

        const contract_notice = try extractDocAlloc(
            allocator,
            (try documentedAnnotationConst(contract)).doc_tags.items,
            "notice",
        );
        if (contract_notice.len != 0)
            try putString(allocator, &document, "notice", contract_notice);

        const functions = try ASTImplementation.contractInterfaceFunctionsAlloc(
            type_provider,
            allocator,
            contract,
            true,
        );
        defer allocator.free(functions);
        for (functions) |entry| {
            const function_type = entry.function_type.payload.Function;
            const declaration = function_type.declaration orelse continue;
            const notice = switch (declaration.nodeKind()) {
                .function_definition, .variable_declaration => try extractDocAlloc(
                    allocator,
                    (try documentedAnnotationConst(declaration)).doc_tags.items,
                    "notice",
                ),
                else => continue,
            };
            if (notice.len == 0) continue;
            const signature = try TypeBehavior.externalSignatureAlloc(
                type_provider,
                allocator,
                function_type,
            );
            var method: Json = .{ .object = .empty };
            try putString(allocator, &method, "notice", notice);
            try document.object.getPtr("methods").?.object.put(
                allocator,
                signature,
                method,
            );
        }

        const events = try uniqueInterfaceEventsAlloc(
            allocator,
            type_provider,
            compatibility_ids,
            contract,
        );
        defer allocator.free(events);
        for (events) |event| {
            const notice = try extractDocAlloc(
                allocator,
                (try documentedAnnotationConst(event)).doc_tags.items,
                "notice",
            );
            if (notice.len == 0) continue;
            const signature = try declarationSignatureAlloc(
                allocator,
                type_provider,
                event,
            );
            const events_object = try ensureObject(allocator, &document, "events");
            var event_doc: Json = .{ .object = .empty };
            try putString(allocator, &event_doc, "notice", notice);
            try events_object.object.put(allocator, signature, event_doc);
        }

        const errors = try ASTImplementation.contractInterfaceErrorsAlloc(
            allocator,
            contract,
            true,
        );
        defer allocator.free(errors);
        sortNodesByCompatibilityId(compatibility_ids, errors);
        for (errors) |error_node| {
            const notice = try extractDocAlloc(
                allocator,
                (try documentedAnnotationConst(error_node)).doc_tags.items,
                "notice",
            );
            if (notice.len == 0) continue;
            const signature = try declarationSignatureAlloc(
                allocator,
                type_provider,
                error_node,
            );
            const errors_object = try ensureObject(allocator, &document, "errors");
            const array = try ensureArray(allocator, errors_object, signature);
            var error_doc: Json = .{ .object = .empty };
            try putString(allocator, &error_doc, "notice", notice);
            try array.array.append(error_doc);
        }
        return document;
    }

    pub fn devDocumentation(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        compatibility_ids: CompatibilityIdResolver,
        contract: *const AST.Node,
    ) NatspecError!Json {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        const contract_tags = (try documentedAnnotationConst(contract)).doc_tags.items;
        var document = try extractCustomDoc(allocator, contract_tags);
        try document.object.put(allocator, "version", .{ .integer = natspec_version });
        try putString(allocator, &document, "kind", "dev");
        const author = try extractDocAlloc(allocator, contract_tags, "author");
        if (author.len != 0) try putString(allocator, &document, "author", author);
        const title = try extractDocAlloc(allocator, contract_tags, "title");
        if (title.len != 0) try putString(allocator, &document, "title", title);
        const details = try extractDocAlloc(allocator, contract_tags, "dev");
        if (details.len != 0) try putString(allocator, &document, "details", details);
        try document.object.put(allocator, "methods", .{ .object = .empty });

        if (ASTImplementation.contractConstructor(contract)) |constructor| {
            const constructor_doc = try devTags(
                allocator,
                (try documentedAnnotationConst(constructor)).doc_tags.items,
            );
            if (!jsonObjectEmpty(constructor_doc))
                try document.object.getPtr("methods").?.object.put(
                    allocator,
                    "constructor",
                    constructor_doc,
                );
        }

        const functions = try ASTImplementation.contractInterfaceFunctionsAlloc(
            type_provider,
            allocator,
            contract,
            true,
        );
        defer allocator.free(functions);
        for (functions) |entry| {
            const function_type = entry.function_type.payload.Function;
            const declaration = function_type.declaration orelse continue;
            if (declaration.nodeKind() != .function_definition) continue;
            const tags = (try documentedAnnotationConst(declaration)).doc_tags.items;
            var method = try devTags(allocator, tags);
            const return_docs = try extractReturnParameterDocs(
                allocator,
                tags,
                function_type.return_parameter_names,
            );
            if (!jsonObjectEmpty(return_docs))
                try method.object.put(allocator, "returns", return_docs);
            if (jsonObjectEmpty(method)) continue;
            const signature = try TypeBehavior.externalSignatureAlloc(
                type_provider,
                allocator,
                function_type,
            );
            try document.object.getPtr("methods").?.object.put(
                allocator,
                signature,
                method,
            );
        }

        for (contract.payload.contract_definition.sub_nodes) |variable| {
            if (variable.nodeKind() != .variable_declaration or
                !ASTImplementation.isStateVariable(variable)) continue;
            const name = variable.payload.variable_declaration.declaration.name;
            const tags = (try documentedAnnotationConst(variable)).doc_tags.items;
            const base_doc = try devTags(allocator, tags);
            if (!jsonObjectEmpty(base_doc)) {
                const state = try ensureObject(allocator, &document, "stateVariables");
                try state.object.put(allocator, name, base_doc);
            }
            const state = if (document.object.getPtr("stateVariables")) |existing|
                existing
            else
                null;
            if (countTag(tags, "return") == 1) {
                const return_doc = try extractDocAlloc(allocator, tags, "return");
                if (return_doc.len != 0) {
                    const variables = state orelse try ensureObject(
                        allocator,
                        &document,
                        "stateVariables",
                    );
                    const variable_doc = try ensureObject(allocator, variables, name);
                    try putString(allocator, variable_doc, "return", return_doc);
                }
            }
            if (variable.isPublic()) {
                const getter = try type_provider.functionFromVariable(variable);
                const return_docs = try extractReturnParameterDocs(
                    allocator,
                    tags,
                    getter.payload.Function.return_parameter_names,
                );
                if (!jsonObjectEmpty(return_docs)) {
                    const variables = state orelse try ensureObject(
                        allocator,
                        &document,
                        "stateVariables",
                    );
                    const variable_doc = try ensureObject(allocator, variables, name);
                    try variable_doc.object.put(allocator, "returns", return_docs);
                }
            }
        }

        const events = try uniqueInterfaceEventsAlloc(
            allocator,
            type_provider,
            compatibility_ids,
            contract,
        );
        defer allocator.free(events);
        for (events) |event| {
            const event_doc = try devTags(
                allocator,
                (try documentedAnnotationConst(event)).doc_tags.items,
            );
            if (jsonObjectEmpty(event_doc)) continue;
            const signature = try declarationSignatureAlloc(
                allocator,
                type_provider,
                event,
            );
            const events_object = try ensureObject(allocator, &document, "events");
            try events_object.object.put(allocator, signature, event_doc);
        }

        const errors = try ASTImplementation.contractInterfaceErrorsAlloc(
            allocator,
            contract,
            true,
        );
        defer allocator.free(errors);
        sortNodesByCompatibilityId(compatibility_ids, errors);
        for (errors) |error_node| {
            const error_doc = try devTags(
                allocator,
                (try documentedAnnotationConst(error_node)).doc_tags.items,
            );
            if (jsonObjectEmpty(error_doc)) continue;
            const signature = try declarationSignatureAlloc(
                allocator,
                type_provider,
                error_node,
            );
            const errors_object = try ensureObject(allocator, &document, "errors");
            const array = try ensureArray(allocator, errors_object, signature);
            try array.array.append(error_doc);
        }
        return document;
    }
};

fn extractReturnParameterDocs(
    allocator: std.mem.Allocator,
    tags: []const ASTAnnotations.DocTagEntry,
    return_parameter_names: []const []const u8,
) NatspecError!Json {
    var result: Json = .{ .object = .empty };
    if (return_parameter_names.len == 0) return result;
    var ordinal: usize = 0;
    for (tags) |entry| {
        if (!std.mem.eql(u8, entry.name, "return")) continue;
        if (ordinal >= return_parameter_names.len) return error.InvalidAst;
        var parameter_name = return_parameter_names[ordinal];
        var content = entry.tag.content;
        if (parameter_name.len == 0) {
            parameter_name = try std.fmt.allocPrint(allocator, "_{d}", .{ordinal});
        } else if (firstWhitespace(content)) |name_end| {
            if (!std.mem.eql(u8, content[0..name_end], parameter_name))
                return error.InvalidAst;
            content = content[name_end + 1 ..];
        } else if (!std.mem.eql(u8, content, parameter_name)) {
            return error.InvalidAst;
        }
        try putString(allocator, &result, parameter_name, content);
        ordinal += 1;
    }
    return result;
}

fn extractDocAlloc(
    allocator: std.mem.Allocator,
    tags: []const ASTAnnotations.DocTagEntry,
    name: []const u8,
) std.mem.Allocator.Error![]const u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (tags) |entry|
        if (std.mem.eql(u8, entry.name, name))
            try output.appendSlice(allocator, entry.tag.content);
    return output.toOwnedSlice(allocator);
}

fn extractCustomDoc(
    allocator: std.mem.Allocator,
    tags: []const ASTAnnotations.DocTagEntry,
) std.mem.Allocator.Error!Json {
    var result: Json = .{ .object = .empty };
    var index: usize = 0;
    while (index != tags.len) {
        const name = tags[index].name;
        var group_end = index + 1;
        while (group_end != tags.len and
            std.mem.eql(u8, tags[group_end].name, name)) : (group_end += 1)
        {}
        if (std.mem.startsWith(u8, name, "custom")) {
            var content: std.ArrayList(u8) = .empty;
            for (tags[index..group_end]) |entry|
                try content.appendSlice(allocator, entry.tag.content);
            try putString(allocator, &result, name, try content.toOwnedSlice(allocator));
        }
        index = group_end;
    }
    return result;
}

fn devTags(
    allocator: std.mem.Allocator,
    tags: []const ASTAnnotations.DocTagEntry,
) NatspecError!Json {
    var result = try extractCustomDoc(allocator, tags);
    const details = try extractDocAlloc(allocator, tags, "dev");
    if (details.len != 0) try putString(allocator, &result, "details", details);
    const author = try extractDocAlloc(allocator, tags, "author");
    if (author.len != 0) try putString(allocator, &result, "author", author);
    var parameters: Json = .{ .object = .empty };
    for (tags) |entry|
        if (std.mem.eql(u8, entry.name, "param"))
            try putString(
                allocator,
                &parameters,
                entry.tag.parameter_name,
                entry.tag.content,
            );
    if (!jsonObjectEmpty(parameters))
        try result.object.put(allocator, "params", parameters);
    return result;
}

const EventEntry = struct {
    signature: []const u8,
    event: ?*const AST.Node,
};

fn uniqueInterfaceEventsAlloc(
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    contract: *const AST.Node,
) NatspecError![]*const AST.Node {
    var selected: std.ArrayList(EventEntry) = .empty;
    defer selected.deinit(allocator);
    const defined = try ASTImplementation.contractDefinedInterfaceEventsAlloc(
        type_provider,
        allocator,
        contract,
    );
    defer allocator.free(defined);
    for (defined) |event| {
        const signature = try declarationSignatureAlloc(allocator, type_provider, event);
        if (findEventEntry(selected.items, signature) == null)
            try selected.append(allocator, .{ .signature = signature, .event = event });
    }

    var used_entries: std.ArrayList(EventEntry) = .empty;
    defer used_entries.deinit(allocator);
    const used = try ASTImplementation.contractUsedInterfaceEventsAlloc(allocator, contract);
    defer allocator.free(used);
    sortNodesByCompatibilityId(compatibility_ids, used);
    for (used) |event| {
        const signature = try declarationSignatureAlloc(allocator, type_provider, event);
        if (findEventEntryMutable(used_entries.items, signature)) |existing|
            existing.event = null
        else
            try used_entries.append(allocator, .{ .signature = signature, .event = event });
    }
    for (used_entries.items) |entry| {
        const event = entry.event orelse continue;
        if (findEventEntry(selected.items, entry.signature) == null)
            try selected.append(allocator, .{ .signature = entry.signature, .event = event });
    }
    std.sort.insertion(EventEntry, selected.items, {}, struct {
        fn lessThan(_: void, left: EventEntry, right: EventEntry) bool {
            return std.mem.order(u8, left.signature, right.signature) == .lt;
        }
    }.lessThan);
    const result = try allocator.alloc(*const AST.Node, selected.items.len);
    for (selected.items, result) |entry, *target| target.* = entry.event.?;
    return result;
}

fn sortNodesByCompatibilityId(
    compatibility_ids: CompatibilityIdResolver,
    nodes: []*const AST.Node,
) void {
    std.mem.sort(*const AST.Node, nodes, compatibility_ids, struct {
        fn lessThan(
            resolver: CompatibilityIdResolver,
            left: *const AST.Node,
            right: *const AST.Node,
        ) bool {
            return resolver.id(left).? < resolver.id(right).?;
        }
    }.lessThan);
}

fn declarationSignatureAlloc(
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    declaration: *const AST.Node,
) NatspecError![]u8 {
    const type_ref: *const Types.Type = switch (declaration.nodeKind()) {
        .function_definition => try type_provider.functionFromDefinition(declaration, .Internal),
        .variable_declaration => try type_provider.functionFromVariable(declaration),
        .event_definition => try type_provider.functionFromEvent(declaration),
        .error_definition => try type_provider.functionFromError(declaration),
        else => return error.InvalidAst,
    };
    return TypeBehavior.externalSignatureAlloc(
        type_provider,
        allocator,
        type_ref.payload.Function,
    );
}

fn documentedAnnotationConst(
    node: *const AST.Node,
) NatspecError!*const ASTAnnotations.StructurallyDocumentedAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .contract_definition => |*value| &value.documented,
        .documented_callable => |*value| &value.documented,
        .variable_declaration => |*value| &value.documented,
        .type_class_definition => |*value| &value.documented,
        else => error.InvalidAst,
    };
}

fn ensureObject(
    allocator: std.mem.Allocator,
    parent: *Json,
    key: []const u8,
) NatspecError!*Json {
    if (parent.object.getPtr(key)) |existing| {
        if (existing.* != .object) return error.InvalidAst;
        return existing;
    }
    try parent.object.put(allocator, key, .{ .object = .empty });
    return parent.object.getPtr(key).?;
}

fn ensureArray(
    allocator: std.mem.Allocator,
    parent: *Json,
    key: []const u8,
) NatspecError!*Json {
    if (parent.object.getPtr(key)) |existing| {
        if (existing.* != .array) return error.InvalidAst;
        return existing;
    }
    try parent.object.put(allocator, key, .{ .array = std.json.Array.init(allocator) });
    return parent.object.getPtr(key).?;
}

fn putString(
    allocator: std.mem.Allocator,
    object: *Json,
    key: []const u8,
    value: []const u8,
) std.mem.Allocator.Error!void {
    try object.object.put(allocator, key, .{ .string = value });
}

fn jsonObjectEmpty(value: Json) bool {
    return switch (value) {
        .object => |object| object.count() == 0,
        else => true,
    };
}

fn countTag(tags: []const ASTAnnotations.DocTagEntry, name: []const u8) usize {
    var count: usize = 0;
    for (tags) |entry| if (std.mem.eql(u8, entry.name, name)) {
        count += 1;
    };
    return count;
}

fn firstWhitespace(content: []const u8) ?usize {
    for (content, 0..) |byte, index|
        if (byte == ' ' or byte == '\t') return index;
    return null;
}

fn findEventEntry(entries: []const EventEntry, signature: []const u8) ?*const EventEntry {
    for (entries) |*entry|
        if (std.mem.eql(u8, entry.signature, signature)) return entry;
    return null;
}

fn findEventEntryMutable(entries: []EventEntry, signature: []const u8) ?*EventEntry {
    for (entries) |*entry|
        if (std.mem.eql(u8, entry.signature, signature)) return entry;
    return null;
}
