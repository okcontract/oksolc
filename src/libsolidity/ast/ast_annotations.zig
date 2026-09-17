// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Semantic side data translated from `ASTAnnotations.h`.
//!
//! Semantic revisions own annotation unions in a side table keyed by stable
//! `NodeRef`. Syntax trees retain only a stable binding context, so the same
//! immutable nodes can participate in successive semantic revisions.

const std = @import("std");
const AST = @import("ast.zig");
const Types = @import("types.zig");
const Enums = @import("ast_enums.zig");
const Features = @import("experimental_features.zig");
const CallGraph = @import("call_graph.zig");
const YulAST = @import("../../libyul/ast.zig");
const YulAnalysis = @import("../../libyul/asm_analysis_info.zig");
const SetOnce = @import("../../libsolutil/set_once.zig").SetOnce;
const CompatibilityIds = @import("../../incremental/compatibility_ids.zig");

pub const TypeRef = *const Types.Type;
pub const YulIdentifierRef = *const YulAST.Identifier;
pub const YulAnalysisInfoRef = *YulAnalysis.AsmAnalysisInfo;
pub const CallGraphRef = *const CallGraph.CallGraph;

pub const DocTag = struct {
    content: []const u8,
    parameter_name: []const u8 = "",
};

pub const DocTagEntry = struct {
    name: []const u8,
    tag: DocTag,
};

pub const StructurallyDocumentedAnnotation = struct {
    /// Kept as a stable sorted list by the docstring analyzer; duplicate names
    /// are allowed like `std::multimap`.
    doc_tags: std.ArrayList(DocTagEntry) = .empty,
    inheritdoc_reference: ?*const AST.Node = null,
};

pub const ScopableAnnotation = struct {
    scope: ?*const AST.Node = null,
    contract: ?*const AST.Node = null,
};

pub const DeclarationAnnotation = struct {
    scopable: ScopableAnnotation = .{},
};

pub const ExportedSymbol = struct {
    name: []const u8,
    declarations: AST.NodeList,
};

pub const SourceUnitAnnotation = struct {
    path: SetOnce([]const u8) = .{},
    exported_symbols: SetOnce([]const ExportedSymbol) = .{},
    experimental_features: std.ArrayList(Features.ExperimentalFeature) = .empty,
    use_abi_coder_v2: SetOnce(bool) = .{},
};

pub const ImportAnnotation = struct {
    declaration: DeclarationAnnotation = .{},
    absolute_path: SetOnce([]const u8) = .{},
    source_unit: ?*const AST.Node = null,
};

pub const TypeDeclarationAnnotation = struct {
    declaration: DeclarationAnnotation = .{},
    canonical_name: SetOnce([]const u8) = .{},
};

pub const StructDeclarationAnnotation = struct {
    type_declaration: TypeDeclarationAnnotation = .{},
    recursive: ?bool = null,
    contains_nested_mapping: ?bool = null,
};

pub const BaseConstructorArgument = struct {
    function: *const AST.Node,
    argument_node: *const AST.Node,
};

pub const ContractDependency = struct {
    contract: *const AST.Node,
    referencing_node: *const AST.Node,
};

pub const InternalFunctionId = struct {
    function: *const AST.Node,
    id: u64,
};

pub const ContractDefinitionAnnotation = struct {
    type_declaration: TypeDeclarationAnnotation = .{},
    documented: StructurallyDocumentedAnnotation = .{},
    unimplemented_declarations: ?AST.NodeList = null,
    linearized_base_contracts: AST.NodeList = &.{},
    base_constructor_arguments: std.ArrayList(BaseConstructorArgument) = .empty,
    creation_call_graph: SetOnce(CallGraphRef) = .{},
    deployed_call_graph: SetOnce(CallGraphRef) = .{},
    /// Arena-owned event and error lists merged from the creation and deployed
    /// call graphs for analyzed-AST and ABI output.
    interface_events: std.ArrayList(*const AST.Node) = .empty,
    interface_errors: std.ArrayList(*const AST.Node) = .empty,
    contract_dependencies: std.ArrayList(ContractDependency) = .empty,
    internal_function_ids: std.ArrayList(InternalFunctionId) = .empty,
};

pub const StorageLayoutSpecifierAnnotation = struct {
    base_slot: SetOnce(u256) = .{},
};

pub const CallableDeclarationAnnotation = struct {
    declaration: DeclarationAnnotation = .{},
    base_functions: std.ArrayList(*const AST.Node) = .empty,
    /// Mirrors the `VariableScope` mixin. Buffers use the owning syntax
    /// tree's arena and therefore require no independent teardown.
    local_variables: std.ArrayList(*const AST.Node) = .empty,
};

pub const DocumentedCallableAnnotation = struct {
    callable: CallableDeclarationAnnotation = .{},
    documented: StructurallyDocumentedAnnotation = .{},
};

pub const VariableDeclarationAnnotation = struct {
    declaration: DeclarationAnnotation = .{},
    documented: StructurallyDocumentedAnnotation = .{},
    type_ref: ?TypeRef = null,
    base_functions: std.ArrayList(*const AST.Node) = .empty,
};

pub const InlineAssemblyExternalIdentifierInfo = struct {
    declaration: ?*const AST.Node = null,
    suffix: []const u8 = "",
    value_size: usize = std.math.maxInt(usize),
};

pub const InlineAssemblyExternalReference = struct {
    identifier: YulIdentifierRef,
    info: InlineAssemblyExternalIdentifierInfo,
};

pub const InlineAssemblyAnnotation = struct {
    external_references: std.ArrayList(InlineAssemblyExternalReference) = .empty,
    /// The analysis object and all of its maps/scopes use the Solidity tree's
    /// arena. This is the Zig equivalent of the upstream shared ownership:
    /// syntax and analysis state are released together by `Tree.deinit`.
    analysis_info: ?YulAnalysisInfoRef = null,
    marked_memory_safe: bool = false,
    has_memory_effects: SetOnce(bool) = .{},

    pub fn createAnalysisInfo(
        self: *InlineAssemblyAnnotation,
        tree: *AST.Tree,
    ) std.mem.Allocator.Error!*YulAnalysis.AsmAnalysisInfo {
        std.debug.assert(self.analysis_info == null);
        const result = try tree.allocator().create(YulAnalysis.AsmAnalysisInfo);
        result.* = YulAnalysis.AsmAnalysisInfo.init(tree.allocator());
        self.analysis_info = result;
        return result;
    }
};

pub const ReturnAnnotation = struct {
    function_return_parameters: ?*const AST.Node = null,
    function: ?*const AST.Node = null,
};

pub const TypeNameAnnotation = struct {
    type_ref: ?TypeRef = null,
};

pub const IdentifierPathAnnotation = struct {
    referenced_declaration: ?*const AST.Node = null,
    required_lookup: SetOnce(Enums.VirtualLookup) = .{},
    path_declarations: std.ArrayList(*const AST.Node) = .empty,
};

pub const ExpressionAnnotation = struct {
    type_ref: ?TypeRef = null,
    is_constant: SetOnce(bool) = .{},
    is_pure: SetOnce(bool) = .{},
    is_lvalue: SetOnce(bool) = .{},
    will_be_written_to: bool = false,
    arguments: ?Enums.FuncCallArguments = null,
    called_directly: bool = false,
};

pub const IdentifierAnnotation = struct {
    expression: ExpressionAnnotation = .{},
    referenced_declaration: ?*const AST.Node = null,
    required_lookup: SetOnce(Enums.VirtualLookup) = .{},
    candidate_declarations: std.ArrayList(*const AST.Node) = .empty,
    overloaded_declarations: std.ArrayList(*const AST.Node) = .empty,
};

pub const MemberAccessAnnotation = struct {
    expression: ExpressionAnnotation = .{},
    referenced_declaration: ?*const AST.Node = null,
    required_lookup: SetOnce(Enums.VirtualLookup) = .{},
};

pub const OperationAnnotation = struct {
    expression: ExpressionAnnotation = .{},
    user_defined_function: SetOnce(?*const AST.Node) = .{},
};

pub const BinaryOperationAnnotation = struct {
    operation: OperationAnnotation = .{},
    common_type: ?TypeRef = null,
};

pub const FunctionCallKind = enum(c_int) {
    FunctionCall,
    TypeConversion,
    StructConstructorCall,
};

pub const FunctionCallAnnotation = struct {
    expression: ExpressionAnnotation = .{},
    kind: SetOnce(FunctionCallKind) = .{},
    try_call: bool = false,
};

pub const BlockAnnotation = struct { scopable: ScopableAnnotation = .{} };
pub const TryCatchClauseAnnotation = struct { scopable: ScopableAnnotation = .{} };
pub const ForStatementAnnotation = struct {
    scopable: ScopableAnnotation = .{},
    is_simple_counter_loop: SetOnce(bool) = .{},
};
pub const ForAllQuantifierAnnotation = struct { scopable: ScopableAnnotation = .{} };

pub const Annotation = union(enum) {
    base: void,
    source_unit: SourceUnitAnnotation,
    declaration: DeclarationAnnotation,
    import: ImportAnnotation,
    type_declaration: TypeDeclarationAnnotation,
    struct_declaration: StructDeclarationAnnotation,
    contract_definition: ContractDefinitionAnnotation,
    storage_layout_specifier: StorageLayoutSpecifierAnnotation,
    callable_declaration: CallableDeclarationAnnotation,
    documented_callable: DocumentedCallableAnnotation,
    variable_declaration: VariableDeclarationAnnotation,
    statement: void,
    inline_assembly: InlineAssemblyAnnotation,
    block: BlockAnnotation,
    try_catch_clause: TryCatchClauseAnnotation,
    for_statement: ForStatementAnnotation,
    return_statement: ReturnAnnotation,
    type_name: TypeNameAnnotation,
    identifier_path: IdentifierPathAnnotation,
    expression: ExpressionAnnotation,
    identifier: IdentifierAnnotation,
    member_access: MemberAccessAnnotation,
    operation: OperationAnnotation,
    binary_operation: BinaryOperationAnnotation,
    function_call: FunctionCallAnnotation,
    type_class_definition: struct {
        type_declaration: TypeDeclarationAnnotation = .{},
        documented: StructurallyDocumentedAnnotation = .{},
    },
    for_all_quantifier: ForAllQuantifierAnnotation,
};

const AnnotationEntry = struct {
    node: *AST.Node,
    annotation: *Annotation,
};

/// Revision-owned semantic side data. The arena state is separately allocated
/// so table moves never invalidate allocator context pointers.
pub const AnnotationTable = struct {
    backing_allocator: std.mem.Allocator,
    arena_state: *std.heap.ArenaAllocator,
    entries: std.AutoHashMapUnmanaged(AST.NodeRef, AnnotationEntry) = .empty,
    bound_contexts: std.ArrayList(*AST.SemanticContext) = .empty,
    parent: ?*const AnnotationTable = null,
    masked_sources: ?std.DynamicBitSetUnmanaged = null,
    compatibility_ids: ?*const CompatibilityIds.CompatibilityIdProjection = null,

    pub fn create(
        backing_allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error!*AnnotationTable {
        const table = try backing_allocator.create(AnnotationTable);
        errdefer backing_allocator.destroy(table);
        const arena_state = try backing_allocator.create(std.heap.ArenaAllocator);
        errdefer backing_allocator.destroy(arena_state);
        arena_state.* = std.heap.ArenaAllocator.init(backing_allocator);
        table.* = .{
            .backing_allocator = backing_allocator,
            .arena_state = arena_state,
        };
        return table;
    }

    /// Creates a copy-on-write view over a preceding semantic revision.
    /// Entries belonging to dirty sources are hidden; all other lookups fall
    /// through to the immutable parent table.
    pub fn createOverlay(
        backing_allocator: std.mem.Allocator,
        parent: *const AnnotationTable,
        source_capacity: usize,
        masked_sources: []const AST.SourceId,
    ) std.mem.Allocator.Error!*AnnotationTable {
        const table = try create(backing_allocator);
        errdefer table.destroy();
        var masked = try std.DynamicBitSetUnmanaged.initEmpty(
            backing_allocator,
            source_capacity,
        );
        errdefer masked.deinit(backing_allocator);
        for (masked_sources) |source| {
            const index: usize = @intCast(source.index());
            if (index < source_capacity) masked.set(index);
        }
        table.parent = parent;
        table.masked_sources = masked;
        return table;
    }

    pub fn destroy(self: *AnnotationTable) void {
        for (self.bound_contexts.items) |context|
            if (annotationTableForContext(context) == self) {
                context.annotation_table = null;
                context.owns_annotation_table = false;
            };
        const backing_allocator = self.backing_allocator;
        const arena_state = self.arena_state;
        self.bound_contexts.deinit(self.allocator());
        self.entries.deinit(self.allocator());
        if (self.masked_sources) |*masked| masked.deinit(backing_allocator);
        arena_state.deinit();
        backing_allocator.destroy(arena_state);
        backing_allocator.destroy(self);
    }

    pub fn allocator(self: *AnnotationTable) std.mem.Allocator {
        return self.arena_state.allocator();
    }

    pub fn setCompatibilityIds(
        self: *AnnotationTable,
        compatibility_ids: *const CompatibilityIds.CompatibilityIdProjection,
    ) void {
        std.debug.assert(self.compatibility_ids == null);
        self.compatibility_ids = compatibility_ids;
    }

    pub fn bindTree(
        self: *AnnotationTable,
        tree: *AST.Tree,
    ) std.mem.Allocator.Error!void {
        if (annotationTableForContext(tree.semantic_context)) |current|
            if (current == self) return;
        try self.bound_contexts.append(self.allocator(), tree.semantic_context);
        unbindTree(tree);
        tree.semantic_context.annotation_table = self;
        tree.semantic_context.owns_annotation_table = false;
    }

    /// Rollback counterpart to `bindTree`. A previously bound table retains
    /// the capacity released when a candidate table displaced this context.
    pub fn bindTreeAssumeCapacity(self: *AnnotationTable, tree: *AST.Tree) void {
        if (annotationTableForContext(tree.semantic_context)) |current|
            if (current == self) return;
        self.bound_contexts.appendAssumeCapacity(tree.semantic_context);
        unbindTree(tree);
        tree.semantic_context.annotation_table = self;
        tree.semantic_context.owns_annotation_table = false;
    }

    fn get(self: *const AnnotationTable, node: *const AST.Node) ?*Annotation {
        if (self.entries.get(node.node_ref)) |entry| {
            if (entry.node != node) return null;
            return entry.annotation;
        }
        if (self.masked_sources) |masked| {
            const source_index: usize = @intCast(node.node_ref.source.index());
            if (source_index < masked.capacity() and masked.isSet(source_index))
                return null;
        }
        const parent = self.parent orelse return null;
        return parent.get(node);
    }

    fn ensure(
        self: *AnnotationTable,
        node: *AST.Node,
    ) std.mem.Allocator.Error!*Annotation {
        const result = try self.entries.getOrPut(self.allocator(), node.node_ref);
        if (result.found_existing) {
            std.debug.assert(result.value_ptr.node == node);
            return result.value_ptr.annotation;
        }
        errdefer _ = self.entries.remove(node.node_ref);
        const created = try self.allocator().create(Annotation);
        created.* = initialAnnotation(node.nodeKind());
        result.value_ptr.* = .{ .node = node, .annotation = created };
        return created;
    }

    fn rebindImportSource(
        self: *AnnotationTable,
        node: *AST.Node,
        source_unit: *const AST.Node,
    ) (std.mem.Allocator.Error || error{InvalidImportAnnotation})!void {
        if (self.entries.get(node.node_ref)) |entry| {
            if (entry.node != node) return error.InvalidImportAnnotation;
            switch (entry.annotation.*) {
                .import => |*value| value.source_unit = source_unit,
                else => return error.InvalidImportAnnotation,
            }
            return;
        }
        const inherited = self.get(node) orelse return error.InvalidImportAnnotation;
        const imported = switch (inherited.*) {
            .import => |value| value,
            else => return error.InvalidImportAnnotation,
        };
        const result = try self.entries.getOrPut(self.allocator(), node.node_ref);
        std.debug.assert(!result.found_existing);
        errdefer _ = self.entries.remove(node.node_ref);
        const created = try self.allocator().create(Annotation);
        created.* = .{ .import = imported };
        created.import.source_unit = source_unit;
        result.value_ptr.* = .{ .node = node, .annotation = created };
    }
};

fn annotationTableForContext(context: *const AST.SemanticContext) ?*AnnotationTable {
    const erased = context.annotation_table orelse return null;
    return @ptrCast(@alignCast(erased));
}

fn annotationTableForNode(node: *const AST.Node) ?*AnnotationTable {
    return annotationTableForContext(node.semantic_context orelse return null);
}

pub fn semanticAllocator(tree: *AST.Tree) ?std.mem.Allocator {
    const table = annotationTableForContext(tree.semantic_context) orelse return null;
    return table.allocator();
}

fn unbindTree(tree: *AST.Tree) void {
    const context = tree.semantic_context;
    const table = annotationTableForContext(context) orelse return;
    var index: usize = 0;
    while (index < table.bound_contexts.items.len) : (index += 1)
        if (table.bound_contexts.items[index] == context) {
            _ = table.bound_contexts.swapRemove(index);
            break;
        };
    context.annotation_table = null;
    const owned = context.owns_annotation_table;
    context.owns_annotation_table = false;
    if (owned) table.destroy();
}

pub fn deinitTreeBinding(tree: *AST.Tree) void {
    unbindTree(tree);
}

fn ensureLegacyTable(tree: *AST.Tree) std.mem.Allocator.Error!*AnnotationTable {
    if (annotationTableForContext(tree.semantic_context)) |table| return table;
    const table = try AnnotationTable.create(tree.backing_allocator);
    errdefer table.destroy();
    try table.bindTree(tree);
    tree.semantic_context.owns_annotation_table = true;
    return table;
}

fn initialAnnotation(kind: AST.Kind) Annotation {
    return switch (kind) {
        .source_unit => .{ .source_unit = .{} },
        .import_directive => .{ .import = .{} },
        .contract_definition => .{ .contract_definition = .{} },
        .storage_layout_specifier => .{ .storage_layout_specifier = .{} },
        .struct_definition => .{ .struct_declaration = .{} },
        .enum_definition,
        .user_defined_value_type_definition,
        .type_definition,
        => .{ .type_declaration = .{} },
        .function_definition,
        .modifier_definition,
        .event_definition,
        .error_definition,
        => .{ .documented_callable = .{} },
        .variable_declaration => .{ .variable_declaration = .{} },
        .enum_value, .magic_variable_declaration => .{ .declaration = .{} },
        .inline_assembly => .{ .inline_assembly = .{} },
        .block => .{ .block = .{} },
        .try_catch_clause => .{ .try_catch_clause = .{} },
        .for_statement => .{ .for_statement = .{} },
        .return_statement => .{ .return_statement = .{} },
        .elementary_type_name,
        .user_defined_type_name,
        .function_type_name,
        .mapping,
        .array_type_name,
        => .{ .type_name = .{} },
        .identifier_path => .{ .identifier_path = .{} },
        .identifier => .{ .identifier = .{} },
        .member_access => .{ .member_access = .{} },
        .unary_operation => .{ .operation = .{} },
        .binary_operation => .{ .binary_operation = .{} },
        .function_call => .{ .function_call = .{} },
        .conditional,
        .assignment,
        .tuple_expression,
        .function_call_options,
        .new_expression,
        .index_access,
        .index_range_access,
        .elementary_type_name_expression,
        .literal,
        .builtin,
        => .{ .expression = .{} },
        .type_class_definition => .{ .type_class_definition = .{} },
        .for_all_quantifier => .{ .for_all_quantifier = .{} },
        .pragma_directive,
        .structured_documentation,
        .inheritance_specifier,
        .using_for_directive,
        .parameter_list,
        .override_specifier,
        .modifier_invocation,
        .placeholder_statement,
        .if_statement,
        .try_statement,
        .while_statement,
        .continue_statement,
        .break_statement,
        .throw_statement,
        .revert_statement,
        .emit_statement,
        .variable_declaration_statement,
        .expression_statement,
        .type_class_instantiation,
        .type_class_name,
        => .{ .base = {} },
    };
}

pub fn annotation(node: *AST.Node) ?*Annotation {
    if (node.annotation) |erased| return @ptrCast(@alignCast(erased));
    const table = annotationTableForNode(node) orelse return null;
    return table.get(node);
}

pub fn annotationConst(node: *const AST.Node) ?*const Annotation {
    return annotation(@constCast(node));
}

/// Rebinds only the revision-local import target while retaining all other
/// semantic annotations for an otherwise clean source.
pub fn rebindImportSource(
    tree: *AST.Tree,
    node: *AST.Node,
    source_unit: *const AST.Node,
) (std.mem.Allocator.Error || error{ InvalidImportAnnotation, MissingAnnotationTable })!void {
    const table = annotationTableForContext(tree.semantic_context) orelse
        return error.MissingAnnotationTable;
    try table.rebindImportSource(node, source_unit);
}

/// Compatibility ordering for diagnostics and legacy semantic algorithms.
/// Detached test nodes retain their stored adapter ID.
pub fn compatibilityId(node: *const AST.Node) i64 {
    if (node.nodeKind() == .magic_variable_declaration) return node.id;
    const table = annotationTableForNode(node) orelse return node.id;
    const projection = table.compatibility_ids orelse return node.id;
    return projection.id(node.node_ref) orelse node.id;
}

/// Returns the common `ScopableAnnotation` projection for every node that
/// inherits upstream's `Scopable` mixin.
pub fn scopable(value: *Annotation) ?*ScopableAnnotation {
    return switch (value.*) {
        .import => |*entry| &entry.declaration.scopable,
        .contract_definition => |*entry| &entry.type_declaration.declaration.scopable,
        .struct_declaration => |*entry| &entry.type_declaration.declaration.scopable,
        .type_declaration => |*entry| &entry.declaration.scopable,
        .documented_callable => |*entry| &entry.callable.declaration.scopable,
        .variable_declaration => |*entry| &entry.declaration.scopable,
        .declaration => |*entry| &entry.scopable,
        .block => |*entry| &entry.scopable,
        .try_catch_clause => |*entry| &entry.scopable,
        .for_statement => |*entry| &entry.scopable,
        .type_class_definition => |*entry| &entry.type_declaration.declaration.scopable,
        .for_all_quantifier => |*entry| &entry.scopable,
        else => null,
    };
}

pub fn scopableConst(value: *const Annotation) ?*const ScopableAnnotation {
    return scopable(@constCast(value));
}

pub fn scopableForNode(node: *AST.Node) ?*ScopableAnnotation {
    return scopable(annotation(node) orelse return null);
}

pub fn scopableForNodeConst(node: *const AST.Node) ?*const ScopableAnnotation {
    return scopableForNode(@constCast(node));
}

pub fn ensure(tree: *AST.Tree, node: *AST.Node) std.mem.Allocator.Error!*Annotation {
    if (annotation(node)) |existing| return existing;
    std.debug.assert(node.semantic_context == tree.semantic_context);
    return (try ensureLegacyTable(tree)).ensure(node);
}

test "annotations are lazy, stable, and specialized by closed node kind" {
    var tree = try AST.Tree.init(std.testing.allocator, "x + y", "A.sol");
    defer tree.deinit();
    const left = try tree.createNode(.{}, .{ .identifier = .{ .name = "x" } });
    const right = try tree.createNode(.{}, .{ .identifier = .{ .name = "y" } });
    const binary = try tree.createNode(.{}, .{ .binary_operation = .{
        .left = left,
        .operator = .Add,
        .right = right,
    } });

    try std.testing.expect(annotation(binary) == null);
    const first = try ensure(&tree, binary);
    const second = try ensure(&tree, binary);
    try std.testing.expect(first == second);
    try std.testing.expectEqual(@as(std.meta.Tag(Annotation), .binary_operation), std.meta.activeTag(first.*));
    try first.binary_operation.operation.expression.is_lvalue.assign(false);
    try std.testing.expect(!(try first.binary_operation.operation.expression.is_lvalue.get()).*);
}

test "annotation overlays reuse clean sources and mask dirty sources" {
    var clean_tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(1),
        "clean",
        "Clean.sol",
    );
    defer clean_tree.deinit();
    const clean = try clean_tree.createNode(.{}, .{ .identifier = .{ .name = "clean" } });
    var dirty_tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(2),
        "dirty",
        "Dirty.sol",
    );
    defer dirty_tree.deinit();
    const dirty = try dirty_tree.createNode(.{}, .{ .identifier = .{ .name = "dirty" } });

    const parent = try AnnotationTable.create(std.testing.allocator);
    defer parent.destroy();
    try parent.bindTree(&clean_tree);
    try parent.bindTree(&dirty_tree);
    const clean_parent = try ensure(&clean_tree, clean);
    const dirty_parent = try ensure(&dirty_tree, dirty);

    const overlay = try AnnotationTable.createOverlay(
        std.testing.allocator,
        parent,
        3,
        &.{AST.SourceId.init(2)},
    );
    try overlay.bindTree(&clean_tree);
    try overlay.bindTree(&dirty_tree);
    try std.testing.expect(annotation(clean) == clean_parent);
    try std.testing.expect(annotation(dirty) == null);
    const dirty_overlay = try ensure(&dirty_tree, dirty);
    try std.testing.expect(dirty_overlay != dirty_parent);
    overlay.destroy();

    parent.bindTreeAssumeCapacity(&clean_tree);
    parent.bindTreeAssumeCapacity(&dirty_tree);
    try std.testing.expect(annotation(clean) == clean_parent);
    try std.testing.expect(annotation(dirty) == dirty_parent);
}

test "clean import rebinding is isolated to the child annotation table" {
    var importer_tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(1),
        "import 'Target.sol';",
        "Importer.sol",
    );
    defer importer_tree.deinit();
    const import = try importer_tree.createNode(.{}, .{ .import_directive = .{
        .declaration = .{},
        .path = "Target.sol",
    } });
    var old_target_tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(2),
        "contract Target {}",
        "Target.sol",
    );
    defer old_target_tree.deinit();
    const old_target = try old_target_tree.createNode(.{}, .{ .source_unit = .{} });
    var new_target_tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(2),
        "contract Target { uint256 value; }",
        "Target.sol",
    );
    defer new_target_tree.deinit();
    const new_target = try new_target_tree.createNode(.{}, .{ .source_unit = .{} });

    const parent = try AnnotationTable.create(std.testing.allocator);
    defer parent.destroy();
    try parent.bindTree(&importer_tree);
    const parent_annotation = try ensure(&importer_tree, import);
    try parent_annotation.import.absolute_path.assign("Target.sol");
    parent_annotation.import.source_unit = old_target;

    const overlay = try AnnotationTable.createOverlay(
        std.testing.allocator,
        parent,
        3,
        &.{},
    );
    try overlay.bindTree(&importer_tree);
    try rebindImportSource(&importer_tree, import, new_target);
    const child_annotation = annotation(import).?;
    try std.testing.expect(child_annotation != parent_annotation);
    try std.testing.expect(child_annotation.import.source_unit == new_target);
    try std.testing.expectEqualStrings(
        "Target.sol",
        (try child_annotation.import.absolute_path.get()).*,
    );
    overlay.destroy();

    parent.bindTreeAssumeCapacity(&importer_tree);
    try std.testing.expect(annotation(import).?.import.source_unit == old_target);
}

test "revision tables rebind immutable syntax without overwriting prior annotations" {
    var tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(7),
        "value",
        "A.sol",
    );
    defer tree.deinit();
    const identifier = try tree.createNode(.{}, .{ .identifier = .{ .name = "value" } });

    const first = try AnnotationTable.create(std.testing.allocator);
    defer first.destroy();
    try first.bindTree(&tree);
    const first_annotation = try ensure(&tree, identifier);
    first_annotation.identifier.referenced_declaration = identifier;
    try std.testing.expect(identifier.annotation == null);

    const second = try AnnotationTable.create(std.testing.allocator);
    defer second.destroy();
    try second.bindTree(&tree);
    try std.testing.expect(annotation(identifier) == null);
    const second_annotation = try ensure(&tree, identifier);
    try std.testing.expect(second_annotation != first_annotation);
    try std.testing.expect(second_annotation.identifier.referenced_declaration == null);

    try first.bindTree(&tree);
    try std.testing.expect(annotation(identifier) == first_annotation);
    try std.testing.expect(first_annotation.identifier.referenced_declaration == identifier);
}

test "semantic compatibility order ignores a retained node's stored offset" {
    const source_id = AST.SourceId.init(7);
    var tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        source_id,
        "value",
        "A.sol",
    );
    defer tree.deinit();
    const identifier = try tree.createNode(.{}, .{ .identifier = .{ .name = "value" } });
    try std.testing.expectEqual(@as(i64, 1), identifier.id);

    const table = try AnnotationTable.create(std.testing.allocator);
    defer table.destroy();
    try table.bindTree(&tree);
    var projection = try CompatibilityIds.CompatibilityIdProjection.initAlloc(
        std.testing.allocator,
        &.{
            .{ .source = AST.SourceId.init(9), .node_count = 5 },
            .{ .source = source_id, .node_count = 1 },
        },
    );
    defer projection.deinit();
    table.setCompatibilityIds(&projection);

    try std.testing.expectEqual(@as(i64, 6), compatibilityId(identifier));
}

test "source-unit and declaration annotations preserve set-once failure classes" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "A.sol");
    defer tree.deinit();
    const source = try tree.createNode(.{}, .{ .source_unit = .{} });
    const value = try ensure(&tree, source);
    try value.source_unit.path.assign("A.sol");
    try std.testing.expectError(
        error.BadSetOnceReassignment,
        value.source_unit.path.assign("B.sol"),
    );
}

test "inline-assembly annotations retain concrete Yul identities and analysis state" {
    var tree = try AST.Tree.init(std.testing.allocator, "assembly {}", "A.sol");
    defer tree.deinit();

    const assembly = try tree.createNode(.{}, .{ .inline_assembly = .{} });
    const value = try ensure(&tree, assembly);
    var identifier: YulAST.Identifier = .{};
    try value.inline_assembly.external_references.append(tree.allocator(), .{
        .identifier = &identifier,
        .info = .{},
    });
    const analysis = try value.inline_assembly.createAnalysisInfo(&tree);

    try std.testing.expect(value.inline_assembly.external_references.items[0].identifier == &identifier);
    try std.testing.expect(value.inline_assembly.analysis_info.? == analysis);
}
