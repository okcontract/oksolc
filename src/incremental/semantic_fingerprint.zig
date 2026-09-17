// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Source-level semantic surfaces used to narrow import invalidation.
//!
//! The fingerprints are syntax-derived so they are available before semantic
//! analysis begins. They divide a parsed source into surfaces that importers
//! may consume, while retaining the complete source bytes for call-graph and
//! code-generation inputs. False positives are safe; a false negative would
//! permit an importer to retain stale semantic state.

const std = @import("std");
const AST = @import("../libsolidity/ast/ast.zig");
const FixedHash = @import("../libsolutil/fixed_hash.zig");
const Keccak256 = @import("../libsolutil/keccak256.zig");
const KeyHasher = @import("key_hasher.zig").KeyHasher;
const Identity = @import("identity.zig");

pub const H256 = FixedHash.H256;
pub const SourceId = Identity.SourceId;

pub const Category = enum(u3) {
    exported_symbols,
    inheritance,
    storage_layout,
    abi_types,
    call_dependencies,
    codegen_inputs,
};

pub const CategoryMask = struct {
    bits: u8 = 0,

    pub const none: CategoryMask = .{};
    pub const all: CategoryMask = .{ .bits = 0b00_111111 };
    pub const exported_only: CategoryMask = from(.exported_symbols);

    pub fn from(category: Category) CategoryMask {
        return .{ .bits = @as(u8, 1) << @intFromEnum(category) };
    }

    pub fn contains(self: CategoryMask, category: Category) bool {
        return self.bits & from(category).bits != 0;
    }

    pub fn intersects(self: CategoryMask, other: CategoryMask) bool {
        return self.bits & other.bits != 0;
    }

    pub fn merge(self: *CategoryMask, other: CategoryMask) bool {
        const previous = self.bits;
        self.bits |= other.bits;
        return self.bits != previous;
    }
};

pub const SourceFingerprints = struct {
    exported_symbols: H256,
    inheritance: H256,
    storage_layout: H256,
    abi_types: H256,
    call_dependencies: H256,
    codegen_inputs: H256,

    pub fn changedCategories(
        self: *const SourceFingerprints,
        other: *const SourceFingerprints,
    ) CategoryMask {
        var result: CategoryMask = .none;
        if (!self.exported_symbols.eql(&other.exported_symbols))
            _ = result.merge(.from(.exported_symbols));
        if (!self.inheritance.eql(&other.inheritance))
            _ = result.merge(.from(.inheritance));
        if (!self.storage_layout.eql(&other.storage_layout))
            _ = result.merge(.from(.storage_layout));
        if (!self.abi_types.eql(&other.abi_types))
            _ = result.merge(.from(.abi_types));
        if (!self.call_dependencies.eql(&other.call_dependencies))
            _ = result.merge(.from(.call_dependencies));
        if (!self.codegen_inputs.eql(&other.codegen_inputs))
            _ = result.merge(.from(.codegen_inputs));
        return result;
    }
};

pub const SourceFingerprintEntry = struct {
    source: SourceId,
    fingerprints: SourceFingerprints,
};

pub const FingerprintRevision = struct {
    allocator: std.mem.Allocator,
    values: []?SourceFingerprints,

    pub fn initAlloc(
        allocator: std.mem.Allocator,
        source_capacity: usize,
        entries: []const SourceFingerprintEntry,
    ) (std.mem.Allocator.Error || error{ DuplicateSource, InvalidSourceId })!FingerprintRevision {
        const values = try allocator.alloc(?SourceFingerprints, source_capacity);
        errdefer allocator.free(values);
        @memset(values, null);
        for (entries) |entry| {
            const index: usize = @intCast(entry.source.index());
            if (index >= values.len) return error.InvalidSourceId;
            if (values[index] != null) return error.DuplicateSource;
            values[index] = entry.fingerprints;
        }
        return .{ .allocator = allocator, .values = values };
    }

    pub fn deinit(self: *FingerprintRevision) void {
        self.allocator.free(self.values);
        self.* = undefined;
    }

    pub fn get(
        self: *const FingerprintRevision,
        source: SourceId,
    ) ?*const SourceFingerprints {
        const index: usize = @intCast(source.index());
        if (index >= self.values.len) return null;
        return if (self.values[index]) |*value| value else null;
    }
};

pub const DependencyMaskEntry = struct {
    importer: SourceId,
    imported: SourceId,
    categories: CategoryMask = .exported_only,
};

pub fn dependencyMask(
    entries: []const DependencyMaskEntry,
    importer: SourceId,
    imported: SourceId,
) CategoryMask {
    var left: usize = 0;
    var right = entries.len;
    while (left < right) {
        const middle = left + (right - left) / 2;
        const entry = entries[middle];
        const order = dependencyOrder(entry.importer, entry.imported, importer, imported);
        switch (order) {
            .lt => left = middle + 1,
            .gt => right = middle,
            .eq => return entry.categories,
        }
    }
    // Missing metadata is a compatibility/failure boundary, never evidence
    // that an edge consumes nothing.
    return .all;
}

fn dependencyOrder(
    left_importer: SourceId,
    left_imported: SourceId,
    right_importer: SourceId,
    right_imported: SourceId,
) std.math.Order {
    if (left_importer != right_importer)
        return std.math.order(left_importer.index(), right_importer.index());
    return std.math.order(left_imported.index(), right_imported.index());
}

const FingerprintBuilder = struct {
    exported_symbols: KeyHasher = KeyHasher.init("source.exported-symbols", 1),
    inheritance: KeyHasher = KeyHasher.init("source.inheritance", 1),
    storage_layout: KeyHasher = KeyHasher.init("source.storage-layout", 1),
    abi_types: KeyHasher = KeyHasher.init("source.abi-types", 1),
    call_dependencies: KeyHasher = KeyHasher.init("source.call-dependencies", 1),
    codegen_inputs: KeyHasher = KeyHasher.init("source.codegen-inputs", 1),

    fn finish(self: *FingerprintBuilder) SourceFingerprints {
        return .{
            .exported_symbols = self.exported_symbols.finish(),
            .inheritance = self.inheritance.finish(),
            .storage_layout = self.storage_layout.finish(),
            .abi_types = self.abi_types.finish(),
            .call_dependencies = self.call_dependencies.finish(),
            .codegen_inputs = self.codegen_inputs.finish(),
        };
    }
};

pub fn compute(tree: *const AST.Tree) SourceFingerprints {
    const content_digest = Keccak256.keccak256(tree.source);
    return computeWithContentDigest(tree, &content_digest);
}

pub fn computeWithContentDigest(
    tree: *const AST.Tree,
    content_digest: *const H256,
) SourceFingerprints {
    var builder: FingerprintBuilder = .{};
    builder.call_dependencies.addDigest(1, content_digest);
    builder.codegen_inputs.addDigest(1, content_digest);

    const root = tree.root orelse {
        addToInterfaceSurfaces(&builder, 1, tree.source);
        return builder.finish();
    };
    for (root.payload.source_unit.nodes) |node|
        hashTopLevel(&builder, tree.source, node);
    return builder.finish();
}

fn hashTopLevel(
    builder: *FingerprintBuilder,
    source: []const u8,
    node: *const AST.Node,
) void {
    switch (node.payload) {
        .pragma_directive => {
            const text = nodeText(source, node);
            addToInterfaceSurfaces(builder, 2, text);
        },
        .import_directive => {
            const text = nodeText(source, node);
            builder.exported_symbols.addBytes(2, text);
            addToInterfaceSurfaces(builder, 3, text);
        },
        .contract_definition => |contract| {
            hashExportedDeclaration(&builder.exported_symbols, node);
            addContractHeader(builder, source, node);
            addDocumentation(builder, source, contract.documentation);
            for (contract.sub_nodes) |member|
                hashContractMember(builder, source, member);
        },
        .function_definition => |function| {
            hashExportedDeclaration(&builder.exported_symbols, node);
            addCallableSurface(builder, source, node, function.body);
            addDocumentation(builder, source, function.documentation);
        },
        .modifier_definition => |modifier| {
            hashExportedDeclaration(&builder.exported_symbols, node);
            addCallableSurface(builder, source, node, modifier.body);
            addDocumentation(builder, source, modifier.documentation);
        },
        .variable_declaration => |variable| {
            hashExportedDeclaration(&builder.exported_symbols, node);
            addDeclarationSurface(builder, source, node, variable.value);
            addDocumentation(builder, source, variable.documentation);
        },
        .struct_definition => |structure| {
            hashExportedDeclaration(&builder.exported_symbols, node);
            addToInterfaceSurfaces(builder, 4, nodeText(source, node));
            addDocumentation(builder, source, structure.documentation);
        },
        .enum_definition => |enumeration| {
            hashExportedDeclaration(&builder.exported_symbols, node);
            addToInterfaceSurfaces(builder, 5, nodeText(source, node));
            addDocumentation(builder, source, enumeration.documentation);
        },
        .user_defined_value_type_definition,
        .event_definition,
        .error_definition,
        .type_class_definition,
        .type_definition,
        => {
            hashExportedDeclaration(&builder.exported_symbols, node);
            addToInterfaceSurfaces(builder, 6, nodeText(source, node));
        },
        .using_for_directive => {
            const text = nodeText(source, node);
            builder.exported_symbols.addBytes(5, text);
            addToInterfaceSurfaces(builder, 6, text);
        },
        else => addToInterfaceSurfaces(builder, 7, nodeText(source, node)),
    }
}

fn hashContractMember(
    builder: *FingerprintBuilder,
    source: []const u8,
    node: *const AST.Node,
) void {
    switch (node.payload) {
        .function_definition => |function| {
            addCallableSurface(builder, source, node, function.body);
            addDocumentation(builder, source, function.documentation);
        },
        .modifier_definition => |modifier| {
            addCallableSurface(builder, source, node, modifier.body);
            addDocumentation(builder, source, modifier.documentation);
        },
        .variable_declaration => |variable| {
            addDeclarationSurface(builder, source, node, variable.value);
            addDocumentation(builder, source, variable.documentation);
        },
        .struct_definition => |structure| {
            addToInterfaceSurfaces(builder, 8, nodeText(source, node));
            addDocumentation(builder, source, structure.documentation);
        },
        .enum_definition => |enumeration| {
            addToInterfaceSurfaces(builder, 9, nodeText(source, node));
            addDocumentation(builder, source, enumeration.documentation);
        },
        .event_definition,
        .error_definition,
        .user_defined_value_type_definition,
        .using_for_directive,
        .type_class_definition,
        .type_definition,
        => addToInterfaceSurfaces(builder, 10, nodeText(source, node)),
        else => {},
    }
}

fn addContractHeader(
    builder: *FingerprintBuilder,
    source: []const u8,
    node: *const AST.Node,
) void {
    const contract = node.payload.contract_definition;
    builder.inheritance.addU32(10, @intCast(@intFromEnum(contract.contract_kind)));
    builder.inheritance.addBool(11, contract.abstract);
    builder.storage_layout.addU32(10, @intCast(@intFromEnum(contract.contract_kind)));
    builder.storage_layout.addBool(11, contract.abstract);
    builder.abi_types.addU32(10, @intCast(@intFromEnum(contract.contract_kind)));
    builder.abi_types.addBool(11, contract.abstract);
    addDeclarationName(&builder.inheritance, 12, node);
    addDeclarationName(&builder.storage_layout, 12, node);
    addDeclarationName(&builder.abi_types, 12, node);
    for (contract.base_contracts) |base| {
        const text = nodeText(source, base);
        addToInterfaceSurfaces(builder, 13, text);
    }
    if (contract.storage_layout_specifier) |specifier| {
        const text = nodeText(source, specifier);
        builder.storage_layout.addBytes(14, text);
        builder.inheritance.addBytes(14, text);
    }
}

fn addCallableSurface(
    builder: *FingerprintBuilder,
    source: []const u8,
    declaration: *const AST.Node,
    body: ?*const AST.Node,
) void {
    const chunks = nodeTextExcluding(source, declaration, body);
    builder.inheritance.addBytes(20, chunks.before);
    builder.inheritance.addBytes(21, chunks.after);
    builder.storage_layout.addBytes(20, chunks.before);
    builder.storage_layout.addBytes(21, chunks.after);
    builder.abi_types.addBytes(20, chunks.before);
    builder.abi_types.addBytes(21, chunks.after);
}

fn addDeclarationSurface(
    builder: *FingerprintBuilder,
    source: []const u8,
    declaration: *const AST.Node,
    initializer: ?*const AST.Node,
) void {
    const chunks = nodeTextExcluding(source, declaration, initializer);
    builder.inheritance.addBytes(22, chunks.before);
    builder.inheritance.addBytes(23, chunks.after);
    builder.storage_layout.addBytes(22, chunks.before);
    builder.storage_layout.addBytes(23, chunks.after);
    builder.abi_types.addBytes(22, chunks.before);
    builder.abi_types.addBytes(23, chunks.after);
}

fn addDocumentation(
    builder: *FingerprintBuilder,
    source: []const u8,
    documentation: ?*const AST.Node,
) void {
    const node = documentation orelse return;
    const text = nodeText(source, node);
    builder.inheritance.addBytes(24, text);
    builder.abi_types.addBytes(24, text);
}

fn hashExportedDeclaration(hasher: *KeyHasher, node: *const AST.Node) void {
    hasher.addU32(3, @intFromEnum(node.nodeKind()));
    addDeclarationName(hasher, 4, node);
}

fn addDeclarationName(hasher: *KeyHasher, tag: u8, node: *const AST.Node) void {
    const declaration = node.declarationConst() orelse {
        hasher.addBytes(tag, "");
        return;
    };
    hasher.addBytes(tag, declaration.name);
}

fn addToInterfaceSurfaces(
    builder: *FingerprintBuilder,
    tag: u8,
    value: []const u8,
) void {
    builder.inheritance.addBytes(tag, value);
    builder.storage_layout.addBytes(tag, value);
    builder.abi_types.addBytes(tag, value);
}

const TextChunks = struct {
    before: []const u8,
    after: []const u8 = "",
};

fn nodeTextExcluding(
    source: []const u8,
    node: *const AST.Node,
    excluded: ?*const AST.Node,
) TextChunks {
    const whole = nodeBounds(source, node) orelse return .{ .before = "" };
    const child = nodeBounds(source, excluded orelse return .{
        .before = source[whole.start..whole.end],
    }) orelse return .{ .before = source[whole.start..whole.end] };
    if (child.start < whole.start or child.end > whole.end)
        return .{ .before = source[whole.start..whole.end] };
    return .{
        .before = source[whole.start..child.start],
        .after = source[child.end..whole.end],
    };
}

fn nodeText(source: []const u8, node: *const AST.Node) []const u8 {
    const bounds = nodeBounds(source, node) orelse return "";
    return source[bounds.start..bounds.end];
}

const Bounds = struct { start: usize, end: usize };

fn nodeBounds(source: []const u8, node: *const AST.Node) ?Bounds {
    if (node.location.start < 0 or node.location.end < node.location.start)
        return null;
    const start: usize = @intCast(node.location.start);
    const end: usize = @intCast(node.location.end);
    if (end > source.len) return null;
    return .{ .start = start, .end = end };
}

test "body-only edits change call and codegen fingerprints" {
    const Parser = @import("../libsolidity/parsing/parser.zig");
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;

    var first_reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer first_reporter.deinit();
    var first = try Parser.parseSourceWithIdentity(
        std.testing.allocator,
        "contract A { function value() external pure returns (uint256) { return 1; } }",
        "A.sol",
        &first_reporter,
        EVMVersion.current(),
        SourceId.init(0),
        0,
    );
    defer first.deinit();
    var second_reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer second_reporter.deinit();
    var second = try Parser.parseSourceWithIdentity(
        std.testing.allocator,
        "contract A { function value() external pure returns (uint256) { return 2; } }",
        "A.sol",
        &second_reporter,
        EVMVersion.current(),
        SourceId.init(0),
        0,
    );
    defer second.deinit();

    const changed = compute(&first.tree).changedCategories(&compute(&second.tree));
    try std.testing.expectEqual(
        CategoryMask.from(.call_dependencies).bits |
            CategoryMask.from(.codegen_inputs).bits,
        changed.bits,
    );
}

test "signature edits change semantic interface surfaces" {
    const Parser = @import("../libsolidity/parsing/parser.zig");
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;

    var first_reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer first_reporter.deinit();
    var first = try Parser.parseSourceWithIdentity(
        std.testing.allocator,
        "contract A { function value(uint256) external {} }",
        "A.sol",
        &first_reporter,
        EVMVersion.current(),
        SourceId.init(0),
        0,
    );
    defer first.deinit();
    var second_reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer second_reporter.deinit();
    var second = try Parser.parseSourceWithIdentity(
        std.testing.allocator,
        "contract A { function value(address) external {} }",
        "A.sol",
        &second_reporter,
        EVMVersion.current(),
        SourceId.init(0),
        0,
    );
    defer second.deinit();

    const changed = compute(&first.tree).changedCategories(&compute(&second.tree));
    try std.testing.expect(changed.contains(.inheritance));
    try std.testing.expect(changed.contains(.storage_layout));
    try std.testing.expect(changed.contains(.abi_types));
    try std.testing.expect(changed.contains(.call_dependencies));
    try std.testing.expect(changed.contains(.codegen_inputs));
}
