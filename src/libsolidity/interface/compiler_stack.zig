// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Metadata construction translated from `CompilerStack.cpp`.
//!
//! The Standard JSON dispatcher calls these helpers for the via-IR bytecode path.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ABI = @import("abi.zig");
const DebugSettings = @import("debug_settings.zig");
const OptimiserSettings = @import("optimiser_settings.zig").OptimiserSettings;
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const LinkerObject = @import("../../libevmasm/linker_object.zig");
const CommonData = @import("../../libsolutil/common_data.zig");
const IpfsHash = @import("../../libsolutil/ipfs_hash.zig");
const ImportRemapper = @import("import_remapper.zig");
const JSON = @import("../../libsolutil/json.zig");
const Keccak256 = @import("../../libsolutil/keccak256.zig");
const Natspec = @import("natspec.zig");
const SwarmHash = @import("../../libsolutil/swarm_hash.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const OptimiserSuite = @import("../../libyul/optimiser/suite.zig").OptimiserSuite;
const Version = @import("version.zig");
const SourceId = @import("../../incremental/identity.zig").SourceId;
const SourceGraph = @import("../../incremental/source_graph.zig").SourceGraph;

const Json = JSON.Json;

pub const MetadataHash = enum {
    ipfs,
    bzzr1,
    none,

    pub fn name(self: MetadataHash) []const u8 {
        return switch (self) {
            .ipfs => "ipfs",
            .bzzr1 => "bzzr1",
            .none => "none",
        };
    }
};

pub const MetadataSource = struct {
    id: SourceId,
    tree: *AST.Tree,
    root: *AST.Node,
};

pub const MetadataSources = struct {
    items: []const MetadataSource,
    indices_by_active_index: []const usize,
    graph: *const SourceGraph,

    fn indexForId(self: MetadataSources, id: SourceId) ?usize {
        const active_index = self.graph.activeIndex(id) orelse return null;
        if (active_index >= self.indices_by_active_index.len) return null;
        const index = self.indices_by_active_index[active_index];
        return if (index < self.items.len) index else null;
    }
};

pub const MetadataOptions = struct {
    evm_version: EVMVersion = EVMVersion.current(),
    optimiser: OptimiserSettings = OptimiserSettings.minimal(),
    bytecode_hash: MetadataHash = .ipfs,
    append_cbor: bool = true,
    use_literal_sources: bool = false,
    via_ir: bool = true,
    experimental: bool = false,
    via_ssa_cfg: bool = false,
    revert_strings: DebugSettings.RevertStrings = .Default,
    libraries: []const LinkerObject.LibraryAddress = &.{},
    remappings: []const ImportRemapper.NormalizedRemapping = &.{},
};

pub fn createMetadataAlloc(
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    sources: MetadataSources,
    contract_source_id: SourceId,
    contract_tree: *AST.Tree,
    contract: *AST.Node,
    options: MetadataOptions,
) ![]u8 {
    if (contract.nodeKind() != .contract_definition) return error.InvalidAst;

    var scratch_arena = std.heap.ArenaAllocator.init(allocator);
    defer scratch_arena.deinit();
    const scratch = scratch_arena.allocator();

    var metadata: Json = .{ .object = .empty };

    var compiler: Json = .{ .object = .empty };
    try putString(scratch, &compiler, "version", Version.MetadataVersion);
    try metadata.object.put(scratch, "compiler", compiler);
    try putString(scratch, &metadata, "language", "Solidity");

    var output: Json = .{ .object = .empty };
    try output.object.put(
        scratch,
        "abi",
        try ABI.ABI.generate(
            scratch,
            type_provider,
            compatibility_ids,
            contract_tree,
            contract,
        ),
    );
    try output.object.put(
        scratch,
        "devdoc",
        try Natspec.Natspec.devDocumentation(
            scratch,
            type_provider,
            compatibility_ids,
            contract,
        ),
    );
    try output.object.put(
        scratch,
        "userdoc",
        try Natspec.Natspec.userDocumentation(
            scratch,
            type_provider,
            compatibility_ids,
            contract,
        ),
    );
    try metadata.object.put(scratch, "output", output);

    try metadata.object.put(
        scratch,
        "settings",
        try metadataSettings(scratch, contract_tree, contract, options),
    );
    try metadata.object.put(
        scratch,
        "sources",
        try metadataSources(scratch, sources, contract_source_id, options),
    );
    try metadata.object.put(scratch, "version", .{ .integer = 1 });

    return JSON.jsonCompactPrintAlloc(allocator, &metadata);
}

pub fn createCBORMetadataAlloc(
    allocator: std.mem.Allocator,
    metadata_json: []const u8,
    options: MetadataOptions,
) ![]u8 {
    if (!options.append_cbor) return allocator.alloc(u8, 0);

    var encoder = MetadataCBOREncoder.init(allocator);
    defer encoder.deinit();
    switch (options.bytecode_hash) {
        .ipfs => {
            const digest = try IpfsHash.ipfsHash(allocator, metadata_json);
            try encoder.pushBytes("ipfs", &digest);
        },
        .bzzr1 => {
            const digest = SwarmHash.bzzr1Hash(metadata_json);
            try encoder.pushBytes("bzzr1", digest.array());
        },
        .none => {},
    }
    if (options.experimental) try encoder.pushBool("experimental", true);
    try encoder.pushBytes("solc", &Version.VersionCompactBytes);
    return encoder.serialise();
}

fn metadataSources(
    allocator: std.mem.Allocator,
    sources: MetadataSources,
    contract_source_id: SourceId,
    options: MetadataOptions,
) !Json {
    const referenced = try referencedSourcesAlloc(
        allocator,
        sources,
        contract_source_id,
    );
    defer allocator.free(referenced);

    var result: Json = .{ .object = .empty };
    for (sources.items, 0..) |source, index| {
        if (!referenced[index]) continue;
        var entry: Json = .{ .object = .empty };
        const keccak = Keccak256.keccak256(source.tree.source);
        try putString(
            allocator,
            &entry,
            "keccak256",
            try CommonData.toHexAlloc(allocator, keccak.array(), .add, .lower),
        );
        if (source.root.payload.source_unit.license) |license|
            try putString(allocator, &entry, "license", license);

        if (options.use_literal_sources) {
            try putString(allocator, &entry, "content", source.tree.source);
        } else {
            var urls = std.json.Array.init(allocator);
            const swarm = SwarmHash.bzzr1Hash(source.tree.source);
            const swarm_hex = try CommonData.toHexAlloc(
                allocator,
                swarm.array(),
                .dont_add,
                .lower,
            );
            try urls.append(.{ .string = try std.fmt.allocPrint(
                allocator,
                "bzz-raw://{s}",
                .{swarm_hex},
            ) });
            const ipfs = try IpfsHash.ipfsHashBase58Alloc(allocator, source.tree.source);
            try urls.append(.{ .string = try std.fmt.allocPrint(
                allocator,
                "dweb:/ipfs/{s}",
                .{ipfs},
            ) });
            try entry.object.put(allocator, "urls", .{ .array = urls });
        }
        try result.object.put(allocator, source.tree.source_name, entry);
    }
    return result;
}

fn metadataSettings(
    allocator: std.mem.Allocator,
    contract_tree: *const AST.Tree,
    contract: *const AST.Node,
    options: MetadataOptions,
) !Json {
    var result: Json = .{ .object = .empty };

    var compilation_target: Json = .{ .object = .empty };
    try putString(
        allocator,
        &compilation_target,
        contract_tree.source_name,
        canonicalContractName(contract),
    );
    try result.object.put(allocator, "compilationTarget", compilation_target);
    try putString(allocator, &result, "evmVersion", options.evm_version.name());
    if (options.experimental)
        try result.object.put(allocator, "experimental", .{ .bool = true });

    var libraries: Json = .{ .object = .empty };
    for (options.libraries) |library| {
        try putString(
            allocator,
            &libraries,
            library.name,
            try CommonData.toHexAlloc(
                allocator,
                library.address.array(),
                .add,
                .lower,
            ),
        );
    }
    try result.object.put(allocator, "libraries", libraries);

    var metadata: Json = .{ .object = .empty };
    if (!options.append_cbor)
        try metadata.object.put(allocator, "appendCBOR", .{ .bool = false });
    try putString(allocator, &metadata, "bytecodeHash", options.bytecode_hash.name());
    if (options.use_literal_sources)
        try metadata.object.put(allocator, "useLiteralContent", .{ .bool = true });
    try result.object.put(allocator, "metadata", metadata);

    try result.object.put(
        allocator,
        "optimizer",
        try metadataOptimiserSettings(allocator, options.optimiser),
    );
    try result.object.put(
        allocator,
        "remappings",
        try metadataRemappings(allocator, options.remappings),
    );
    if (options.revert_strings != .Default) {
        var debug: Json = .{ .object = .empty };
        try putString(
            allocator,
            &debug,
            "revertStrings",
            options.revert_strings.toString(),
        );
        try result.object.put(allocator, "debug", debug);
    }
    if (options.via_ir)
        try result.object.put(allocator, "viaIR", .{ .bool = true });
    if (options.via_ssa_cfg)
        try result.object.put(allocator, "viaSSACFG", .{ .bool = true });
    return result;
}

fn metadataRemappings(
    allocator: std.mem.Allocator,
    remappings: []const ImportRemapper.NormalizedRemapping,
) !Json {
    const rendered = try allocator.alloc([]const u8, remappings.len);
    for (remappings, rendered) |normalized, *entry| {
        const remapping = normalized.original();
        entry.* = try std.fmt.allocPrint(
            allocator,
            "{s}:{s}={s}",
            .{ remapping.context, remapping.prefix, remapping.target },
        );
    }
    std.sort.insertion([]const u8, rendered, {}, struct {
        fn lessThan(_: void, left: []const u8, right: []const u8) bool {
            return std.mem.order(u8, left, right) == .lt;
        }
    }.lessThan);

    var result = std.json.Array.init(allocator);
    errdefer result.deinit();
    for (rendered, 0..) |entry, index| {
        if (index != 0 and std.mem.eql(u8, rendered[index - 1], entry)) continue;
        try result.append(.{ .string = entry });
    }
    return .{ .array = result };
}

fn metadataOptimiserSettings(
    allocator: std.mem.Allocator,
    settings: OptimiserSettings,
) !Json {
    var result: Json = .{ .object = .empty };
    try result.object.put(
        allocator,
        "runs",
        try unsignedJson(allocator, settings.expected_executions_per_deployment),
    );

    var without_runs = settings;
    without_runs.expected_executions_per_deployment =
        OptimiserSettings.minimal().expected_executions_per_deployment;
    if (without_runs.eql(OptimiserSettings.minimal())) {
        try result.object.put(allocator, "enabled", .{ .bool = false });
        return result;
    }
    if (without_runs.eql(OptimiserSettings.standard())) {
        try result.object.put(allocator, "enabled", .{ .bool = true });
        return result;
    }

    var details: Json = .{ .object = .empty };
    try details.object.put(allocator, "orderLiterals", .{ .bool = settings.run_order_literals });
    try details.object.put(allocator, "inliner", .{ .bool = settings.run_inliner });
    try details.object.put(allocator, "jumpdestRemover", .{ .bool = settings.run_jumpdest_remover });
    try details.object.put(allocator, "peephole", .{ .bool = settings.run_peephole });
    try details.object.put(allocator, "deduplicate", .{ .bool = settings.run_deduplicate });
    try details.object.put(allocator, "cse", .{ .bool = settings.run_cse });
    try details.object.put(allocator, "constantOptimizer", .{ .bool = settings.run_constant_optimiser });
    try details.object.put(
        allocator,
        "simpleCounterForLoopUncheckedIncrement",
        .{ .bool = settings.simple_counter_for_loop_unchecked_increment },
    );
    try details.object.put(allocator, "yul", .{ .bool = settings.run_yul_optimiser });
    if (settings.run_yul_optimiser) {
        var yul_details: Json = .{ .object = .empty };
        try yul_details.object.put(
            allocator,
            "stackAllocation",
            .{ .bool = settings.optimize_stack_allocation },
        );
        try putString(
            allocator,
            &yul_details,
            "optimizerSteps",
            try std.fmt.allocPrint(
                allocator,
                "{s}:{s}",
                .{ settings.yul_optimiser_steps, settings.yul_optimiser_cleanup_steps },
            ),
        );
        try details.object.put(allocator, "yulDetails", yul_details);
    } else if (OptimiserSuite.isEmptyOptimizerSequence(
        try std.fmt.allocPrint(
            allocator,
            "{s}:{s}",
            .{ settings.yul_optimiser_steps, settings.yul_optimiser_cleanup_steps },
        ),
    )) {
        var yul_details: Json = .{ .object = .empty };
        try putString(allocator, &yul_details, "optimizerSteps", ":");
        try details.object.put(allocator, "yulDetails", yul_details);
    }
    try result.object.put(allocator, "details", details);
    return result;
}

fn referencedSourcesAlloc(
    allocator: std.mem.Allocator,
    sources: MetadataSources,
    contract_source_id: SourceId,
) ![]bool {
    const referenced = try allocator.alloc(bool, sources.items.len);
    @memset(referenced, false);
    errdefer allocator.free(referenced);

    var pending: std.ArrayList(usize) = .empty;
    defer pending.deinit(allocator);
    const start = sources.indexForId(contract_source_id) orelse
        return error.MissingContractSource;
    referenced[start] = true;
    try pending.append(allocator, start);
    while (pending.pop()) |source_index| {
        for (sources.graph.imports(sources.items[source_index].id)) |imported_id| {
            const imported_index = sources.indexForId(imported_id) orelse
                return error.MissingImportedSource;
            if (referenced[imported_index]) continue;
            referenced[imported_index] = true;
            try pending.append(allocator, imported_index);
        }
    }
    return referenced;
}

fn canonicalContractName(contract: *const AST.Node) []const u8 {
    const annotation = ASTAnnotations.annotationConst(contract) orelse
        return contract.payload.contract_definition.declaration.name;
    return switch (annotation.*) {
        .contract_definition => |value| value.type_declaration.canonical_name.value orelse
            contract.payload.contract_definition.declaration.name,
        else => contract.payload.contract_definition.declaration.name,
    };
}

fn unsignedJson(allocator: std.mem.Allocator, value: u64) !Json {
    if (value <= std.math.maxInt(i64))
        return .{ .integer = @intCast(value) };
    return .{ .number_string = try std.fmt.allocPrint(allocator, "{d}", .{value}) };
}

fn putString(
    allocator: std.mem.Allocator,
    object: *Json,
    key: []const u8,
    value: []const u8,
) !void {
    try object.object.put(allocator, key, .{ .string = value });
}

const MetadataCBOREncoder = struct {
    allocator: std.mem.Allocator,
    data: std.ArrayList(u8) = .empty,
    entry_count: u8 = 0,

    fn init(allocator: std.mem.Allocator) MetadataCBOREncoder {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *MetadataCBOREncoder) void {
        self.data.deinit(self.allocator);
    }

    fn pushBytes(self: *MetadataCBOREncoder, key: []const u8, value: []const u8) !void {
        self.entry_count = try std.math.add(u8, self.entry_count, 1);
        try self.pushTextString(key);
        try self.pushByteString(value);
    }

    fn pushBool(self: *MetadataCBOREncoder, key: []const u8, value: bool) !void {
        self.entry_count = try std.math.add(u8, self.entry_count, 1);
        try self.pushTextString(key);
        try self.data.append(self.allocator, if (value) 0xf5 else 0xf4);
    }

    fn serialise(self: *const MetadataCBOREncoder) ![]u8 {
        if (self.entry_count > 0x1f) return error.TooManyMetadataEntries;
        const encoded_size = try std.math.add(usize, self.data.items.len, 1);
        if (encoded_size > std.math.maxInt(u16)) return error.MetadataTooLarge;
        const output = try self.allocator.alloc(u8, encoded_size + 2);
        output[0] = 0xa0 + self.entry_count;
        @memcpy(output[1..encoded_size], self.data.items);
        std.mem.writeInt(u16, output[encoded_size..][0..2], @intCast(encoded_size), .big);
        return output;
    }

    fn pushTextString(self: *MetadataCBOREncoder, value: []const u8) !void {
        try self.pushStringHeader(0x60, 0x78, value.len);
        try self.data.appendSlice(self.allocator, value);
    }

    fn pushByteString(self: *MetadataCBOREncoder, value: []const u8) !void {
        try self.pushStringHeader(0x40, 0x58, value.len);
        try self.data.appendSlice(self.allocator, value);
    }

    fn pushStringHeader(
        self: *MetadataCBOREncoder,
        short_base: u8,
        long_marker: u8,
        length: usize,
    ) !void {
        if (length < 24) {
            try self.data.append(self.allocator, short_base + @as(u8, @intCast(length)));
        } else if (length <= 0xff) {
            try self.data.appendSlice(
                self.allocator,
                &.{ long_marker, @intCast(length) },
            );
        } else return error.MetadataStringTooLarge;
    }
};

test "CBOR metadata encodes the compatibility version" {
    const metadata =
        "{\"compiler\":{\"version\":\"" ++ Version.MetadataVersion ++ "\"}," ++
        "\"language\":\"Solidity\",\"output\":{\"abi\":[]," ++
        "\"devdoc\":{\"kind\":\"dev\",\"methods\":{},\"version\":1}," ++
        "\"userdoc\":{\"kind\":\"user\",\"methods\":{},\"version\":1}}," ++
        "\"settings\":{\"compilationTarget\":{\"C.sol\":\"C\"}," ++
        "\"evmVersion\":\"osaka\",\"libraries\":{}," ++
        "\"metadata\":{\"bytecodeHash\":\"ipfs\"}," ++
        "\"optimizer\":{\"enabled\":true,\"runs\":200}," ++
        "\"remappings\":[],\"viaIR\":true},\"sources\":{},\"version\":1}";
    const encoded = try createCBORMetadataAlloc(
        std.testing.allocator,
        metadata,
        .{},
    );
    defer std.testing.allocator.free(encoded);
    const hex = try CommonData.toHexAlloc(
        std.testing.allocator,
        encoded,
        .dont_add,
        .lower,
    );
    defer std.testing.allocator.free(hex);
    try std.testing.expect(std.mem.startsWith(u8, hex, "a2646970667358221220"));
    try std.testing.expect(std.mem.endsWith(u8, hex, "64736f6c63430008240033"));
    try std.testing.expectEqual(@as(usize, 106), hex.len);
}

test "disabled CBOR metadata is empty" {
    const encoded = try createCBORMetadataAlloc(
        std.testing.allocator,
        "{}",
        .{ .append_cbor = false },
    );
    defer std.testing.allocator.free(encoded);
    try std.testing.expectEqual(@as(usize, 0), encoded.len);
}

test "metadata remappings are canonicalized like the upstream set" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const remappings = [_]ImportRemapper.Remapping{
        .{ .context = "src", .prefix = "b/", .target = "vendor/b/" },
        .{ .context = "", .prefix = "a/", .target = "vendor/a/" },
        .{ .context = "src", .prefix = "b/", .target = "vendor/b/" },
    };
    var remapper = ImportRemapper.ImportRemapper.init(arena.allocator());
    defer remapper.deinit();
    try remapper.setRemappings(&remappings);
    const value = try metadataRemappings(
        arena.allocator(),
        remapper.remappings(),
    );
    try std.testing.expectEqual(@as(usize, 2), value.array.items.len);
    try std.testing.expectEqualStrings(
        ":a/=vendor/a/",
        value.array.items[0].string,
    );
    try std.testing.expectEqualStrings(
        "src:b/=vendor/b/",
        value.array.items[1].string,
    );
}

test "metadata remappings preserve original path spelling" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const remapping: ImportRemapper.NormalizedRemapping = .{
        .original_context = try allocator.dupe(u8, "src\\windows"),
        .original_prefix = try allocator.dupe(u8, "pkg\\"),
        .original_target = try allocator.dupe(u8, "vendor\\pkg\\"),
        .context = try allocator.dupe(u8, "src/windows"),
        .prefix = try allocator.dupe(u8, "pkg/"),
        .target = try allocator.dupe(u8, "vendor/pkg/"),
    };
    const value = try metadataRemappings(allocator, &.{remapping});
    try std.testing.expectEqualStrings(
        "src\\windows:pkg\\=vendor\\pkg\\",
        value.array.items[0].string,
    );
}
