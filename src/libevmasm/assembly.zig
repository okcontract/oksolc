// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned legacy assembly tree, optimizer orchestration, and bytecode emission.

const std = @import("std");
const Numeric = @import("../libsolutil/numeric.zig");
const CommonData = @import("../libsolutil/common_data.zig");
const JSON = @import("../libsolutil/json.zig");
const Keccak256 = @import("../libsolutil/keccak256.zig");
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;
const CharStream = @import("../liblangutil/char_stream.zig");
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const AssemblyItemModule = @import("assembly_item.zig");
const AssemblyItem = AssemblyItemModule.AssemblyItem;
const InstructionModule = @import("instruction.zig");
const LinkerObjectModule = @import("linker_object.zig");
const LinkerObject = LinkerObjectModule.LinkerObject;
pub const SubAssemblyID = @import("sub_assembly_id.zig").SubAssemblyID;
const BlockDeduplicator = @import("block_deduplicator.zig");
const CommonSubexpressionEliminator = @import("common_subexpression_eliminator.zig");
const ConstantOptimiser = @import("constant_optimiser.zig");
const Inliner = @import("inliner.zig");
const JumpdestRemover = @import("jumpdest_remover.zig");
const KnownState = @import("known_state.zig").KnownState;
const PeepholeOptimiser = @import("peephole_optimiser.zig");

pub const OptimiserSettings = struct {
    run_inliner: bool = false,
    run_jumpdest_remover: bool = false,
    run_peephole: bool = false,
    run_deduplicate: bool = false,
    run_cse: bool = false,
    run_constant_optimiser: bool = false,
    expected_executions_per_deployment: u64 = 200,
};

pub const SourceCode = struct {
    name: []const u8,
    code: []const u8,
};

pub const SourceIndex = AssemblyItemModule.SourceIndex;

pub const OwnedAssemblyJson = struct {
    backing_allocator: std.mem.Allocator,
    arena: *std.heap.ArenaAllocator,
    value: JSON.Json,

    fn init(backing_allocator: std.mem.Allocator) std.mem.Allocator.Error!OwnedAssemblyJson {
        const arena = try backing_allocator.create(std.heap.ArenaAllocator);
        arena.* = std.heap.ArenaAllocator.init(backing_allocator);
        return .{ .backing_allocator = backing_allocator, .arena = arena, .value = .null };
    }

    pub fn deinit(self: *OwnedAssemblyJson) void {
        self.arena.deinit();
        self.backing_allocator.destroy(self.arena);
        self.* = undefined;
    }
};

const NamedTagInfo = struct {
    name: []u8,
    id: usize,
    source_id: ?usize,
    params: usize,
    returns: usize,
};

/// Borrowed, pointer-free view used by portable assembly serializers.
pub const NamedTag = struct {
    name: []const u8,
    id: usize,
    source_id: ?usize,
    params: usize,
    returns: usize,
};

const DataEntry = struct { hash: u256, bytes: []u8 };
const NamedHash = struct { hash: u256, name: []u8 };
const SubPath = struct { path: []SubAssemblyID, id: SubAssemblyID };

pub const SubPathView = struct {
    path: []const SubAssemblyID,
    id: SubAssemblyID,
};

pub const AssemblyError = anyerror;

pub const Assembly = struct {
    allocator: std.mem.Allocator,
    invalid: bool = false,
    used_tags: u32 = 1,
    named_tags: std.ArrayList(NamedTagInfo) = .empty,
    data_entries: std.ArrayList(DataEntry) = .empty,
    auxiliary_data: std.ArrayList(u8) = .empty,
    subs: std.ArrayList(*Assembly) = .empty,
    assembly_items: std.ArrayList(AssemblyItem) = .empty,
    libraries: std.ArrayList(NamedHash) = .empty,
    immutables: std.ArrayList(NamedHash) = .empty,
    sub_paths: std.ArrayList(SubPath) = .empty,
    tag_replacements: ?std.ArrayList(BlockDeduplicator.TagReplacement) = null,
    assembled_object: LinkerObject = .{},
    tag_positions_in_bytecode: std.ArrayList(usize) = .empty,
    evm_version: EVMVersion,
    stack_deposit: i32 = 0,
    creation: bool,
    assembly_name: []u8,
    current_source_location: SourceLocation = .{},
    current_modifier_depth: usize = 0,
    owned_source_names: std.ArrayList([]u8) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        evm_version: EVMVersion,
        creation: bool,
        assembly_name_input: []const u8,
    ) std.mem.Allocator.Error!Assembly {
        return .{
            .allocator = allocator,
            .evm_version = evm_version,
            .creation = creation,
            .assembly_name = try allocator.dupe(u8, assembly_name_input),
        };
    }

    pub fn create(
        allocator: std.mem.Allocator,
        evm_version: EVMVersion,
        creation: bool,
        assembly_name_input: []const u8,
    ) std.mem.Allocator.Error!*Assembly {
        const result = try allocator.create(Assembly);
        errdefer allocator.destroy(result);
        result.* = try init(allocator, evm_version, creation, assembly_name_input);
        return result;
    }

    pub fn destroy(self: *Assembly) void {
        const allocator = self.allocator;
        self.deinit();
        allocator.destroy(self);
    }

    pub fn deinit(self: *Assembly) void {
        self.allocator.free(self.assembly_name);
        for (self.named_tags.items) |entry| self.allocator.free(entry.name);
        self.named_tags.deinit(self.allocator);
        for (self.data_entries.items) |entry| self.allocator.free(entry.bytes);
        self.data_entries.deinit(self.allocator);
        self.auxiliary_data.deinit(self.allocator);
        for (self.subs.items) |sub_assembly| sub_assembly.destroy();
        self.subs.deinit(self.allocator);
        deinitItems(self.allocator, &self.assembly_items);
        for (self.libraries.items) |entry| self.allocator.free(entry.name);
        self.libraries.deinit(self.allocator);
        for (self.immutables.items) |entry| self.allocator.free(entry.name);
        self.immutables.deinit(self.allocator);
        for (self.sub_paths.items) |entry| self.allocator.free(entry.path);
        self.sub_paths.deinit(self.allocator);
        if (self.tag_replacements) |*replacements| replacements.deinit(self.allocator);
        self.assembled_object.deinit(self.allocator);
        self.tag_positions_in_bytecode.deinit(self.allocator);
        for (self.owned_source_names.items) |source_name| self.allocator.free(source_name);
        self.owned_source_names.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn items(self: *Assembly) *std.ArrayList(AssemblyItem) {
        return &self.assembly_items;
    }

    pub fn itemsConst(self: *const Assembly) []const AssemblyItem {
        return self.assembly_items.items;
    }

    pub fn name(self: *const Assembly) []const u8 {
        return self.assembly_name;
    }

    pub fn setName(self: *Assembly, value: []const u8) std.mem.Allocator.Error!void {
        const owned = try self.allocator.dupe(u8, value);
        self.allocator.free(self.assembly_name);
        self.assembly_name = owned;
    }

    pub fn isCreation(self: *const Assembly) bool {
        return self.creation;
    }

    pub fn isInvalid(self: *const Assembly) bool {
        return self.invalid;
    }

    pub fn evmVersion(self: *const Assembly) EVMVersion {
        return self.evm_version;
    }

    pub fn deposit(self: *const Assembly) i32 {
        return self.stack_deposit;
    }

    pub fn adjustDeposit(self: *Assembly, adjustment: i32) AssemblyError!void {
        self.stack_deposit += adjustment;
        if (self.stack_deposit < 0) return error.StackUnderflow;
    }

    pub fn setDeposit(self: *Assembly, value: i32) AssemblyError!void {
        if (value < 0) return error.StackUnderflow;
        self.stack_deposit = value;
    }

    pub fn setSourceLocation(self: *Assembly, location: SourceLocation) void {
        self.current_source_location = location;
    }

    pub fn markAsInvalid(self: *Assembly) void {
        self.invalid = true;
    }

    pub fn newTag(self: *Assembly) AssemblyError!AssemblyItem {
        if (self.used_tags == std.math.maxInt(u32)) return error.OutOfTags;
        const result = AssemblyItem.initType(.Tag, self.used_tags, .{});
        self.used_tags += 1;
        return result;
    }

    pub fn newPushTag(self: *Assembly) AssemblyError!AssemblyItem {
        var result = try self.newTag();
        result.item_type = .PushTag;
        return result;
    }

    pub fn namedTag(
        self: *Assembly,
        tag_name: []const u8,
        params: usize,
        returns: usize,
        source_id: ?usize,
    ) AssemblyError!AssemblyItem {
        if (tag_name.len == 0) return error.EmptyNamedTag;
        const index = searchNamedTag(self.named_tags.items, tag_name);
        if (index.found) {
            const info = self.named_tags.items[index.index];
            if (info.params != params or info.returns != returns or info.source_id != source_id)
                return error.InconsistentNamedTag;
            return AssemblyItem.initType(.Tag, info.id, .{});
        }
        const tag = try self.newTag();
        const owned_name = try self.allocator.dupe(u8, tag_name);
        errdefer self.allocator.free(owned_name);
        try self.named_tags.insert(self.allocator, index.index, .{
            .name = owned_name,
            .id = @intCast(tag.data_value),
            .source_id = source_id,
            .params = params,
            .returns = returns,
        });
        return tag;
    }

    pub fn namedTagCount(self: *const Assembly) usize {
        return self.named_tags.items.len;
    }

    pub fn namedTagAt(self: *const Assembly, index: usize) NamedTag {
        const info = self.named_tags.items[index];
        return .{
            .name = info.name,
            .id = info.id,
            .source_id = info.source_id,
            .params = info.params,
            .returns = info.returns,
        };
    }

    /// Restores a named-tag side table after importing portable assembly JSON.
    /// The JSON already established `used_tags`, so an out-of-range or reused
    /// tag identifier proves that the persisted artifact is inconsistent.
    pub fn restoreNamedTag(self: *Assembly, info: NamedTag) AssemblyError!void {
        if (info.name.len == 0) return error.EmptyNamedTag;
        if (info.id == 0 or info.id >= self.used_tags)
            return error.ReferenceToMissingTag;
        const index = searchNamedTag(self.named_tags.items, info.name);
        if (index.found) return error.InconsistentNamedTag;
        for (self.named_tags.items) |existing|
            if (existing.id == info.id) return error.InconsistentNamedTag;
        const owned_name = try self.allocator.dupe(u8, info.name);
        errdefer self.allocator.free(owned_name);
        try self.named_tags.insert(self.allocator, index.index, .{
            .name = owned_name,
            .id = info.id,
            .source_id = info.source_id,
            .params = info.params,
            .returns = info.returns,
        });
    }

    pub fn usedTagCount(self: *const Assembly) u32 {
        return self.used_tags;
    }

    pub fn restoreUsedTagCount(self: *Assembly, value: u32) AssemblyError!void {
        if (value < self.used_tags) return error.InconsistentUsedTagCount;
        self.used_tags = value;
    }

    pub fn subPathCount(self: *const Assembly) usize {
        return self.sub_paths.items.len;
    }

    pub fn subPathAt(self: *const Assembly, index: usize) SubPathView {
        const entry = self.sub_paths.items[index];
        return .{ .path = entry.path, .id = entry.id };
    }

    pub fn clearSubPaths(self: *Assembly) void {
        for (self.sub_paths.items) |entry| self.allocator.free(entry.path);
        self.sub_paths.clearRetainingCapacity();
    }

    /// Restores the explicit ID-to-path mapping used by multi-level data
    /// references. These IDs depend on encounter order and cannot be
    /// reconstructed from legacy assembly JSON alone.
    pub fn restoreSubPath(
        self: *Assembly,
        id: SubAssemblyID,
        path: []const SubAssemblyID,
    ) AssemblyError!void {
        if (path.len < 2 or id.toInt() < self.subs.items.len)
            return error.InvalidSubPath;
        var target = self;
        for (path) |component| target = try target.sub(component);
        const index = searchSubPath(self.sub_paths.items, path);
        if (index.found) return error.DuplicateSubPath;
        for (self.sub_paths.items) |entry|
            if (entry.id.eql(id)) return error.DuplicateSubPathId;
        const owned_path = try self.allocator.dupe(SubAssemblyID, path);
        errdefer self.allocator.free(owned_path);
        try self.sub_paths.insert(self.allocator, index.index, .{
            .path = owned_path,
            .id = id,
        });
    }

    pub fn newData(self: *Assembly, data_bytes: []const u8) AssemblyError!AssemblyItem {
        const hash = Keccak256.keccak256(data_bytes).toInteger();
        const index = searchData(self.data_entries.items, hash);
        if (index.found) {
            const owned = try self.allocator.dupe(u8, data_bytes);
            self.allocator.free(self.data_entries.items[index.index].bytes);
            self.data_entries.items[index.index].bytes = owned;
        } else {
            const owned = try self.allocator.dupe(u8, data_bytes);
            errdefer self.allocator.free(owned);
            try self.data_entries.insert(self.allocator, index.index, .{ .hash = hash, .bytes = owned });
        }
        return AssemblyItem.initType(.PushData, hash, .{});
    }

    pub fn data(self: *const Assembly, hash: u256) AssemblyError![]const u8 {
        const index = searchData(self.data_entries.items, hash);
        if (!index.found) return error.DataNotFound;
        return self.data_entries.items[index.index].bytes;
    }

    pub fn newSub(self: *Assembly, sub_assembly: *Assembly) std.mem.Allocator.Error!AssemblyItem {
        errdefer sub_assembly.destroy();
        try self.subs.append(self.allocator, sub_assembly);
        return AssemblyItem.initType(.PushSub, self.subs.items.len - 1, .{});
    }

    pub fn sub(self: *Assembly, id: SubAssemblyID) AssemblyError!*Assembly {
        const index = try id.asIndex();
        if (index >= self.subs.items.len) return error.SubassemblyNotFound;
        return self.subs.items[index];
    }

    pub fn newPushSubSize(_: *Assembly, id: SubAssemblyID) AssemblyItem {
        return AssemblyItem.initType(.PushSubSize, id.value, .{});
    }

    pub fn newPushLibraryAddress(self: *Assembly, identifier: []const u8) AssemblyError!AssemblyItem {
        const hash = Keccak256.keccak256(identifier).toInteger();
        try putNamedHash(self.allocator, &self.libraries, hash, identifier);
        return AssemblyItem.initType(.PushLibraryAddress, hash, .{});
    }

    pub fn newPushImmutable(self: *Assembly, identifier: []const u8) AssemblyError!AssemblyItem {
        const hash = Keccak256.keccak256(identifier).toInteger();
        try putNamedHash(self.allocator, &self.immutables, hash, identifier);
        return AssemblyItem.initType(.PushImmutable, hash, .{});
    }

    pub fn newImmutableAssignment(self: *Assembly, identifier: []const u8) AssemblyError!AssemblyItem {
        const hash = Keccak256.keccak256(identifier).toInteger();
        try putNamedHash(self.allocator, &self.immutables, hash, identifier);
        return AssemblyItem.initType(.AssignImmutable, hash, .{});
    }

    /// Transfers ownership of `item` to the assembly.
    pub fn append(self: *Assembly, item_value: AssemblyItem) AssemblyError!*const AssemblyItem {
        if (self.stack_deposit < 0) return error.StackUnderflow;
        var item = item_value;
        self.stack_deposit += @intCast(item.deposit());
        if (!item.location().isValid() and self.current_source_location.isValid())
            item.setLocation(self.current_source_location);
        item.modifier_depth = self.current_modifier_depth;
        try self.assembly_items.append(self.allocator, item);
        return &self.assembly_items.items[self.assembly_items.items.len - 1];
    }

    pub fn appendData(self: *Assembly, data_bytes: []const u8) AssemblyError!*const AssemblyItem {
        return self.append(try self.newData(data_bytes));
    }

    pub fn appendProgramSize(self: *Assembly) AssemblyError!void {
        _ = try self.append(AssemblyItem.initType(.PushProgramSize, 0, .{}));
    }

    pub fn appendToAuxiliaryData(self: *Assembly, data_bytes: []const u8) std.mem.Allocator.Error!void {
        try self.auxiliary_data.appendSlice(self.allocator, data_bytes);
    }

    pub fn appendVerbatim(
        self: *Assembly,
        data_bytes: []const u8,
        arguments: usize,
        returns: usize,
    ) AssemblyError!void {
        _ = try self.append(try AssemblyItem.initVerbatim(self.allocator, data_bytes, arguments, returns));
    }

    pub fn codeSize(self: *const Assembly, initial_tag_size: u32) AssemblyError!u32 {
        var tag_size = initial_tag_size;
        while (true) : (tag_size += 1) {
            var result: usize = 1;
            for (self.data_entries.items) |entry| result += entry.bytes.len;
            for (self.assembly_items.items) |*item|
                result += try item.bytesRequired(tag_size, self.evm_version, .Precise);
            if (Numeric.numberEncodingSize(usize, result) <= tag_size) return @intCast(result);
        }
    }

    pub fn optimise(self: *Assembly, settings: OptimiserSettings) AssemblyError!void {
        _ = try self.optimiseInternal(settings, &.{});
    }

    fn optimiseInternal(
        self: *Assembly,
        settings: OptimiserSettings,
        outside_tags_input: []const usize,
    ) AssemblyError![]const BlockDeduplicator.TagReplacement {
        if (self.tag_replacements) |*cached| return cached.items;

        var outside_tags: JumpdestRemover.TagSet = .{};
        defer outside_tags.deinit(self.allocator);
        for (outside_tags_input) |tag| _ = try outside_tags.insert(self.allocator, tag);

        for (self.subs.items, 0..) |sub_assembly, sub_index| {
            var references = try JumpdestRemover.referencedTagsAlloc(
                self.allocator,
                self.assembly_items.items,
                SubAssemblyID.init(sub_index),
            );
            defer references.deinit(self.allocator);
            const replacements = try sub_assembly.optimiseInternal(settings, references.values.items);
            _ = BlockDeduplicator.applyTagReplacement(
                self.assembly_items.items,
                replacements,
                SubAssemblyID.init(sub_index),
            );
        }

        var replacements: std.ArrayList(BlockDeduplicator.TagReplacement) = .empty;
        errdefer replacements.deinit(self.allocator);
        var iteration_count: u32 = 1;
        while (iteration_count != 0) {
            iteration_count = 0;
            if (settings.run_inliner) {
                var inliner = Inliner.Inliner.init(
                    self.allocator,
                    &self.assembly_items,
                    outside_tags.values.items,
                    settings.expected_executions_per_deployment,
                    self.creation,
                    self.evm_version,
                );
                try inliner.optimise();
            }
            if (settings.run_jumpdest_remover and try JumpdestRemover.optimise(
                self.allocator,
                &self.assembly_items,
                outside_tags.values.items,
            )) iteration_count += 1;

            if (settings.run_peephole) {
                while (try PeepholeOptimiser.optimise(self.allocator, &self.assembly_items, self.evm_version)) {
                    iteration_count += 1;
                    if (iteration_count >= 64_000) return error.PeepholeOptimizerStuck;
                }
            }

            if (settings.run_deduplicate) {
                var deduplicator: BlockDeduplicator.BlockDeduplicator = .{};
                defer deduplicator.deinit(self.allocator);
                if (try deduplicator.deduplicate(self.allocator, &self.assembly_items)) {
                    for (deduplicator.replacements()) |replacement| {
                        const found = searchReplacement(replacements.items, replacement.from);
                        if (found.found) return error.ReplacementAlreadyKnown;
                        try replacements.insert(self.allocator, found.index, replacement);
                        if (outside_tags.contains(@intCast(replacement.from))) {
                            _ = removeTag(&outside_tags, @intCast(replacement.from));
                            _ = try outside_tags.insert(self.allocator, @intCast(replacement.to));
                        }
                    }
                    iteration_count += 1;
                }
            }

            if (settings.run_cse) {
                try self.optimiseCSE(&iteration_count);
            }
        }

        if (settings.run_constant_optimiser) {
            _ = try ConstantOptimiser.optimiseConstants(
                self.allocator,
                self.creation,
                if (self.creation) 1 else settings.expected_executions_per_deployment,
                self.evm_version,
                &self.assembly_items,
                .{ .context = self, .add_data = addConstantData },
            );
        }
        self.tag_replacements = replacements;
        return self.tag_replacements.?.items;
    }

    fn optimiseCSE(self: *Assembly, iteration_count: *u32) AssemblyError!void {
        var uses_msize = false;
        for (self.assembly_items.items) |*item| {
            if (item.eqlInstruction(.MSIZE) or item.item_type == .VerbatimBytecode) {
                uses_msize = true;
                break;
            }
        }
        var optimized: std.ArrayList(AssemblyItem) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitItems(self.allocator, &optimized);
        var index: usize = 0;
        while (index < self.assembly_items.items.len) {
            var state = try KnownState.init(self.allocator);
            defer state.deinit();
            var eliminator = try CommonSubexpressionEliminator.CommonSubexpressionEliminator.init(
                self.allocator,
                &state,
                self.evm_version,
            );
            defer eliminator.deinit();
            const consumed = try eliminator.feedItems(self.assembly_items.items[index..], uses_msize);
            var chunk = eliminator.getOptimizedItems() catch |err| switch (err) {
                error.StackTooDeep, error.ItemNotAvailable => {
                    for (self.assembly_items.items[index .. index + consumed]) |*item|
                        try appendClone(self.allocator, &optimized, item);
                    index += consumed;
                    continue;
                },
                else => return err,
            };
            defer deinitItems(self.allocator, &chunk);
            if (chunk.items.len < consumed) {
                iteration_count.* += 1;
                for (chunk.items) |*item| try appendClone(self.allocator, &optimized, item);
            } else {
                for (self.assembly_items.items[index .. index + consumed]) |*item|
                    try appendClone(self.allocator, &optimized, item);
            }
            index += consumed;
        }
        if (optimized.items.len < self.assembly_items.items.len) {
            deinitItems(self.allocator, &self.assembly_items);
            self.assembly_items = optimized;
            optimized = .empty;
            iteration_count.* += 1;
        }
        deinitItems(self.allocator, &optimized);
    }

    fn addConstantData(context: *anyopaque, data_bytes: [32]u8) anyerror!AssemblyItem {
        const self: *Assembly = @ptrCast(@alignCast(context));
        return self.newData(&data_bytes);
    }

    pub fn assemble(self: *Assembly) AssemblyError!*const LinkerObject {
        if (self.invalid) return error.InvalidAssembly;
        if (self.assembled_object.bytecode.items.len != 0) return &self.assembled_object;
        if (self.assembled_object.link_references.items.len != 0) return error.UnexpectedLinkReferences;
        return self.assembleLegacy();
    }

    fn assembleLegacy(self: *Assembly) AssemblyError!*const LinkerObject {
        if (self.invalid) return error.InvalidAssembly;
        if (self.assembled_object.bytecode.items.len != 0) return &self.assembled_object;
        if (self.assembled_object.link_references.items.len != 0) return error.UnexpectedLinkReferences;

        var sub_tag_size: usize = 1;
        var immutable_by_sub: std.ArrayList(LinkerObjectModule.ImmutableReference) = .empty;
        defer {
            for (immutable_by_sub.items) |*reference| reference.references.deinit(self.allocator);
            immutable_by_sub.deinit(self.allocator);
        }
        for (self.subs.items) |sub_assembly| {
            const object = try sub_assembly.assemble();
            if (object.immutable_references.items.len != 0) {
                if (immutable_by_sub.items.len != 0) return error.MultipleImmutableSubassemblies;
                for (object.immutable_references.items) |reference|
                    try immutable_by_sub.append(self.allocator, .{
                        .hash = reference.hash,
                        .references = try reference.references.clone(self.allocator),
                    });
            }
            for (sub_assembly.tag_positions_in_bytecode.items) |tag_position| {
                if (tag_position != std.math.maxInt(usize))
                    sub_tag_size = @max(sub_tag_size, Numeric.numberEncodingSize(usize, tag_position));
            }
        }

        var sets_immutables = false;
        var pushes_immutables = false;
        for (self.assembly_items.items) |*item| {
            if (item.item_type == .AssignImmutable) {
                item.immutable_occurrences = immutableOffsets(immutable_by_sub.items, item.data_value).len;
                sets_immutables = true;
            } else if (item.item_type == .PushImmutable) {
                pushes_immutables = true;
            }
        }
        if ((sets_immutables or pushes_immutables) and sets_immutables == pushes_immutables)
            return error.PushAndAssignImmutables;

        const bytes_required_for_code = try self.codeSize(@intCast(sub_tag_size));
        self.tag_positions_in_bytecode.clearRetainingCapacity();
        try self.tag_positions_in_bytecode.appendNTimes(
            self.allocator,
            std.math.maxInt(usize),
            self.used_tags,
        );
        var bytes_per_tag = Numeric.numberEncodingSize(u32, bytes_required_for_code);
        for (self.assembly_items.items) |*item| {
            if (item.item_type != .PushTag) continue;
            const split = try item.splitForeignPushTag();
            if (split[0].empty()) continue;
            const sub_assembly = try self.sub(split[0]);
            if (split[1] >= sub_assembly.tag_positions_in_bytecode.items.len)
                return error.ReferenceToMissingTag;
            const position = sub_assembly.tag_positions_in_bytecode.items[split[1]];
            if (position == std.math.maxInt(usize)) return error.ReferenceToTagWithoutPosition;
            bytes_per_tag = @max(bytes_per_tag, Numeric.numberEncodingSize(usize, position));
        }

        var bytes_required_including_data: usize = bytes_required_for_code + 1 + self.auxiliary_data.items.len;
        for (self.subs.items) |sub_assembly|
            bytes_required_including_data += (try sub_assembly.assemble()).bytecode.items.len;
        const bytes_per_data_ref = Numeric.numberEncodingSize(usize, bytes_required_including_data);

        const TagRef = struct { offset: usize, sub_id: SubAssemblyID, tag_id: usize };
        const DataRef = struct { hash: u256, offset: usize };
        const SubRef = struct { id: SubAssemblyID, offset: usize };
        var tag_refs: std.ArrayList(TagRef) = .empty;
        defer tag_refs.deinit(self.allocator);
        var data_refs: std.ArrayList(DataRef) = .empty;
        defer data_refs.deinit(self.allocator);
        var sub_refs: std.ArrayList(SubRef) = .empty;
        defer sub_refs.deinit(self.allocator);
        var size_refs: std.ArrayList(usize) = .empty;
        defer size_refs.deinit(self.allocator);

        const ret = &self.assembled_object;
        try ret.bytecode.ensureTotalCapacity(self.allocator, bytes_required_including_data);
        var code_locations: LinkerObjectModule.CodeSectionLocation = .{ .start = 0 };
        errdefer code_locations.deinit(self.allocator);
        try code_locations.instruction_locations.ensureTotalCapacity(self.allocator, self.assembly_items.items.len);

        const tag_push = @intFromEnum(InstructionModule.pushInstruction(@intCast(bytes_per_tag)));
        const data_ref_push = @intFromEnum(InstructionModule.pushInstruction(@intCast(bytes_per_data_ref)));
        for (self.assembly_items.items, 0..) |*item, item_index| {
            var location_start = ret.bytecode.items.len;
            if (item.item_type != .Tag and self.tag_positions_in_bytecode.items[0] == std.math.maxInt(usize))
                self.tag_positions_in_bytecode.items[0] = ret.bytecode.items.len;
            switch (item.item_type) {
                .Operation => try ret.bytecode.append(self.allocator, @intFromEnum(item.instruction_value.?)),
                .Push => try appendPush(self.allocator, &ret.bytecode, item.data_value, self.evm_version),
                .PushTag => {
                    try ret.bytecode.append(self.allocator, tag_push);
                    const split = try item.splitForeignPushTag();
                    try tag_refs.append(self.allocator, .{
                        .offset = ret.bytecode.items.len,
                        .sub_id = split[0],
                        .tag_id = split[1],
                    });
                    try ret.bytecode.appendNTimes(self.allocator, 0, bytes_per_tag);
                },
                .PushData => {
                    try ret.bytecode.append(self.allocator, data_ref_push);
                    try insertDataRef(self.allocator, &data_refs, DataRef{
                        .hash = item.data_value,
                        .offset = ret.bytecode.items.len,
                    });
                    try ret.bytecode.appendNTimes(self.allocator, 0, bytes_per_data_ref);
                },
                .PushSub => {
                    const id = try SubAssemblyID.fromU256(item.data_value);
                    try ret.bytecode.append(self.allocator, data_ref_push);
                    try insertSubRef(
                        self.allocator,
                        &sub_refs,
                        SubRef{ .id = id, .offset = ret.bytecode.items.len },
                    );
                    try ret.bytecode.appendNTimes(self.allocator, 0, bytes_per_data_ref);
                },
                .PushSubSize => {
                    const sub_assembly = try self.subAssemblyById(try SubAssemblyID.fromU256(item.data_value));
                    const size = (try sub_assembly.assemble()).bytecode.items.len;
                    item.pushed_value = size;
                    const width = @max(@as(usize, 1), Numeric.numberEncodingSize(usize, size));
                    try ret.bytecode.append(
                        self.allocator,
                        @intFromEnum(InstructionModule.pushInstruction(@intCast(width))),
                    );
                    try appendBigEndian(self.allocator, &ret.bytecode, width, size);
                },
                .PushProgramSize => {
                    try ret.bytecode.append(self.allocator, data_ref_push);
                    try size_refs.append(self.allocator, ret.bytecode.items.len);
                    try ret.bytecode.appendNTimes(self.allocator, 0, bytes_per_data_ref);
                },
                .PushLibraryAddress => {
                    try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.PUSH20));
                    try ret.putLinkReference(
                        self.allocator,
                        ret.bytecode.items.len,
                        try lookupNamedHash(self.libraries.items, item.data_value),
                    );
                    try ret.bytecode.appendNTimes(self.allocator, 0, 20);
                },
                .PushImmutable => {
                    try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.PUSH32));
                    try appendImmutableReference(
                        self.allocator,
                        ret,
                        item.data_value,
                        try lookupNamedHash(self.immutables.items, item.data_value),
                        ret.bytecode.items.len,
                    );
                    try ret.bytecode.appendNTimes(self.allocator, 0, 32);
                },
                .VerbatimBytecode => try ret.bytecode.appendSlice(self.allocator, try item.verbatimData()),
                .AssignImmutable => {
                    const offsets = immutableOffsets(immutable_by_sub.items, item.data_value);
                    for (offsets, 0..) |offset, index| {
                        if (index != offsets.len - 1) {
                            try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.DUP2));
                            try emitLocation(self.allocator, &code_locations, item_index, &location_start, ret.bytecode.items.len);
                            try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.DUP2));
                            try emitLocation(self.allocator, &code_locations, item_index, &location_start, ret.bytecode.items.len);
                        }
                        const width = @max(@as(usize, 1), Numeric.numberEncodingSize(usize, offset));
                        try ret.bytecode.append(
                            self.allocator,
                            @intFromEnum(InstructionModule.pushInstruction(@intCast(width))),
                        );
                        try appendBigEndian(self.allocator, &ret.bytecode, width, offset);
                        try emitLocation(self.allocator, &code_locations, item_index, &location_start, ret.bytecode.items.len);
                        try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.ADD));
                        try emitLocation(self.allocator, &code_locations, item_index, &location_start, ret.bytecode.items.len);
                        try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.MSTORE));
                    }
                    if (offsets.len == 0) {
                        try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.POP));
                        try emitLocation(self.allocator, &code_locations, item_index, &location_start, ret.bytecode.items.len);
                        try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.POP));
                    }
                    removeImmutableReference(self.allocator, &immutable_by_sub, item.data_value);
                },
                .PushDeployTimeAddress => {
                    try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.PUSH20));
                    try ret.bytecode.appendNTimes(self.allocator, 0, 20);
                },
                .Tag => try self.assembleTag(item, ret.bytecode.items.len, true, &ret.bytecode),
                .UndefinedItem => return error.UnexpectedAssemblyItem,
            }
            try emitLocation(self.allocator, &code_locations, item_index, &location_start, ret.bytecode.items.len);
        }
        code_locations.end = ret.bytecode.items.len;
        ret.code_section_location.deinit(self.allocator);
        ret.code_section_location = code_locations;
        code_locations = .{};

        if (immutable_by_sub.items.len != 0) return error.UnassignedImmutable;
        if (self.subs.items.len != 0 or self.data_entries.items.len != 0 or self.auxiliary_data.items.len != 0)
            try ret.bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.INVALID));

        const SubOffset = struct { object: *const LinkerObject, offset: usize };
        var sub_offsets: std.ArrayList(SubOffset) = .empty;
        defer sub_offsets.deinit(self.allocator);
        for (sub_refs.items) |reference| {
            const sub_object = try (try self.subAssemblyById(reference.id)).assemble();
            const existing_offset = findSubObject(sub_offsets.items, sub_object);
            const offset = existing_offset orelse ret.bytecode.items.len;
            writeBigEndian(ret.bytecode.items[reference.offset..][0..bytes_per_data_ref], offset);
            if (existing_offset == null) {
                try sub_offsets.append(self.allocator, .{ .object = sub_object, .offset = offset });
                try ret.bytecode.appendSlice(self.allocator, sub_object.bytecode.items);
            }
            for (sub_object.link_references.items) |link_reference|
                try ret.putLinkReference(
                    self.allocator,
                    link_reference.offset + offset,
                    link_reference.library_name,
                );
        }

        for (tag_refs.items) |reference| {
            const positions = if (reference.sub_id.empty())
                self.tag_positions_in_bytecode.items
            else
                (try self.sub(reference.sub_id)).tag_positions_in_bytecode.items;
            if (reference.tag_id >= positions.len) return error.ReferenceToMissingTag;
            const position = positions[reference.tag_id];
            if (position == std.math.maxInt(usize)) return error.ReferenceToTagWithoutPosition;
            if (Numeric.numberEncodingSize(usize, position) > bytes_per_tag) return error.TagTooLarge;
            writeBigEndian(ret.bytecode.items[reference.offset..][0..bytes_per_tag], position);
        }

        for (self.named_tags.items) |named_tag| {
            if (named_tag.id >= self.tag_positions_in_bytecode.items.len) return error.ReferenceToMissingTag;
            const position = self.tag_positions_in_bytecode.items[named_tag.id];
            var instruction_index: ?usize = null;
            for (self.assembly_items.items, 0..) |item, index| {
                if (item.item_type == .Tag and item.data_value == named_tag.id) {
                    instruction_index = index;
                    break;
                }
            }
            try ret.putFunctionDebugData(self.allocator, named_tag.name, .{
                .bytecode_offset = if (position == std.math.maxInt(usize)) null else position,
                .instruction_index = instruction_index,
                .source_id = named_tag.source_id,
                .params = named_tag.params,
                .returns = named_tag.returns,
            });
        }

        for (self.data_entries.items) |data_entry| {
            var referenced = false;
            for (data_refs.items) |reference| {
                if (reference.hash != data_entry.hash) continue;
                referenced = true;
                writeBigEndian(
                    ret.bytecode.items[reference.offset..][0..bytes_per_data_ref],
                    ret.bytecode.items.len,
                );
            }
            if (referenced) try ret.bytecode.appendSlice(self.allocator, data_entry.bytes);
        }
        try ret.bytecode.appendSlice(self.allocator, self.auxiliary_data.items);
        for (size_refs.items) |offset|
            writeBigEndian(ret.bytecode.items[offset..][0..bytes_per_data_ref], ret.bytecode.items.len);
        return ret;
    }

    fn assembleTag(
        self: *Assembly,
        item: *const AssemblyItem,
        position: usize,
        add_jump_dest: bool,
        bytecode: *std.ArrayList(u8),
    ) AssemblyError!void {
        if (item.data_value == 0) return error.InvalidTagPosition;
        const split = try item.splitForeignPushTag();
        if (!split[0].empty()) return error.ForeignTag;
        if (position >= 0xffff_ffff) return error.TagTooLarge;
        if (split[1] >= self.tag_positions_in_bytecode.items.len) return error.ReferenceToMissingTag;
        if (self.tag_positions_in_bytecode.items[split[1]] != std.math.maxInt(usize))
            return error.DuplicateTagPosition;
        self.tag_positions_in_bytecode.items[split[1]] = position;
        if (add_jump_dest)
            try bytecode.append(self.allocator, @intFromEnum(InstructionModule.Instruction.JUMPDEST));
    }

    pub fn encodeSubPath(self: *Assembly, path: []const SubAssemblyID) AssemblyError!SubAssemblyID {
        if (path.len == 0) return error.EmptySubPath;
        if (path.len == 1) {
            if (path[0].value >= self.subs.items.len) return error.SubassemblyNotFound;
            return path[0];
        }
        const found = searchSubPath(self.sub_paths.items, path);
        if (found.found) return self.sub_paths.items[found.index].id;
        const id = SubAssemblyID.init(std.math.maxInt(u64) - self.sub_paths.items.len);
        if (id.value < self.subs.items.len) return error.OutOfSubassemblyIds;
        const owned_path = try self.allocator.dupe(SubAssemblyID, path);
        errdefer self.allocator.free(owned_path);
        try self.sub_paths.insert(self.allocator, found.index, .{ .path = owned_path, .id = id });
        return id;
    }

    pub fn decodeSubPathAlloc(
        self: *const Assembly,
        allocator: std.mem.Allocator,
        id: SubAssemblyID,
    ) AssemblyError![]SubAssemblyID {
        if (id.value < self.subs.items.len) {
            const result = try allocator.alloc(SubAssemblyID, 1);
            result[0] = id;
            return result;
        }
        for (self.sub_paths.items) |entry|
            if (entry.id.eql(id)) return allocator.dupe(SubAssemblyID, entry.path);
        return error.SubassemblyNotFound;
    }

    fn subAssemblyById(self: *Assembly, id: SubAssemblyID) AssemblyError!*Assembly {
        const path = try self.decodeSubPathAlloc(self.allocator, id);
        defer self.allocator.free(path);
        var current = self;
        for (path) |component| current = try current.sub(component);
        if (current == self) return error.SubassemblyNotFound;
        return current;
    }

    fn decodeSubPathContext(
        context: ?*const anyopaque,
        allocator: std.mem.Allocator,
        id: SubAssemblyID,
    ) AssemblyItemModule.AssemblyItemError![]SubAssemblyID {
        const self: *const Assembly = @ptrCast(@alignCast(context.?));
        return self.decodeSubPathAlloc(allocator, id) catch |err| switch (err) {
            error.OutOfMemory => error.OutOfMemory,
            else => error.MissingSubPathDecoder,
        };
    }

    pub fn assemblyStringAlloc(
        self: *const Assembly,
        allocator: std.mem.Allocator,
        selection: DebugInfoSelection,
        source_codes: []const SourceCode,
    ) AssemblyError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(allocator);
        if (selection.ethdebug) try output.appendSlice(allocator, "/// ethdebug: enabled\n");
        try self.appendAssemblyText(allocator, &output, selection, "", source_codes);
        return output.toOwnedSlice(allocator);
    }

    pub fn assemblyJSONAlloc(
        self: *const Assembly,
        allocator: std.mem.Allocator,
        source_indices: []const SourceIndex,
        include_source_list: bool,
    ) AssemblyError!OwnedAssemblyJson {
        var result = try OwnedAssemblyJson.init(allocator);
        errdefer result.deinit();
        result.value = try buildAssemblyJSON(
            self,
            result.arena.allocator(),
            source_indices,
            include_source_list,
        );
        return result;
    }

    /// Builds the assembly JSON directly in a caller-owned arena. This is the
    /// natural form for Standard JSON, whose complete output already has one
    /// enclosing arena and is serialized before that arena is released.
    pub fn assemblyJSONValue(
        self: *const Assembly,
        allocator: std.mem.Allocator,
        source_indices: []const SourceIndex,
        include_source_list: bool,
    ) AssemblyError!JSON.Json {
        return buildAssemblyJSON(
            self,
            allocator,
            source_indices,
            include_source_list,
        );
    }

    pub fn sourceNames(self: *const Assembly) []const []u8 {
        return self.owned_source_names.items;
    }

    pub fn fromJSON(
        allocator: std.mem.Allocator,
        input: *const JSON.Json,
    ) AssemblyError!*Assembly {
        return fromJSONForVersion(allocator, input, EVMVersion.current());
    }

    /// Imports the portable legacy-assembly representation for an explicit
    /// EVM revision. Persistent artifacts must not silently adopt the running
    /// compiler's default revision when an older target is requested.
    pub fn fromJSONForVersion(
        allocator: std.mem.Allocator,
        input: *const JSON.Json,
        evm_version: EVMVersion,
    ) AssemblyError!*Assembly {
        const root_object = jsonObject(input) orelse return error.AssemblyJsonNotObject;
        try validateJsonMembers(root_object, &.{ ".code", ".data", ".auxdata", "sourceList" });

        var source_names: std.ArrayList([]u8) = .empty;
        errdefer {
            for (source_names.items) |source_name| allocator.free(source_name);
            source_names.deinit(allocator);
        }
        if (root_object.getPtr("sourceList")) |source_list_value| {
            const source_list = jsonArray(source_list_value) orelse return error.SourceListNotArray;
            for (source_list.items) |*source_name_value| {
                const source_name = jsonString(source_name_value) orelse return error.InvalidSourceListItem;
                for (source_names.items) |existing|
                    if (std.mem.eql(u8, existing, source_name)) return error.DuplicateSourceName;
                const owned_name = try allocator.dupe(u8, source_name);
                errdefer allocator.free(owned_name);
                try source_names.append(allocator, owned_name);
            }
        }

        const result = try parseAssemblyJSONNode(
            allocator,
            input,
            source_names.items,
            0,
            evm_version,
        );
        errdefer result.destroy();
        result.owned_source_names = source_names;
        source_names = .empty;
        try result.encodeAllPossibleSubPaths();
        return result;
    }

    fn encodeAllPossibleSubPaths(self: *Assembly) AssemblyError!void {
        var path: std.ArrayList(SubAssemblyID) = .empty;
        defer path.deinit(self.allocator);
        var ancestors: std.ArrayList(*Assembly) = .empty;
        defer ancestors.deinit(self.allocator);
        try encodeSubPathsRecursive(self, &path, &ancestors);
    }

    fn appendAssemblyText(
        self: *const Assembly,
        allocator: std.mem.Allocator,
        output: *std.ArrayList(u8),
        selection: DebugInfoSelection,
        prefix: []const u8,
        source_codes: []const SourceCode,
    ) AssemblyError!void {
        var pending: std.ArrayList([]u8) = .empty;
        defer {
            for (pending.items) |expression| allocator.free(expression);
            pending.deinit(allocator);
        }
        var location: SourceLocation = .{};
        for (self.assembly_items.items) |*item| {
            if (item.location().isValid() and !item.location().eql(location)) {
                try flushExpressions(allocator, output, prefix, &pending);
                location = item.location().*;
                try appendLocation(allocator, output, prefix, location, selection, source_codes);
            }
            var expression = try item.toAssemblyTextAlloc(allocator, .{
                .evm_version = self.evm_version,
                .context = self,
                .decode_sub_path = decodeSubPathContext,
            });
            errdefer allocator.free(expression);
            if (!item.canBeFunctional() or item.returnValues() > 1 or item.arguments() > pending.items.len) {
                try flushExpressions(allocator, output, prefix, &pending);
                try output.appendSlice(allocator, prefix);
                if (item.item_type != .Tag) try output.appendSlice(allocator, "  ");
                try output.appendSlice(allocator, expression);
                try output.append(allocator, '\n');
                allocator.free(expression);
                continue;
            }
            if (item.arguments() != 0) {
                var functional: std.ArrayList(u8) = .empty;
                errdefer functional.deinit(allocator);
                try functional.appendSlice(allocator, expression);
                try functional.append(allocator, '(');
                allocator.free(expression);
                for (0..item.arguments()) |argument_index| {
                    const argument = pending.pop().?;
                    defer allocator.free(argument);
                    try functional.appendSlice(allocator, argument);
                    if (argument_index + 1 < item.arguments()) try functional.appendSlice(allocator, ", ");
                }
                try functional.append(allocator, ')');
                expression = try functional.toOwnedSlice(allocator);
            }
            try pending.append(allocator, expression);
            if (item.returnValues() != 1) try flushExpressions(allocator, output, prefix, &pending);
        }
        try flushExpressions(allocator, output, prefix, &pending);

        if (self.data_entries.items.len != 0 or self.subs.items.len != 0) {
            try output.appendSlice(allocator, prefix);
            try output.appendSlice(allocator, "stop\n");
            for (self.data_entries.items) |entry| {
                if (entry.hash < self.subs.items.len) continue;
                const hash = Numeric.toBigEndian256(entry.hash);
                const hash_hex = try CommonData.toHexAlloc(allocator, &hash, .dont_add, .lower);
                defer allocator.free(hash_hex);
                const data_hex = try CommonData.toHexAlloc(allocator, entry.bytes, .dont_add, .lower);
                defer allocator.free(data_hex);
                try appendFormat(allocator, output, "{s}data_{s} {s}\n", .{ prefix, hash_hex, data_hex });
            }
            for (self.subs.items, 0..) |sub_assembly, index| {
                try appendFormat(allocator, output, "\n{s}sub_{d}: assembly {{\n", .{ prefix, index });
                const child_prefix = try std.fmt.allocPrint(allocator, "{s}    ", .{prefix});
                defer allocator.free(child_prefix);
                try sub_assembly.appendAssemblyText(allocator, output, selection, child_prefix, source_codes);
                try appendFormat(allocator, output, "{s}}}\n", .{prefix});
            }
        }
        if (self.auxiliary_data.items.len != 0) {
            const auxiliary_hex = try CommonData.toHexAlloc(
                allocator,
                self.auxiliary_data.items,
                .dont_add,
                .lower,
            );
            defer allocator.free(auxiliary_hex);
            try appendFormat(allocator, output, "\n{s}auxdata: 0x{s}\n", .{ prefix, auxiliary_hex });
        }
    }
};

fn buildAssemblyJSON(
    assembly: *const Assembly,
    allocator: std.mem.Allocator,
    source_indices: []const SourceIndex,
    include_source_list: bool,
) AssemblyError!JSON.Json {
    var root: JSON.Json = .{ .object = .empty };
    var code = std.json.Array.init(allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result

    for (assembly.assembly_items.items) |*item| {
        const source_index = try sourceIndexForLocation(item.location().*, source_indices);
        try code.append(try assemblyItemJSON(assembly, allocator, item, source_index, false));
        if (item.item_type == .Tag)
            try code.append(try assemblyItemJSON(assembly, allocator, item, source_index, true));
    }
    try root.object.put(allocator, ".code", .{ .array = code });

    if (include_source_list) {
        var source_list = std.json.Array.init(allocator);
        for (0..source_indices.len) |_| try source_list.append(.null);
        for (source_indices, 0..) |entry, entry_index| {
            if (entry.index >= source_indices.len) return error.NonContiguousSourceIndices;
            for (source_indices[0..entry_index]) |previous| {
                if (std.mem.eql(u8, previous.source_name, entry.source_name))
                    return error.DuplicateSourceName;
                if (previous.index == entry.index) return error.DuplicateSourceIndex;
            }
            source_list.items[@intCast(entry.index)] = try jsonOwnedString(allocator, entry.source_name);
        }
        try root.object.put(allocator, "sourceList", .{ .array = source_list });
    }

    if (assembly.data_entries.items.len != 0 or assembly.subs.items.len != 0) {
        var data: JSON.Json = .{ .object = .empty };
        for (assembly.data_entries.items) |entry| {
            if (entry.hash < assembly.subs.items.len) continue;
            const hash_bytes = Numeric.toBigEndian256(entry.hash);
            const key = try CommonData.toHexAlloc(allocator, &hash_bytes, .dont_add, .upper);
            const value = try CommonData.toHexAlloc(allocator, entry.bytes, .dont_add, .lower);
            try data.object.put(allocator, key, .{ .string = value });
        }
        for (assembly.subs.items, 0..) |sub_assembly, index| {
            const key = try std.fmt.allocPrint(allocator, "{x}", .{index});
            try data.object.put(
                allocator,
                key,
                try buildAssemblyJSON(sub_assembly, allocator, source_indices, false),
            );
        }
        try root.object.put(allocator, ".data", data);
    }

    if (assembly.auxiliary_data.items.len != 0) {
        const auxiliary = try CommonData.toHexAlloc(
            allocator,
            assembly.auxiliary_data.items,
            .dont_add,
            .lower,
        );
        try root.object.put(allocator, ".auxdata", .{ .string = auxiliary });
    }
    return root;
}

fn assemblyItemJSON(
    assembly: *const Assembly,
    allocator: std.mem.Allocator,
    item: *const AssemblyItem,
    source_index: i32,
    synthetic_jumpdest: bool,
) AssemblyError!JSON.Json {
    var result: JSON.Json = .{ .object = .empty };
    var name_and_data = try item.nameAndDataAlloc(allocator, assembly.evm_version);
    defer name_and_data.deinit(allocator);

    const name: []const u8 = if (synthetic_jumpdest) "JUMPDEST" else name_and_data.name;
    var data: []const u8 = name_and_data.data;
    if (!synthetic_jumpdest) {
        if (item.item_type == .PushLibraryAddress)
            data = try lookupNamedHash(assembly.libraries.items, item.data_value)
        else if (item.item_type == .PushImmutable or item.item_type == .AssignImmutable)
            data = try lookupNamedHash(assembly.immutables.items, item.data_value);
    } else data = "";

    try result.object.put(allocator, "name", try jsonOwnedString(allocator, name));
    try result.object.put(allocator, "begin", .{ .integer = item.location().start });
    try result.object.put(allocator, "end", .{ .integer = item.location().end });
    if (item.modifier_depth != 0) {
        if (item.modifier_depth > std.math.maxInt(i32)) return error.ModifierDepthTooLarge;
        try result.object.put(allocator, "modifierDepth", .{ .integer = @intCast(item.modifier_depth) });
    }
    if (!synthetic_jumpdest) {
        const jump_type = item.getJumpTypeAsString();
        if (jump_type.len != 0)
            try result.object.put(allocator, "jumpType", try jsonOwnedString(allocator, jump_type));
        if (data.len != 0)
            try result.object.put(allocator, "value", try jsonOwnedString(allocator, data));
    }
    try result.object.put(allocator, "source", .{ .integer = source_index });
    return result;
}

fn sourceIndexForLocation(
    location: SourceLocation,
    source_indices: []const SourceIndex,
) AssemblyError!i32 {
    const source_name = location.source_name orelse return -1;
    for (source_indices) |entry| {
        if (!std.mem.eql(u8, entry.source_name, source_name)) continue;
        if (entry.index > std.math.maxInt(i32)) return error.SourceIndexTooLarge;
        return @intCast(entry.index);
    }
    return -1;
}

fn jsonOwnedString(allocator: std.mem.Allocator, value: []const u8) !JSON.Json {
    return .{ .string = try allocator.dupe(u8, value) };
}

const IndexedSubAssembly = struct {
    index: usize,
    assembly: ?*Assembly,
};

fn parseAssemblyJSONNode(
    allocator: std.mem.Allocator,
    input: *const JSON.Json,
    source_names: []const []u8,
    level: usize,
    evm_version: EVMVersion,
) AssemblyError!*Assembly {
    const object = jsonObject(input) orelse return error.AssemblyJsonNotObject;
    try validateJsonMembers(object, &.{ ".code", ".data", ".auxdata", "sourceList" });
    if (level != 0 and object.contains("sourceList")) return error.NestedSourceList;

    const result = try Assembly.create(allocator, evm_version, level == 0, "");
    errdefer result.destroy();

    const code_value = object.getPtr(".code") orelse return error.MissingAssemblyCode;
    const code = jsonArray(code_value) orelse return error.AssemblyCodeNotArray;
    for (code.items) |*code_item|
        if (jsonObject(code_item) == null) return error.AssemblyCodeItemNotObject;
    try importAssemblyItemsFromJSON(result, code, source_names);

    if (object.getPtr(".auxdata")) |auxiliary_value| {
        const auxiliary_text = jsonString(auxiliary_value) orelse return error.AuxiliaryDataNotString;
        const auxiliary = try CommonData.fromHexAlloc(allocator, auxiliary_text, .dont_throw);
        if (auxiliary.len == 0) {
            allocator.free(auxiliary);
            return error.InvalidAuxiliaryData;
        }
        result.auxiliary_data = .fromOwnedSlice(auxiliary);
    }

    if (object.getPtr(".data")) |data_value| {
        const data_object = jsonObject(data_value) orelse return error.AssemblyDataNotObject;
        var indexed_subs: std.ArrayList(IndexedSubAssembly) = .empty;
        defer {
            for (indexed_subs.items) |entry| if (entry.assembly) |sub_assembly| sub_assembly.destroy();
            indexed_subs.deinit(allocator);
        }
        for (data_object.keys(), data_object.values()) |key, *value| {
            switch (value.*) {
                .string => |encoded_data| {
                    const decoded = try CommonData.fromHexAlloc(allocator, encoded_data, .dont_throw);
                    if (encoded_data.len != 0 and decoded.len == 0) {
                        allocator.free(decoded);
                        return error.InvalidAssemblyDataHex;
                    }
                    const hash = try assemblyDataKey(allocator, key);
                    try putDataEntryOwned(result, hash, decoded);
                },
                .object => {
                    const index = try parseHexStoiIndex(key);
                    const sub_assembly = try parseAssemblyJSONNode(
                        allocator,
                        value,
                        source_names,
                        level + 1,
                        evm_version,
                    );
                    errdefer sub_assembly.destroy();
                    var insertion_index: usize = 0;
                    while (insertion_index < indexed_subs.items.len and
                        indexed_subs.items[insertion_index].index < index) : (insertion_index += 1)
                    {}
                    if (insertion_index < indexed_subs.items.len and
                        indexed_subs.items[insertion_index].index == index)
                        return error.DuplicateSubassemblyIndex;
                    try indexed_subs.insert(allocator, insertion_index, .{
                        .index = index,
                        .assembly = sub_assembly,
                    });
                },
                else => return error.InvalidAssemblyDataValue,
            }
        }
        if (indexed_subs.items.len != 0) {
            if (indexed_subs.items[indexed_subs.items.len - 1].index != indexed_subs.items.len - 1)
                return error.NonContiguousSubassemblyIndices;
            for (indexed_subs.items, 0..) |*entry, expected_index| {
                if (entry.index != expected_index) return error.NonContiguousSubassemblyIndices;
                try result.subs.append(allocator, entry.assembly.?);
                entry.assembly = null;
            }
        }
    }
    return result;
}

fn importAssemblyItemsFromJSON(
    assembly: *Assembly,
    code: *const std.json.Array,
    source_names: []const []u8,
) AssemblyError!void {
    if (assembly.assembly_items.items.len != 0) return error.AssemblyItemsNotEmpty;
    var index: usize = 0;
    while (index < code.items.len) : (index += 1) {
        var item = try createAssemblyItemFromJSON(assembly, &code.items[index], source_names);
        var item_owned = true;
        errdefer if (item_owned) item.deinit(assembly.allocator);
        if (item.eqlInstruction(.JUMPDEST)) return error.JumpdestWithoutTag;
        try assembly.assembly_items.append(assembly.allocator, item);
        item_owned = false;
        if (item.item_type != .Tag) continue;
        index += 1;
        if (index == code.items.len) break;
        var jumpdest = try createAssemblyItemFromJSON(assembly, &code.items[index], source_names);
        defer jumpdest.deinit(assembly.allocator);
        if (!jumpdest.eqlInstruction(.JUMPDEST)) return error.JumpdestExpectedAfterTag;
    }
}

fn createAssemblyItemFromJSON(
    assembly: *Assembly,
    input: *const JSON.Json,
    source_names: []const []u8,
) AssemblyError!AssemblyItem {
    const object = jsonObject(input) orelse return error.AssemblyCodeItemNotObject;
    try validateJsonMembers(object, &.{ "name", "begin", "end", "source", "value", "modifierDepth", "jumpType" });

    const name_value = object.getPtr("name") orelse return error.MissingAssemblyItemName;
    const name = jsonString(name_value) orelse return error.AssemblyItemNameNotString;
    if (name.len == 0) return error.EmptyAssemblyItemName;
    const start = try jsonOptionalI32(object, "begin", -1);
    const end = try jsonOptionalI32(object, "end", -1);
    const source_index = try jsonOptionalI32(object, "source", -1);
    const modifier_depth_value = try jsonOptionalI32(object, "modifierDepth", 0);
    const value = try jsonOptionalString(object, "value", "");
    const jump_type_text = try jsonOptionalString(object, "jumpType", "");
    if (source_index < -1 or
        (source_index >= 0 and @as(usize, @intCast(source_index)) >= source_names.len))
        return error.SourceIndexOutOfBounds;

    var location: SourceLocation = .{ .start = start, .end = end };
    if (source_index != -1) location.source_name = source_names[@intCast(source_index)];
    const modifier_depth: usize = @bitCast(@as(isize, modifier_depth_value));

    var result: AssemblyItem = undefined;
    if (InstructionModule.instructionByName(name)) |instruction| {
        if (value.len != 0) return error.UnexpectedAssemblyItemValue;
        result = AssemblyItem.initInstruction(instruction, .{});
        if (jump_type_text.len != 0) {
            if (instruction != .JUMP and instruction != .JUMPI) return error.JumpTypeOnNonJump;
            result.setJumpType(AssemblyItem.parseJumpType(jump_type_text) orelse
                return error.InvalidJumpType);
        }
    } else {
        if (jump_type_text.len != 0) return error.JumpTypeOnNonJump;
        result = try createSpecialAssemblyItem(assembly, name, value);
    }
    result.setLocation(location);
    result.modifier_depth = modifier_depth;
    return result;
}

fn createSpecialAssemblyItem(
    assembly: *Assembly,
    name: []const u8,
    value: []const u8,
) AssemblyError!AssemblyItem {
    if (std.mem.eql(u8, name, "PUSH")) {
        try requireAssemblyValue(value);
        return AssemblyItem.initPush(try parseU256Hex(value), .{});
    }
    if (std.mem.eql(u8, name, "PUSH [ErrorTag]")) {
        try requireNoAssemblyValue(value);
        return AssemblyItem.initType(.PushTag, 0, .{});
    }
    if (std.mem.eql(u8, name, "PUSH [tag]")) {
        try requireAssemblyValue(value);
        const tag = try parseU256Decimal(value);
        const item = AssemblyItem.initType(.PushTag, tag, .{});
        const split = try item.splitForeignPushTag();
        if (split[0].empty()) try updateUsedTags(assembly, split[1]);
        return item;
    }
    if (std.mem.eql(u8, name, "PUSH [$]")) {
        try requireAssemblyValue(value);
        return AssemblyItem.initType(.PushSub, try parseU256Hex(value), .{});
    }
    if (std.mem.eql(u8, name, "PUSH #[$]")) {
        try requireAssemblyValue(value);
        return AssemblyItem.initType(.PushSubSize, try parseU256Hex(value), .{});
    }
    if (std.mem.eql(u8, name, "PUSHSIZE")) {
        try requireNoAssemblyValue(value);
        return AssemblyItem.initType(.PushProgramSize, 0, .{});
    }
    if (std.mem.eql(u8, name, "PUSHLIB")) {
        try requireAssemblyValue(value);
        return assembly.newPushLibraryAddress(value);
    }
    if (std.mem.eql(u8, name, "PUSHDEPLOYADDRESS")) {
        try requireNoAssemblyValue(value);
        return AssemblyItem.initType(.PushDeployTimeAddress, 0, .{});
    }
    if (std.mem.eql(u8, name, "PUSHIMMUTABLE")) {
        try requireAssemblyValue(value);
        return assembly.newPushImmutable(value);
    }
    if (std.mem.eql(u8, name, "ASSIGNIMMUTABLE")) {
        try requireAssemblyValue(value);
        return assembly.newImmutableAssignment(value);
    }
    if (std.mem.eql(u8, name, "tag")) {
        try requireAssemblyValue(value);
        const tag = try parseU256Decimal(value);
        try updateUsedTags(assembly, tag);
        return AssemblyItem.initType(.Tag, tag, .{});
    }
    if (std.mem.eql(u8, name, "PUSH data")) {
        try requireAssemblyValue(value);
        return AssemblyItem.initType(.PushData, try parseU256Hex(value), .{});
    }
    if (std.mem.eql(u8, name, "VERBATIM")) {
        try requireAssemblyValue(value);
        const decoded = try CommonData.fromHexAlloc(assembly.allocator, value, .dont_throw);
        defer assembly.allocator.free(decoded);
        return AssemblyItem.initVerbatim(assembly.allocator, decoded, 0, 0);
    }
    return error.InvalidAssemblyOpcode;
}

fn requireAssemblyValue(value: []const u8) error{MissingAssemblyItemValue}!void {
    if (value.len == 0) return error.MissingAssemblyItemValue;
}

fn requireNoAssemblyValue(value: []const u8) error{UnexpectedAssemblyItemValue}!void {
    if (value.len != 0) return error.UnexpectedAssemblyItemValue;
}

fn updateUsedTags(assembly: *Assembly, tag: u256) AssemblyError!void {
    if (tag >= std.math.maxInt(u32)) return error.TagTooLarge;
    assembly.used_tags = @max(assembly.used_tags, @as(u32, @intCast(tag)) + 1);
}

fn parseU256Hex(input: []const u8) AssemblyError!u256 {
    const digits = if (std.mem.startsWith(u8, input, "0x")) input[2..] else input;
    if (digits.len == 0) return error.InvalidAssemblyItemValue;
    return std.fmt.parseUnsigned(u256, digits, 16) catch return error.InvalidAssemblyItemValue;
}

fn parseU256Decimal(input: []const u8) AssemblyError!u256 {
    return std.fmt.parseUnsigned(u256, input, 10) catch return error.InvalidAssemblyItemValue;
}

fn jsonObject(value: *const JSON.Json) ?*const std.json.ObjectMap {
    return switch (value.*) {
        .object => |*object| object,
        else => null,
    };
}

fn jsonArray(value: *const JSON.Json) ?*const std.json.Array {
    return switch (value.*) {
        .array => |*array| array,
        else => null,
    };
}

fn jsonString(value: *const JSON.Json) ?[]const u8 {
    return switch (value.*) {
        .string => |string| string,
        else => null,
    };
}

fn validateJsonMembers(
    object: *const std.json.ObjectMap,
    valid_members: []const []const u8,
) AssemblyError!void {
    for (object.keys()) |key| {
        var found = false;
        for (valid_members) |valid| {
            if (!std.mem.eql(u8, key, valid)) continue;
            found = true;
            break;
        }
        if (!found) return error.UnknownAssemblyJsonMember;
    }
}

fn jsonOptionalI32(
    object: *const std.json.ObjectMap,
    name: []const u8,
    default: i32,
) AssemblyError!i32 {
    const value = object.getPtr(name) orelse return default;
    return JSON.get(i32, value) catch return error.InvalidAssemblyJsonInteger;
}

fn jsonOptionalString(
    object: *const std.json.ObjectMap,
    name: []const u8,
    default: []const u8,
) AssemblyError![]const u8 {
    const value = object.getPtr(name) orelse return default;
    return jsonString(value) orelse error.InvalidAssemblyJsonString;
}

fn assemblyDataKey(allocator: std.mem.Allocator, key: []const u8) AssemblyError!u256 {
    const decoded = try CommonData.fromHexAlloc(allocator, key, .dont_throw);
    defer allocator.free(decoded);
    if (decoded.len != 32) return 0;
    return Numeric.fromBigEndian(u256, decoded);
}

fn putDataEntryOwned(assembly: *Assembly, hash: u256, bytes: []u8) AssemblyError!void {
    errdefer assembly.allocator.free(bytes);
    const found = searchData(assembly.data_entries.items, hash);
    if (found.found) {
        assembly.allocator.free(assembly.data_entries.items[found.index].bytes);
        assembly.data_entries.items[found.index].bytes = bytes;
    } else try assembly.data_entries.insert(
        assembly.allocator,
        found.index,
        .{ .hash = hash, .bytes = bytes },
    );
}

fn parseHexStoiIndex(input: []const u8) AssemblyError!usize {
    var index: usize = 0;
    while (index < input.len and std.ascii.isWhitespace(input[index])) : (index += 1) {}
    var negative = false;
    if (index < input.len and (input[index] == '+' or input[index] == '-')) {
        negative = input[index] == '-';
        index += 1;
    }
    if (index + 2 <= input.len and input[index] == '0' and
        (input[index + 1] == 'x' or input[index + 1] == 'X')) index += 2;
    const digit_start = index;
    var value: u32 = 0;
    while (index < input.len) : (index += 1) {
        const digit: u8 = switch (input[index]) {
            '0'...'9' => input[index] - '0',
            'a'...'f' => input[index] - 'a' + 10,
            'A'...'F' => input[index] - 'A' + 10,
            else => break,
        };
        if (value > (@as(u32, std.math.maxInt(i32)) - digit) / 16)
            return error.SubassemblyIndexOutOfRange;
        value = value * 16 + digit;
    }
    if (index == digit_start) return error.SubassemblyIndexNotInteger;
    if (negative) return error.SubassemblyIndexOutOfRange;
    return value;
}

fn encodeSubPathsRecursive(
    current: *Assembly,
    path: *std.ArrayList(SubAssemblyID),
    ancestors: *std.ArrayList(*Assembly),
) AssemblyError!void {
    try ancestors.append(current.allocator, current);
    defer _ = ancestors.pop();
    for (current.subs.items, 0..) |sub_assembly, index| {
        try path.append(current.allocator, .{ .value = @intCast(index) });
        defer _ = path.pop();
        for (ancestors.items, 0..) |ancestor, distance_from_root|
            _ = try ancestor.encodeSubPath(path.items[distance_from_root..]);
        try encodeSubPathsRecursive(sub_assembly, path, ancestors);
    }
}

fn appendPush(
    allocator: std.mem.Allocator,
    bytecode: *std.ArrayList(u8),
    value: u256,
    evm_version: EVMVersion,
) std.mem.Allocator.Error!void {
    var width = Numeric.numberEncodingSize(u256, value);
    if (width == 0 and !evm_version.hasPush0()) width = 1;
    try bytecode.append(allocator, @intFromEnum(InstructionModule.pushInstruction(@intCast(width))));
    try appendBigEndian(allocator, bytecode, width, value);
}

fn appendBigEndian(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    width: usize,
    value: anytype,
) std.mem.Allocator.Error!void {
    const start = output.items.len;
    try output.appendNTimes(allocator, 0, width);
    Numeric.toBigEndian(@TypeOf(value), value, output.items[start..]);
}

fn writeBigEndian(output: []u8, value: anytype) void {
    Numeric.toBigEndian(@TypeOf(value), value, output);
}

fn emitLocation(
    allocator: std.mem.Allocator,
    locations: *LinkerObjectModule.CodeSectionLocation,
    item_index: usize,
    start: *usize,
    end: usize,
) std.mem.Allocator.Error!void {
    try locations.instruction_locations.append(allocator, .{
        .start = start.*,
        .end = end,
        .assembly_item_index = item_index,
    });
    start.* = end;
}

fn appendImmutableReference(
    allocator: std.mem.Allocator,
    object: *LinkerObject,
    hash: u256,
    identifier: []const u8,
    offset: usize,
) std.mem.Allocator.Error!void {
    var lower: usize = 0;
    var upper = object.immutable_references.items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (object.immutable_references.items[middle].hash < hash) lower = middle + 1 else upper = middle;
    }
    if (lower < object.immutable_references.items.len and object.immutable_references.items[lower].hash == hash) {
        try object.immutable_references.items[lower].references.offsets.append(allocator, offset);
        return;
    }
    var references: LinkerObjectModule.ImmutableRefs = .{
        .identifier = try allocator.dupe(u8, identifier),
    };
    errdefer references.deinit(allocator);
    try references.offsets.append(allocator, offset);
    try object.immutable_references.insert(allocator, lower, .{ .hash = hash, .references = references });
}

fn immutableOffsets(references: []const LinkerObjectModule.ImmutableReference, hash: u256) []const usize {
    for (references) |reference| if (reference.hash == hash) return reference.references.offsets.items;
    return &.{};
}

fn removeImmutableReference(
    allocator: std.mem.Allocator,
    references: *std.ArrayList(LinkerObjectModule.ImmutableReference),
    hash: u256,
) void {
    for (references.items, 0..) |reference, index| {
        if (reference.hash != hash) continue;
        var removed = references.orderedRemove(index);
        removed.references.deinit(allocator);
        return;
    }
}

fn findSubObject(items: anytype, object: *const LinkerObject) ?usize {
    for (items) |entry| if (linkerObjectsEqual(entry.object, object)) return entry.offset;
    return null;
}

fn linkerObjectsEqual(left: *const LinkerObject, right: *const LinkerObject) bool {
    if (!std.mem.eql(u8, left.bytecode.items, right.bytecode.items)) return false;
    if (left.link_references.items.len != right.link_references.items.len or
        left.immutable_references.items.len != right.immutable_references.items.len) return false;
    for (left.link_references.items, right.link_references.items) |a, b| {
        if (a.offset != b.offset or !std.mem.eql(u8, a.library_name, b.library_name)) return false;
    }
    for (left.immutable_references.items, right.immutable_references.items) |a, b| {
        if (a.hash != b.hash or !std.mem.eql(u8, a.references.identifier, b.references.identifier) or
            !std.mem.eql(usize, a.references.offsets.items, b.references.offsets.items)) return false;
    }
    return true;
}

fn insertDataRef(allocator: std.mem.Allocator, refs: anytype, value: anytype) !void {
    var index: usize = 0;
    while (index < refs.items.len and (refs.items[index].hash < value.hash or
        (refs.items[index].hash == value.hash and refs.items[index].offset <= value.offset))) : (index += 1)
    {}
    try refs.insert(allocator, index, value);
}

fn insertSubRef(allocator: std.mem.Allocator, refs: anytype, value: anytype) !void {
    var index: usize = 0;
    while (index < refs.items.len and (refs.items[index].id.value < value.id.value or
        (refs.items[index].id.value == value.id.value and refs.items[index].offset <= value.offset))) : (index += 1)
    {}
    try refs.insert(allocator, index, value);
}

const SearchResult = struct { index: usize, found: bool };

fn searchData(items: []const DataEntry, hash: u256) SearchResult {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (items[middle].hash < hash) lower = middle + 1 else upper = middle;
    }
    return .{ .index = lower, .found = lower < items.len and items[lower].hash == hash };
}

fn searchNamedHash(items: []const NamedHash, hash: u256) SearchResult {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (items[middle].hash < hash) lower = middle + 1 else upper = middle;
    }
    return .{ .index = lower, .found = lower < items.len and items[lower].hash == hash };
}

fn putNamedHash(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(NamedHash),
    hash: u256,
    name: []const u8,
) std.mem.Allocator.Error!void {
    const found = searchNamedHash(items.items, hash);
    const owned = try allocator.dupe(u8, name);
    errdefer allocator.free(owned);
    if (found.found) {
        allocator.free(items.items[found.index].name);
        items.items[found.index].name = owned;
    } else try items.insert(allocator, found.index, .{ .hash = hash, .name = owned });
}

fn lookupNamedHash(items: []const NamedHash, hash: u256) error{NameNotFound}![]const u8 {
    const found = searchNamedHash(items, hash);
    if (!found.found) return error.NameNotFound;
    return items[found.index].name;
}

fn searchNamedTag(items: []const NamedTagInfo, name: []const u8) SearchResult {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (std.mem.order(u8, items[middle].name, name) == .lt) lower = middle + 1 else upper = middle;
    }
    return .{
        .index = lower,
        .found = lower < items.len and std.mem.eql(u8, items[lower].name, name),
    };
}

fn searchReplacement(items: []const BlockDeduplicator.TagReplacement, from: u256) SearchResult {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (items[middle].from < from) lower = middle + 1 else upper = middle;
    }
    return .{ .index = lower, .found = lower < items.len and items[lower].from == from };
}

fn removeTag(tags: *JumpdestRemover.TagSet, value: usize) bool {
    var lower: usize = 0;
    var upper = tags.values.items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (tags.values.items[middle] < value) lower = middle + 1 else upper = middle;
    }
    if (lower >= tags.values.items.len or tags.values.items[lower] != value) return false;
    _ = tags.values.orderedRemove(lower);
    return true;
}

fn compareSubPaths(left: []const SubAssemblyID, right: []const SubAssemblyID) std.math.Order {
    for (left[0..@min(left.len, right.len)], right[0..@min(left.len, right.len)]) |a, b| {
        if (a.value < b.value) return .lt;
        if (a.value > b.value) return .gt;
    }
    return std.math.order(left.len, right.len);
}

fn flushExpressions(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    prefix: []const u8,
    pending: *std.ArrayList([]u8),
) std.mem.Allocator.Error!void {
    for (pending.items) |expression| {
        try output.appendSlice(allocator, prefix);
        try output.appendSlice(allocator, "  ");
        try output.appendSlice(allocator, expression);
        try output.append(allocator, '\n');
        allocator.free(expression);
    }
    pending.clearRetainingCapacity();
}

fn appendLocation(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    prefix: []const u8,
    location: SourceLocation,
    selection: DebugInfoSelection,
    source_codes: []const SourceCode,
) std.mem.Allocator.Error!void {
    if (!location.isValid() or (!selection.location and !selection.snippet)) return;

    try output.appendSlice(allocator, prefix);
    try output.appendSlice(allocator, "    /*");
    if (selection.location) {
        if (location.source_name) |source_name| {
            const quoted = try CommonData.escapeAndQuoteStringAlloc(allocator, source_name);
            defer allocator.free(quoted);
            try output.append(allocator, ' ');
            try output.appendSlice(allocator, quoted);
        }
        if (location.hasText())
            try appendFormat(allocator, output, ":{d}:{d}", .{ location.start, location.end });
    }
    if (selection.snippet) {
        if (selection.location) try output.appendSlice(allocator, "  ");
        if (location.hasText()) {
            if (location.source_name) |source_name| {
                for (source_codes) |source_code| {
                    if (!std.mem.eql(u8, source_code.name, source_name)) continue;
                    const snippet = try CharStream.singleLineSnippetFromTextAlloc(
                        allocator,
                        source_code.code,
                        location,
                    );
                    defer allocator.free(snippet);
                    try output.appendSlice(allocator, snippet);
                    break;
                }
            }
        }
    }
    try output.appendSlice(allocator, " */\n");
}

fn appendFormat(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    comptime format: []const u8,
    arguments: anytype,
) std.mem.Allocator.Error!void {
    const rendered = try std.fmt.allocPrint(allocator, format, arguments);
    defer allocator.free(rendered);
    try output.appendSlice(allocator, rendered);
}

fn searchSubPath(items: []const SubPath, path: []const SubAssemblyID) SearchResult {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (compareSubPaths(items[middle].path, path) == .lt) lower = middle + 1 else upper = middle;
    }
    return .{
        .index = lower,
        .found = lower < items.len and compareSubPaths(items[lower].path, path) == .eq,
    };
}

fn appendClone(allocator: std.mem.Allocator, items: *std.ArrayList(AssemblyItem), item: *const AssemblyItem) !void {
    var cloned = try item.clone(allocator);
    errdefer cloned.deinit(allocator);
    try items.append(allocator, cloned);
}

fn deinitItems(allocator: std.mem.Allocator, items: *std.ArrayList(AssemblyItem)) void {
    for (items.items) |*item| item.deinit(allocator);
    items.deinit(allocator);
    items.* = .empty;
}

test "assembly emits tags, data references, program size, and auxiliary bytes" {
    var assembly = try Assembly.init(
        std.testing.allocator,
        EVMVersion.init(.Shanghai),
        false,
        "test",
    );
    defer assembly.deinit();
    const tag = try assembly.newTag();
    _ = try assembly.append(try tag.pushTag());
    _ = try assembly.append(AssemblyItem.initInstruction(.JUMP, .{}));
    _ = try assembly.append(tag);
    _ = try assembly.appendData("payload");
    try assembly.appendProgramSize();
    try assembly.appendToAuxiliaryData(&.{ 0xaa, 0xbb });
    const object = try assembly.assemble();
    try std.testing.expect(object.bytecode.items.len > 2);
    try std.testing.expectEqual(@as(u8, 0xaa), object.bytecode.items[object.bytecode.items.len - 2]);
    try std.testing.expectEqual(@as(u8, 0xbb), object.bytecode.items[object.bytecode.items.len - 1]);
}

test "assembly JSON preserves code, source names, data, and subassemblies" {
    const allocator = std.testing.allocator;
    const version = EVMVersion.current();
    var assembly = try Assembly.init(allocator, version, true, "json");
    defer assembly.deinit();

    var push = AssemblyItem.initPush(0x1234, .{});
    push.setLocation(.{ .start = 2, .end = 8, .source_name = "input.sol" });
    push.modifier_depth = 2;
    try assembly.assembly_items.append(allocator, push);
    const tag = try assembly.newTag();
    try assembly.assembly_items.append(allocator, tag);
    try assembly.assembly_items.append(allocator, try assembly.newData(&.{ 0xde, 0xad }));
    try assembly.assembly_items.append(allocator, try assembly.newPushLibraryAddress("input.sol:L"));
    try assembly.assembly_items.append(allocator, try assembly.newPushImmutable("value"));

    const sub_assembly = try Assembly.create(allocator, version, false, "sub");
    try sub_assembly.assembly_items.append(allocator, AssemblyItem.initInstruction(.STOP, .{}));
    const sub_item = try assembly.newSub(sub_assembly);
    try assembly.assembly_items.append(allocator, sub_item);
    try assembly.appendToAuxiliaryData(&.{ 0xaa, 0xbb });

    var encoded = try assembly.assemblyJSONAlloc(
        allocator,
        &.{.{ .source_name = "input.sol", .index = 0 }},
        true,
    );
    defer encoded.deinit();
    const imported = try Assembly.fromJSON(allocator, &encoded.value);
    defer imported.destroy();
    try std.testing.expectEqual(@as(usize, 1), imported.sourceNames().len);
    try std.testing.expectEqualStrings("input.sol", imported.sourceNames()[0]);

    var round_trip = try imported.assemblyJSONAlloc(
        allocator,
        &.{.{ .source_name = "input.sol", .index = 0 }},
        true,
    );
    defer round_trip.deinit();
    const expected = try JSON.jsonCompactPrintAlloc(allocator, &encoded.value);
    defer allocator.free(expected);
    const actual = try JSON.jsonCompactPrintAlloc(allocator, &round_trip.value);
    defer allocator.free(actual);
    try std.testing.expectEqualStrings(expected, actual);
}
