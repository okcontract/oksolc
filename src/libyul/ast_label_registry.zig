// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Immutable AST label lookup and its parser/importer-side builder.

const std = @import("std");

pub const LabelID = usize;

pub const ASTLabelRegistry = struct {
    allocator: std.mem.Allocator,
    label_storage: std.ArrayList([]u8) = .empty,
    id_to_label_mapping: std.ArrayList(usize) = .empty,

    pub fn initEmpty(allocator: std.mem.Allocator) !ASTLabelRegistry {
        return init(allocator, &.{""}, &.{0});
    }

    pub fn init(
        allocator: std.mem.Allocator,
        labels_input: []const []const u8,
        mapping: []const usize,
    ) !ASTLabelRegistry {
        var result: ASTLabelRegistry = .{ .allocator = allocator };
        errdefer result.deinit();
        for (labels_input) |label_value| {
            const owned = try allocator.dupe(u8, label_value);
            errdefer allocator.free(owned);
            try result.label_storage.append(allocator, owned);
        }
        try result.id_to_label_mapping.appendSlice(allocator, mapping);
        try result.validate();
        return result;
    }

    pub fn deinit(self: *ASTLabelRegistry) void {
        for (self.label_storage.items) |label_value| self.allocator.free(label_value);
        self.label_storage.deinit(self.allocator);
        self.id_to_label_mapping.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const ASTLabelRegistry, allocator: std.mem.Allocator) !ASTLabelRegistry {
        return init(allocator, self.labels(), self.id_to_label_mapping.items);
    }

    pub fn label(self: *const ASTLabelRegistry, id: LabelID) ![]const u8 {
        const label_index = try self.idToLabelIndex(id);
        if (label_index == ghostLabelIndex()) return error.GhostLabel;
        if (!empty(id) and label_index == 0) return error.UnusedLabel;
        return self.label_storage.items[label_index];
    }

    pub fn empty(id: LabelID) bool {
        return id == emptyID();
    }

    pub fn emptyID() LabelID {
        return 0;
    }

    pub fn ghostLabelIndex() usize {
        return std.math.maxInt(usize);
    }

    pub fn unused(self: *const ASTLabelRegistry, id: LabelID) !bool {
        return !empty(id) and try self.idToLabelIndex(id) == 0;
    }

    pub fn ghost(self: *const ASTLabelRegistry, id: LabelID) !bool {
        return try self.idToLabelIndex(id) == ghostLabelIndex();
    }

    pub fn labels(self: *const ASTLabelRegistry) []const []const u8 {
        return self.label_storage.items;
    }

    pub fn maxID(self: *const ASTLabelRegistry) LabelID {
        std.debug.assert(self.id_to_label_mapping.items.len != 0);
        return self.id_to_label_mapping.items.len - 1;
    }

    pub fn idToLabelIndex(self: *const ASTLabelRegistry, id: LabelID) !usize {
        if (id >= self.id_to_label_mapping.items.len) return error.LabelIDOutOfBounds;
        return self.id_to_label_mapping.items[id];
    }

    pub fn findIDForLabel(self: *const ASTLabelRegistry, needle: []const u8) !?LabelID {
        var id: LabelID = 0;
        while (id <= self.maxID()) : (id += 1) {
            if (try self.unused(id) or try self.ghost(id)) continue;
            if (std.mem.eql(u8, try self.label(id), needle)) return id;
        }
        return null;
    }

    fn validate(self: *const ASTLabelRegistry) !void {
        if (self.label_storage.items.len == 0 or self.label_storage.items[0].len != 0)
            return error.InvalidEmptyLabel;
        if (self.id_to_label_mapping.items.len == 0 or self.id_to_label_mapping.items[0] != 0)
            return error.InvalidEmptyLabelMapping;
        const visited = try self.allocator.alloc(bool, self.label_storage.items.len);
        defer self.allocator.free(visited);
        @memset(visited, false);
        var number_of_labels: usize = 0;
        for (self.id_to_label_mapping.items) |label_index| {
            if (label_index == ghostLabelIndex()) continue;
            if (label_index >= self.label_storage.items.len) return error.LabelIndexOutOfBounds;
            if (label_index != 0 and visited[label_index]) return error.DuplicateLabelReference;
            visited[label_index] = true;
            if (label_index >= 1) number_of_labels += 1;
        }
        if (number_of_labels + 1 != self.label_storage.items.len)
            return error.UnreferencedLabel;
        for (self.label_storage.items, 0..) |left, left_index|
            for (self.label_storage.items[left_index + 1 ..]) |right|
                if (std.mem.eql(u8, left, right)) return error.DuplicateLabel;
    }
};

const DefinedLabel = struct {
    label: []u8,
    id: LabelID,
};

pub const ASTLabelRegistryBuilder = struct {
    allocator: std.mem.Allocator,
    defined_labels: std.ArrayList(DefinedLabel) = .empty,
    ghosts: std.ArrayList(LabelID) = .empty,
    next_id: usize = 1,

    pub fn init(allocator: std.mem.Allocator) !ASTLabelRegistryBuilder {
        var result: ASTLabelRegistryBuilder = .{ .allocator = allocator };
        errdefer result.deinit();
        _ = try result.insertDefined("", 0);
        return result;
    }

    pub fn initFromRegistry(
        allocator: std.mem.Allocator,
        registry: *const ASTLabelRegistry,
    ) !ASTLabelRegistryBuilder {
        var result = try init(allocator);
        errdefer result.deinit();
        var id: LabelID = 1;
        while (id <= registry.maxID()) : (id += 1) {
            if (try registry.unused(id)) continue;
            if (try registry.ghost(id)) {
                try result.ghosts.append(allocator, id);
            } else {
                const inserted = try result.insertDefined(try registry.label(id), id);
                if (!inserted) return error.DuplicateExistingLabel;
            }
        }
        result.next_id = registry.maxID() + 1;
        return result;
    }

    pub fn deinit(self: *ASTLabelRegistryBuilder) void {
        for (self.defined_labels.items) |entry| self.allocator.free(entry.label);
        self.defined_labels.deinit(self.allocator);
        self.ghosts.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn define(self: *ASTLabelRegistryBuilder, label_value: []const u8) !LabelID {
        if (self.findDefined(label_value)) |entry| return entry.id;
        const id = self.next_id;
        _ = try self.insertDefined(label_value, id);
        self.next_id += 1;
        return id;
    }

    pub fn addGhost(self: *ASTLabelRegistryBuilder) !LabelID {
        const id = self.next_id;
        try self.ghosts.append(self.allocator, id);
        self.next_id += 1;
        return id;
    }

    pub fn build(self: *const ASTLabelRegistryBuilder) !ASTLabelRegistry {
        var indices: std.ArrayList(usize) = .empty;
        defer indices.deinit(self.allocator);
        for (self.defined_labels.items, 0..) |_, index| try indices.append(self.allocator, index);
        std.sort.insertion(usize, indices.items, self, struct {
            fn lessThan(builder: *const ASTLabelRegistryBuilder, left: usize, right: usize) bool {
                return std.mem.order(
                    u8,
                    builder.defined_labels.items[left].label,
                    builder.defined_labels.items[right].label,
                ) == .lt;
            }
        }.lessThan);

        var labels_list: std.ArrayList([]const u8) = .empty;
        defer labels_list.deinit(self.allocator);
        try labels_list.append(self.allocator, "");
        var mapping: std.ArrayList(usize) = .empty;
        defer mapping.deinit(self.allocator);
        try mapping.resize(self.allocator, self.next_id + 1);
        @memset(mapping.items, 0);
        for (indices.items) |index| {
            const entry = self.defined_labels.items[index];
            if (ASTLabelRegistry.empty(entry.id)) continue;
            try labels_list.append(self.allocator, entry.label);
            mapping.items[entry.id] = labels_list.items.len - 1;
        }
        for (self.ghosts.items) |id| mapping.items[id] = ASTLabelRegistry.ghostLabelIndex();
        return ASTLabelRegistry.init(self.allocator, labels_list.items, mapping.items);
    }

    fn findDefined(self: *const ASTLabelRegistryBuilder, label_value: []const u8) ?DefinedLabel {
        for (self.defined_labels.items) |entry|
            if (std.mem.eql(u8, entry.label, label_value)) return entry;
        return null;
    }

    fn insertDefined(
        self: *ASTLabelRegistryBuilder,
        label_value: []const u8,
        id: LabelID,
    ) !bool {
        if (self.findDefined(label_value) != null) return false;
        const owned = try self.allocator.dupe(u8, label_value);
        errdefer self.allocator.free(owned);
        try self.defined_labels.append(self.allocator, .{ .label = owned, .id = id });
        return true;
    }
};

test "AST label registry preserves duplicate definitions, gaps, and ghosts" {
    const allocator = std.testing.allocator;
    var builder = try ASTLabelRegistryBuilder.init(allocator);
    defer builder.deinit();
    const alpha = try builder.define("alpha");
    try std.testing.expectEqual(alpha, try builder.define("alpha"));
    const ghost_id = try builder.addGhost();
    const beta = try builder.define("beta");
    var registry = try builder.build();
    defer registry.deinit();
    try std.testing.expectEqualStrings("alpha", try registry.label(alpha));
    try std.testing.expect(try registry.ghost(ghost_id));
    try std.testing.expectEqual(beta, (try registry.findIDForLabel("beta")).?);
}
