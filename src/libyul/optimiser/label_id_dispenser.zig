// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic label-ID spawning and registry compaction.

const std = @import("std");
const AST = @import("../ast.zig");
const LabelRegistryModule = @import("../ast_label_registry.zig");
const OptimizerUtilities = @import("optimizer_utilities.zig");

pub const LabelID = LabelRegistryModule.LabelID;
pub const ASTLabelRegistry = LabelRegistryModule.ASTLabelRegistry;

pub const LabelIDDispenser = struct {
    allocator: std.mem.Allocator,
    parent_labels: *const ASTLabelRegistry,
    reserved_labels: std.StringHashMap(void),
    reserved_storage: std.ArrayList([]u8) = .empty,
    id_to_label_mapping: std.ArrayList(LabelID) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        labels_value: *const ASTLabelRegistry,
        reserved: []const []const u8,
    ) !LabelIDDispenser {
        var result: LabelIDDispenser = .{
            .allocator = allocator,
            .parent_labels = labels_value,
            .reserved_labels = std.StringHashMap(void).init(allocator),
        };
        errdefer result.deinit();
        for (reserved) |label_value| {
            if (result.reserved_labels.contains(label_value)) continue;
            try result.reserved_storage.ensureUnusedCapacity(allocator, 1);
            const owned = try allocator.dupe(u8, label_value);
            errdefer allocator.free(owned);
            try result.reserved_labels.put(owned, {});
            // The map borrows the name. Publish its owner only after the last
            // fallible operation, so cleanup never owns the same name twice.
            result.reserved_storage.appendAssumeCapacity(owned);
        }
        return result;
    }

    pub fn deinit(self: *LabelIDDispenser) void {
        self.id_to_label_mapping.deinit(self.allocator);
        self.reserved_labels.deinit();
        for (self.reserved_storage.items) |label_value| self.allocator.free(label_value);
        self.reserved_storage.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn labels(self: *const LabelIDDispenser) *const ASTLabelRegistry {
        return self.parent_labels;
    }

    pub fn newID(self: *LabelIDDispenser, parent: LabelID) !LabelID {
        const parent_label_id = try self.resolveParentLabelID(parent);
        if (try self.parent_labels.ghost(parent_label_id)) return error.ParentLabelIsGhost;
        try self.id_to_label_mapping.append(self.allocator, parent_label_id);
        return std.math.add(
            LabelID,
            self.parent_labels.maxID(),
            self.id_to_label_mapping.items.len,
        ) catch error.LabelIDOverflow;
    }

    pub fn newEmptyID(self: *LabelIDDispenser) !LabelID {
        return self.newID(ASTLabelRegistry.emptyID());
    }

    pub fn newGhost(self: *LabelIDDispenser) !LabelID {
        try self.id_to_label_mapping.append(self.allocator, ASTLabelRegistry.ghostLabelIndex());
        return std.math.add(
            LabelID,
            self.parent_labels.maxID(),
            self.id_to_label_mapping.items.len,
        ) catch error.LabelIDOverflow;
    }

    pub fn generateNewLabels(
        self: *const LabelIDDispenser,
        used_ids_input: []const LabelID,
        dialect: AST.Dialect,
    ) !ASTLabelRegistry {
        if (used_ids_input.len == 0) return ASTLabelRegistry.initEmpty(self.allocator);

        const used_ids = try self.allocator.dupe(LabelID, used_ids_input);
        defer self.allocator.free(used_ids);
        std.sort.insertion(LabelID, used_ids, {}, std.sort.asc(LabelID));
        var unique_count: usize = 0;
        for (used_ids) |id| {
            if (unique_count != 0 and used_ids[unique_count - 1] == id) continue;
            used_ids[unique_count] = id;
            unique_count += 1;
        }
        // Keep the allocation's full extent for deferred cleanup.
        const unique_ids = used_ids[0..unique_count];
        if (unique_ids[0] == ASTLabelRegistry.emptyID()) return error.EmptyLabelIDCannotBeSelected;
        const maximum_id = unique_ids[unique_ids.len - 1];
        try self.validateID(maximum_id);

        const original_labels = self.parent_labels.labels();
        const reused_labels = try self.allocator.alloc(bool, original_labels.len);
        defer self.allocator.free(reused_labels);
        @memset(reused_labels, false);
        reused_labels[0] = true;

        var output_labels: std.ArrayList([]const u8) = .empty;
        defer output_labels.deinit(self.allocator);
        try output_labels.append(self.allocator, "");

        const id_to_label_map = try self.allocator.alloc(usize, maximum_id + 1);
        defer self.allocator.free(id_to_label_map);
        @memset(id_to_label_map, 0);

        var already_defined = std.StringHashMap(void).init(self.allocator);
        defer already_defined.deinit();
        var reserved_iterator = self.reserved_labels.keyIterator();
        while (reserved_iterator.next()) |label_value| try already_defined.put(label_value.*, {});

        var to_generate: std.ArrayList(LabelID) = .empty;
        defer to_generate.deinit(self.allocator);
        for (unique_ids) |id| {
            if (try self.ghost(id)) {
                id_to_label_map[id] = ASTLabelRegistry.ghostLabelIndex();
                continue;
            }

            const parent_label_id = try self.resolveParentLabelID(id);
            const original_label_index = try self.parent_labels.idToLabelIndex(parent_label_id);
            const original_label = original_labels[original_label_index];
            if (!reused_labels[original_label_index] and
                (parent_label_id == id or !self.isInvalidLabel(original_label, dialect)))
            {
                try output_labels.append(self.allocator, original_label);
                id_to_label_map[id] = output_labels.items.len - 1;
                try already_defined.put(original_label, {});
                reused_labels[original_label_index] = true;
            } else {
                try to_generate.append(self.allocator, id);
            }
        }

        const label_suffixes = try self.allocator.alloc(usize, self.parent_labels.maxID() + 1);
        defer self.allocator.free(label_suffixes);
        @memset(label_suffixes, 1);
        var generated_storage: std.ArrayList([]u8) = .empty;
        defer {
            for (generated_storage.items) |label_value| self.allocator.free(label_value);
            generated_storage.deinit(self.allocator);
        }
        for (to_generate.items) |id| {
            if (try self.ghost(id)) return error.GhostScheduledForGeneration;
            const parent_label_id = try self.resolveParentLabelID(id);
            const parent_label_index = try self.parent_labels.idToLabelIndex(parent_label_id);
            const parent_label = original_labels[parent_label_index];
            var generated_label: []u8 = undefined;
            while (true) {
                generated_label = try std.fmt.allocPrint(
                    self.allocator,
                    "{s}_{d}",
                    .{ parent_label, label_suffixes[parent_label_id] },
                );
                label_suffixes[parent_label_id] = std.math.add(
                    usize,
                    label_suffixes[parent_label_id],
                    1,
                ) catch {
                    self.allocator.free(generated_label);
                    return error.LabelSuffixOverflow;
                };
                if (!OptimizerUtilities.isRestrictedIdentifier(dialect, generated_label) and
                    !already_defined.contains(generated_label)) break;
                self.allocator.free(generated_label);
            }
            var generated_label_owned = true;
            defer if (generated_label_owned) self.allocator.free(generated_label);
            try generated_storage.append(self.allocator, generated_label);
            generated_label_owned = false;
            try output_labels.append(self.allocator, generated_label);
            id_to_label_map[id] = output_labels.items.len - 1;
            try already_defined.put(generated_label, {});
        }

        return ASTLabelRegistry.init(self.allocator, output_labels.items, id_to_label_map);
    }

    pub fn generateAllLabels(
        self: *const LabelIDDispenser,
        dialect: AST.Dialect,
    ) !ASTLabelRegistry {
        const maximum_id = std.math.add(
            LabelID,
            self.parent_labels.maxID(),
            self.id_to_label_mapping.items.len,
        ) catch return error.LabelIDOverflow;
        if (maximum_id == 0) return ASTLabelRegistry.initEmpty(self.allocator);
        const used_ids = try self.allocator.alloc(LabelID, maximum_id);
        defer self.allocator.free(used_ids);
        for (used_ids, 1..) |*id, value| id.* = value;
        return self.generateNewLabels(used_ids, dialect);
    }

    fn validateID(self: *const LabelIDDispenser, id: LabelID) !void {
        const upper_bound = std.math.add(
            LabelID,
            self.parent_labels.maxID(),
            self.id_to_label_mapping.items.len,
        ) catch return error.LabelIDOverflow;
        if (id > upper_bound) return error.LabelIDOutOfBounds;
    }

    fn resolveParentLabelID(self: *const LabelIDDispenser, input_id: LabelID) !LabelID {
        try self.validateID(input_id);
        var id = input_id;
        if (id > self.parent_labels.maxID())
            id = self.id_to_label_mapping.items[id - self.parent_labels.maxID() - 1];
        if (id > self.parent_labels.maxID() or try self.parent_labels.unused(id))
            return error.InvalidParentLabelID;
        return id;
    }

    fn ghost(self: *const LabelIDDispenser, id: LabelID) !bool {
        try self.validateID(id);
        if (id > self.parent_labels.maxID())
            return self.id_to_label_mapping.items[id - self.parent_labels.maxID() - 1] ==
                ASTLabelRegistry.ghostLabelIndex();
        return self.parent_labels.ghost(id);
    }

    fn isInvalidLabel(
        self: *const LabelIDDispenser,
        label_value: []const u8,
        dialect: AST.Dialect,
    ) bool {
        return OptimizerUtilities.isRestrictedIdentifier(dialect, label_value) or
            self.reserved_labels.contains(label_value);
    }
};

test "label ID dispenser reuses originals before allocating suffixes" {
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const allocator = std.testing.allocator;
    var labels_value = try ASTLabelRegistry.init(
        allocator,
        &.{ "", "alpha", "add" },
        &.{ 0, 1, 2 },
    );
    defer labels_value.deinit();
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var dispenser = try LabelIDDispenser.init(allocator, &labels_value, &.{"alpha_1"});
    defer dispenser.deinit();
    const alpha_copy = try dispenser.newID(1);
    const builtin_copy = try dispenser.newID(2);
    const ghost_id = try dispenser.newGhost();
    var generated = try dispenser.generateNewLabels(
        &.{ 1, 2, alpha_copy, builtin_copy, ghost_id },
        dialect.dialect(),
    );
    defer generated.deinit();
    try std.testing.expectEqualStrings("alpha", try generated.label(1));
    try std.testing.expectEqualStrings("add", try generated.label(2));
    try std.testing.expectEqualStrings("alpha_2", try generated.label(alpha_copy));
    try std.testing.expectEqualStrings("add_1", try generated.label(builtin_copy));
    try std.testing.expect(try generated.ghost(ghost_id));
}

test "label ID dispenser owns compacted ID storage through failures" {
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const Check = struct {
        const Case = enum { duplicates, empty, selected_empty, out_of_bounds };

        fn run(allocator: std.mem.Allocator, dialect: AST.Dialect, case: Case) !void {
            // The returned registry must remain independent after both its
            // parent and the dispenser's temporary owners have been destroyed.
            var generated = blk: {
                var parent = try ASTLabelRegistry.init(
                    allocator,
                    &.{ "", "alpha", "alpha_1", "add" },
                    &.{ 0, 1, 2, 3 },
                );
                defer parent.deinit();
                var dispenser = try LabelIDDispenser.init(allocator, &parent, &.{});
                defer dispenser.deinit();
                const alpha_copy = try dispenser.newID(1);
                const builtin_copy = try dispenser.newID(3);
                const ghost_id = try dispenser.newGhost();
                const input: []const LabelID = switch (case) {
                    .duplicates => &.{ ghost_id, alpha_copy, 1, 3, 2, builtin_copy, alpha_copy, ghost_id, 2, 1 },
                    .empty => &.{},
                    .selected_empty => &.{ 1, 0, 1, 0 },
                    .out_of_bounds => &.{ 1, 99, 99, 1 },
                };
                const original = try allocator.dupe(LabelID, input);
                defer allocator.free(original);
                var result = dispenser.generateNewLabels(input, dialect) catch |err| {
                    if (err == error.OutOfMemory) return err;
                    try std.testing.expectEqualSlices(LabelID, original, input);
                    try std.testing.expectEqual(switch (case) {
                        .selected_empty => error.EmptyLabelIDCannotBeSelected,
                        .out_of_bounds => error.LabelIDOutOfBounds,
                        else => return err,
                    }, err);
                    return;
                };
                errdefer result.deinit();
                try std.testing.expect(case == .duplicates or case == .empty);
                try std.testing.expectEqualSlices(LabelID, original, input);
                break :blk result;
            };
            defer generated.deinit();
            if (case == .empty) {
                try std.testing.expectEqual(@as(usize, 0), generated.maxID());
                try std.testing.expectEqualStrings("", try generated.label(0));
            } else {
                try std.testing.expectEqual(@as(usize, 6), generated.maxID());
                for ([_][]const u8{ "", "alpha", "alpha_1", "add", "alpha_2", "add_1" }, 0..) |expected, id|
                    try std.testing.expectEqualStrings(expected, try generated.label(id));
                try std.testing.expect(try generated.ghost(6));
            }
        }
    };
    var dialect = try EVMDialect.init(std.testing.allocator, .current(), false);
    defer dialect.deinit();
    for (std.enums.values(Check.Case)) |case|
        try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{ dialect.dialect(), case });
}

test "label ID dispenser publishes reserved names once across allocation failures" {
    const Check = struct {
        fn run(allocator: std.mem.Allocator, parent: *const ASTLabelRegistry) !void {
            const reserved: []const []const u8 = &.{ "alpha_1", "beta", "gamma", "alpha_1", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa", "lambda", "beta" };
            var dispenser = try LabelIDDispenser.init(allocator, parent, reserved);
            defer dispenser.deinit();
            try std.testing.expectEqual(@as(usize, 11), dispenser.reserved_storage.items.len);
            try std.testing.expectEqual(@as(usize, 11), dispenser.reserved_labels.count());
            for (reserved) |label_value|
                try std.testing.expect(dispenser.reserved_labels.contains(label_value));
        }
    };
    var parent = try ASTLabelRegistry.initEmpty(std.testing.allocator);
    defer parent.deinit();
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{&parent});
}
