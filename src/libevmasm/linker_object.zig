// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned linker object translated from `LinkerObject.cpp`.

const std = @import("std");
const CommonData = @import("../libsolutil/common_data.zig");
const FixedHash = @import("../libsolutil/fixed_hash.zig");
const Keccak256 = @import("../libsolutil/keccak256.zig");

pub const H160 = FixedHash.H160;

pub const LinkReference = struct {
    offset: usize,
    /// Allocator-owned UTF-8 bytes.
    library_name: []u8,
};

pub const ImmutableRefs = struct {
    /// Allocator-owned full immutable identifier.
    identifier: []u8,
    offsets: std.ArrayList(usize) = .empty,

    pub fn deinit(self: *ImmutableRefs, allocator: std.mem.Allocator) void {
        allocator.free(self.identifier);
        self.offsets.deinit(allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const ImmutableRefs, allocator: std.mem.Allocator) !ImmutableRefs {
        const identifier = try allocator.dupe(u8, self.identifier);
        errdefer allocator.free(identifier);
        var offsets: std.ArrayList(usize) = .empty;
        errdefer offsets.deinit(allocator);
        try offsets.ensureTotalCapacityPrecise(allocator, self.offsets.items.len);
        offsets.appendSliceAssumeCapacity(self.offsets.items);
        return .{ .identifier = identifier, .offsets = offsets };
    }
};

pub const ImmutableReference = struct {
    hash: u256,
    references: ImmutableRefs,
};

pub const InstructionLocation = struct {
    start: usize = 0,
    end: usize = 0,
    assembly_item_index: usize = 0,
};

pub const CodeSectionLocation = struct {
    start: usize = 0,
    end: usize = 0,
    instruction_locations: std.ArrayList(InstructionLocation) = .empty,

    pub fn deinit(self: *CodeSectionLocation, allocator: std.mem.Allocator) void {
        self.instruction_locations.deinit(allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const CodeSectionLocation, allocator: std.mem.Allocator) !CodeSectionLocation {
        var locations: std.ArrayList(InstructionLocation) = .empty;
        errdefer locations.deinit(allocator);
        try locations.ensureTotalCapacityPrecise(allocator, self.instruction_locations.items.len);
        locations.appendSliceAssumeCapacity(self.instruction_locations.items);
        return .{
            .start = self.start,
            .end = self.end,
            .instruction_locations = locations,
        };
    }
};

pub const FunctionDebugData = struct {
    bytecode_offset: ?usize = null,
    instruction_index: ?usize = null,
    source_id: ?usize = null,
    params: usize = 0,
    returns: usize = 0,
};

pub const NamedFunctionDebugData = struct {
    /// Allocator-owned function name.
    name: []u8,
    data: FunctionDebugData,
};

pub const LibraryAddress = struct {
    name: []const u8,
    address: H160,
};

pub const LinkError = std.mem.Allocator.Error || error{ReferenceOutOfBounds};

pub const LinkerObject = struct {
    bytecode: std.ArrayList(u8) = .empty,
    /// Sorted by `offset`, exactly like `std::map<size_t, string>`.
    link_references: std.ArrayList(LinkReference) = .empty,
    /// Sorted by the numeric hash key.
    immutable_references: std.ArrayList(ImmutableReference) = .empty,
    code_section_location: CodeSectionLocation = .{},
    /// Sorted lexicographically by name.
    function_debug_data: std.ArrayList(NamedFunctionDebugData) = .empty,

    pub fn deinit(self: *LinkerObject, allocator: std.mem.Allocator) void {
        self.bytecode.deinit(allocator);
        for (self.link_references.items) |reference| allocator.free(reference.library_name);
        self.link_references.deinit(allocator);
        for (self.immutable_references.items) |*reference| reference.references.deinit(allocator);
        self.immutable_references.deinit(allocator);
        self.code_section_location.deinit(allocator);
        for (self.function_debug_data.items) |entry| allocator.free(entry.name);
        self.function_debug_data.deinit(allocator);
        self.* = undefined;
    }

    pub fn clone(self: *const LinkerObject, allocator: std.mem.Allocator) !LinkerObject {
        var result: LinkerObject = .{};
        errdefer result.deinit(allocator);
        try result.bytecode.ensureTotalCapacityPrecise(allocator, self.bytecode.items.len);
        result.bytecode.appendSliceAssumeCapacity(self.bytecode.items);
        // Reserve before cloning children: completed children transfer through
        // non-failing appends and partial results always have one cleanup owner.
        try result.link_references.ensureTotalCapacityPrecise(allocator, self.link_references.items.len);
        for (self.link_references.items) |reference| {
            result.link_references.appendAssumeCapacity(.{
                .offset = reference.offset,
                .library_name = try allocator.dupe(u8, reference.library_name),
            });
        }
        try result.immutable_references.ensureTotalCapacityPrecise(allocator, self.immutable_references.items.len);
        for (self.immutable_references.items) |reference| {
            result.immutable_references.appendAssumeCapacity(.{
                .hash = reference.hash,
                .references = try reference.references.clone(allocator),
            });
        }
        result.code_section_location = try self.code_section_location.clone(allocator);
        try result.function_debug_data.ensureTotalCapacityPrecise(allocator, self.function_debug_data.items.len);
        for (self.function_debug_data.items) |entry| {
            result.function_debug_data.appendAssumeCapacity(.{
                .name = try allocator.dupe(u8, entry.name),
                .data = entry.data,
            });
        }
        return result;
    }

    pub fn take(self: *LinkerObject) LinkerObject {
        const result = self.*;
        self.* = .{};
        return result;
    }

    pub fn append(
        self: *LinkerObject,
        allocator: std.mem.Allocator,
        other: *const LinkerObject,
    ) std.mem.Allocator.Error!void {
        const base = self.bytecode.items.len;
        for (other.link_references.items) |reference| {
            try self.putLinkReference(allocator, base + reference.offset, reference.library_name);
        }
        try self.bytecode.appendSlice(allocator, other.bytecode.items);
    }

    pub fn putLinkReference(
        self: *LinkerObject,
        allocator: std.mem.Allocator,
        offset: usize,
        library_name: []const u8,
    ) std.mem.Allocator.Error!void {
        const index = lowerBoundLinkReference(self.link_references.items, offset);
        const owned_name = try allocator.dupe(u8, library_name);
        errdefer allocator.free(owned_name);
        if (index < self.link_references.items.len and self.link_references.items[index].offset == offset) {
            allocator.free(self.link_references.items[index].library_name);
            self.link_references.items[index].library_name = owned_name;
            return;
        }
        try self.link_references.insert(allocator, index, .{
            .offset = offset,
            .library_name = owned_name,
        });
    }

    pub fn putImmutableReference(
        self: *LinkerObject,
        allocator: std.mem.Allocator,
        hash: u256,
        identifier: []const u8,
        offsets: []const usize,
    ) std.mem.Allocator.Error!void {
        const index = lowerBoundImmutableReference(self.immutable_references.items, hash);
        var references: ImmutableRefs = .{
            .identifier = try allocator.dupe(u8, identifier),
        };
        errdefer references.deinit(allocator);
        try references.offsets.appendSlice(allocator, offsets);
        if (index < self.immutable_references.items.len and self.immutable_references.items[index].hash == hash) {
            self.immutable_references.items[index].references.deinit(allocator);
            self.immutable_references.items[index].references = references;
            return;
        }
        try self.immutable_references.insert(allocator, index, .{
            .hash = hash,
            .references = references,
        });
    }

    pub fn putFunctionDebugData(
        self: *LinkerObject,
        allocator: std.mem.Allocator,
        name: []const u8,
        data: FunctionDebugData,
    ) std.mem.Allocator.Error!void {
        const index = lowerBoundFunction(self.function_debug_data.items, name);
        const owned_name = try allocator.dupe(u8, name);
        errdefer allocator.free(owned_name);
        if (index < self.function_debug_data.items.len and
            std.mem.eql(u8, self.function_debug_data.items[index].name, name))
        {
            allocator.free(self.function_debug_data.items[index].name);
            self.function_debug_data.items[index] = .{ .name = owned_name, .data = data };
            return;
        }
        try self.function_debug_data.insert(allocator, index, .{ .name = owned_name, .data = data });
    }

    /// Replaces every resolvable 20-byte placeholder and removes only those
    /// references. Address names and bytes are borrowed for the duration.
    pub fn link(self: *LinkerObject, allocator: std.mem.Allocator, addresses: []const LibraryAddress) LinkError!void {
        // Reject malformed selected references before freeing any names or
        // changing bytes. An error leaves the object safe to retry or destroy.
        for (self.link_references.items) |reference| {
            if (findLibrary(addresses, reference.library_name) == null) continue;
            if (reference.offset > self.bytecode.items.len or
                self.bytecode.items.len - reference.offset < H160.size)
                return error.ReferenceOutOfBounds;
        }
        var output_index: usize = 0;
        for (self.link_references.items) |reference| {
            if (findLibrary(addresses, reference.library_name)) |address| {
                @memcpy(
                    self.bytecode.items[reference.offset..][0..H160.size],
                    address.bytes(),
                );
                allocator.free(reference.library_name);
            } else {
                self.link_references.items[output_index] = reference;
                output_index += 1;
            }
        }
        self.link_references.shrinkRetainingCapacity(output_index);
    }

    pub fn toHexAlloc(self: *const LinkerObject, allocator: std.mem.Allocator) LinkError![]u8 {
        const output = try CommonData.toHexAlloc(allocator, self.bytecode.items, .dont_add, .lower);
        errdefer allocator.free(output);
        for (self.link_references.items) |reference| {
            if (reference.offset > self.bytecode.items.len or
                self.bytecode.items.len - reference.offset < H160.size)
            {
                return error.ReferenceOutOfBounds;
            }
            const position = reference.offset * 2;
            const placeholder = libraryPlaceholder(reference.library_name);
            output[position] = '_';
            output[position + 1] = '_';
            @memcpy(output[position + 2 ..][0..placeholder.len], &placeholder);
            output[position + 38] = '_';
            output[position + 39] = '_';
        }
        return output;
    }

    pub fn lessThan(self: *const LinkerObject, other: *const LinkerObject) bool {
        const bytecode_order = std.mem.order(u8, self.bytecode.items, other.bytecode.items);
        if (bytecode_order != .eq) return bytecode_order == .lt;
        if (compareLinkReferences(self.link_references.items, other.link_references.items)) |less| return less;
        if (compareImmutableReferences(self.immutable_references.items, other.immutable_references.items)) |less| return less;
        return false;
    }
};

pub fn libraryPlaceholder(library_name: []const u8) [36]u8 {
    const hash = Keccak256.keccak256(library_name);
    const hex = hash.hex();
    var result: [36]u8 = undefined;
    result[0] = '$';
    @memcpy(result[1..35], hex[0..34]);
    result[35] = '$';
    return result;
}

fn lowerBoundLinkReference(items: []const LinkReference, offset: usize) usize {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (items[middle].offset < offset) lower = middle + 1 else upper = middle;
    }
    return lower;
}

fn lowerBoundImmutableReference(items: []const ImmutableReference, hash: u256) usize {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (items[middle].hash < hash) lower = middle + 1 else upper = middle;
    }
    return lower;
}

fn lowerBoundFunction(items: []const NamedFunctionDebugData, name: []const u8) usize {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (std.mem.order(u8, items[middle].name, name) == .lt) lower = middle + 1 else upper = middle;
    }
    return lower;
}

fn findLibrary(addresses: []const LibraryAddress, name: []const u8) ?*const H160 {
    for (addresses) |*entry| if (std.mem.eql(u8, entry.name, name)) return &entry.address;
    return null;
}

fn compareLinkReferences(lhs: []const LinkReference, rhs: []const LinkReference) ?bool {
    const count = @min(lhs.len, rhs.len);
    for (lhs[0..count], rhs[0..count]) |left, right| {
        if (left.offset != right.offset) return left.offset < right.offset;
        const name_order = std.mem.order(u8, left.library_name, right.library_name);
        if (name_order != .eq) return name_order == .lt;
    }
    if (lhs.len != rhs.len) return lhs.len < rhs.len;
    return null;
}

fn compareImmutableReferences(lhs: []const ImmutableReference, rhs: []const ImmutableReference) ?bool {
    const count = @min(lhs.len, rhs.len);
    for (lhs[0..count], rhs[0..count]) |left, right| {
        if (left.hash != right.hash) return left.hash < right.hash;
        const identifier_order = std.mem.order(
            u8,
            left.references.identifier,
            right.references.identifier,
        );
        if (identifier_order != .eq) return identifier_order == .lt;
        const offset_count = @min(left.references.offsets.items.len, right.references.offsets.items.len);
        for (
            left.references.offsets.items[0..offset_count],
            right.references.offsets.items[0..offset_count],
        ) |left_offset, right_offset| {
            if (left_offset != right_offset) return left_offset < right_offset;
        }
        if (left.references.offsets.items.len != right.references.offsets.items.len) {
            return left.references.offsets.items.len < right.references.offsets.items.len;
        }
    }
    if (lhs.len != rhs.len) return lhs.len < rhs.len;
    return null;
}

test "linker placeholders and selective linking preserve offsets and ownership" {
    var object: LinkerObject = .{};
    defer object.deinit(std.testing.allocator);
    try object.bytecode.appendNTimes(std.testing.allocator, 0, 25);
    try object.putLinkReference(std.testing.allocator, 2, "lib.sol:Math");

    const placeholder = libraryPlaceholder("lib.sol:Math");
    const unlinked = try object.toHexAlloc(std.testing.allocator);
    defer std.testing.allocator.free(unlinked);
    try std.testing.expectEqualStrings("0000__", unlinked[0..6]);
    try std.testing.expectEqualStrings(&placeholder, unlinked[6..42]);
    try std.testing.expectEqualStrings("__", unlinked[42..44]);

    var address = H160.init();
    @memset(address.mutableBytes(), 0xab);
    try object.link(std.testing.allocator, &.{.{
        .name = "lib.sol:Math",
        .address = address,
    }});
    try std.testing.expect(object.link_references.items.len == 0);
    try std.testing.expectEqualSlices(u8, address.bytes(), object.bytecode.items[2..22]);
}

test "append rebases references while clone is independent" {
    var first: LinkerObject = .{};
    defer first.deinit(std.testing.allocator);
    try first.bytecode.appendSlice(std.testing.allocator, &.{ 1, 2, 3 });

    var second: LinkerObject = .{};
    defer second.deinit(std.testing.allocator);
    try second.bytecode.appendNTimes(std.testing.allocator, 0, 20);
    try second.putLinkReference(std.testing.allocator, 0, "L");
    try first.append(std.testing.allocator, &second);
    try std.testing.expectEqual(@as(usize, 3), first.link_references.items[0].offset);

    var cloned = try first.clone(std.testing.allocator);
    defer cloned.deinit(std.testing.allocator);
    cloned.bytecode.items[0] = 0xff;
    try std.testing.expectEqual(@as(u8, 1), first.bytecode.items[0]);
}

test "linker clone cleans all partial children on allocation failure" {
    const allocator = std.testing.allocator;
    var original: LinkerObject = .{};
    defer original.deinit(allocator);
    try original.bytecode.appendNTimes(allocator, 0, 40);
    try original.putLinkReference(allocator, 0, "A");
    try original.putLinkReference(allocator, 20, "B");
    try original.putImmutableReference(allocator, 1, "first", &.{ 2, 4 });
    try original.putImmutableReference(allocator, 2, "second", &.{6});
    try original.putFunctionDebugData(allocator, "f", .{ .params = 2 });
    try original.putFunctionDebugData(allocator, "g", .{ .returns = 1 });
    original.code_section_location.start = 1;
    original.code_section_location.end = 40;
    try original.code_section_location.instruction_locations.append(allocator, .{ .start = 1, .end = 2 });
    const Check = struct {
        fn run(failing: std.mem.Allocator, source: *const LinkerObject) !void {
            var copy = try source.clone(failing);
            defer copy.deinit(failing);
            try std.testing.expectEqualSlices(u8, source.bytecode.items, copy.bytecode.items);
            try std.testing.expectEqualStrings("first", copy.immutable_references.items[0].references.identifier);
            try std.testing.expectEqualSlices(usize, &.{ 2, 4 }, copy.immutable_references.items[0].references.offsets.items);
            try std.testing.expectEqual(@as(usize, 2), copy.function_debug_data.items[0].data.params);
            try std.testing.expectEqual(@as(usize, 40), copy.code_section_location.end);
            copy.bytecode.items[0] = 1;
            copy.link_references.items[0].library_name[0] = 'C';
            copy.immutable_references.items[0].references.offsets.items[0] = 8;
            copy.function_debug_data.items[0].name[0] = 'h';
            copy.code_section_location.instruction_locations.items[0].end = 9;
            try std.testing.expectEqual(@as(u8, 0), source.bytecode.items[0]);
            try std.testing.expectEqualStrings("A", source.link_references.items[0].library_name);
            try std.testing.expectEqual(@as(usize, 2), source.immutable_references.items[0].references.offsets.items[0]);
            try std.testing.expectEqualStrings("f", source.function_debug_data.items[0].name);
            try std.testing.expectEqual(@as(usize, 2), source.code_section_location.instruction_locations.items[0].end);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{&original});
}

test "linker invalid late reference preserves ownership and permits retry" {
    const allocator = std.testing.allocator;
    for ([_]usize{ 21, std.math.maxInt(usize) }) |bad_offset| {
        var object: LinkerObject = .{};
        defer object.deinit(allocator);
        try object.bytecode.appendNTimes(allocator, 0, 40);
        try object.putLinkReference(allocator, 0, "A");
        try object.putLinkReference(allocator, 10, "B");
        try object.putLinkReference(allocator, bad_offset, "A");
        const original_name = object.link_references.items[0].library_name.ptr;
        var address = H160.init();
        @memset(address.mutableBytes(), 0xab);
        const addresses = [_]LibraryAddress{.{ .name = "A", .address = address }};
        try std.testing.expectError(error.ReferenceOutOfBounds, object.link(allocator, &addresses));
        try std.testing.expectEqualSlices(u8, &([_]u8{0} ** 40), object.bytecode.items);
        try std.testing.expectEqual(@as(usize, 3), object.link_references.items.len);
        try std.testing.expectEqual(original_name, object.link_references.items[0].library_name.ptr);
        try std.testing.expectEqualStrings("A", object.link_references.items[0].library_name);
        const removed = object.link_references.orderedRemove(2);
        allocator.free(removed.library_name);
        try object.link(allocator, &addresses);
        try std.testing.expectEqual(@as(usize, 1), object.link_references.items.len);
        try std.testing.expectEqualStrings("B", object.link_references.items[0].library_name);
        try std.testing.expectEqualSlices(u8, address.bytes(), object.bytecode.items[0..20]);
    }
}
