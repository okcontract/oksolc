// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Explicit runtime interface for the open `AbstractAssemblyStack` hierarchy.

const std = @import("std");
const JSON = @import("../libsolutil/json.zig");
const LinkerObject = @import("linker_object.zig").LinkerObject;

pub const NamedSource = struct {
    name: []const u8,
    source: []const u8,
};

pub const OwnedStrings = struct {
    allocator: std.mem.Allocator,
    values: [][]u8,

    pub fn deinit(self: *OwnedStrings) void {
        for (self.values) |value| self.allocator.free(value);
        self.allocator.free(self.values);
        self.* = undefined;
    }

    pub fn fromBorrowed(
        allocator: std.mem.Allocator,
        values: []const []const u8,
    ) std.mem.Allocator.Error!OwnedStrings {
        const output = try allocator.alloc([]u8, values.len);
        var initialized: usize = 0;
        errdefer {
            for (output[0..initialized]) |value| allocator.free(value);
            allocator.free(output);
        }
        for (values, output) |value, *owned| {
            owned.* = try allocator.dupe(u8, value);
            initialized += 1;
        }
        return .{ .allocator = allocator, .values = output };
    }
};

/// Returned `LinkerObject` and mapping/string slices are borrows valid until
/// the next mutation of the concrete stack. Allocated strings, string lists,
/// and JSON documents are owned by the caller.
pub const AbstractAssemblyStack = struct {
    context: *anyopaque,
    vtable: *const VTable,

    pub const VTable = struct {
        object: *const fn (*anyopaque, []const u8) anyerror!*const LinkerObject,
        runtime_object: *const fn (*anyopaque, []const u8) anyerror!*const LinkerObject,
        source_mapping: *const fn (*anyopaque, []const u8) ?[]const u8,
        runtime_source_mapping: *const fn (*anyopaque, []const u8) ?[]const u8,
        ethdebug_contract: *const fn (*anyopaque, std.mem.Allocator, []const u8) anyerror!JSON.JsonDocument,
        ethdebug_runtime: *const fn (*anyopaque, std.mem.Allocator, []const u8) anyerror!JSON.JsonDocument,
        ethdebug_all: *const fn (*anyopaque, std.mem.Allocator) anyerror!JSON.JsonDocument,
        ethdebug_compilation: *const fn (*anyopaque, std.mem.Allocator) anyerror!JSON.JsonDocument,
        assembly_json: *const fn (*anyopaque, std.mem.Allocator, []const u8) anyerror!JSON.JsonDocument,
        assembly_string: *const fn (
            *anyopaque,
            std.mem.Allocator,
            []const u8,
            []const NamedSource,
        ) anyerror![]u8,
        filesystem_friendly_name: *const fn (*anyopaque, std.mem.Allocator, []const u8) anyerror![]u8,
        contract_names: *const fn (*anyopaque, std.mem.Allocator) anyerror!OwnedStrings,
        source_names: *const fn (*anyopaque, std.mem.Allocator) anyerror!OwnedStrings,
        compilation_successful: *const fn (*anyopaque) bool,
    };

    pub fn object(self: AbstractAssemblyStack, contract_name: []const u8) !*const LinkerObject {
        return self.vtable.object(self.context, contract_name);
    }

    pub fn runtimeObject(self: AbstractAssemblyStack, contract_name: []const u8) !*const LinkerObject {
        return self.vtable.runtime_object(self.context, contract_name);
    }

    pub fn sourceMapping(self: AbstractAssemblyStack, contract_name: []const u8) ?[]const u8 {
        return self.vtable.source_mapping(self.context, contract_name);
    }

    pub fn runtimeSourceMapping(self: AbstractAssemblyStack, contract_name: []const u8) ?[]const u8 {
        return self.vtable.runtime_source_mapping(self.context, contract_name);
    }

    pub fn ethdebugContract(
        self: AbstractAssemblyStack,
        allocator: std.mem.Allocator,
        contract_name: []const u8,
    ) !JSON.JsonDocument {
        return self.vtable.ethdebug_contract(self.context, allocator, contract_name);
    }

    pub fn ethdebugRuntime(
        self: AbstractAssemblyStack,
        allocator: std.mem.Allocator,
        contract_name: []const u8,
    ) !JSON.JsonDocument {
        return self.vtable.ethdebug_runtime(self.context, allocator, contract_name);
    }

    pub fn ethdebug(self: AbstractAssemblyStack, allocator: std.mem.Allocator) !JSON.JsonDocument {
        return self.vtable.ethdebug_all(self.context, allocator);
    }

    pub fn ethdebugCompilation(self: AbstractAssemblyStack, allocator: std.mem.Allocator) !JSON.JsonDocument {
        return self.vtable.ethdebug_compilation(self.context, allocator);
    }

    pub fn assemblyJSON(
        self: AbstractAssemblyStack,
        allocator: std.mem.Allocator,
        contract_name: []const u8,
    ) !JSON.JsonDocument {
        return self.vtable.assembly_json(self.context, allocator, contract_name);
    }

    pub fn assemblyString(
        self: AbstractAssemblyStack,
        allocator: std.mem.Allocator,
        contract_name: []const u8,
        source_codes: []const NamedSource,
    ) ![]u8 {
        return self.vtable.assembly_string(self.context, allocator, contract_name, source_codes);
    }

    pub fn filesystemFriendlyName(
        self: AbstractAssemblyStack,
        allocator: std.mem.Allocator,
        contract_name: []const u8,
    ) ![]u8 {
        return self.vtable.filesystem_friendly_name(self.context, allocator, contract_name);
    }

    pub fn contractNames(self: AbstractAssemblyStack, allocator: std.mem.Allocator) !OwnedStrings {
        return self.vtable.contract_names(self.context, allocator);
    }

    pub fn sourceNames(self: AbstractAssemblyStack, allocator: std.mem.Allocator) !OwnedStrings {
        return self.vtable.source_names(self.context, allocator);
    }

    pub fn compilationSuccessful(self: AbstractAssemblyStack) bool {
        return self.vtable.compilation_successful(self.context);
    }
};

test "open assembly-stack interface keeps borrows and caller ownership explicit" {
    const Mock = struct {
        object_value: LinkerObject = .{},
        compilation_ok: bool = true,

        fn object(context: *anyopaque, _: []const u8) anyerror!*const LinkerObject {
            const self: *@This() = @ptrCast(@alignCast(context));
            return &self.object_value;
        }
        fn mapping(_: *anyopaque, _: []const u8) ?[]const u8 {
            return "1:2:0";
        }
        fn json(_: *anyopaque, _: std.mem.Allocator, _: []const u8) anyerror!JSON.JsonDocument {
            return error.NotImplemented;
        }
        fn jsonAll(_: *anyopaque, _: std.mem.Allocator) anyerror!JSON.JsonDocument {
            return error.NotImplemented;
        }
        fn assemblyString(
            _: *anyopaque,
            allocator: std.mem.Allocator,
            contract_name: []const u8,
            _: []const NamedSource,
        ) anyerror![]u8 {
            return allocator.dupe(u8, contract_name);
        }
        fn name(_: *anyopaque, allocator: std.mem.Allocator, contract_name: []const u8) anyerror![]u8 {
            return allocator.dupe(u8, contract_name);
        }
        fn names(_: *anyopaque, allocator: std.mem.Allocator) anyerror!OwnedStrings {
            return OwnedStrings.fromBorrowed(allocator, &.{ "A", "B" });
        }
        fn isSuccessful(context: *anyopaque) bool {
            const self: *@This() = @ptrCast(@alignCast(context));
            return self.compilation_ok;
        }

        const vtable: AbstractAssemblyStack.VTable = .{
            .object = object,
            .runtime_object = object,
            .source_mapping = mapping,
            .runtime_source_mapping = mapping,
            .ethdebug_contract = json,
            .ethdebug_runtime = json,
            .ethdebug_all = jsonAll,
            .ethdebug_compilation = jsonAll,
            .assembly_json = json,
            .assembly_string = assemblyString,
            .filesystem_friendly_name = name,
            .contract_names = names,
            .source_names = names,
            .compilation_successful = isSuccessful,
        };
    };

    var mock: Mock = .{};
    const interface: AbstractAssemblyStack = .{ .context = &mock, .vtable = &Mock.vtable };
    try std.testing.expect((try interface.object("A")) == &mock.object_value);
    try std.testing.expectEqualStrings("1:2:0", interface.sourceMapping("A").?);
    try std.testing.expect(interface.compilationSuccessful());
    var names = try interface.contractNames(std.testing.allocator);
    defer names.deinit();
    try std.testing.expectEqualStrings("B", names.values[1]);
}
