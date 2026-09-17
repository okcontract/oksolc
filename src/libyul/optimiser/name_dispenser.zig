// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic generation of short Yul names that avoid declarations,
//! reserved names, language keywords, and dialect builtins.

const std = @import("std");
const AST = @import("../ast.zig");
const NameCollectorModule = @import("name_collector.zig");
const NameSet = NameCollectorModule.NameSet;
const OptimizerUtilities = @import("optimizer_utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

const UsedNameContext = struct {
    pub fn hash(_: @This(), name: YulName) u64 {
        return name.hashValue();
    }

    pub fn eql(_: @This(), left: YulName, right: YulName) bool {
        return left.eql(right);
    }
};

/// Membership index for names which the dispenser must not generate. No
/// optimizer path observes its iteration order.
pub const UsedNameSet = std.HashMapUnmanaged(YulName, void, UsedNameContext, 80);

pub const NameDispenser = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    used_names: UsedNameSet = .empty,
    reserved_names: NameSet = .{},
    counter: usize = 0,

    pub fn initFromAst(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *const AST.Block,
        reserved_names: *const NameSet,
    ) !NameDispenser {
        var collector = try NameCollectorModule.NameCollector.initBlock(
            allocator,
            ast,
            .variables_and_functions,
        );
        defer collector.deinit();
        var used_names = collector.takeNames();
        defer used_names.deinit(allocator);
        for (0..reserved_names.len()) |index|
            _ = try used_names.insert(allocator, reserved_names.at(index));
        var result: NameDispenser = .{
            .allocator = allocator,
            .dialect = dialect,
            .used_names = try indexNames(allocator, used_names.take()),
        };
        errdefer result.deinit();
        result.reserved_names = try reserved_names.clone(allocator);
        return result;
    }

    /// Takes ownership of `owned_names`, including on allocation failure.
    pub fn initWithUsedNames(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        owned_names: NameSet,
    ) !NameDispenser {
        return .{
            .allocator = allocator,
            .dialect = dialect,
            .used_names = try indexNames(allocator, owned_names),
        };
    }

    pub fn deinit(self: *NameDispenser) void {
        self.used_names.deinit(self.allocator);
        self.reserved_names.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn newName(self: *NameDispenser, name_hint: YulName) anyerror!YulName {
        var name = name_hint;
        while (try self.illegalName(name)) {
            if (self.counter == std.math.maxInt(usize)) return error.NameCounterOverflow;
            self.counter += 1;
            name = try YulName.initGenerated(name_hint, self.counter);
        }
        try self.used_names.put(self.allocator, name, {});
        return name;
    }

    pub fn markUsed(self: *NameDispenser, name: YulName) !void {
        try self.used_names.put(self.allocator, name, {});
    }

    pub fn usedNames(self: *const NameDispenser) *const UsedNameSet {
        return &self.used_names;
    }

    pub fn illegalName(self: *const NameDispenser, name: YulName) !bool {
        return OptimizerUtilities.isRestrictedIdentifier(self.dialect, try name.str()) or
            self.used_names.contains(name);
    }

    pub fn reset(self: *NameDispenser, ast: *const AST.Block) !void {
        var collector = try NameCollectorModule.NameCollector.initBlock(
            self.allocator,
            ast,
            .variables_and_functions,
        );
        defer collector.deinit();
        var replacement = collector.takeNames();
        defer replacement.deinit(self.allocator);
        for (0..self.reserved_names.len()) |index|
            _ = try replacement.insert(self.allocator, self.reserved_names.at(index));
        const replacement_index = try indexNames(self.allocator, replacement.take());
        self.used_names.deinit(self.allocator);
        self.used_names = replacement_index;
        self.counter = 0;
    }

    fn indexNames(allocator: std.mem.Allocator, owned_names: NameSet) !UsedNameSet {
        var names = owned_names;
        defer names.deinit(allocator);
        var result: UsedNameSet = .empty;
        errdefer result.deinit(allocator);
        try result.ensureTotalCapacity(allocator, @intCast(names.len()));
        for (0..names.len()) |index|
            try result.putNoClobber(allocator, names.at(index), {});
        return result;
    }
};

test "name dispenser respects used, reserved, and builtin names" {
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var used: NameSet = .{};
    defer used.deinit(allocator);
    const x = try YulName.init("x");
    _ = try used.insert(allocator, x);
    var dispenser = try NameDispenser.initWithUsedNames(allocator, dialect.dialect(), used.take());
    defer dispenser.deinit();
    try std.testing.expectEqual(@as(u32, 1), dispenser.usedNames().count());
    try dispenser.markUsed(x);
    try std.testing.expectEqual(@as(u32, 1), dispenser.usedNames().count());
    try std.testing.expectEqualStrings("x_1", try (try dispenser.newName(try YulName.init("x"))).str());
    try std.testing.expectEqualStrings("x_2", try (try dispenser.newName(try YulName.init("x"))).str());
    try std.testing.expectEqualStrings("add_3", try (try dispenser.newName(try YulName.init("add"))).str());
    try std.testing.expectEqual(@as(u32, 4), dispenser.usedNames().count());
}
