// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Debug-info component selection and serialization.

const std = @import("std");

pub const Component = enum {
    location,
    snippet,
    ast_id,
    ethdebug,

    pub fn name(self: Component) []const u8 {
        return switch (self) {
            .location => "location",
            .snippet => "snippet",
            .ast_id => "ast-id",
            .ethdebug => "ethdebug",
        };
    }
};

/// `std::map` iteration in the original is lexical, not declaration order.
const lexical_components = [_]Component{ .ast_id, .ethdebug, .location, .snippet };

pub const DebugInfoSelection = struct {
    location: bool = false,
    snippet: bool = false,
    ast_id: bool = false,
    ethdebug: bool = false,

    pub fn allValue(value: bool) DebugInfoSelection {
        return .{ .location = value, .snippet = value, .ast_id = value, .ethdebug = value };
    }

    pub fn noneValue() DebugInfoSelection {
        return allValue(false);
    }

    pub fn only(component: Component) DebugInfoSelection {
        var result: DebugInfoSelection = .{};
        result.set(component, true);
        return result;
    }

    pub fn defaultValue() DebugInfoSelection {
        return allExceptExperimental();
    }

    pub fn allExcept(components: []const Component) DebugInfoSelection {
        var result = allValue(true);
        for (components) |component| result.set(component, false);
        return result;
    }

    pub fn allExceptExperimental() DebugInfoSelection {
        return allExcept(&.{.ethdebug});
    }

    pub fn fromString(input: []const u8) ?DebugInfoSelection {
        if (std.mem.eql(u8, input, "all")) return allExceptExperimental();
        if (std.mem.eql(u8, input, "none")) return noneValue();
        var result: DebugInfoSelection = .{};
        var iterator = std.mem.splitScalar(u8, input, ',');
        while (iterator.next()) |name| {
            if (!result.enable(name)) return null;
        }
        return result;
    }

    pub fn fromComponents(names: []const []const u8, accept_wildcards: bool) ?DebugInfoSelection {
        var result: DebugInfoSelection = .{};
        for (names) |name| {
            if (std.mem.eql(u8, name, "*")) {
                return if (accept_wildcards) allExceptExperimental() else null;
            }
            if (!result.enable(name)) return null;
        }
        return result;
    }

    pub fn enable(self: *DebugInfoSelection, raw_name: []const u8) bool {
        const name = std.mem.trim(u8, raw_name, " \t\r\n\x0b\x0c");
        for (lexical_components) |component| {
            if (std.mem.eql(u8, name, component.name())) {
                self.set(component, true);
                return true;
            }
        }
        return false;
    }

    pub fn all(self: DebugInfoSelection) bool {
        return self.location and self.snippet and self.ast_id and self.ethdebug;
    }

    pub fn any(self: DebugInfoSelection) bool {
        return self.location or self.snippet or self.ast_id or self.ethdebug;
    }

    pub fn none(self: DebugInfoSelection) bool {
        return !self.any();
    }

    pub fn onlyComponent(self: DebugInfoSelection, component: Component) bool {
        return self.eql(only(component));
    }

    pub fn intersect(self: DebugInfoSelection, other: DebugInfoSelection) DebugInfoSelection {
        return .{
            .location = self.location and other.location,
            .snippet = self.snippet and other.snippet,
            .ast_id = self.ast_id and other.ast_id,
            .ethdebug = self.ethdebug and other.ethdebug,
        };
    }

    pub fn merge(self: DebugInfoSelection, other: DebugInfoSelection) DebugInfoSelection {
        return .{
            .location = self.location or other.location,
            .snippet = self.snippet or other.snippet,
            .ast_id = self.ast_id or other.ast_id,
            .ethdebug = self.ethdebug or other.ethdebug,
        };
    }

    pub fn eql(self: DebugInfoSelection, other: DebugInfoSelection) bool {
        return self.location == other.location and self.snippet == other.snippet and
            self.ast_id == other.ast_id and self.ethdebug == other.ethdebug;
    }

    pub fn selectedNamesAlloc(
        self: DebugInfoSelection,
        allocator: std.mem.Allocator,
    ) ![]const []const u8 {
        var result: std.ArrayList([]const u8) = .empty;
        errdefer result.deinit(allocator);
        for (lexical_components) |component| {
            if (self.get(component)) try result.append(allocator, component.name());
        }
        return result.toOwnedSlice(allocator);
    }

    pub fn renderAlloc(self: DebugInfoSelection, allocator: std.mem.Allocator) ![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(allocator);
        var first = true;
        for (lexical_components) |component| {
            if (!self.get(component)) continue;
            if (!first) try output.append(allocator, ',');
            try output.appendSlice(allocator, component.name());
            first = false;
        }
        return output.toOwnedSlice(allocator);
    }

    fn get(self: DebugInfoSelection, component: Component) bool {
        return switch (component) {
            .location => self.location,
            .snippet => self.snippet,
            .ast_id => self.ast_id,
            .ethdebug => self.ethdebug,
        };
    }

    fn set(self: *DebugInfoSelection, component: Component, value: bool) void {
        switch (component) {
            .location => self.location = value,
            .snippet => self.snippet = value,
            .ast_id => self.ast_id = value,
            .ethdebug => self.ethdebug = value,
        }
    }
};

test "debug selections trim, wildcard, combine, and serialize lexically" {
    const selection = DebugInfoSelection.fromString(" snippet,ast-id , location").?;
    try std.testing.expect(!selection.ethdebug);
    const rendered = try selection.renderAlloc(std.testing.allocator);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("ast-id,location,snippet", rendered);
    try std.testing.expect(DebugInfoSelection.fromComponents(&.{"*"}, true).?.eql(
        DebugInfoSelection.defaultValue(),
    ));
}
