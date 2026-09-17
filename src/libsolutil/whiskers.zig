// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned, allocation-explicit translation of the Whiskers template engine.

const std = @import("std");

pub const WhiskersError = error{
    InvalidTemplate,
    InvalidParameter,
    ParameterAlreadySet,
    TagNotFound,
    ValueNotProvided,
    ListNotSet,
    ConditionNotSet,
    TagConditionNotSet,
    ParameterCollision,
};

pub const Error = std.mem.Allocator.Error || WhiskersError;

pub const StringPair = struct {
    name: []const u8,
    value: []const u8,
};

const StringMap = std.array_hash_map.String([]u8);
const ConditionMap = std.array_hash_map.String(bool);

const OwnedStringMap = struct {
    values: StringMap = .empty,

    fn deinit(self: *@This(), allocator: std.mem.Allocator) void {
        for (self.values.keys(), self.values.values()) |key, value| {
            allocator.free(key);
            allocator.free(value);
        }
        self.values.deinit(allocator);
        self.* = undefined;
    }

    fn put(
        self: *@This(),
        allocator: std.mem.Allocator,
        name: []const u8,
        value: []const u8,
    ) Error!void {
        if (self.values.contains(name)) return error.ParameterCollision;
        const owned_name = try allocator.dupe(u8, name);
        errdefer allocator.free(owned_name);
        const owned_value = try allocator.dupe(u8, value);
        errdefer allocator.free(owned_value);
        try self.values.put(allocator, owned_name, owned_value);
    }
};

const OwnedList = struct {
    elements: []OwnedStringMap,

    fn deinit(self: *@This(), allocator: std.mem.Allocator) void {
        for (self.elements) |*element| element.deinit(allocator);
        allocator.free(self.elements);
        self.* = undefined;
    }
};

const ListMap = std.array_hash_map.String(OwnedList);

pub const Whiskers = struct {
    const Self = @This();

    allocator: std.mem.Allocator,
    template: []u8,
    parameters: StringMap = .empty,
    conditions: ConditionMap = .empty,
    list_parameters: ListMap = .empty,

    pub fn init(allocator: std.mem.Allocator, template: []const u8) Error!Self {
        try checkTemplateValid(template);
        return .{
            .allocator = allocator,
            .template = try allocator.dupe(u8, template),
        };
    }

    pub fn deinit(self: *Self) void {
        for (self.parameters.keys(), self.parameters.values()) |key, value| {
            self.allocator.free(key);
            self.allocator.free(value);
        }
        self.parameters.deinit(self.allocator);
        for (self.conditions.keys()) |key| self.allocator.free(key);
        self.conditions.deinit(self.allocator);
        for (self.list_parameters.keys(), self.list_parameters.values()) |key, *list| {
            self.allocator.free(key);
            list.deinit(self.allocator);
        }
        self.list_parameters.deinit(self.allocator);
        self.allocator.free(self.template);
        self.* = undefined;
    }

    pub fn setString(self: *Self, parameter: []const u8, value: []const u8) Error!*Self {
        try checkParameterValid(parameter);
        try self.checkParameterUnknown(parameter);
        try self.checkTemplateContainsTag("", parameter);

        const owned_parameter = try self.allocator.dupe(u8, parameter);
        errdefer self.allocator.free(owned_parameter);
        const owned_value = try self.allocator.dupe(u8, value);
        errdefer self.allocator.free(owned_value);
        try self.parameters.put(self.allocator, owned_parameter, owned_value);
        return self;
    }

    pub fn setCondition(self: *Self, parameter: []const u8, value: bool) Error!*Self {
        try checkParameterValid(parameter);
        try self.checkParameterUnknown(parameter);
        try self.checkTemplateContainsTag("?", parameter);
        try self.checkTemplateContainsTag("/", parameter);

        const owned_parameter = try self.allocator.dupe(u8, parameter);
        errdefer self.allocator.free(owned_parameter);
        try self.conditions.put(self.allocator, owned_parameter, value);
        return self;
    }

    pub fn setList(
        self: *Self,
        parameter: []const u8,
        elements: []const []const StringPair,
    ) Error!*Self {
        try checkParameterValid(parameter);
        try self.checkParameterUnknown(parameter);
        try self.checkTemplateContainsTag("#", parameter);
        try self.checkTemplateContainsTag("/", parameter);

        const owned_elements = try self.allocator.alloc(OwnedStringMap, elements.len);
        for (owned_elements) |*element| element.* = .{};
        var list: OwnedList = .{ .elements = owned_elements };
        errdefer list.deinit(self.allocator);

        for (elements, owned_elements) |source_element, *owned_element| {
            for (source_element) |pair| {
                try checkParameterValid(pair.name);
                try owned_element.put(self.allocator, pair.name, pair.value);
            }
        }

        const owned_parameter = try self.allocator.dupe(u8, parameter);
        errdefer self.allocator.free(owned_parameter);
        try self.list_parameters.put(self.allocator, owned_parameter, list);
        return self;
    }

    pub fn renderAlloc(
        self: *const Self,
        allocator: std.mem.Allocator,
    ) Error![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(allocator);
        const parameters: ParameterContext = .{ .global = &self.parameters };
        try self.renderInto(
            allocator,
            &output,
            self.template,
            parameters,
            &self.list_parameters,
        );
        return output.toOwnedSlice(allocator);
    }

    fn checkParameterUnknown(self: *const Self, parameter: []const u8) WhiskersError!void {
        if (self.parameters.contains(parameter) or
            self.conditions.contains(parameter) or
            self.list_parameters.contains(parameter))
            return error.ParameterAlreadySet;
    }

    fn checkTemplateContainsTag(
        self: *const Self,
        prefix: []const u8,
        parameter: []const u8,
    ) Error!void {
        const tag = try std.fmt.allocPrint(self.allocator, "<{s}{s}>", .{ prefix, parameter });
        defer self.allocator.free(tag);
        if (std.mem.find(u8, self.template, tag) == null) return error.TagNotFound;
    }

    fn renderInto(
        self: *const Self,
        allocator: std.mem.Allocator,
        output: *std.ArrayList(u8),
        source: []const u8,
        parameters: ParameterContext,
        lists: ?*const ListMap,
    ) Error!void {
        var cursor: usize = 0;
        while (findNextMatch(source, cursor)) |match| {
            try output.appendSlice(allocator, source[cursor..match.start]);
            switch (match.kind) {
                .value => |name| {
                    const value = parameters.get(name) orelse return error.ValueNotProvided;
                    // Values are intentionally appended literally and never
                    // scanned as newly generated template text.
                    try output.appendSlice(allocator, value);
                },
                .list => |list_match| {
                    const available_lists = lists orelse return error.ListNotSet;
                    const list = available_lists.getPtr(list_match.name) orelse
                        return error.ListNotSet;
                    for (list.elements) |*element| {
                        if (hasCollision(parameters, &element.values))
                            return error.ParameterCollision;
                        try self.renderInto(
                            allocator,
                            output,
                            list_match.body,
                            .{ .global = parameters.global, .local = &element.values },
                            null,
                        );
                    }
                },
                .condition => |condition_match| {
                    const condition_value = if (condition_match.nonempty) nonempty: {
                        if (parameters.get(condition_match.name)) |value|
                            break :nonempty value.len != 0;
                        if (lists) |available_lists| {
                            if (available_lists.getPtr(condition_match.name)) |list|
                                break :nonempty list.elements.len != 0;
                        }
                        return error.TagConditionNotSet;
                    } else self.conditions.get(condition_match.name) orelse
                        return error.ConditionNotSet;
                    try self.renderInto(
                        allocator,
                        output,
                        if (condition_value) condition_match.if_body else condition_match.else_body,
                        parameters,
                        lists,
                    );
                },
            }
            cursor = match.end;
        }
        try output.appendSlice(allocator, source[cursor..]);
    }
};

const ParameterContext = struct {
    global: *const StringMap,
    local: ?*const StringMap = null,

    fn get(self: @This(), name: []const u8) ?[]const u8 {
        if (self.local) |local| if (local.get(name)) |value| return value;
        return self.global.get(name);
    }
};

fn hasCollision(parameters: ParameterContext, local: *const StringMap) bool {
    for (local.keys()) |name| if (parameters.get(name) != null) return true;
    return false;
}

const Match = struct {
    start: usize,
    end: usize,
    kind: union(enum) {
        value: []const u8,
        list: struct {
            name: []const u8,
            body: []const u8,
        },
        condition: struct {
            name: []const u8,
            nonempty: bool,
            if_body: []const u8,
            else_body: []const u8,
        },
    },
};

fn findNextMatch(source: []const u8, start: usize) ?Match {
    var cursor = start;
    while (std.mem.findScalarPos(u8, source, cursor, '<')) |opening| {
        if (parseValueTag(source, opening)) |tag|
            return .{ .start = opening, .end = tag.end, .kind = .{ .value = tag.name } };

        if (parseOpeningTag(source, opening, '#')) |tag| {
            if (findClosingTag(source, tag.end, tag.name, false)) |closing| {
                return .{
                    .start = opening,
                    .end = closing.end,
                    .kind = .{ .list = .{
                        .name = tag.name,
                        .body = source[tag.end..closing.start],
                    } },
                };
            }
        }

        if (parseConditionTag(source, opening)) |tag| {
            if (findClosingTag(source, tag.end, tag.name, tag.nonempty)) |closing| {
                const else_tag = findElseTag(
                    source,
                    tag.end,
                    closing.start,
                    tag.name,
                    tag.nonempty,
                );
                return .{
                    .start = opening,
                    .end = closing.end,
                    .kind = .{ .condition = .{
                        .name = tag.name,
                        .nonempty = tag.nonempty,
                        .if_body = source[tag.end..if (else_tag) |tag_value| tag_value.start else closing.start],
                        .else_body = if (else_tag) |tag_value|
                            source[tag_value.end..closing.start]
                        else
                            "",
                    } },
                };
            }
        }
        cursor = opening + 1;
    }
    return null;
}

const ParsedTag = struct { name: []const u8, end: usize };

fn parseValueTag(source: []const u8, opening: usize) ?ParsedTag {
    const name_start = opening + 1;
    if (name_start >= source.len or !isParameterCharacter(source[name_start])) return null;
    var end = name_start;
    while (end < source.len and isParameterCharacter(source[end])) end += 1;
    if (end >= source.len or source[end] != '>') return null;
    return .{ .name = source[name_start..end], .end = end + 1 };
}

fn parseOpeningTag(source: []const u8, opening: usize, prefix: u8) ?ParsedTag {
    const name_start = opening + 2;
    if (opening + 1 >= source.len or source[opening + 1] != prefix or
        name_start >= source.len or !isParameterCharacter(source[name_start]))
        return null;
    var end = name_start;
    while (end < source.len and isParameterCharacter(source[end])) end += 1;
    if (end >= source.len or source[end] != '>') return null;
    return .{ .name = source[name_start..end], .end = end + 1 };
}

fn parseConditionTag(
    source: []const u8,
    opening: usize,
) ?struct { name: []const u8, nonempty: bool, end: usize } {
    if (opening + 1 >= source.len or source[opening + 1] != '?') return null;
    var name_start = opening + 2;
    const nonempty = name_start < source.len and source[name_start] == '+';
    if (nonempty) name_start += 1;
    if (name_start >= source.len or !isParameterCharacter(source[name_start])) return null;
    var end = name_start;
    while (end < source.len and isParameterCharacter(source[end])) end += 1;
    if (end >= source.len or source[end] != '>') return null;
    return .{ .name = source[name_start..end], .nonempty = nonempty, .end = end + 1 };
}

const ClosingTag = struct { start: usize, end: usize };

fn findClosingTag(
    source: []const u8,
    start: usize,
    name: []const u8,
    plus: bool,
) ?ClosingTag {
    var cursor = start;
    while (std.mem.find(u8, source[cursor..], "</")) |relative| {
        const opening = cursor + relative;
        var position = opening + 2;
        if (plus) {
            if (position >= source.len or source[position] != '+') {
                cursor = opening + 2;
                continue;
            }
            position += 1;
        } else if (position < source.len and source[position] == '+') {
            cursor = opening + 2;
            continue;
        }
        if (position + name.len < source.len and
            std.mem.eql(u8, source[position .. position + name.len], name) and
            source[position + name.len] == '>')
            return .{ .start = opening, .end = position + name.len + 1 };
        cursor = opening + 2;
    }
    return null;
}

fn findElseTag(
    source: []const u8,
    start: usize,
    limit: usize,
    name: []const u8,
    plus: bool,
) ?ClosingTag {
    var cursor = start;
    while (cursor < limit) {
        const relative = std.mem.find(u8, source[cursor..limit], "<!") orelse break;
        const opening = cursor + relative;
        var position = opening + 2;
        if (plus) {
            if (position >= limit or source[position] != '+') {
                cursor = opening + 2;
                continue;
            }
            position += 1;
        } else if (position < limit and source[position] == '+') {
            cursor = opening + 2;
            continue;
        }
        if (position + name.len < source.len and
            position + name.len < limit and
            std.mem.eql(u8, source[position .. position + name.len], name) and
            source[position + name.len] == '>')
            return .{ .start = opening, .end = position + name.len + 1 };
        cursor = opening + 2;
    }
    return null;
}

fn checkTemplateValid(template: []const u8) WhiskersError!void {
    var cursor: usize = 0;
    while (std.mem.findScalarPos(u8, template, cursor, '<')) |opening| {
        if (opening + 1 >= template.len) return;
        const prefix = template[opening + 1];
        if (prefix != '#' and prefix != '?' and prefix != '!' and prefix != '/') {
            cursor = opening + 1;
            continue;
        }
        var position = opening + 2;
        if (position < template.len and template[position] == '+') position += 1;
        const name_start = position;
        while (position < template.len and isParameterCharacter(template[position])) position += 1;
        // The upstream regex only diagnoses special tags once at least one
        // parameter character has been seen.
        if (position != name_start and (position == template.len or template[position] != '>'))
            return error.InvalidTemplate;
        cursor = opening + 1;
    }
}

fn checkParameterValid(parameter: []const u8) WhiskersError!void {
    if (parameter.len == 0) return error.InvalidParameter;
    for (parameter) |character| if (!isParameterCharacter(character))
        return error.InvalidParameter;
}

fn isParameterCharacter(character: u8) bool {
    return std.ascii.isAlphanumeric(character) or
        character == '_' or character == '$' or character == '-';
}

test "basic values and conditions render without rescanning values" {
    var whiskers = try Whiskers.init(
        std.testing.allocator,
        "a <b> <?condition><value><!condition>no</condition>",
    );
    defer whiskers.deinit();
    _ = try whiskers.setString("b", "CO<M>PL");
    _ = try whiskers.setString("value", "yes");
    _ = try whiskers.setCondition("condition", true);
    const rendered = try whiskers.renderAlloc(std.testing.allocator);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("a CO<M>PL yes", rendered);
}

test "lists merge local and upper parameters and do not rescan replacements" {
    var whiskers = try Whiskers.init(
        std.testing.allocator,
        "a<#items>(<upper>:<key>=<value>)</items><tail>",
    );
    defer whiskers.deinit();
    _ = try whiskers.setString("upper", "U");
    _ = try whiskers.setString("tail", "X");
    const first = [_]StringPair{
        .{ .name = "key", .value = "one" },
        .{ .name = "value", .value = "<tail>" },
    };
    const second = [_]StringPair{
        .{ .name = "key", .value = "two" },
        .{ .name = "value", .value = "2" },
    };
    const elements = [_][]const StringPair{ &first, &second };
    _ = try whiskers.setList("items", &elements);
    const rendered = try whiskers.renderAlloc(std.testing.allocator);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("a(U:one=<tail>)(U:two=2)X", rendered);
}

test "conditions can select lists and nonempty string branches" {
    var whiskers = try Whiskers.init(
        std.testing.allocator,
        "<?show><#items><x></items><!show>hidden</show><?+name>+<name><!+name>-</+name>",
    );
    defer whiskers.deinit();
    _ = try whiskers.setCondition("show", true);
    _ = try whiskers.setString("name", "abc");
    const element = [_]StringPair{.{ .name = "x", .value = "X" }};
    const elements = [_][]const StringPair{&element};
    _ = try whiskers.setList("items", &elements);
    const rendered = try whiskers.renderAlloc(std.testing.allocator);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("X+abc", rendered);
}

test "unmatched nonempty conditional remains literal while inner value expands" {
    var whiskers = try Whiskers.init(std.testing.allocator, "<?+b>+<b></b>");
    defer whiskers.deinit();
    _ = try whiskers.setString("b", "abc");
    const rendered = try whiskers.renderAlloc(std.testing.allocator);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("<?+b>+abc</b>", rendered);
}

test "validation and missing parameter errors match upstream boundaries" {
    try std.testing.expectError(
        error.InvalidTemplate,
        Whiskers.init(std.testing.allocator, "<?b>X<!bY</b>"),
    );
    var missing = try Whiskers.init(std.testing.allocator, "<#items><x></items>");
    defer missing.deinit();
    try std.testing.expectError(error.ListNotSet, missing.renderAlloc(std.testing.allocator));
    try std.testing.expectError(
        error.InvalidParameter,
        missing.setString("bad name", "x"),
    );
}

test "list-local parameter collisions fail during rendering" {
    var whiskers = try Whiskers.init(std.testing.allocator, "<a><#items><a></items>");
    defer whiskers.deinit();
    _ = try whiskers.setString("a", "global");
    const element = [_]StringPair{.{ .name = "a", .value = "local" }};
    const elements = [_][]const StringPair{&element};
    _ = try whiskers.setList("items", &elements);
    try std.testing.expectError(
        error.ParameterCollision,
        whiskers.renderAlloc(std.testing.allocator),
    );
}
