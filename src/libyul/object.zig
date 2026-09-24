// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned Yul code/data object tree.
//!
//! Names, data bytes, source-name mappings, ASTs, child nodes, and optional
//! analysis state are all owned by the object tree.  Hash-map keys borrow the
//! stable name allocations owned by their corresponding child nodes.

const std = @import("std");
const AST = @import("ast.zig");
const AsmAnalysisInfo = @import("asm_analysis_info.zig").AsmAnalysisInfo;
const AsmJsonConverterModule = @import("asm_json_converter.zig");
const AsmParser = @import("asm_parser.zig");
const AsmPrinter = @import("asm_printer.zig");
const CharStreamProvider = @import("../liblangutil/char_stream_provider.zig").CharStreamProvider;
const CommonData = @import("../libsolutil/common_data.zig");
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const JSON = @import("../libsolutil/json.zig");
const SubAssemblyID = @import("../libevmasm/sub_assembly_id.zig").SubAssemblyID;

pub const ObjectError = AsmPrinter.PrintError || std.mem.Allocator.Error || error{
    MissingCode,
    MissingDebugData,
    EmptyPath,
    InvalidPath,
    DataPath,
    MissingSubAssemblyId,
};

pub const ObjectJsonError = AsmJsonConverterModule.JsonError || error{MissingCode};

pub const SourceNameEntry = struct {
    index: u32,
    name: []const u8,
};

/// Owned, index-sorted counterpart of the upstream `SourceNameMap`.
pub const SourceNameMap = struct {
    entries: std.ArrayList(SourceNameEntry) = .empty,

    pub fn deinit(self: *SourceNameMap, allocator: std.mem.Allocator) void {
        for (self.entries.items) |entry| allocator.free(entry.name);
        self.entries.deinit(allocator);
        self.* = undefined;
    }

    pub fn put(
        self: *SourceNameMap,
        allocator: std.mem.Allocator,
        index: u32,
        name: []const u8,
    ) std.mem.Allocator.Error!void {
        const owned_name = try allocator.dupe(u8, name);
        errdefer allocator.free(owned_name);
        for (self.entries.items) |*entry| {
            if (entry.index != index) continue;
            allocator.free(entry.name);
            entry.name = owned_name;
            return;
        }
        try self.entries.append(allocator, .{ .index = index, .name = owned_name });
        std.sort.insertion(SourceNameEntry, self.entries.items, {}, sourceNameLessThan);
    }

    pub fn parserEntriesAlloc(
        self: *const SourceNameMap,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]AsmParser.SourceIndexName {
        const result = try allocator.alloc(AsmParser.SourceIndexName, self.entries.items.len);
        for (self.entries.items, result) |source, *target| {
            target.* = .{ .index = source.index, .name = source.name };
        }
        return result;
    }

    pub fn printerEntriesAlloc(
        self: *const SourceNameMap,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]AsmPrinter.SourceIndexName {
        const result = try allocator.alloc(AsmPrinter.SourceIndexName, self.entries.items.len);
        for (self.entries.items, result) |source, *target| {
            target.* = .{ .index = source.index, .name = source.name };
        }
        return result;
    }

    fn sourceNameLessThan(_: void, left: SourceNameEntry, right: SourceNameEntry) bool {
        return left.index < right.index;
    }
};

pub const ObjectDebugData = struct {
    source_names: ?SourceNameMap = null,

    pub fn deinit(self: *ObjectDebugData, allocator: std.mem.Allocator) void {
        if (self.source_names) |*source_names| source_names.deinit(allocator);
        self.* = undefined;
    }

    pub fn formatUseSrcCommentAlloc(
        self: *const ObjectDebugData,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        var output = std.Io.Writer.Allocating.init(allocator);
        defer output.deinit();
        self.writeUseSrcComment(&output.writer) catch return error.OutOfMemory;
        return output.toOwnedSlice();
    }

    pub fn writeUseSrcComment(self: *const ObjectDebugData, writer: anytype) !void {
        const source_names = self.source_names orelse return;
        try writer.writeAll("/// @use-src ");
        for (source_names.entries.items, 0..) |entry, index| {
            if (index != 0) try writer.writeAll(", ");
            var buffer: [10]u8 = undefined;
            const number = std.fmt.bufPrint(&buffer, "{d}", .{entry.index}) catch unreachable; // zlinter-disable-current-line no_swallow_error - 10 bytes fit every u32 source index
            try writer.writeAll(number);
            try writer.writeByte(':');
            try CommonData.writeEscapedQuoted(writer, entry.name);
        }
        try writer.writeByte('\n');
    }
};

pub const Data = struct {
    name: []const u8,
    data: []const u8,

    pub fn init(
        allocator: std.mem.Allocator,
        name: []const u8,
        data: []const u8,
    ) std.mem.Allocator.Error!Data {
        const owned_name = try allocator.dupe(u8, name);
        errdefer allocator.free(owned_name);
        return .{
            .name = owned_name,
            .data = try allocator.dupe(u8, data),
        };
    }

    pub fn initOwned(name: []const u8, data: []const u8) Data {
        return .{ .name = name, .data = data };
    }

    pub fn deinit(self: *Data, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
        allocator.free(self.data);
        self.* = undefined;
    }

    pub fn toStringAlloc(self: *const Data, allocator: std.mem.Allocator) std.mem.Allocator.Error![]u8 {
        var output = std.Io.Writer.Allocating.init(allocator);
        defer output.deinit();
        self.writeTo(&output.writer) catch return error.OutOfMemory;
        return output.toOwnedSlice();
    }

    pub fn writeTo(self: *const Data, writer: anytype) !void {
        try writer.writeAll("data ");
        try CommonData.writeEscapedQuoted(writer, self.name);
        try writer.writeAll(" hex\"");
        for (self.data) |byte| {
            const encoded = std.fmt.bytesToHex([_]u8{byte}, .lower);
            try writer.writeAll(&encoded);
        }
        try writer.writeByte('"');
    }
};

pub const ObjectNode = union(enum) {
    object: *Object,
    data: Data,

    pub fn name(self: *const ObjectNode) []const u8 {
        return switch (self.*) {
            .object => |object| object.name,
            .data => |*data| data.name,
        };
    }

    pub fn deinit(self: *ObjectNode, allocator: std.mem.Allocator) void {
        switch (self.*) {
            .object => |object| object.destroy(),
            .data => |*data| data.deinit(allocator),
        }
        self.* = undefined;
    }

    pub fn toStringAlloc(
        self: *const ObjectNode,
        allocator: std.mem.Allocator,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
    ) ObjectError![]u8 {
        return switch (self.*) {
            .object => |object| object.formatAlloc(allocator, debug_info_selection, solidity_source_provider),
            .data => |*data| data.toStringAlloc(allocator),
        };
    }
};

pub const StringSet = struct {
    values: std.ArrayList([]const u8) = .empty,

    pub fn deinit(self: *StringSet, allocator: std.mem.Allocator) void {
        for (self.values.items) |value| allocator.free(value);
        self.values.deinit(allocator);
        self.* = undefined;
    }

    pub fn contains(self: *const StringSet, value: []const u8) bool {
        for (self.values.items) |candidate| {
            if (std.mem.eql(u8, candidate, value)) return true;
        }
        return false;
    }

    pub fn put(
        self: *StringSet,
        allocator: std.mem.Allocator,
        value: []const u8,
    ) std.mem.Allocator.Error!void {
        if (self.contains(value)) return;
        const owned_value = try allocator.dupe(u8, value);
        errdefer allocator.free(owned_value);
        try self.values.append(allocator, owned_value);
        std.sort.insertion([]const u8, self.values.items, {}, stringLessThan);
    }

    fn stringLessThan(_: void, left: []const u8, right: []const u8) bool {
        return std.mem.order(u8, left, right) == .lt;
    }
};

pub const Structure = struct {
    allocator: std.mem.Allocator,
    object_name: []const u8,
    object_paths: StringSet = .{},
    data_paths: StringSet = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        object_name: []const u8,
    ) std.mem.Allocator.Error!Structure {
        return .{
            .allocator = allocator,
            .object_name = try allocator.dupe(u8, object_name),
        };
    }

    pub fn deinit(self: *Structure) void {
        self.object_paths.deinit(self.allocator);
        self.data_paths.deinit(self.allocator);
        self.allocator.free(self.object_name);
        self.* = undefined;
    }

    pub fn contains(self: *const Structure, path: []const u8) bool {
        return self.containsObject(path) or self.containsData(path);
    }

    pub fn containsObject(self: *const Structure, path: []const u8) bool {
        return self.object_paths.contains(path);
    }

    pub fn containsData(self: *const Structure, path: []const u8) bool {
        return self.data_paths.contains(path);
    }

    pub fn topLevelSubObjectNames(
        self: *const Structure,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error!StringSet {
        var result: StringSet = .{};
        errdefer result.deinit(allocator);
        for (self.object_paths.values.items) |path| {
            if (std.mem.findScalar(u8, path, '.') == null and
                !std.mem.eql(u8, path, self.object_name))
            {
                try result.put(allocator, path);
            }
        }
        return result;
    }
};

pub const Object = struct {
    allocator: std.mem.Allocator,
    name: []const u8,
    code_value: ?AST.AST = null,
    sub_id: SubAssemblyID = .{},
    sub_objects: std.ArrayList(ObjectNode) = .empty,
    sub_index_by_name: std.StringHashMap(usize),
    analysis_info: ?AsmAnalysisInfo = null,
    debug_data: ?ObjectDebugData = null,

    pub fn create(
        allocator: std.mem.Allocator,
        name: []const u8,
    ) std.mem.Allocator.Error!*Object {
        const object = try allocator.create(Object);
        errdefer allocator.destroy(object);
        object.* = .{
            .allocator = allocator,
            .name = try allocator.dupe(u8, name),
            .sub_index_by_name = std.StringHashMap(usize).init(allocator),
        };
        return object;
    }

    pub fn destroy(self: *Object) void {
        const allocator = self.allocator;
        self.deinit();
        allocator.destroy(self);
    }

    pub fn deinit(self: *Object) void {
        // Scopes borrow AST nodes, and AST debug locations borrow source names.
        if (self.analysis_info) |*info| info.deinit();
        if (self.code_value) |*ast_value| ast_value.deinit();
        self.sub_index_by_name.deinit();
        for (self.sub_objects.items) |*node| node.deinit(self.allocator);
        self.sub_objects.deinit(self.allocator);
        if (self.debug_data) |*debug_data| debug_data.deinit(self.allocator);
        self.allocator.free(self.name);
        self.* = undefined;
    }

    pub fn code(self: *const Object) ?*const AST.AST {
        return if (self.code_value != null) &self.code_value.? else null;
    }

    pub fn codeMut(self: *Object) ?*AST.AST {
        return if (self.code_value != null) &self.code_value.? else null;
    }

    /// Transfers the mutable root without copying nodes or their storage.
    /// Discard address-based analysis before moving the root. Keep an empty AST
    /// shell so object/dialect queries still work during the consuming pass.
    /// The caller owns the returned block with this allocator; debug source
    /// names continue to borrow this object and must not outlive it.
    pub fn takeCodeRoot(self: *Object) !AST.Block {
        const ast = self.codeMut() orelse return error.MissingObjectCode;
        if (self.analysis_info) |*info| info.deinit();
        self.analysis_info = null;
        const result = ast.root_block;
        ast.root_block = .{};
        return result;
    }

    pub fn setCode(self: *Object, code_value: AST.AST, analysis_info: ?AsmAnalysisInfo) void {
        std.debug.assert(self.code_value == null);
        std.debug.assert(self.analysis_info == null);
        self.code_value = code_value;
        self.analysis_info = analysis_info;
    }

    /// Replaces the currently owned code and its AST-borrowing analysis state.
    /// This is the ownership-explicit counterpart of assigning the upstream
    /// shared pointers during optimizer orchestration.
    pub fn replaceCode(self: *Object, code_value: AST.AST, analysis_info: ?AsmAnalysisInfo) void {
        if (self.analysis_info) |*info| info.deinit();
        self.analysis_info = null;
        if (self.code_value) |*ast_value| ast_value.deinit();
        self.code_value = code_value;
        self.analysis_info = analysis_info;
    }

    pub fn hasCode(self: *const Object) bool {
        return self.code_value != null;
    }

    pub fn dialect(self: *const Object) ?*const AST.Dialect {
        const code_value = self.code() orelse return null;
        return code_value.dialect();
    }

    pub fn addSubObject(self: *Object, node: ObjectNode) std.mem.Allocator.Error!void {
        const child_name = node.name();
        try self.sub_objects.append(self.allocator, node);
        errdefer _ = self.sub_objects.pop();
        const map_entry = try self.sub_index_by_name.getOrPut(child_name);
        if (!map_entry.found_existing) map_entry.value_ptr.* = self.sub_objects.items.len;
        if (!map_entry.found_existing) map_entry.value_ptr.* -= 1;
    }

    pub fn toStringAlloc(
        self: *const Object,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
    ) ObjectError![]u8 {
        return self.formatAlloc(self.allocator, debug_info_selection, solidity_source_provider);
    }

    /// Render into caller-owned output storage, including borrowed children.
    pub fn formatAlloc(
        self: *const Object,
        allocator: std.mem.Allocator,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
    ) ObjectError![]u8 {
        var bytes = std.Io.Writer.Allocating.init(allocator);
        defer bytes.deinit();
        self.writeTo(&bytes.writer, debug_info_selection, solidity_source_provider) catch |err| switch (err) {
            error.WriteFailed => return error.OutOfMemory,
            else => |remaining| return remaining,
        };
        return bytes.toOwnedSlice();
    }

    /// Writes borrowed object/source data without retaining it or allocating
    /// renderer storage. The caller owns the writer and its output storage.
    /// Input owners must remain alive and unchanged until this call returns.
    pub fn writeTo(
        self: *const Object,
        writer: *std.Io.Writer,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
    ) (ObjectError || std.Io.Writer.Error)!void {
        const Stream = @import("asm_stream.zig");
        var output: Stream.Output = .{ .writer = writer };
        var renderer: Stream.Renderer = .{
            .output = &output,
            .dialect = .{},
            .selection = debug_info_selection,
            .provider = solidity_source_provider,
        };
        renderer.object(self) catch |err| switch (err) {
            error.LayoutLimit => unreachable, // No limit on the output adapter.
            else => |remaining| return remaining,
        };
    }

    /// Returns final IR owned by output_allocator, including its optional
    /// ethdebug header and trailing newline. No scratch or object data escapes.
    pub fn formatIRAlloc(
        self: *const Object,
        output_allocator: std.mem.Allocator,
        selection: DebugInfoSelection,
        source_provider: ?CharStreamProvider,
    ) ObjectError![]u8 {
        var bytes = std.Io.Writer.Allocating.init(output_allocator);
        defer bytes.deinit();
        if (selection.ethdebug)
            bytes.writer.writeAll("/// ethdebug: enabled\n") catch return error.OutOfMemory;
        self.writeTo(&bytes.writer, selection, source_provider) catch |err| switch (err) {
            error.WriteFailed => return error.OutOfMemory,
            else => |remaining| return remaining,
        };
        bytes.writer.writeByte('\n') catch return error.OutOfMemory;
        return bytes.toOwnedSlice();
    }

    pub fn toJsonAlloc(
        self: *const Object,
        backing_allocator: std.mem.Allocator,
    ) ObjectJsonError!AsmJsonConverterModule.OwnedYulJson {
        var result = try AsmJsonConverterModule.OwnedYulJson.init(backing_allocator);
        errdefer result.deinit();
        result.value = try self.toJsonValue(result.allocator());
        return result;
    }

    fn toJsonValue(
        self: *const Object,
        allocator: std.mem.Allocator,
    ) ObjectJsonError!JSON.Json {
        const code_value = self.code() orelse return error.MissingCode;
        var code_json: JSON.Json = .{ .object = .empty };
        try code_json.object.put(
            allocator,
            "nodeType",
            .{ .string = try allocator.dupe(u8, "YulCode") },
        );
        var converter = AsmJsonConverterModule.AsmJsonConverter.init(
            allocator,
            code_value.dialect().*,
            0,
        );
        try code_json.object.put(allocator, "block", try converter.convertBlock(code_value.root()));

        var sub_objects = std.json.Array.init(allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (self.sub_objects.items) |*node| {
            try sub_objects.append(switch (node.*) {
                .object => |child| try child.toJsonValue(allocator),
                .data => |*data| try dataToJsonValue(allocator, data),
            });
        }

        var result: JSON.Json = .{ .object = .empty };
        try result.object.put(
            allocator,
            "nodeType",
            .{ .string = try allocator.dupe(u8, "YulObject") },
        );
        try result.object.put(
            allocator,
            "name",
            .{ .string = try allocator.dupe(u8, self.name) },
        );
        try result.object.put(allocator, "code", code_json);
        try result.object.put(allocator, "subObjects", .{ .array = sub_objects });
        return result;
    }

    pub fn summarizeStructure(self: *const Object) std.mem.Allocator.Error!Structure {
        var structure = try Structure.init(self.allocator, self.name);
        errdefer structure.deinit();
        if (self.name.len != 0 and std.mem.findScalar(u8, self.name, '.') == null) {
            try structure.object_paths.put(self.allocator, self.name);
        }
        for (self.sub_objects.items) |*node| {
            const child_name = node.name();
            std.debug.assert(!structure.contains(child_name));
            if (std.mem.findScalar(u8, child_name, '.') != null) continue;
            switch (node.*) {
                .object => |child| {
                    try structure.object_paths.put(self.allocator, child_name);
                    var child_structure = try child.summarizeStructure();
                    defer child_structure.deinit();
                    for (child_structure.object_paths.values.items) |path| {
                        if (std.mem.eql(u8, child.name, path)) continue;
                        const qualified = try std.fmt.allocPrint(self.allocator, "{s}.{s}", .{ child.name, path });
                        defer self.allocator.free(qualified);
                        std.debug.assert(!structure.contains(qualified));
                        try structure.object_paths.put(self.allocator, qualified);
                    }
                    for (child_structure.data_paths.values.items) |path| {
                        if (std.mem.eql(u8, child.name, path)) continue;
                        const qualified = try std.fmt.allocPrint(self.allocator, "{s}.{s}", .{ child.name, path });
                        defer self.allocator.free(qualified);
                        std.debug.assert(!structure.contains(qualified));
                        try structure.data_paths.put(self.allocator, qualified);
                    }
                },
                .data => try structure.data_paths.put(self.allocator, child_name),
            }
        }
        std.debug.assert(!structure.contains(""));
        return structure;
    }

    pub fn pathToSubObject(
        self: *const Object,
        qualified_name_input: []const u8,
    ) ObjectError![]SubAssemblyID {
        if (std.mem.eql(u8, qualified_name_input, self.name)) return error.EmptyPath;
        std.debug.assert(!self.sub_index_by_name.contains(self.name));
        var qualified_name = qualified_name_input;
        if (self.name.len != 0 and
            std.mem.startsWith(u8, qualified_name, self.name) and
            qualified_name.len > self.name.len and
            qualified_name[self.name.len] == '.')
        {
            qualified_name = qualified_name[self.name.len + 1 ..];
        }
        if (qualified_name.len == 0) return error.EmptyPath;

        var path: std.ArrayList(SubAssemblyID) = .empty;
        errdefer path.deinit(self.allocator);
        var object = self;
        var components = std.mem.splitScalar(u8, qualified_name, '.');
        while (components.next()) |component| {
            if (component.len == 0) return error.InvalidPath;
            const child_index = object.sub_index_by_name.get(component) orelse return error.InvalidPath;
            const child = switch (object.sub_objects.items[child_index]) {
                .object => |child_object| child_object,
                .data => return error.DataPath,
            };
            if (child.sub_id.empty()) return error.MissingSubAssemblyId;
            try path.append(self.allocator, child.sub_id);
            object = child;
        }
        return path.toOwnedSlice(self.allocator);
    }

    pub fn collectSourceIndices(
        self: *const Object,
        indices: *std.StringHashMap(u32),
    ) std.mem.Allocator.Error!void {
        if (self.debug_data) |debug_data| {
            if (debug_data.source_names) |source_names| {
                for (source_names.entries.items) |entry| {
                    const result = try indices.getOrPut(entry.name);
                    if (result.found_existing) {
                        std.debug.assert(result.value_ptr.* == entry.index);
                    } else {
                        result.value_ptr.* = entry.index;
                    }
                }
            }
        }
        for (self.sub_objects.items) |node| switch (node) {
            .object => |child| try child.collectSourceIndices(indices),
            .data => {},
        };
    }

    pub fn hasContiguousSourceIndices(self: *const Object) std.mem.Allocator.Error!bool {
        var source_indices = std.StringHashMap(u32).init(self.allocator);
        defer source_indices.deinit();
        try self.collectSourceIndices(&source_indices);
        if (source_indices.count() == 0) return true;
        var maximum: u32 = 0;
        var distinct = std.AutoHashMap(u32, void).init(self.allocator);
        defer distinct.deinit();
        var values = source_indices.valueIterator();
        while (values.next()) |source_index| {
            maximum = @max(maximum, source_index.*);
            try distinct.put(source_index.*, {});
        }
        return distinct.count() == @as(usize, maximum) + 1;
    }

    pub fn metadataName() []const u8 {
        return ".metadata";
    }
};

fn dataToJsonValue(
    allocator: std.mem.Allocator,
    data: *const Data,
) ObjectJsonError!JSON.Json {
    var result: JSON.Json = .{ .object = .empty };
    try result.object.put(
        allocator,
        "nodeType",
        .{ .string = try allocator.dupe(u8, "YulData") },
    );
    const value = try CommonData.toHexAlloc(allocator, data.data, .dont_add, .lower);
    try result.object.put(allocator, "value", .{ .string = value });
    return result;
}

test "object code transfer invalidates analysis and preserves storage and dialect" {
    const allocator = std.testing.allocator;
    const object = try Object.create(allocator, "Root");
    defer object.destroy();
    try std.testing.expectError(error.MissingObjectCode, object.takeCodeRoot());
    var root: AST.Block = .{};
    try root.statements.append(allocator, .{ .leave_statement = .{} });
    object.setCode(AST.AST.init(allocator, .{}, root), AsmAnalysisInfo.init(allocator));
    _ = try object.analysis_info.?.getOrCreateScope(object.code().?.root());
    const dialect = object.dialect().?;
    var moved = try object.takeCodeRoot();
    defer moved.deinit(allocator);
    try std.testing.expectEqual(root.statements.items.ptr, moved.statements.items.ptr);
    try std.testing.expect(object.analysis_info == null);
    try std.testing.expectEqual(@as(usize, 0), object.code().?.root().statements.items.len);
    try std.testing.expectEqual(dialect, object.dialect().?);
}

test "object structure and subassembly paths preserve object/data distinctions" {
    const allocator = std.testing.allocator;
    const root = try Object.create(allocator, "A");
    defer root.destroy();
    const child = try Object.create(allocator, "B");
    child.sub_id = SubAssemblyID.init(7);
    const grandchild = try Object.create(allocator, "C");
    grandchild.sub_id = SubAssemblyID.init(9);
    try child.addSubObject(.{ .object = grandchild });
    try child.addSubObject(.{ .data = try Data.init(allocator, "blob", "abc") });
    try root.addSubObject(.{ .object = child });

    var structure = try root.summarizeStructure();
    defer structure.deinit();
    try std.testing.expect(structure.containsObject("A"));
    try std.testing.expect(structure.containsObject("B.C"));
    try std.testing.expect(structure.containsData("B.blob"));
    const path = try root.pathToSubObject("A.B.C");
    defer allocator.free(path);
    try std.testing.expectEqualSlices(SubAssemblyID, &.{
        SubAssemblyID.init(7),
        SubAssemblyID.init(9),
    }, path);
}

test "source-name maps replace duplicate indices and serialize in index order" {
    const allocator = std.testing.allocator;
    var map: SourceNameMap = .{};
    try map.put(allocator, 2, "two.sol");
    try map.put(allocator, 0, "old.sol");
    try map.put(allocator, 0, "zero.sol");
    var debug_data: ObjectDebugData = .{ .source_names = map };
    map = undefined;
    defer debug_data.deinit(allocator);
    const rendered = try debug_data.formatUseSrcCommentAlloc(allocator);
    defer allocator.free(rendered);
    try std.testing.expectEqualStrings(
        "/// @use-src 0:\"zero.sol\", 2:\"two.sol\"\n",
        rendered,
    );
}
