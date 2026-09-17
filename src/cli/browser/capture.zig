// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! One compilation's exact source callback bytes. The wrapped loader retains
//! the CLI's existing filesystem capabilities; this layer never opens paths.
const std = @import("std");
const solidity = @import("solidity");
const Source = @import("store.zig").Source;
const digest = @import("store.zig").digest;

pub const Capture = struct {
    allocator: std.mem.Allocator,
    loader: solidity.standard_json.SourceLoader,
    sources: std.array_hash_map.String(solidity.standard_json.SourceReadResult) = .empty,
    total_bytes: usize = 0,

    pub fn deinit(self: *Capture) void {
        for (self.sources.keys(), self.sources.values()) |name, content| {
            self.allocator.free(name);
            content.deinit(self.allocator);
        }
        self.sources.deinit(self.allocator);
    }

    pub fn interface(self: *Capture) solidity.standard_json.SourceLoader {
        return .{ .context = self, .read_fn = read };
    }

    pub fn listAlloc(self: *const Capture, allocator: std.mem.Allocator) ![]Source {
        var count: usize = 0;
        for (self.sources.values()) |value| if (value == .contents) {
            count += 1;
        };
        const result = try allocator.alloc(Source, count);
        var index: usize = 0;
        for (self.sources.keys(), self.sources.values()) |name, value| {
            if (value != .contents) continue;
            result[index] = .{ .name = name, .content = value.contents };
            index += 1;
        }
        return result;
    }

    /// Probe exactly the previous callback read set, including missing imports.
    /// The caller resets the loader's per-compilation byte budget first.
    pub fn changed(self: *const Capture, allocator: std.mem.Allocator) !bool {
        for (self.sources.keys(), self.sources.values()) |name, previous| {
            const current = try self.loader.read(allocator, "source", name);
            defer current.deinit(allocator);
            if (!equal(previous, current)) return true;
        }
        return false;
    }

    pub fn includes(self: *const Capture, other: *const Capture) bool {
        for (other.sources.keys(), other.sources.values()) |name, value| {
            if (!equal(value, self.sources.get(name) orelse return false)) return false;
        }
        return true;
    }

    const Entry = struct {
        name: []const u8,
        kind: std.meta.Tag(solidity.standard_json.SourceReadResult),
        sha256: []const u8,

        pub fn jsonParse(allocator: std.mem.Allocator, source: anytype, options: std.json.ParseOptions) std.json.ParseError(@TypeOf(source.*))!Entry {
            // Inspect JSON value kinds before conversion: typed decoding also
            // accepts numeric enum tags and arrays for byte slices. All values
            // below share the parsed document's arena lifetime.
            const value = try std.json.Value.jsonParse(allocator, source, options);
            if (value != .object or value.object.count() != 3) return error.UnexpectedToken;
            const name = value.object.get("name") orelse return error.MissingField;
            const kind = value.object.get("kind") orelse return error.MissingField;
            const sha256 = value.object.get("sha256") orelse return error.MissingField;
            if (name != .string or kind != .string or sha256 != .string) return error.UnexpectedToken;
            return .{
                .name = name.string,
                .kind = std.meta.stringToEnum(std.meta.Tag(solidity.standard_json.SourceReadResult), kind.string) orelse return error.InvalidEnumTag,
                .sha256 = sha256.string,
            };
        }
    };

    pub fn manifestAlloc(self: *const Capture, allocator: std.mem.Allocator) ![]u8 {
        var arena = std.heap.ArenaAllocator.init(allocator);
        defer arena.deinit();
        const entries = try arena.allocator().alloc(Entry, self.sources.count());
        for (self.sources.keys(), self.sources.values(), entries) |name, value, *entry| {
            const hash = digest(valueBytes(value));
            entry.* = .{ .name = name, .kind = std.meta.activeTag(value), .sha256 = try arena.allocator().dupe(u8, &hash) };
        }
        std.mem.sort(Entry, entries, {}, struct {
            fn less(_: void, a: Entry, b: Entry) bool {
                return std.mem.lessThan(u8, a.name, b.name);
            }
        }.less);
        return std.json.Stringify.valueAlloc(allocator, entries, .{});
    }

    /// Authenticate the manifest before calling this. A fresh candidate owns
    /// all replayed bytes; discard it on any mismatch, never merge a partial
    /// historical read set into a new compilation's capture.
    pub fn restore(self: *Capture, allocator: std.mem.Allocator, manifest: []const u8) !bool {
        std.debug.assert(self.sources.count() == 0);
        const parsed = std.json.parseFromSlice([]Entry, allocator, manifest, .{ .max_value_len = @import("store.zig").max_manifest_bytes }) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return false,
        };
        defer parsed.deinit();
        if (parsed.value.len > 8192) return false;
        var previous: ?[]const u8 = null;
        for (parsed.value) |entry| {
            if (previous) |name| if (!std.mem.lessThan(u8, name, entry.name)) return false;
            previous = entry.name;
            const value = try self.interface().read(allocator, "source", entry.name);
            defer value.deinit(allocator);
            const hash = digest(valueBytes(value));
            if (entry.kind != std.meta.activeTag(value) or !std.mem.eql(u8, entry.sha256, &hash)) return false;
        }
        return true;
    }

    fn valueBytes(value: solidity.standard_json.SourceReadResult) []const u8 {
        return switch (value) {
            .contents => |content| content,
            .failure => |failure| failure,
            .unsupported => "",
        };
    }

    fn equal(a: solidity.standard_json.SourceReadResult, b: solidity.standard_json.SourceReadResult) bool {
        if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
        return switch (a) {
            .contents => |bytes| std.mem.eql(u8, bytes, b.contents),
            .failure => |bytes| std.mem.eql(u8, bytes, b.failure),
            .unsupported => true,
        };
    }

    fn read(context: ?*anyopaque, allocator: std.mem.Allocator, kind: []const u8, path: []const u8) solidity.standard_json.SourceReadError!solidity.standard_json.SourceReadResult {
        const self: *Capture = @ptrCast(@alignCast(context.?));
        const result = try self.loader.read(allocator, kind, path);
        errdefer result.deinit(allocator);
        if (std.mem.eql(u8, kind, "source")) {
            // Repeated reads must describe the same snapshot, including if a
            // file changes while the compilation is resolving its imports.
            if (self.sources.get(path)) |previous| {
                if (!equal(previous, result)) return error.InternalFailure;
            } else {
                const content_bytes = valueBytes(result);
                if (self.sources.count() >= 8192 or content_bytes.len > 64 * 1024 * 1024 -| self.total_bytes) return error.InternalFailure;
                const name = try self.allocator.dupe(u8, path);
                errdefer self.allocator.free(name);
                const content: solidity.standard_json.SourceReadResult = switch (result) {
                    .contents => .{ .contents = try self.allocator.dupe(u8, content_bytes) },
                    .failure => .{ .failure = try self.allocator.dupe(u8, content_bytes) },
                    .unsupported => .unsupported,
                };
                errdefer content.deinit(self.allocator);
                try self.sources.put(self.allocator, name, content);
                self.total_bytes += content_bytes.len;
            }
        }
        return result;
    }
};

test "browser source capture owns callback bytes and rejects inconsistent rereads" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        fn run(allocator: std.mem.Allocator) !void {
            var fixture: Fixture = .{};
            var capture: Capture = .{ .allocator = allocator, .loader = .{ .context = &fixture, .read_fn = Fixture.read } };
            defer capture.deinit();
            const result = try capture.interface().read(allocator, "source", "lib/C.sol");
            result.deinit(allocator);
            const repeated = try capture.interface().read(allocator, "source", "lib/C.sol");
            repeated.deinit(allocator);
            const sources = try capture.listAlloc(allocator);
            defer allocator.free(sources);
            try std.testing.expectEqual(@as(usize, 1), sources.len);
            try std.testing.expectEqualStrings("contract C {}", sources[0].content);
            fixture.changed = true;
            // Propagate OOM from the delegated read so allocation-failure
            // testing can also exercise cleanup before consistency validation.
            const unexpected = capture.interface().read(allocator, "source", "lib/C.sol") catch |err| switch (err) {
                error.InternalFailure => return,
                else => return err,
            };
            unexpected.deinit(allocator);
            return error.ExpectedInconsistentRead;
        }
        const Fixture = struct {
            changed: bool = false,
            fn read(context: ?*anyopaque, allocator: std.mem.Allocator, _: []const u8, _: []const u8) solidity.standard_json.SourceReadError!solidity.standard_json.SourceReadResult {
                const self: *Fixture = @ptrCast(@alignCast(context.?));
                return .{ .contents = try allocator.dupe(u8, if (self.changed) "contract D {}" else "contract C {}") };
            }
        };
    }.run, .{});
}

test "read-set manifests replay failures and unsupported reads with owned bytes" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        const Fixture = struct {
            installed: bool = false,
            fn read(context: ?*anyopaque, allocator: std.mem.Allocator, _: []const u8, path: []const u8) solidity.standard_json.SourceReadError!solidity.standard_json.SourceReadResult {
                const self: *@This() = @ptrCast(@alignCast(context.?));
                if (std.mem.eql(u8, path, "unsupported")) return .unsupported;
                if (std.mem.eql(u8, path, "missing") and !self.installed) return .{ .failure = try allocator.dupe(u8, "File not found") };
                return .{ .contents = try allocator.dupe(u8, "contract C {}") };
            }
        };
        fn run(allocator: std.mem.Allocator) !void {
            var fixture: Fixture = .{};
            const loader: solidity.standard_json.SourceLoader = .{ .context = &fixture, .read_fn = Fixture.read };
            var captured: Capture = .{ .allocator = allocator, .loader = loader };
            defer captured.deinit();
            for ([_][]const u8{ "unsupported", "missing", "C.sol" }) |path| {
                const value = try captured.interface().read(allocator, "source", path);
                value.deinit(allocator);
            }
            const manifest = try captured.manifestAlloc(allocator);
            defer allocator.free(manifest);
            var restored: Capture = .{ .allocator = allocator, .loader = loader };
            defer restored.deinit();
            try std.testing.expect(try restored.restore(allocator, manifest));
            try std.testing.expect(restored.includes(&captured));
            const canonical = try restored.manifestAlloc(allocator);
            defer allocator.free(canonical);
            try std.testing.expectEqualStrings(manifest, canonical);
            fixture.installed = true;
            try std.testing.expect(try restored.changed(allocator));
            var mismatch: Capture = .{ .allocator = allocator, .loader = loader };
            defer mismatch.deinit();
            try std.testing.expect(!try mismatch.restore(allocator, manifest));
            var invalid: Capture = .{ .allocator = allocator, .loader = loader };
            defer invalid.deinit();
            try std.testing.expect(!try invalid.restore(allocator, "[{\"name\":\"C.sol\"}]"));
        }
    }.run, .{});
}

test "read-set manifests reject coerced fields and malformed entries before replay" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const hash = digest("contract C {}");
    const hash_string = try std.json.Stringify.valueAlloc(allocator, &hash, .{});
    const hash_array = try std.json.Stringify.valueAlloc(allocator, &hash, .{ .emit_strings_as_arrays = true });
    const valid = try std.fmt.allocPrint(allocator, "{{\"name\":\"C.sol\",\"kind\":\"contents\",\"sha256\":{s}}}", .{hash_string});
    const Field = struct { name: []const u8 = "\"C.sol\"", kind: []const u8 = "\"contents\"", sha256: []const u8 };
    const fields = [_]Field{
        .{ .kind = "0", .sha256 = hash_string },
        .{ .kind = "\"0\"", .sha256 = hash_string },
        .{ .kind = "\"unknown\"", .sha256 = hash_string },
        .{ .name = "[67,46,115,111,108]", .sha256 = hash_string },
        .{ .sha256 = hash_array },
        .{ .name = "null", .sha256 = hash_string },
        .{ .kind = "false", .sha256 = hash_string },
        .{ .sha256 = "42" },
    };
    for (fields) |field| {
        const entry = try std.fmt.allocPrint(allocator, "{{\"name\":{s},\"kind\":{s},\"sha256\":{s}}}", .{ field.name, field.kind, field.sha256 });
        try expectRejectedManifest(try std.fmt.allocPrint(allocator, "[{s}]", .{entry}));
        // A later malformed entry must fail decoding before any earlier entry
        // invokes the source callback.
        try expectRejectedManifest(try std.fmt.allocPrint(allocator, "[{s},{s}]", .{ valid, entry }));
    }
    for ([_][]const u8{
        "null",
        "{}",
        "[null]",
        "[{}]",
        "[{\"name\":\"C.sol\",\"kind\":\"contents\"}]",
        "[{\"name\":\"C.sol\",\"kind\":\"contents\",\"sha256\":\"x\",\"extra\":true}]",
        "[{\"name\":\"C.sol\",\"kind\":\"contents\",\"sha256\":\"x\",\"name\":\"C.sol\"}]",
        "[] []",
    }) |manifest| try expectRejectedManifest(manifest);
}

fn expectRejectedManifest(manifest: []const u8) !void {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        const Fixture = struct {
            reads: usize = 0,

            fn read(context: ?*anyopaque, allocator: std.mem.Allocator, _: []const u8, _: []const u8) solidity.standard_json.SourceReadError!solidity.standard_json.SourceReadResult {
                const self: *@This() = @ptrCast(@alignCast(context.?));
                self.reads += 1;
                return .{ .contents = try allocator.dupe(u8, "contract C {}") };
            }
        };

        fn run(allocator: std.mem.Allocator, input: []const u8) !void {
            var fixture: Fixture = .{};
            var capture: Capture = .{ .allocator = allocator, .loader = .{ .context = &fixture, .read_fn = Fixture.read } };
            defer capture.deinit();
            try std.testing.expect(!try capture.restore(allocator, input));
            try std.testing.expectEqual(@as(usize, 0), fixture.reads);
            try std.testing.expectEqual(@as(usize, 0), capture.sources.count());
        }
    }.run, .{manifest});
}
