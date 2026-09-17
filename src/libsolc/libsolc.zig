// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Standard JSON envelope dispatcher and libsolc-compatible C ABI.
//!
//! This slice parses the request, owns source-callback results, and dispatches
//! Yul to the StandardCompiler path. Solidity requests also enter
//! that path so the via-IR-only EVM policy is enforced before the remaining
//! frontend stages.

const std = @import("std");
const build_options = @import("build_options");
const common = @import("common");
const adapter = @import("yyjson_adapter_c");
const JSON = @import("../libsolutil/json.zig");
const Profiler = @import("../libsolutil/profiler.zig").Profiler;
const StandardCompiler = @import("../libsolidity/interface/standard_compiler.zig");
const ReadFile = @import("../libsolidity/interface/read_file.zig");
const Version = @import("../libsolidity/interface/version.zig");
const ObjectOptimizer = @import("../libyul/object_optimizer.zig").ObjectOptimizer;
const BackendArtifactCache = @import("../incremental/backend_artifact_cache.zig").BackendArtifactCache;
const CompilerSession = @import("../incremental/compiler_session.zig").CompilerSession;
const FrontendRevisionState = @import("../incremental/frontend_revision_state.zig").FrontendRevisionState;
const ArtifactKey = @import("../incremental/phase_key.zig").ArtifactKey;
const YulString = @import("../libyul/yul_string.zig");

pub const max_standard_json_source_entries: usize =
    @intCast(adapter.SOLIDITY_JSON_MAX_SOURCE_ENTRIES);

pub const responses = struct {
    pub const no_input_sources =
        \\{"errors":[{"component":"general","formattedMessage":"No input sources specified.","message":"No input sources specified.","severity":"error","type":"JSONError"}]}
    ++ "\n";
    pub const invalid_json =
        \\{"errors":[{"component":"general","formattedMessage":"Invalid Standard JSON input.","message":"Invalid Standard JSON input.","severity":"error","type":"JSONError"}]}
    ++ "\n";
    pub const invalid_envelope =
        \\{"errors":[{"component":"general","formattedMessage":"Invalid Standard JSON envelope.","message":"Invalid Standard JSON envelope.","severity":"error","type":"JSONError"}]}
    ++ "\n";
    pub const source_callback_failed =
        \\{"errors":[{"component":"general","formattedMessage":"Source callback failed.","message":"Source callback failed.","severity":"error","type":"IOError"}]}
    ++ "\n";
    pub const source_callback_unsupported =
        \\{"errors":[{"component":"general","formattedMessage":"Source callback is not available in this request.","message":"Source callback is not available in this request.","severity":"error","type":"IOError"}]}
    ++ "\n";
};

/// C callback shape retained for consumers of `libsolc.h`.
pub const CStyleReadFileCallback = *const fn (
    context: ?*anyopaque,
    kind: [*:0]const u8,
    data: [*:0]const u8,
    contents: *?[*:0]u8,
    error_message: *?[*:0]u8,
) callconv(.c) void;

const AbiAllocation = struct {
    bytes: []u8,
    usable_len: usize,
};

const abi_allocator = std.heap.c_allocator;
var abi_allocations: std.ArrayList(AbiAllocation) = .empty;
var abi_allocations_mutex: std.Io.Mutex = .init;
var abi_live_session_count: usize = 0;
var abi_sessions_mutex: std.Io.Mutex = .init;
const license_text_z = blk: {
    @setEvalBranchQuota(1_000_000);
    break :blk std.fmt.comptimePrint(
        "{s}\n{s}\x00",
        .{ build_options.third_party_licenses, build_options.license_text },
    );
};

/// Borrowed static dependency notices and GPLv3 license text.
pub export fn solidity_license() callconv(.c) [*:0]const u8 {
    return license_text_z.ptr;
}

/// Borrowed static compiler version.
pub export fn solidity_version() callconv(.c) [*:0]const u8 {
    return Version.VersionString.ptr;
}

/// Allocates callback storage tracked by the process-wide C ABI registry.
pub export fn solidity_alloc(size: usize) callconv(.c) ?[*:0]u8 {
    const storage_len = @max(size, 1);
    const bytes = abi_allocator.alloc(u8, storage_len) catch return null; // zlinter-disable-current-line no_hidden_allocations - C ABI allocations use the process-wide registry allocator
    @memset(bytes, 0);
    if (!registerAbiAllocation(.{ .bytes = bytes, .usable_len = size })) {
        abi_allocator.free(bytes); // zlinter-disable-current-line no_hidden_allocations - C ABI allocations use the process-wide registry allocator
        return null;
    }
    return @ptrCast(bytes.ptr);
}

/// Releases one pointer returned by `solidity_alloc` or `solidity_compile`.
/// Invalid pointers retain upstream's caller-programming-error contract.
pub export fn solidity_free(data: ?[*]u8) callconv(.c) void {
    const pointer = data orelse @trap();
    const allocation = takeAbiAllocation(pointer) orelse @trap();
    abi_allocator.free(allocation.bytes); // zlinter-disable-current-line no_hidden_allocations - C ABI allocations use the process-wide registry allocator
}

/// Releases every outstanding C ABI allocation.
pub export fn solidity_reset() callconv(.c) void {
    lockAbiSessions();
    if (abi_live_session_count == 0)
        YulString.reset() catch {}; // zlinter-disable-current-line no_swallow_error - C reset ABI is void and cleanup is necessarily best effort
    unlockAbiSessions();
    lockAbiAllocations();
    defer unlockAbiAllocations();
    for (abi_allocations.items) |allocation|
        abi_allocator.free(allocation.bytes); // zlinter-disable-current-line no_hidden_allocations - C ABI allocations use the process-wide registry allocator
    abi_allocations.clearRetainingCapacity();
}

/// Compiles one NUL-terminated Standard JSON request through the Zig
/// dispatcher and returns registry-owned NUL-terminated output.
pub export fn solidity_compile(
    input: ?[*:0]const u8,
    read_callback: ?CStyleReadFileCallback,
    read_context: ?*anyopaque,
) callconv(.c) ?[*:0]u8 {
    var dispatcher: Dispatcher = .{};
    return abiCompile(
        dispatcher.compiler(),
        input,
        read_callback,
        read_context,
    );
}

const AbiSession = struct {
    session: CompilerSession,
};

/// Creates an opaque in-memory C compiler session.
pub export fn solidity_session_create() callconv(.c) ?*AbiSession {
    const handle = abi_allocator.create(AbiSession) catch return null; // zlinter-disable-current-line no_hidden_allocations - C ABI sessions use the process allocator
    handle.* = .{ .session = CompilerSession.init(abi_allocator) };
    lockAbiSessions();
    abi_live_session_count += 1;
    unlockAbiSessions();
    return handle;
}

/// Compiles one request while retaining reusable state in an opaque C session.
pub export fn solidity_session_compile(
    session: ?*AbiSession,
    input: ?[*:0]const u8,
    read_callback: ?CStyleReadFileCallback,
    read_context: ?*anyopaque,
) callconv(.c) ?[*:0]u8 {
    const handle = session orelse return null;
    return abiCompile(
        handle.session.compiler(),
        input,
        read_callback,
        read_context,
    );
}

/// Destroys an opaque C compiler session after all active calls have returned.
pub export fn solidity_session_destroy(session: ?*AbiSession) callconv(.c) void {
    const handle = session orelse return;
    handle.session.deinit();
    lockAbiSessions();
    std.debug.assert(abi_live_session_count != 0);
    abi_live_session_count -= 1;
    unlockAbiSessions();
    abi_allocator.destroy(handle); // zlinter-disable-current-line no_hidden_allocations - C ABI sessions use the process allocator
}

fn abiCompile(
    compiler_interface: common.standard_json.Compiler,
    input: ?[*:0]const u8,
    read_callback: ?CStyleReadFileCallback,
    read_context: ?*anyopaque,
) ?[*:0]u8 {
    const input_pointer = input orelse return null;
    var callback_context: AbiReadContext = .{
        .callback = read_callback,
        .context = read_context,
    };
    var output = compiler_interface.compile(abi_allocator, .{
        .input = std.mem.span(input_pointer),
        .source_loader = if (read_callback != null)
            .{ .context = &callback_context, .read_fn = abiRead }
        else
            null,
    }) catch return null;
    defer output.deinit();
    return registerAbiCopyZ(output.bytes);
}

fn registerAbiAllocation(allocation: AbiAllocation) bool {
    lockAbiAllocations();
    defer unlockAbiAllocations();
    abi_allocations.append(abi_allocator, allocation) catch return false;
    return true;
}

fn registerAbiCopyZ(bytes: []const u8) ?[*:0]u8 {
    const storage = abi_allocator.alloc(u8, bytes.len + 1) catch return null; // zlinter-disable-current-line no_hidden_allocations - C ABI allocations use the process-wide registry allocator
    @memcpy(storage[0..bytes.len], bytes);
    storage[bytes.len] = 0;
    if (!registerAbiAllocation(.{
        .bytes = storage,
        .usable_len = storage.len,
    })) {
        abi_allocator.free(storage); // zlinter-disable-current-line no_hidden_allocations - C ABI allocations use the process-wide registry allocator
        return null;
    }
    return @ptrCast(storage.ptr);
}

fn takeAbiAllocation(pointer: [*]u8) ?AbiAllocation {
    lockAbiAllocations();
    defer unlockAbiAllocations();
    for (abi_allocations.items, 0..) |allocation, index| {
        if (@intFromPtr(allocation.bytes.ptr) == @intFromPtr(pointer))
            return abi_allocations.swapRemove(index);
    }
    return null;
}

fn lockAbiAllocations() void {
    std.Io.Threaded.mutexLock(&abi_allocations_mutex);
}

fn unlockAbiAllocations() void {
    std.Io.Threaded.mutexUnlock(&abi_allocations_mutex);
}

fn lockAbiSessions() void {
    std.Io.Threaded.mutexLock(&abi_sessions_mutex);
}

fn unlockAbiSessions() void {
    std.Io.Threaded.mutexUnlock(&abi_sessions_mutex);
}

const AbiReadContext = struct {
    callback: ?CStyleReadFileCallback,
    context: ?*anyopaque,
};

fn abiRead(
    opaque_context: ?*anyopaque,
    allocator: std.mem.Allocator,
    kind: []const u8,
    data: []const u8,
) common.standard_json.SourceReadError!common.standard_json.SourceReadResult {
    const state: *AbiReadContext = @ptrCast(@alignCast(opaque_context orelse
        return error.InternalFailure));
    const callback = state.callback orelse return .unsupported;
    const kind_z = try allocator.dupeSentinel(u8, kind, 0);
    defer allocator.free(kind_z);
    const data_z = try allocator.dupeSentinel(u8, data, 0);
    defer allocator.free(data_z);

    var contents_pointer: ?[*:0]u8 = null;
    var error_pointer: ?[*:0]u8 = null;
    callback(
        state.context,
        kind_z.ptr,
        data_z.ptr,
        &contents_pointer,
        &error_pointer,
    );

    const contents = if (contents_pointer) |pointer|
        takeAbiAllocation(@ptrCast(pointer)) orelse @trap()
    else
        null;
    defer if (contents) |allocation| abi_allocator.free(allocation.bytes); // zlinter-disable-current-line no_hidden_allocations - C ABI allocations use the process-wide registry allocator
    const callback_error = if (error_pointer) |pointer|
        takeAbiAllocation(@ptrCast(pointer)) orelse @trap()
    else
        null;
    defer if (callback_error) |allocation| abi_allocator.free(allocation.bytes); // zlinter-disable-current-line no_hidden_allocations - C ABI allocations use the process-wide registry allocator

    if (callback_error) |allocation|
        return .{ .failure = try allocator.dupe(
            u8,
            abiCString(allocation),
        ) };
    if (contents) |allocation|
        return .{ .contents = try allocator.dupe(
            u8,
            abiCString(allocation),
        ) };
    return .unsupported;
}

fn abiCString(allocation: AbiAllocation) []const u8 {
    const bytes = allocation.bytes[0..@min(
        allocation.usable_len,
        allocation.bytes.len,
    )];
    const end = std.mem.findScalar(u8, bytes, 0) orelse bytes.len;
    return bytes[0..end];
}

pub const Dispatcher = struct {
    optimizer_profiler: ?*Profiler = null,

    pub fn compiler(self: *Dispatcher) common.standard_json.Compiler {
        return .{
            .context = self,
            .compile_fn = compile,
        };
    }

    fn compile(
        context: *anyopaque,
        allocator: std.mem.Allocator,
        request: common.standard_json.Request,
    ) common.standard_json.CompileError!common.standard_json.Output {
        const self: *Dispatcher = @ptrCast(@alignCast(context));
        return self.compileWithCaches(allocator, request, null, null);
    }

    pub fn compileWithObjectOptimizer(
        self: *Dispatcher,
        allocator: std.mem.Allocator,
        request: common.standard_json.Request,
        object_optimizer: ?*ObjectOptimizer,
    ) common.standard_json.CompileError!common.standard_json.Output {
        return self.compileWithCaches(allocator, request, object_optimizer, null);
    }

    pub fn compileWithCaches(
        self: *Dispatcher,
        allocator: std.mem.Allocator,
        request: common.standard_json.Request,
        object_optimizer: ?*ObjectOptimizer,
        backend_cache: ?*BackendArtifactCache,
    ) common.standard_json.CompileError!common.standard_json.Output {
        return self.compileWithCachesAndFrontendState(
            allocator,
            request,
            object_optimizer,
            backend_cache,
            null,
            null,
        );
    }

    pub fn compileWithCachesAndFrontendState(
        self: *Dispatcher,
        allocator: std.mem.Allocator,
        request: common.standard_json.Request,
        object_optimizer: ?*ObjectOptimizer,
        backend_cache: ?*BackendArtifactCache,
        shared_frontend_state: ?*FrontendRevisionState,
        request_key: ?ArtifactKey,
    ) common.standard_json.CompileError!common.standard_json.Output {
        var callback_state: CallbackState = .{
            .allocator = allocator,
            .loader = request.source_loader,
        };
        defer callback_state.deinit();
        var summary: adapter.solidity_json_summary = undefined;
        const status = adapter.solidity_json_inspect(
            request.input.ptr,
            request.input.len,
            sourceUrlCallback,
            &callback_state,
            &summary,
        );

        if (status == adapter.SOLIDITY_JSON_OUT_OF_MEMORY or
            callback_state.outcome == .out_of_memory)
        {
            return error.OutOfMemory;
        }
        if (status == adapter.SOLIDITY_JSON_SYNTAX_ERROR) {
            return ownedOutput(allocator, responses.invalid_json);
        }
        if (status == adapter.SOLIDITY_JSON_CALLBACK_FAILED) {
            return ownedOutput(allocator, switch (callback_state.outcome) {
                .unsupported, .none => responses.source_callback_unsupported,
                .failure, .loaded => responses.source_callback_failed,
                .out_of_memory => unreachable,
            });
        }
        if (status != adapter.SOLIDITY_JSON_OK) {
            if (status == adapter.SOLIDITY_JSON_ROOT_NOT_OBJECT or
                status == adapter.SOLIDITY_JSON_INVALID_LANGUAGE or
                status == adapter.SOLIDITY_JSON_INVALID_SOURCES or
                status == adapter.SOLIDITY_JSON_INVALID_SOURCE)
            {
                return ownedOutput(allocator, responses.invalid_envelope);
            }
            return error.InternalFailure;
        }

        if (summary.source_count == 0) {
            return ownedOutput(allocator, responses.no_input_sources);
        }
        var parsed = try JSON.jsonParseStrict(allocator, request.input);
        defer parsed.deinit();
        const root = switch (parsed) {
            .document => |*document| document.rootConst(),
            .failure => return ownedOutput(allocator, responses.invalid_json),
        };
        const language = switch (root.*) {
            .object => |*object| switch ((object.getPtr("language") orelse
                return ownedOutput(allocator, responses.invalid_envelope)).*) {
                .string => |value| value,
                else => return ownedOutput(allocator, responses.invalid_envelope),
            },
            else => return ownedOutput(allocator, responses.invalid_envelope),
        };
        if (std.mem.eql(u8, language, "Yul")) {
            if (request.progress) |progress| progress.report(.{
                .stage = .compiling_yul,
                .estimated_total_items = 1,
                .item_name = "Yul object",
            });
            const bytes = StandardCompiler.compileYulStandardJsonAlloc(
                allocator,
                root,
                callback_state.loaded_sources.items,
                object_optimizer,
                backend_cache,
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return error.InternalFailure,
            };
            if (request.progress) |progress| progress.report(.{
                .stage = .compiling_yul,
                .completed_items = 1,
                .estimated_total_items = 1,
            });
            return .{
                .allocator = allocator,
                .bytes = bytes,
                .execution = .{ .backend = .zig },
            };
        }
        if (std.mem.eql(u8, language, "Solidity")) {
            var local_frontend_state: FrontendRevisionState = undefined;
            const frontend_state = shared_frontend_state orelse state: {
                local_frontend_state = FrontendRevisionState.init(allocator);
                break :state &local_frontend_state;
            };
            defer if (shared_frontend_state == null) local_frontend_state.deinit();
            var revision = frontend_state.beginRevision(request_key) catch
                return error.InternalFailure;
            defer revision.abort();
            const read_callback: ?ReadFile.ReadCallback = if (callback_state.loader != null)
                .{ .context = &callback_state, .read_fn = compilerReadCallback }
            else
                null;
            const bytes = StandardCompiler.compileSolidityStandardJsonAlloc(
                allocator,
                root,
                callback_state.loaded_sources.items,
                read_callback,
                self.optimizer_profiler,
                request.progress,
                request.io,
                object_optimizer,
                backend_cache,
                &revision,
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return error.InternalFailure,
            };
            revision.commitCompleted();
            return .{
                .allocator = allocator,
                .bytes = bytes,
                .execution = .{ .backend = .zig },
            };
        }
        return error.InternalFailure;
    }
};

fn compilerReadCallback(
    opaque_context: ?*anyopaque,
    allocator: std.mem.Allocator,
    kind: []const u8,
    data: []const u8,
) ReadFile.ReadCallback.ReadError!ReadFile.ReadCallback.Result {
    const context_pointer = opaque_context orelse
        return ReadFile.ReadCallback.Result.init(
            allocator,
            false,
            "File not supplied initially.",
        );
    const state: *CallbackState = @ptrCast(@alignCast(context_pointer));
    const loader = state.loader orelse
        return ReadFile.ReadCallback.Result.init(
            allocator,
            false,
            "File not supplied initially.",
        );
    const result = loader.read(allocator, kind, data) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.InvalidPath => return ReadFile.ReadCallback.Result.init(
            allocator,
            false,
            "Invalid path.",
        ),
        error.InternalFailure => return ReadFile.ReadCallback.Result.init(
            allocator,
            false,
            "Source callback failed.",
        ),
    };
    defer result.deinit(allocator);
    return switch (result) {
        .contents => |contents| ReadFile.ReadCallback.Result.init(
            allocator,
            true,
            contents,
        ),
        .failure => |message| ReadFile.ReadCallback.Result.init(
            allocator,
            false,
            message,
        ),
        .unsupported => ReadFile.ReadCallback.Result.init(
            allocator,
            false,
            "File not supplied initially.",
        ),
    };
}

const CallbackOutcome = enum {
    none,
    loaded,
    failure,
    unsupported,
    out_of_memory,
};

const CallbackState = struct {
    allocator: std.mem.Allocator,
    loader: ?common.standard_json.SourceLoader,
    outcome: CallbackOutcome = .none,
    loaded_sources: std.ArrayList(StandardCompiler.SourceContent) = .empty,

    fn deinit(self: *CallbackState) void {
        for (self.loaded_sources.items) |source| {
            self.allocator.free(source.name);
            self.allocator.free(source.content);
        }
        self.loaded_sources.deinit(self.allocator);
        self.* = undefined;
    }
};

fn sourceUrlCallback(
    opaque_context: ?*anyopaque,
    name_pointer: [*c]const u8,
    name_length: usize,
    url_pointer: [*c]const u8,
    url_length: usize,
) callconv(.c) c_int {
    const context_pointer = opaque_context orelse return -1;
    const state: *CallbackState = @ptrCast(@alignCast(context_pointer));
    const loader = state.loader orelse {
        state.outcome = .unsupported;
        return 1;
    };
    if (name_pointer == null or url_pointer == null) {
        state.outcome = .failure;
        return -1;
    }

    const result = loader.read(
        state.allocator,
        "source",
        url_pointer[0..url_length],
    ) catch |err| {
        state.outcome = switch (err) {
            error.OutOfMemory => .out_of_memory,
            error.InvalidPath, error.InternalFailure => .failure,
        };
        return if (err == error.OutOfMemory) -1 else 1;
    };
    defer result.deinit(state.allocator);

    // The source name remains borrowed by yyjson for this synchronous call.
    _ = name_pointer[0..name_length];
    return switch (result) {
        .contents => |contents| blk: {
            const owned_name = state.allocator.dupe(
                u8,
                name_pointer[0..name_length],
            ) catch {
                state.outcome = .out_of_memory;
                break :blk -1;
            };
            const owned_contents = state.allocator.dupe(u8, contents) catch {
                state.allocator.free(owned_name);
                state.outcome = .out_of_memory;
                break :blk -1;
            };
            state.loaded_sources.append(state.allocator, .{
                .name = owned_name,
                .content = owned_contents,
            }) catch {
                state.allocator.free(owned_contents);
                state.allocator.free(owned_name);
                state.outcome = .out_of_memory;
                break :blk -1;
            };
            state.outcome = .loaded;
            break :blk 0;
        },
        .failure => blk: {
            state.outcome = .failure;
            break :blk 1;
        },
        .unsupported => blk: {
            state.outcome = .unsupported;
            break :blk 1;
        },
    };
}

fn ownedOutput(
    allocator: std.mem.Allocator,
    bytes: []const u8,
) error{OutOfMemory}!common.standard_json.Output {
    return .{
        .allocator = allocator,
        .bytes = try allocator.dupe(u8, bytes),
        .execution = .{ .backend = .zig },
    };
}

fn testAbiReadCallback(
    _: ?*anyopaque,
    kind: [*:0]const u8,
    data: [*:0]const u8,
    contents: *?[*:0]u8,
    error_message: *?[*:0]u8,
) callconv(.c) void {
    contents.* = null;
    error_message.* = null;
    if (!std.mem.eql(u8, std.mem.span(kind), "source") or
        !std.mem.eql(u8, std.mem.span(data), "B.sol")) return;

    const source = "// SPDX-License-Identifier: UNLICENSED\ncontract B {}";
    const output = solidity_alloc(source.len + 1) orelse return;
    @memcpy(output[0..source.len], source);
    output[source.len] = 0;
    contents.* = output;
}

test "libsolc C ABI transfers callback and output ownership" {
    solidity_reset();
    defer solidity_reset();

    const input =
        "{\"language\":\"Solidity\",\"sources\":{\"A.sol\":{\"content\":" ++
        "\"// SPDX-License-Identifier: UNLICENSED\\nimport \\\"B.sol\\\"; contract A is B {}\"}}," ++
        "\"settings\":{}}";
    const raw_output = solidity_compile(input, testAbiReadCallback, null) orelse
        return error.OutOfMemory;
    defer solidity_free(raw_output);

    const output = std.mem.span(raw_output);
    try std.testing.expect(std.mem.find(
        u8,
        output,
        "\"B.sol\":{\"id\":1}",
    ) != null);
    try std.testing.expectEqualStrings(Version.VersionString, std.mem.span(solidity_version()));
    try std.testing.expect(std.mem.span(solidity_license()).len > 30_000);
}

fn testSourceEnvelopeAlloc(
    allocator: std.mem.Allocator,
    language: []const u8,
    source_count: usize,
    duplicate_names: bool,
) ![]u8 {
    var input: std.ArrayList(u8) = .empty;
    errdefer input.deinit(allocator);
    try input.print(
        allocator,
        "{{\"language\":\"{s}\",\"sources\":{{",
        .{language},
    );
    for (0..source_count) |offset| {
        if (offset != 0) try input.append(allocator, ',');
        if (duplicate_names) {
            try input.appendSlice(
                allocator,
                "\"Duplicate.sol\":{\"content\":\"\"}",
            );
        } else {
            const index = source_count - offset - 1;
            try input.print(
                allocator,
                "\"Source{d}.sol\":{{\"content\":\"\"}}",
                .{index},
            );
        }
    }
    try input.appendSlice(allocator, "}}");
    return input.toOwnedSlice(allocator);
}

test "yyjson preflight bounds and sorts Standard JSON source entries" {
    const at_limit = try testSourceEnvelopeAlloc(
        std.testing.allocator,
        "Solidity",
        max_standard_json_source_entries,
        false,
    );
    defer std.testing.allocator.free(at_limit);
    var summary: adapter.solidity_json_summary = undefined;
    const at_limit_status = adapter.solidity_json_inspect(
        at_limit.ptr,
        at_limit.len,
        null,
        null,
        &summary,
    );
    try std.testing.expectEqual(
        @as(@TypeOf(at_limit_status), @intCast(adapter.SOLIDITY_JSON_OK)),
        at_limit_status,
    );
    try std.testing.expectEqual(
        max_standard_json_source_entries,
        summary.source_count,
    );

    const over_limit = try testSourceEnvelopeAlloc(
        std.testing.allocator,
        "Vyper",
        max_standard_json_source_entries + 1,
        true,
    );
    defer std.testing.allocator.free(over_limit);
    const over_limit_status = adapter.solidity_json_inspect(
        over_limit.ptr,
        over_limit.len,
        null,
        null,
        &summary,
    );
    try std.testing.expectEqual(
        @as(
            @TypeOf(over_limit_status),
            @intCast(adapter.SOLIDITY_JSON_INVALID_SOURCES),
        ),
        over_limit_status,
    );

    var dispatcher: Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = over_limit,
    });
    defer output.deinit();
    try common.standard_json.compareExact(responses.invalid_envelope, output.bytes);
}
