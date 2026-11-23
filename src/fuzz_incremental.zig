// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structured, stateful differential fuzzing for incremental Solidity builds.
//!
//! One fuzz input describes a complete edit history. Every warm revision is
//! compared byte-for-byte with a clean compiler, including rejected revisions,
//! so a later valid edit also verifies recovery from frontend failure.

const std = @import("std");
const solidity = @import("solidity");

const modules = solidity.compiler;
const JSON = modules.libsolutil.json;
const Json = JSON.Json;
const CompilerSession = solidity.incremental.CompilerSession;

const overlay_edit_count = solidity.incremental.semantic_revision.max_overlay_depth + 2;
const max_edit_count: u8 = @intCast(overlay_edit_count);

const RecursiveMode = enum(u3) {
    dynamic_array,
    mapping,
    self_dynamic_array,
    fixed_array_cycle,
    nested_direct_cycle,
};

const Projection = enum(u2) {
    bytecode,
    runtime,
    abi_and_bytecode,
};

const Action = enum(u8) {
    first_body,
    second_body,
    signature_failure,
    selective_reexport,
    import_cycle,
    imported_alias_swap,
    recursive_shape,
    source_names,
    source_order,
    extra_source,
    optimizer_runs,
    output_projection,
    inherited_body,
    library_body,
    modifier_limit,
    wide_base_storage,
    inherited_signature_failure,
    super_signature_failure,
    error_signature_failure,
};

const ProjectState = struct {
    first_body: u8 = 1,
    second_body: u8 = 2,
    signature_failure: bool = false,
    selective_reexport: bool = false,
    import_cycle: bool = false,
    imported_alias_swap: bool = false,
    recursive_mode: RecursiveMode = .dynamic_array,
    alternate_source_names: bool = false,
    reverse_source_order: bool = false,
    extra_source: bool = false,
    optimizer_runs: u16 = 200,
    projection: Projection = .bytecode,
    inherited_body: u8 = 3,
    library_body: u8 = 4,
    modifier_limit: u8 = 64,
    wide_base_storage: bool = false,
    inherited_signature_failure: bool = false,
    super_signature_failure: bool = false,
    error_signature_failure: bool = false,

    fn apply(self: *ProjectState, action: Action, value: u8, flag: bool) void {
        switch (action) {
            .first_body => self.first_body = 1 + value % 63,
            .second_body => self.second_body = 1 + value % 63,
            .signature_failure => self.signature_failure = flag,
            .selective_reexport => self.selective_reexport = flag,
            .import_cycle => self.import_cycle = flag,
            .imported_alias_swap => self.imported_alias_swap = flag,
            .recursive_shape => self.recursive_mode = @fromBackingInt(@intCast(
                value % @typeInfo(RecursiveMode).@"enum".field_names.len,
            )),
            .source_names => self.alternate_source_names = flag,
            .source_order => self.reverse_source_order = flag,
            .extra_source => self.extra_source = flag,
            .optimizer_runs => self.optimizer_runs = switch (value % 5) {
                0 => 0,
                1 => 1,
                2 => 200,
                3 => 1_000,
                else => 10_000,
            },
            .output_projection => self.projection = @fromBackingInt(@intCast(
                value % @typeInfo(Projection).@"enum".field_names.len,
            )),
            .inherited_body => self.inherited_body = 1 + value % 63,
            .library_body => self.library_body = 1 + value % 63,
            .modifier_limit => self.modifier_limit = 2 + value % 62,
            .wide_base_storage => self.wide_base_storage = flag,
            .inherited_signature_failure => self.inherited_signature_failure = flag,
            .super_signature_failure => self.super_signature_failure = flag,
            .error_signature_failure => self.error_signature_failure = flag,
        }
    }
};

const SeedEdit = struct {
    action: Action,
    value: u8 = 0,
    flag: bool = false,
};

const reexport_seed = smithHistoryCorpus(&.{
    .{ .action = .selective_reexport, .flag = true },
    .{ .action = .first_body, .value = 19 },
    .{ .action = .signature_failure, .flag = true },
    .{ .action = .signature_failure, .flag = false },
});
const alias_seed = smithHistoryCorpus(&.{
    .{ .action = .imported_alias_swap, .flag = true },
    .{ .action = .source_order, .flag = true },
});
const recursive_seed = smithHistoryCorpus(&.{
    .{ .action = .recursive_shape, .value = @backingInt(RecursiveMode.fixed_array_cycle) },
    .{ .action = .recursive_shape, .value = @backingInt(RecursiveMode.nested_direct_cycle) },
    .{ .action = .recursive_shape, .value = @backingInt(RecursiveMode.mapping) },
});
const dependency_seed = smithHistoryCorpus(&.{
    .{ .action = .inherited_body, .value = 8 },
    .{ .action = .library_body, .value = 10 },
    .{ .action = .modifier_limit, .value = 30 },
    .{ .action = .wide_base_storage, .flag = true },
    .{ .action = .inherited_signature_failure, .flag = true },
    .{ .action = .inherited_signature_failure, .flag = false },
    .{ .action = .error_signature_failure, .flag = true },
    .{ .action = .error_signature_failure, .flag = false },
});
const hierarchy_seed = smithHistoryCorpus(&.{
    .{ .action = .super_signature_failure, .flag = true },
    .{ .action = .super_signature_failure, .flag = false },
});
const overlay_edits = overlaySeedEdits();
const overlay_seed = smithHistoryCorpus(&overlay_edits);

test "fuzz stateful incremental Solidity compilation" {
    try std.testing.fuzz({}, fuzzIncremental, .{ .corpus = &.{
        &reexport_seed,
        &alias_seed,
        &recursive_seed,
        &dependency_seed,
        &hierarchy_seed,
        &overlay_seed,
    } });
}

fn fuzzIncremental(_: void, smith: *std.testing.Smith) !void {
    @disableInstrumentation();
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();

    var state: ProjectState = .{};
    try compareRevision(std.testing.allocator, &session, state);
    const edit_count = smith.valueWeighted(u8, &.{
        .rangeAtMost(u8, 1, 6, 8),
        .rangeAtMost(u8, 7, max_edit_count, 1),
    });
    for (0..edit_count) |_| {
        state.apply(
            smith.value(Action),
            smith.value(u8),
            smith.value(bool),
        );
        try compareRevision(std.testing.allocator, &session, state);
    }
}

fn compareRevision(
    allocator: std.mem.Allocator,
    session: *CompilerSession,
    state: ProjectState,
) !void {
    const request = try requestAlloc(allocator, state);
    defer allocator.free(request);

    var clean_dispatcher: solidity.StandardJsonDispatcher = .{};
    var clean = try clean_dispatcher.compiler().compile(allocator, .{ .solc_version = .v0_8_36, .input = request });
    defer clean.deinit();
    var warm = try session.compiler().compile(allocator, .{ .solc_version = .v0_8_36, .input = request });
    defer warm.deinit();
    try solidity.standard_json.compareExact(clean.bytes, warm.bytes);
}

fn requestAlloc(allocator: std.mem.Allocator, state: ProjectState) ![]u8 {
    const first_name = if (state.alternate_source_names) "RenamedA.sol" else "A.sol";
    const reexport_name = if (state.alternate_source_names) "RenamedB.sol" else "B.sol";
    const first_source = try firstSourceAlloc(allocator, state);
    defer allocator.free(first_source);
    const reexport_source = try reexportSourceAlloc(
        allocator,
        state,
        first_name,
        reexport_name,
    );
    defer allocator.free(reexport_source);
    const cycle_source = try cycleSourceAlloc(allocator, state, reexport_name);
    defer allocator.free(cycle_source);
    const alias_source = try aliasSourceAlloc(allocator, state);
    defer allocator.free(alias_source);
    const main_source = try mainSourceAlloc(allocator, state, reexport_name);
    defer allocator.free(main_source);
    const dependency_source = try dependencySourceAlloc(allocator, state);
    defer allocator.free(dependency_source);
    const hierarchy_source = try hierarchySourceAlloc(allocator, state);
    defer allocator.free(hierarchy_source);

    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sources: Json = .{ .object = .empty };
    const entries = [_]struct { []const u8, []const u8 }{
        .{ first_name, first_source },
        .{ reexport_name, reexport_source },
        .{ "Cycle.sol", cycle_source },
        .{ "Auth.sol", auth_source },
        .{ "Aliases.sol", alias_source },
        .{ "Recursive.sol", recursiveSource(state.recursive_mode) },
        .{ "Main.sol", main_source },
        .{ "Dependency.sol", dependency_source },
        .{ "Consumer.sol", consumer_source },
        .{ "Hierarchy.sol", hierarchy_source },
    };
    if (state.reverse_source_order) {
        var index = entries.len;
        while (index != 0) {
            index -= 1;
            try sources.object.put(
                arena,
                entries[index][0],
                try sourceJson(arena, entries[index][1]),
            );
        }
    } else {
        for (entries) |entry|
            try sources.object.put(arena, entry[0], try sourceJson(arena, entry[1]));
    }
    if (state.extra_source)
        try sources.object.put(arena, "Extra.sol", try sourceJson(arena, extra_source));

    var optimizer: Json = .{ .object = .empty };
    try optimizer.object.put(arena, "enabled", .{ .bool = true });
    try optimizer.object.put(arena, "runs", jsonInteger(state.optimizer_runs));
    var metadata: Json = .{ .object = .empty };
    try metadata.object.put(arena, "appendCBOR", .{ .bool = false });

    var artifacts = std.json.Array.init(arena);
    switch (state.projection) {
        .bytecode => {
            try artifacts.append(.{ .string = "storageLayout" });
            try artifacts.append(.{ .string = "evm.bytecode.object" });
            try artifacts.append(.{ .string = "evm.deployedBytecode.object" });
            try artifacts.append(.{ .string = "evm.methodIdentifiers" });
        },
        .runtime => try artifacts.append(.{ .string = "evm.deployedBytecode.object" }),
        .abi_and_bytecode => {
            try artifacts.append(.{ .string = "abi" });
            try artifacts.append(.{ .string = "evm.bytecode.object" });
        },
    }
    var contracts: Json = .{ .object = .empty };
    try contracts.object.put(arena, "*", .{ .array = artifacts });
    var output_selection: Json = .{ .object = .empty };
    try output_selection.object.put(arena, "*", contracts);

    var settings: Json = .{ .object = .empty };
    try settings.object.put(arena, "viaIR", .{ .bool = true });
    try settings.object.put(arena, "optimizer", optimizer);
    try settings.object.put(arena, "metadata", metadata);
    try settings.object.put(arena, "outputSelection", output_selection);
    var root: Json = .{ .object = .empty };
    try root.object.put(arena, "language", .{ .string = "Solidity" });
    try root.object.put(arena, "sources", sources);
    try root.object.put(arena, "settings", settings);
    return JSON.jsonCompactPrintAlloc(allocator, &root);
}

fn firstSourceAlloc(allocator: std.mem.Allocator, state: ProjectState) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.appendSlice(allocator, preamble);
    if (state.signature_failure) {
        try source.print(
            allocator,
            "function f(bytes32 x) pure returns (uint256) {{ return uint256(x) + {d}; }}\n",
            .{state.first_body},
        );
    } else {
        try source.print(
            allocator,
            "function f(uint256 x) pure returns (uint256) {{ return x + {d}; }}\n",
            .{state.first_body},
        );
    }
    try source.print(
        allocator,
        "function f(address) pure returns (uint256) {{ return {d}; }}\n",
        .{state.second_body},
    );
    return source.toOwnedSlice(allocator);
}

fn reexportSourceAlloc(
    allocator: std.mem.Allocator,
    state: ProjectState,
    first_name: []const u8,
    reexport_name: []const u8,
) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    errdefer source.deinit(allocator);
    try source.appendSlice(allocator, preamble);
    if (state.selective_reexport)
        try source.print(allocator, "import {{f as exportF}} from \"{s}\";\n", .{first_name})
    else
        try source.print(allocator, "import \"{s}\";\n", .{first_name});
    if (state.import_cycle)
        try source.appendSlice(allocator, "import \"Cycle.sol\";\n");
    try source.print(
        allocator,
        "library ReexportMarker {{ function source() internal pure returns (bytes32) {{ return keccak256(\"{s}\"); }} }}\n",
        .{reexport_name},
    );
    return source.toOwnedSlice(allocator);
}

fn cycleSourceAlloc(
    allocator: std.mem.Allocator,
    state: ProjectState,
    reexport_name: []const u8,
) ![]u8 {
    if (!state.import_cycle) return allocator.dupe(u8, preamble ++ "library CycleMarker {}\n");
    return allocator.print(
        preamble ++ "import \"{s}\";\nlibrary CycleMarker {{}}\n",
        .{reexport_name},
    );
}

fn aliasSourceAlloc(allocator: std.mem.Allocator, state: ProjectState) ![]u8 {
    return allocator.dupe(
        u8,
        if (state.imported_alias_swap)
            preamble ++ "import {authorized as rejected, rejected as authorized} from \"Auth.sol\";\n"
        else
            preamble ++ "import {authorized, rejected} from \"Auth.sol\";\n",
    );
}

fn mainSourceAlloc(
    allocator: std.mem.Allocator,
    state: ProjectState,
    reexport_name: []const u8,
) ![]u8 {
    return allocator.print(
        preamble ++
            "import * as R from \"{s}\";\n" ++
            "import * as M from \"Aliases.sol\";\n" ++
            "using {{M.authorized, M.rejected}} for uint256;\n" ++
            "contract Main {{\n" ++
            "    function symbol(uint256 x) external pure returns (uint256) {{ return R.{s}(x); }}\n" ++
            "    function isAuthorized(uint256 x) external pure returns (bool) {{ return x.authorized(); }}\n" ++
            "    function isRejected(uint256 x) external pure returns (bool) {{ return x.rejected(); }}\n" ++
            "}}\n",
        .{ reexport_name, if (state.selective_reexport) "exportF" else "f" },
    );
}

fn dependencySourceAlloc(allocator: std.mem.Allocator, state: ProjectState) ![]u8 {
    const storage_members = if (state.wide_base_storage)
        "uint256 internal left; uint256 internal right;"
    else
        "uint128 internal left; uint128 internal right;";
    const inherited_type = if (state.inherited_signature_failure) "bytes32" else "uint256";
    const inherited_value = if (state.inherited_signature_failure) "uint256(value)" else "value";
    const error_type = if (state.error_signature_failure) "bytes32" else "uint256";
    return allocator.print(
        preamble ++
            "struct Payload {{ uint256 value; uint256 salt; }}\n" ++
            "library PayloadLib {{\n" ++
            "    function score(Payload memory self) internal pure returns (uint256) {{\n" ++
            "        return self.value * 3 + self.salt + {d};\n" ++
            "    }}\n" ++
            "}}\n" ++
            "error SharedError({s} value);\n" ++
            "contract Base {{\n" ++
            "    {s}\n" ++
            "    modifier adjusted(uint256 value) {{\n" ++
            "        require(value < {d});\n" ++
            "        _;\n" ++
            "    }}\n" ++
            "    function inherited({s} value) public pure returns (uint256) {{\n" ++
            "        return {s} + {d};\n" ++
            "    }}\n" ++
            "}}\n",
        .{
            state.library_body,
            error_type,
            storage_members,
            state.modifier_limit,
            inherited_type,
            inherited_value,
            state.inherited_body,
        },
    );
}

fn hierarchySourceAlloc(allocator: std.mem.Allocator, state: ProjectState) ![]u8 {
    return allocator.print(
        preamble ++
            "contract ConcreteBase {{\n" ++
            "    function dispatch(bool value) public pure virtual returns (uint256) {{\n" ++
            "        return value ? 1 : 2147483648;\n" ++
            "    }}\n" ++
            "    function dispatch({s} value) public pure virtual returns (uint256) {{\n" ++
            "        return value + 17;\n" ++
            "    }}\n" ++
            "}}\n" ++
            "abstract contract AbstractBase {{\n" ++
            "    function dispatch(uint256 value) public pure virtual returns (uint256);\n" ++
            "}}\n" ++
            "contract SuperConsumer is ConcreteBase, AbstractBase {{\n" ++
            "    function dispatch(uint256 value) public pure override(ConcreteBase, AbstractBase) returns (uint256) {{\n" ++
            "        return super.dispatch(value);\n" ++
            "    }}\n" ++
            "}}\n",
        .{if (state.super_signature_failure) "uint64" else "uint256"},
    );
}

fn recursiveSource(mode: RecursiveMode) []const u8 {
    return switch (mode) {
        .dynamic_array => preamble ++ "contract Recursive { struct A { B[] children; } struct B { A parent; } }\n",
        .mapping => preamble ++ "contract Recursive { struct A { mapping(uint256 => B) children; } struct B { A parent; } }\n",
        .self_dynamic_array => preamble ++ "contract Recursive { struct A { A[] children; } }\n",
        .fixed_array_cycle => preamble ++ "contract Recursive { struct A { B[1] child; } struct B { A parent; } }\n",
        .nested_direct_cycle => preamble ++ "contract Recursive { struct A { B[] children; } struct B { B parent; } }\n",
    };
}

fn sourceJson(allocator: std.mem.Allocator, source: []const u8) !Json {
    var result: Json = .{ .object = .empty };
    try result.object.put(allocator, "content", .{ .string = source });
    return result;
}

fn jsonInteger(value: anytype) Json {
    return .{ .integer = @intCast(value) };
}

fn smithHistoryCorpus(comptime edits: []const SeedEdit) [8 + edits.len * 24]u8 {
    var result: [8 + edits.len * 24]u8 = undefined;
    std.mem.writeInt(u64, result[0..8], edits.len, .little);
    inline for (edits, 0..) |edit, index| {
        const offset = 8 + index * 24;
        std.mem.writeInt(u64, result[offset..][0..8], @backingInt(edit.action), .little);
        std.mem.writeInt(u64, result[offset + 8 ..][0..8], edit.value, .little);
        std.mem.writeInt(u64, result[offset + 16 ..][0..8], @intFromBool(edit.flag), .little);
    }
    return result;
}

fn overlaySeedEdits() [overlay_edit_count]SeedEdit {
    var result: [overlay_edit_count]SeedEdit = undefined;
    for (&result, 0..) |*edit, index|
        edit.* = .{ .action = .first_body, .value = @intCast(index + 1) };
    return result;
}

const preamble = "// SPDX-License-Identifier: UNLICENSED\npragma solidity 0.8.36;\n";
const auth_source = preamble ++
    "function authorized(uint256 value) pure returns (bool) { return value == 7; }\n" ++
    "function rejected(uint256 value) pure returns (bool) { return value != 7; }\n";
const extra_source = preamble ++
    "contract Extra { function value() external pure returns (uint256) { return 99; } }\n";
const consumer_source = preamble ++
    "import {Base, Payload, PayloadLib, SharedError} from \"Dependency.sol\";\n" ++
    "using PayloadLib for Payload;\n" ++
    "contract Consumer is Base {\n" ++
    "    function run(uint256 value) external pure adjusted(value) returns (uint256) {\n" ++
    "        if (value == 0) revert SharedError(value);\n" ++
    "        return inherited(value) + Payload(value, 5).score();\n" ++
    "    }\n" ++
    "}\n";
