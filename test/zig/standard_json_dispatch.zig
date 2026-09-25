// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");
const solidity = @import("solidity");

const libsolc = solidity.libsolc.libsolc;
const standard_json = solidity.standard_json;
const Profiler = solidity.libsolutil.profiler.Profiler;
const ObjectOptimizer = solidity.libyul.object_optimizer.ObjectOptimizer;

test "calldata reads and checked division preserve solc helper order and bytecode" {
    inline for (.{
        "solidity-calldata-enum-cleanup-order",
        "solidity-unsigned-division-helper-order",
    }) |name| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{
            .input = @embedFile("standard-json/" ++ name ++ ".json"),
        });
        defer output.deinit();
        try standard_json.compareExact(
            @embedFile("standard-json/expected/" ++ name ++ ".json"),
            output.bytes,
        );
    }
}

test "using-for reference receivers preserve calldata memory and storage locations" {
    inline for (.{
        "solidity-using-for-reference-locations",
        "solidity-using-for-invalid-reference-location",
    }) |name| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{
            .input = @embedFile("standard-json/" ++ name ++ ".json"),
        });
        defer output.deinit();
        try standard_json.compareExact(
            @embedFile("standard-json/expected/" ++ name ++ ".json"),
            output.bytes,
        );
    }
}

test "parked analysis settings are rejected by stateless and incremental compilation" {
    var dispatcher: libsolc.Dispatcher = .{};
    var session = solidity.CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    for ([_][]const u8{ "true", "false" }) |enabled| {
        const input = try std.fmt.allocPrint(
            std.testing.allocator,
            "{{\"language\":\"Solidity\",\"sources\":{{\"C.sol\":{{\"content\":\"contract C {{}}\"}}}},\"settings\":{{\"abstractInterpretation\":{{\"enabled\":{s}}}}}}}",
            .{enabled},
        );
        defer std.testing.allocator.free(input);
        var clean = try dispatcher.compiler().compile(std.testing.allocator, .{ .input = input });
        defer clean.deinit();
        const parsed = try std.json.parseFromSlice(std.json.Value, std.testing.allocator, clean.bytes, .{});
        defer parsed.deinit();
        try std.testing.expect(parsed.value.object.get("contracts") == null);
        const diagnostic = parsed.value.object.get("errors").?.array.items[0].object;
        try std.testing.expectEqualStrings("JSONError", diagnostic.get("type").?.string);
        try std.testing.expect(std.mem.find(u8, diagnostic.get("message").?.string, "abstractInterpretation") != null);
        for (0..2) |_| {
            var cached = try session.compile(std.testing.allocator, .{ .input = input });
            defer cached.deinit();
            try standard_json.compareExact(clean.bytes, cached.bytes);
        }
    }
}

const ProgressRecorder = struct {
    stages: [16]standard_json.ProgressStage = undefined,
    stage_count: usize = 0,
    saw_contract_a: bool = false,
    generating_completed: usize = 0,
    generating_total: usize = 0,
    generating_monotonic: bool = true,

    fn reporter(self: *ProgressRecorder) standard_json.ProgressReporter {
        return .{ .context = self, .report_fn = report };
    }

    fn report(
        opaque_context: ?*anyopaque,
        update: standard_json.ProgressUpdate,
    ) void {
        const self: *ProgressRecorder = @ptrCast(@alignCast(opaque_context.?));
        if (self.stage_count < self.stages.len) {
            self.stages[self.stage_count] = update.stage;
            self.stage_count += 1;
        }
        if (update.stage == .generating_contracts) {
            self.generating_monotonic = self.generating_monotonic and
                update.completed_items >= self.generating_completed;
            self.generating_completed = update.completed_items;
            self.generating_total = update.estimated_total_items;
            if (std.mem.eql(u8, update.item_name, "A")) self.saw_contract_a = true;
        }
    }

    fn sawStage(self: *const ProgressRecorder, stage: standard_json.ProgressStage) bool {
        return std.mem.findScalar(
            standard_json.ProgressStage,
            self.stages[0..self.stage_count],
            stage,
        ) != null;
    }
};

test "valid empty-sources request matches the frozen solc output exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/empty-sources.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/empty-sources.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "invalid JSON is handled by Zig with an exact stable response" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = "{\"language\":",
    });
    defer output.deinit();

    try standard_json.compareExact(libsolc.responses.invalid_json, output.bytes);
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "invalid missing-language request preserves solc empty-source validation order" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = "{\"sources\":{}}",
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/empty-sources.json"),
        output.bytes,
    );
}

test "valid source input matches solc after the frontend became available" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}}}
        ,
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-source-success.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity compilation reports factual source and contract progress" {
    var recorder: ProgressRecorder = .{};
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"viaIR":true,"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
        ,
        .progress = recorder.reporter(),
    });
    defer output.deinit();

    try std.testing.expect(std.mem.find(u8, output.bytes, "\"contracts\"") != null);
    try std.testing.expect(recorder.sawStage(.parsing_sources));
    try std.testing.expect(recorder.sawStage(.analyzing_sources));
    try std.testing.expect(recorder.sawStage(.generating_contracts));
    try std.testing.expect(recorder.saw_contract_a);
}

test "Solidity bytecode never silently enters the legacy pipeline" {
    const cases = [_][]const u8{
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"viaIR":false,"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
        ,
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"outputSelection":{"*":{"*":["*"]}}}}
        ,
    };
    const expected =
        "{\"errors\":[{\"component\":\"general\",\"formattedMessage\":\"Zig port: Solidity EVM output requires \\\"settings.viaIR\\\": true; the legacy direct-codegen pipeline is unsupported.\",\"message\":\"Zig port: Solidity EVM output requires \\\"settings.viaIR\\\": true; the legacy direct-codegen pipeline is unsupported.\",\"severity\":\"error\",\"type\":\"UnimplementedFeatureError\"}]}\n";

    for (cases) |input| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{ .input = input });
        defer output.deinit();
        try standard_json.compareExact(expected, output.bytes);
    }
}

test "viaIR false remains accepted for frontend-only Solidity output" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-abi.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-abi.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "complete inherited and library ABI surface matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-complete-abi.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-complete-abi.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "NatSpec user and developer documentation matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-natspec-output.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-natspec-output.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "NatSpec diagnostics and ordering match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-natspec-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-natspec-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "invalid explicit NatSpec inheritance matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-natspec-inherit-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-natspec-inherit-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "inline assembly NatSpec warnings match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-natspec-inline-assembly.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-natspec-inline-assembly.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "documented Solidity metadata matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-natspec-metadata.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-natspec-metadata.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "storage and transient-storage layouts match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-storage-layout.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-storage-layout.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "viaIR false analyzed AST output matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-analyzed-ast.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-analyzed-ast.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity parsed AST matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-parsed-ast.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-parsed-ast.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity parser diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/parser-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/parser-error.json"),
        output.bytes,
    );
}

test "Solidity parser recovery and diagnostic ordering match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-parser-recovery.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-parser-recovery.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity syntax diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-syntax-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-syntax-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity reference diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-reference-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-reference-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity declaration-type diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-declaration-type-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-declaration-type-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity declaration-type mapping and transient boundaries match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-declaration-type-boundaries.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-declaration-type-boundaries.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity rational-operator diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-rational-operator-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-rational-operator-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity static-analysis diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-static-analysis-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-static-analysis-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity static-analyzer storage and constructor boundaries match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-static-analyzer-boundaries.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-static-analyzer-boundaries.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity post-type loop classification and near-end storage layout match via-IR exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-post-type-loop-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-post-type-loop-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity constant-evaluator boundaries match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-constant-evaluator-boundaries.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-constant-evaluator-boundaries.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity control-flow definite-assignment diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-control-flow-uninitialized.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-control-flow-uninitialized.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity unreachable-code ordering matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-control-flow-unreachable.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-control-flow-unreachable.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity structured inline-Yul and virtual control flow match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-control-flow-inline-yul.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-control-flow-inline-yul.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity post-type diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-post-type-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-post-type-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity override graph and public getter signatures match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-override-graph-success.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-override-graph-success.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity constant-cycle diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-constant-cycle-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-constant-cycle-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity constant dependency depth limit matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-constant-depth-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-constant-depth-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity state-mutability diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-mutability-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-mutability-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity inline-Yul instruction mutability matches solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-inline-yul-mutability.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-inline-yul-mutability.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity immutable-write diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-immutable-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-immutable-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity contract-bytecode dependency cycles match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-contract-dependency-cycle-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-contract-dependency-cycle-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity post-type contract diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-post-type-contract-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-post-type-contract-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity storage-layout warnings preserve upstream phase ordering" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-storage-layout-warning.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-storage-layout-warning.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity contract-level diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-contract-level-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-contract-level-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity override diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-override-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-override-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity ambiguous-override diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-ambiguous-override-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-ambiguous-override-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity selector-collision diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-selector-collision-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-selector-collision-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity external-type-clash diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-external-type-clash-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-external-type-clash-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity storage-size diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-storage-size-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-storage-size-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity inherited ABI-coder diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-base-abi-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-base-abi-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity index-access diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-index-type-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-index-type-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity member-access diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-member-type-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-member-type-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity struct-constructor diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-struct-call-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-struct-call-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity abi.decode diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-abi-decode-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-abi-decode-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity ABI encode and encodeCall diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-abi-encode-errors.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-abi-encode-errors.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity tuple-declaration diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-tuple-declaration-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-tuple-declaration-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity emit-statement diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-emit-type-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-emit-type-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity direct-base override dominance diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-override-dominance-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-override-dominance-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity single-branch override dominance retains the inherited ABI" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-override-chain-abi.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-override-chain-abi.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity stateless inheritance matches via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-stateless-inheritance-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-stateless-inheritance-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity interface-getter and diamond-super call graphs match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-function-call-graph-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-function-call-graph-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar public-state getters match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-state-getter-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-state-getter-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar state reads and writes match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-state-read-write-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-state-read-write-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity packed scalar state matches via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-packed-state-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-packed-state-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar constructor state writes match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-scalar-constructor-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-scalar-constructor-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar state initializers match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-state-initializer-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-state-initializer-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar stateful inheritance matches via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-stateful-inheritance-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-stateful-inheritance-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity fallback and receive dispatch match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-fallback-receive-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-fallback-receive-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity address state conversion matches via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-address-state-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-address-state-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity fixed-bytes state conversion matches via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-fixed-bytes-state-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-fixed-bytes-state-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity enum state conversion matches via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-enum-state-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-enum-state-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity no-argument modifiers match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-modifier-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-modifier-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity chained and repeated modifier placeholders match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-multiple-modifiers-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-multiple-modifiers-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity inherited virtual modifier annotations and resolved bodies match via-IR exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-inherited-virtual-modifier-ir.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-inherited-virtual-modifier-ir.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity typed modifier arguments match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-modifier-arguments-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-modifier-arguments-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar constructor arguments match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-constructor-arguments-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-constructor-arguments-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar base-constructor arguments match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-base-constructor-arguments-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-base-constructor-arguments-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity constructor hierarchy, dynamic arguments, and modifiers match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-constructor-hierarchy-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-constructor-hierarchy-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity create and create2 subobjects match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-contract-creation-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-contract-creation-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity contract metatype code, name, and interface ID match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-contract-meta-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-contract-meta-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar unary mutation matches via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-unary-mutation-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-unary-mutation-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar constant state values match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-constant-state-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-constant-state-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity reference constants, internal-function immutables, and inherited modifiers match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-constants-immutables-modifiers-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-constants-immutables-modifiers-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity qualified imports, linked libraries, and external function members match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-qualified-members-library-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-qualified-members-library-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "library-qualified struct constructors remain callable" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-library-struct-constructor.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-library-struct-constructor.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity fixed-bytes indexing and transient value storage match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-fixed-index-transient-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-fixed-index-transient-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity abstract and interface artifacts remain empty exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-nondeployable-artifacts.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-nondeployable-artifacts.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity aggregate storage, memory, calldata, and tuple lvalues match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-aggregate-lvalues-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-aggregate-lvalues-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar immutable state values match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-immutable-state-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-immutable-state-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity inherited scalar immutables match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-immutable-inheritance-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-immutable-inheritance-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity require assert and empty revert match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-require-assert-revert-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-require-assert-revert-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity nested scalar mappings match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-scalar-mapping-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-scalar-mapping-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity public nested scalar mapping getters match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-public-scalar-mapping-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-public-scalar-mapping-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity environment member expressions match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-environment-members-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-environment-members-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity address and fixed-bytes members match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-address-members-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-address-members-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar indexed and anonymous events match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-scalar-events-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-scalar-events-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar custom errors match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-custom-errors-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-custom-errors-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar EVM builtins match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-scalar-builtins-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-scalar-builtins-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity enum and metatype members match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-type-members-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-type-members-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity function error event and message selectors match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-selectors-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-selectors-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity scalar external calls match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-scalar-external-calls-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-scalar-external-calls-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity composite ABI boundaries match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-composite-abi-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-composite-abi-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity memory arrays, indexing, and calldata slicing match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-reference-values-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-reference-values-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity struct, array, magic, getter, and overloaded contract members match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-reference-members-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-reference-members-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity struct construction, ABI builtins, concat, and meta types match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-abi-concat-meta-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-abi-concat-meta-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity library and free-function using-for members match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-using-for-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-using-for-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity call options, dynamic calls, ABI encoders, storage arrays, and call builtins match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-callable-control-flow-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-callable-control-flow-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity inline assembly analysis, external references, and via-IR bytecode match exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-inline-assembly-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-inline-assembly-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity try success and Error, Panic, bytes, and forwarding catch paths match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-try-catch-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-try-catch-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity checked, wrapping, narrow, wide, and literal exponentiation match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-exponentiation-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-exponentiation-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity typed shifts, loops, and external-function comparisons match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-control-flow-shifts-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-control-flow-shifts-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity indexed reference and function events plus dynamic custom errors match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-reference-events-errors-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-reference-events-errors-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity named events and custom errors match upstream argument ordering" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-named-events-errors-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-named-events-errors-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity creation and deployed internal-function dispatch match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-internal-dispatch-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-internal-dispatch-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity array, mapping, struct, bytes getters and calldata fallback match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-composite-getters-fallback-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-composite-getters-fallback-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity user-defined value-type operators match via-IR bytecode exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-udvt-operator-bytecode.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-udvt-operator-bytecode.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity body-type diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-body-type-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-body-type-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity using-for and user-defined operator diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-using-operator-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-using-operator-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity TypeChecker boundary diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-typechecker-boundaries.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-typechecker-boundaries.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity TypeChecker historical EVM gates match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-typechecker-evm-version.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-typechecker-evm-version.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity storage-only member diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-member-special-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-member-special-error.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "valid via-IR Solidity clears implemented frontend semantic phases" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/via-ir-smoke.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/via-ir-smoke.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity using directives and function-typed state variables match solc AST" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-using-ast.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-using-ast.json"),
        output.bytes,
    );
}

test "Solidity inline assembly embeds the exact parsed Yul AST" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-inline-assembly-ast.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-inline-assembly-ast.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Solidity inline assembly parser diagnostics match solc exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-inline-assembly-error.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-inline-assembly-error.json"),
        output.bytes,
    );
}

test "Solidity SPDX warning is emitted by the parser with exact framing" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Solidity","sources":{"C.sol":{"content":"contract C {}"}},"settings":{"stopAfter":"parsing"}}
        ,
    });
    defer output.deinit();

    const expected =
        "{\"errors\":[{\"component\":\"general\",\"errorCode\":\"1878\",\"formattedMessage\":\"Warning: SPDX license identifier not provided in source file. Before publishing, consider adding a comment containing \\\"SPDX-License-Identifier: <SPDX-License>\\\" to each source file. Use \\\"SPDX-License-Identifier: UNLICENSED\\\" for non-open-source code. Please see https://spdx.org for more information.\\n--> C.sol\\n\\n\",\"message\":\"SPDX license identifier not provided in source file. Before publishing, consider adding a comment containing \\\"SPDX-License-Identifier: <SPDX-License>\\\" to each source file. Use \\\"SPDX-License-Identifier: UNLICENSED\\\" for non-open-source code. Please see https://spdx.org for more information.\",\"severity\":\"warning\",\"sourceLocation\":{\"end\":-1,\"file\":\"C.sol\",\"start\":-1},\"type\":\"Warning\"}],\"sources\":{\"C.sol\":{\"id\":0}}}\n";
    try standard_json.compareExact(expected, output.bytes);
}

test "ordinary via-IR orchestration artifacts match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-orchestration-artifacts.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-orchestration-artifacts.json"),
        output.bytes,
    );
}

test "via-IR assembly artifacts match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-assembly-artifacts.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-assembly-artifacts.json"),
        output.bytes,
    );
}

test "remapped imports and compilation-wide AST IDs match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-remapped-import.json"),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-remapped-import.json"),
        output.bytes,
    );
}

const SolidityImportLoader = struct {
    calls: usize = 0,

    fn read(
        opaque_context: ?*anyopaque,
        allocator: std.mem.Allocator,
        kind: []const u8,
        path: []const u8,
    ) standard_json.SourceReadError!standard_json.SourceReadResult {
        const self: *SolidityImportLoader = @ptrCast(@alignCast(opaque_context orelse
            return error.InternalFailure));
        self.calls += 1;
        if (!std.mem.eql(u8, kind, "source") or !std.mem.eql(
            u8,
            path,
            "test/zig/standard-json/callback/CallbackDependency.sol",
        )) return .unsupported;
        return .{ .contents = try allocator.dupe(
            u8,
            @embedFile("standard-json/callback/CallbackDependency.sol"),
        ) };
    }
};

test "discovered Solidity imports use the host callback in upstream order" {
    var loader: SolidityImportLoader = .{};
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/solidity-callback-import.json"),
        .source_loader = .{
            .context = &loader,
            .read_fn = SolidityImportLoader.read,
        },
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-callback-import.json"),
        output.bytes,
    );
    try std.testing.expectEqual(@as(usize, 1), loader.calls);
}

test "valid Yul envelope compiles without requesting artifacts" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code {} }"}}}
        ,
    });
    defer output.deinit();

    try standard_json.compareExact("{\"errors\":[]}\n", output.bytes);
}

test "Yul Standard JSON artifacts match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/yul-basic.json"),
    });
    defer output.deinit();

    try std.testing.expectEqualStrings(
        @embedFile("standard-json/expected/yul-basic.json"),
        output.bytes,
    );
    try std.testing.expectEqual(solidity.execution.Backend.zig, output.execution.backend);
}

test "Yul Standard JSON diagnostics match solc 0.8.36 exactly" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = @embedFile("standard-json/yul-parser-error.json"),
    });
    defer output.deinit();

    try std.testing.expectEqualStrings(
        @embedFile("standard-json/expected/yul-parser-error.json"),
        output.bytes,
    );
}

test "Yul wildcard, optimizer, and deployed artifacts match solc 0.8.36" {
    const cases = [_]struct { input: []const u8, expected: []const u8 }{
        .{
            .input = @embedFile("standard-json/yul-wildcard.json"),
            .expected = @embedFile("standard-json/expected/yul-wildcard.json"),
        },
        .{
            .input = @embedFile("standard-json/yul-optimized.json"),
            .expected = @embedFile("standard-json/expected/yul-optimized.json"),
        },
        .{
            .input = @embedFile("standard-json/yul-deployed.json"),
            .expected = @embedFile("standard-json/expected/yul-deployed.json"),
        },
    };
    for (cases) |case| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{
            .input = case.input,
        });
        defer output.deinit();
        try std.testing.expectEqualStrings(case.expected, output.bytes);
    }
}

test "Yul link references and configured libraries match solc 0.8.36" {
    const cases = [_]struct { input: []const u8, expected: []const u8 }{
        .{
            .input = @embedFile("standard-json/yul-unlinked.json"),
            .expected = @embedFile("standard-json/expected/yul-unlinked.json"),
        },
        .{
            .input = @embedFile("standard-json/yul-linked.json"),
            .expected = @embedFile("standard-json/expected/yul-linked.json"),
        },
    };
    for (cases) |case| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{
            .input = case.input,
        });
        defer output.deinit();
        try std.testing.expectEqualStrings(case.expected, output.bytes);
    }
}

const YulLoaderState = struct {
    calls: usize = 0,

    fn read(
        opaque_context: ?*anyopaque,
        allocator: std.mem.Allocator,
        kind: []const u8,
        data: []const u8,
    ) standard_json.SourceReadError!standard_json.SourceReadResult {
        const context: *YulLoaderState = @ptrCast(@alignCast(opaque_context orelse
            return error.InternalFailure));
        context.calls += 1;
        if (!std.mem.eql(u8, kind, "source") or !std.mem.eql(u8, data, "A.yul"))
            return .unsupported;
        return .{ .contents = try allocator.dupe(u8, "object \"A\" { code { stop() } }") };
    }
};

test "URL-loaded Yul contents survive the callback result lifetime" {
    var loader_state: YulLoaderState = .{};
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Yul","sources":{"A.yul":{"urls":["A.yul"]}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
        ,
        .source_loader = .{ .context = &loader_state, .read_fn = YulLoaderState.read },
    });
    defer output.deinit();

    try std.testing.expectEqualStrings(
        "{\"contracts\":{\"A.yul\":{\"A\":{\"evm\":{\"bytecode\":{\"object\":\"00\"}}}}},\"errors\":[]}\n",
        output.bytes,
    );
    try std.testing.expectEqual(@as(usize, 1), loader_state.calls);
}

test "experimental Yul backends fail explicitly without semantic substitution" {
    const cases = [_]struct { input: []const u8, message: []const u8 }{
        .{
            .input =
            \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code {} }"}},"settings":{"experimental":true,"viaSSACFG":true}}
            ,
            .message = "Zig port: experimental Yul SSA-CFG code generation is not implemented.",
        },
        .{
            .input =
            \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code {} }"}},"settings":{"experimental":true,"debug":{"debugInfo":["ethdebug"]}}}
            ,
            .message = "Zig port: ethdebug output is not implemented.",
        },
        .{
            .input =
            \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code {} }"}},"settings":{"experimental":true,"outputSelection":{"*":{"*":["yulCFGJson"]}}}}
            ,
            .message = "Zig port: experimental Yul CFG JSON output is not implemented.",
        },
    };
    for (cases) |case| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{ .input = case.input });
        defer output.deinit();
        try std.testing.expect(std.mem.find(u8, output.bytes, case.message) != null);
        try std.testing.expect(std.mem.find(u8, output.bytes, "UnimplementedFeatureError") != null);
    }
}

test "experimental Solidity backends fail explicitly without semantic substitution" {
    const cases = [_]struct { input: []const u8, message: []const u8 }{
        .{
            .input =
            \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"experimental":true,"viaIR":true,"viaSSACFG":true}}
            ,
            .message = "Zig port: experimental Solidity SSA-CFG code generation is not implemented.",
        },
        .{
            .input =
            \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"experimental":true,"viaIR":true,"debug":{"debugInfo":["ethdebug"]}}}
            ,
            .message = "Zig port: ethdebug output is not implemented.",
        },
        .{
            .input =
            \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"experimental":true,"viaIR":true,"outputSelection":{"*":{"*":["irAst"]}}}}
            ,
            .message = "Zig port: experimental Solidity IR AST output is not implemented.",
        },
        .{
            .input =
            \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"experimental":true,"viaIR":true,"outputSelection":{"*":{"*":["yulCFGJson"]}}}}
            ,
            .message = "Zig port: experimental Solidity Yul CFG JSON output is not implemented.",
        },
    };
    for (cases) |case| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{ .input = case.input });
        defer output.deinit();
        const expected = try std.fmt.allocPrint(
            std.testing.allocator,
            "{{\"errors\":[{{\"component\":\"general\",\"formattedMessage\":\"{s}\",\"message\":\"{s}\",\"severity\":\"error\",\"type\":\"UnimplementedFeatureError\"}}]}}\n",
            .{ case.message, case.message },
        );
        defer std.testing.allocator.free(expected);
        try standard_json.compareExact(expected, output.bytes);
    }
}

test "unsupported Standard JSON languages have a stable response" {
    const inputs = [_][]const u8{
        "{\"language\":\"Vyper\",\"sources\":{\"A.vy\":{\"content\":\"\"}}}",
        "{\"language\":\"SolidityAST\",\"sources\":{\"A.json\":{\"content\":\"{}\"}}}",
        "{\"language\":\"EVMAssembly\",\"sources\":{\"A.json\":{\"content\":\"{}\"}}}",
    };
    for (inputs) |input| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{ .input = input });
        defer output.deinit();
        try standard_json.compareExact(libsolc.responses.invalid_envelope, output.bytes);
    }
}

const LoaderState = struct {
    calls: usize = 0,
    saw_expected_kind: bool = false,
    saw_loaded_url: bool = false,

    fn read(
        opaque_context: ?*anyopaque,
        allocator: std.mem.Allocator,
        kind: []const u8,
        data: []const u8,
    ) standard_json.SourceReadError!standard_json.SourceReadResult {
        const context: *LoaderState = @ptrCast(@alignCast(opaque_context orelse {
            return error.InternalFailure;
        }));
        context.calls += 1;
        context.saw_expected_kind = context.saw_expected_kind or
            std.mem.eql(u8, kind, "source");

        if (std.mem.eql(u8, data, "missing.sol")) {
            return .{ .failure = try allocator.dupe(u8, "not found") };
        }
        if (std.mem.eql(u8, data, "A.sol")) {
            context.saw_loaded_url = true;
            return .{ .contents = try allocator.dupe(u8, "contract A {}") };
        }
        return .unsupported;
    }
};

const RecordingLoaderState = struct {
    calls: usize = 0,
    order: [8]u8 = undefined,

    fn read(
        opaque_context: ?*anyopaque,
        allocator: std.mem.Allocator,
        _: []const u8,
        data: []const u8,
    ) standard_json.SourceReadError!standard_json.SourceReadResult {
        const context: *RecordingLoaderState = @ptrCast(@alignCast(opaque_context orelse {
            return error.InternalFailure;
        }));
        if (context.calls == context.order.len) return error.InternalFailure;
        context.order[context.calls] = if (data.len == 0) '?' else data[0];
        context.calls += 1;
        return .{ .contents = try allocator.dupe(u8, "") };
    }

    fn loader(self: *RecordingLoaderState) standard_json.SourceLoader {
        return .{ .context = self, .read_fn = read };
    }
};

test "URL callbacks consume and release owned failure and content results" {
    var loader_state: LoaderState = .{};
    const loader: standard_json.SourceLoader = .{
        .context = &loader_state,
        .read_fn = LoaderState.read,
    };
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Solidity","sources":{"A.sol":{"urls":["missing.sol","A.sol"]}}}
        ,
        .source_loader = loader,
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-source-success.json"),
        output.bytes,
    );
    try std.testing.expectEqual(@as(usize, 2), loader_state.calls);
    try std.testing.expect(loader_state.saw_expected_kind);
    try std.testing.expect(loader_state.saw_loaded_url);
}

test "source callbacks follow nlohmann lexicographic object order" {
    var loader_state: RecordingLoaderState = .{};
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Solidity","sources":{"Z.sol":{"urls":["z.url"]},"A.sol":{"urls":["a.url"]}}}
        ,
        .source_loader = loader_state.loader(),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-two-empty-sources-success.json"),
        output.bytes,
    );
    try std.testing.expectEqualStrings("az", loader_state.order[0..loader_state.calls]);
}

test "unknown root and source keys are rejected before callbacks" {
    const inputs = [_][]const u8{
        \\{"language":"Solidity","unknown":true,"sources":{"A.sol":{"urls":["a.url"]}}}
        ,
        \\{"language":"Solidity","sources":{"A.sol":{"urls":["a.url"]},"Z.sol":{"content":"","unknown":true}}}
        ,
    };
    for (inputs) |input| {
        var loader_state: RecordingLoaderState = .{};
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{
            .input = input,
            .source_loader = loader_state.loader(),
        });
        defer output.deinit();

        try standard_json.compareExact(libsolc.responses.invalid_envelope, output.bytes);
        try std.testing.expectEqual(@as(usize, 0), loader_state.calls);
    }
}

test "duplicate object members use the last value" {
    const inputs = [_][]const u8{
        \\{"language":"Vyper","language":"Solidity","sources":{"A.sol":{"urls":["a.url"]}},"sources":{"A.sol":{"content":""}}}
        ,
        \\{"language":"Solidity","sources":{"A.sol":{"urls":["a.url"]},"A.sol":{"content":""}}}
        ,
    };
    for (inputs) |input| {
        var loader_state: RecordingLoaderState = .{};
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{
            .input = input,
            .source_loader = loader_state.loader(),
        });
        defer output.deinit();

        try standard_json.compareExact(
            @embedFile("standard-json/expected/solidity-source-success.json"),
            output.bytes,
        );
        try std.testing.expectEqual(@as(usize, 0), loader_state.calls);
    }
}

test "duplicate source fields select the last URL array" {
    var loader_state: RecordingLoaderState = .{};
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Solidity","sources":{"A.sol":{"urls":["bad.url"],"urls":["good.url"]}}}
        ,
        .source_loader = loader_state.loader(),
    });
    defer output.deinit();

    try standard_json.compareExact(
        @embedFile("standard-json/expected/solidity-source-success.json"),
        output.bytes,
    );
    try std.testing.expectEqualStrings("g", loader_state.order[0..loader_state.calls]);
}

test "missing and null sources retain the no-input result" {
    const inputs = [_][]const u8{
        \\{}
        ,
        \\{"language":"Solidity","sources":null}
        ,
    };
    for (inputs) |input| {
        var dispatcher: libsolc.Dispatcher = .{};
        var output = try dispatcher.compiler().compile(std.testing.allocator, .{
            .input = input,
        });
        defer output.deinit();

        try standard_json.compareExact(libsolc.responses.no_input_sources, output.bytes);
    }
}

test "URL sources without a loader remain explicit" {
    var dispatcher: libsolc.Dispatcher = .{};
    var output = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input =
        \\{"language":"Solidity","sources":{"A.sol":{"urls":["A.sol"]}}}
        ,
    });
    defer output.deinit();

    try standard_json.compareExact(
        libsolc.responses.source_callback_unsupported,
        output.bytes,
    );
}

fn outOfMemoryLoader(
    _: ?*anyopaque,
    _: std.mem.Allocator,
    _: []const u8,
    _: []const u8,
) standard_json.SourceReadError!standard_json.SourceReadResult {
    return error.OutOfMemory;
}

test "source callback allocation failure propagates" {
    var dispatcher: libsolc.Dispatcher = .{};
    try std.testing.expectError(error.OutOfMemory, dispatcher.compiler().compile(
        std.testing.allocator,
        .{
            .input =
            \\{"language":"Solidity","sources":{"A.sol":{"urls":["A.sol"]}}}
            ,
            .source_loader = .{
                .context = null,
                .read_fn = outOfMemoryLoader,
            },
        },
    ));
}

const parallel_solidity_input =
    \\{"language":"Solidity","sources":{"Parallel.sol":{"content":"pragma solidity 0.8.36; contract A { function value(uint256 x) external pure returns (uint256) { return x + 1; } } contract B { function value(uint256 x) external pure returns (uint256) { return x * 2; } } contract C { function value(uint256 x) external pure returns (uint256) { return x - 1; } }"}},"settings":{"viaIR":true,"optimizer":{"enabled":true,"runs":200},"outputSelection":{"*":{"*":["abi","metadata","evm.methodIdentifiers","evm.bytecode.object","evm.deployedBytecode.object"]}}}}
;

fn compileWithParallelJobs(
    allocator: std.mem.Allocator,
    input: []const u8,
    jobs: usize,
    profiler: ?*Profiler,
    progress: ?standard_json.ProgressReporter,
    object_optimizer: ?*ObjectOptimizer,
) standard_json.CompileError!standard_json.Output {
    std.debug.assert(jobs != 0);
    var threaded = std.Io.Threaded.init(std.heap.smp_allocator, .{
        .async_limit = .limited(jobs - 1),
    });
    defer threaded.deinit();
    var dispatcher: libsolc.Dispatcher = .{ .optimizer_profiler = profiler };
    const request: standard_json.Request = .{
        .input = input,
        .io = threaded.io(),
        .progress = progress,
    };
    return if (object_optimizer) |optimizer|
        dispatcher.compileWithObjectOptimizer(allocator, request, optimizer)
    else
        dispatcher.compiler().compile(allocator, request);
}

test "parallel single-worker and multi-worker output matches sequential output" {
    var dispatcher: libsolc.Dispatcher = .{};
    var sequential = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = parallel_solidity_input,
    });
    defer sequential.deinit();

    var single_worker = try compileWithParallelJobs(
        std.testing.allocator,
        parallel_solidity_input,
        1,
        null,
        null,
        null,
    );
    defer single_worker.deinit();
    var object_optimizer = ObjectOptimizer.init(std.testing.allocator);
    defer object_optimizer.deinit();
    var multi_worker = try compileWithParallelJobs(
        std.testing.allocator,
        parallel_solidity_input,
        4,
        null,
        null,
        &object_optimizer,
    );
    defer multi_worker.deinit();

    try standard_json.compareExact(sequential.bytes, single_worker.bytes);
    try standard_json.compareExact(sequential.bytes, multi_worker.bytes);
    try std.testing.expect(object_optimizer.statistics().optimization_runs >= 3);
}

test "parallel multi-worker output is deterministic across fresh backends" {
    var dispatcher: libsolc.Dispatcher = .{};
    var expected = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = parallel_solidity_input,
    });
    defer expected.deinit();

    for (0..4) |_| {
        var output = try compileWithParallelJobs(
            std.testing.allocator,
            parallel_solidity_input,
            4,
            null,
            null,
            null,
        );
        defer output.deinit();
        try standard_json.compareExact(expected.bytes, output.bytes);
    }
}

test "parallel progress and optimizer profiling retain parallel output" {
    var dispatcher: libsolc.Dispatcher = .{};
    var expected = try dispatcher.compiler().compile(std.testing.allocator, .{
        .input = parallel_solidity_input,
    });
    defer expected.deinit();

    var recorder: ProgressRecorder = .{};
    var profiler = Profiler.init(std.testing.allocator, std.testing.io);
    defer profiler.deinit();
    var output = try compileWithParallelJobs(
        std.testing.allocator,
        parallel_solidity_input,
        4,
        &profiler,
        recorder.reporter(),
        null,
    );
    defer output.deinit();

    try standard_json.compareExact(expected.bytes, output.bytes);
    try std.testing.expect(recorder.sawStage(.generating_contracts));
    try std.testing.expect(recorder.saw_contract_a);
    try std.testing.expect(recorder.generating_monotonic);
    try std.testing.expectEqual(@as(usize, 3), recorder.generating_completed);
    try std.testing.expectEqual(@as(usize, 3), recorder.generating_total);
    for ([_][]const u8{
        "Solidity via-IR artifacts",
        "Solidity IR generation",
        "Yul preparation and analysis",
        "Yul optimizer total",
        "Yul assembly",
    }) |metric_name|
        try std.testing.expect(profiler.metricsFor(metric_name) != null);
    // Compilation has already destroyed generated owners and worker scratch.
    // The profile retains scalar observations, never pointers into those arenas.
    for ([_][]const u8{
        "Generated Yul owner retained bytes",
        "Backend worker scratch retained bytes",
        "Backend worker artifact retained bytes",
    }) |counter_name| {
        const counter = profiler.counterFor(counter_name) orelse return error.MissingRetentionCounter;
        try std.testing.expectEqual(@as(usize, 3), counter.sample_count);
        try std.testing.expect(counter.maximum > 0);
        try std.testing.expect(counter.total >= counter.maximum);
    }
    const report = try profiler.reportJsonAlloc(std.testing.allocator);
    defer std.testing.allocator.free(report);
}

const WorkerFailAllocator = struct {
    const Self = @This();

    child: std.mem.Allocator,
    main_thread: std.Thread.Id,
    remaining_worker_allocations: usize,
    failed: bool = false,
    mutex: std.Io.Mutex = .init,

    fn init(child: std.mem.Allocator, remaining_worker_allocations: usize) Self {
        return .{
            .child = child,
            .main_thread = std.Thread.getCurrentId(),
            .remaining_worker_allocations = remaining_worker_allocations,
        };
    }

    fn allocator(self: *Self) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(
        opaque_self: *anyopaque,
        len: usize,
        alignment: std.mem.Alignment,
        return_address: usize,
    ) ?[*]u8 {
        const self: *Self = @ptrCast(@alignCast(opaque_self));
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        if (std.Thread.getCurrentId() != self.main_thread and !self.failed) {
            if (self.remaining_worker_allocations == 0) {
                self.failed = true;
                return null;
            }
            self.remaining_worker_allocations -= 1;
        }
        return self.child.rawAlloc(len, alignment, return_address);
    }

    fn resize(
        opaque_self: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_len: usize,
        return_address: usize,
    ) bool {
        const self: *Self = @ptrCast(@alignCast(opaque_self));
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        return self.child.rawResize(memory, alignment, new_len, return_address);
    }

    fn remap(
        opaque_self: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_len: usize,
        return_address: usize,
    ) ?[*]u8 {
        const self: *Self = @ptrCast(@alignCast(opaque_self));
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        return self.child.rawRemap(memory, alignment, new_len, return_address);
    }

    fn free(
        opaque_self: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        return_address: usize,
    ) void {
        const self: *Self = @ptrCast(@alignCast(opaque_self));
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        self.child.rawFree(memory, alignment, return_address);
    }
};

test "parallel worker allocation failures propagate after outstanding jobs join" {
    for ([_]bool{ false, true }) |profile_enabled|
        for ([_]usize{ 0, 8 }) |successful_worker_allocations| {
            var failing = WorkerFailAllocator.init(
                std.testing.allocator,
                successful_worker_allocations,
            );
            var profiler = Profiler.init(std.testing.allocator, std.testing.io);
            defer profiler.deinit();
            try std.testing.expectError(
                error.OutOfMemory,
                compileWithParallelJobs(
                    failing.allocator(),
                    parallel_solidity_input,
                    2,
                    if (profile_enabled) &profiler else null,
                    null,
                    null,
                ),
            );
            try std.testing.expect(failing.failed);
            if (profile_enabled) {
                const counter = profiler.counterFor("Backend worker scratch retained bytes") orelse return error.MissingRetentionCounter;
                try std.testing.expect(counter.sample_count > 0);
                const report = try profiler.reportJsonAlloc(std.testing.allocator);
                defer std.testing.allocator.free(report);
            }
        };
}
