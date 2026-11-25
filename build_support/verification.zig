// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Opt-in observations of production compiler operations for independent Lean proofs.
const std = @import("std");
const CompilerIdentity = @import("compiler_identity.zig");

pub const Options = struct {
    target: std.Build.ResolvedTarget,
    optimize: std.lang.Optimize,
    big_int: *std.Build.Module,
    build_options: *std.Build.Module,
    identity: CompilerIdentity.BuildIdentity,
};

pub fn add(b: *std.Build, options: Options) void {
    const Adapter = struct {
        name: []const u8,
        file: []const u8,
        description: []const u8,
        filter: ?[]const u8 = null,
        word_imports: bool = false,
    };
    const adapters = [_]Adapter{
        .{
            .name = "compiler-rules-export",
            .file = "src/compiler_rules_export.zig",
            .description = "Export production algebraic rules and opcode map for Lean kernel verification",
        },
        .{
            .name = "compiler-graph-export",
            .file = "src/compiler_graph_export.zig",
            .description = "Export production ExpressionClasses DAGs and cache inventories for Lean translation validation",
            .filter = "graph export",
        },
        .{
            .name = "compiler-word-export",
            .file = "src/compiler_word_export.zig",
            .description = "Assemble admitted source word expressions for Lean EVM bytecode validation",
            .filter = "word export",
            .word_imports = true,
        },
    };
    for (adapters) |adapter| {
        const module = b.createModule(.{
            .root_source_file = b.path(adapter.file),
            .target = options.target,
            .optimize = options.optimize,
            .imports = if (adapter.word_imports) &.{
                .{ .name = "big_int", .module = options.big_int },
                .{ .name = "build_options", .module = options.build_options },
            } else &.{},
        });
        const executable = b.addExecutable(.{ .name = adapter.name, .root_module = module });
        const install = b.addInstallArtifact(executable, .{});
        if (options.identity.validate(b, executable)) |validation|
            install.step.dependOn(validation);
        b.step(b.fmt("build-{s}", .{adapter.name}), adapter.description).dependOn(&install.step);
        if (adapter.filter) |filter| {
            const tests = b.addTest(.{ .root_module = module, .filters = &.{filter} });
            tests.stack_size = 32 * 1024 * 1024;
            const run = b.addRunArtifact(tests);
            if (options.identity.validate(b, tests)) |validation|
                run.step.dependOn(validation);
            b.step(b.fmt("test-{s}", .{adapter.name}), adapter.description).dependOn(&run.step);
        }
    }
}
