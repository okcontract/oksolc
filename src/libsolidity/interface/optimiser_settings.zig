// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Header-only optimizer settings shared by Solidity orchestration and Yul.

const std = @import("std");
const Assembly = @import("../../libevmasm/assembly.zig");

pub const default_yul_optimiser_steps =
    "dfDvulfnTUtnIf" ++
    "xa[r]EscLM" ++
    "Vcul [j]" ++
    "Trpeul" ++
    "xa[r]cL" ++
    "vifM" ++
    "CTUca[r]LSsTFOtfDnca[r]Iulc" ++
    "scCTUt" ++
    "vifM" ++
    "x[scCTUt] TOntnfDIul" ++
    "vifM" ++
    "jmul[jul] VcTOcul jmul";

pub const default_yul_optimiser_cleanup_steps = "fDnTOcmuO";

pub const OptimisationPreset = enum(c_int) {
    none,
    minimal,
    standard,
    full,
};

pub const OptimiserSettings = struct {
    pub const DefaultYulOptimiserSteps = default_yul_optimiser_steps;
    pub const DefaultYulOptimiserCleanupSteps = default_yul_optimiser_cleanup_steps;
    pub const ExecutionCount = u64;

    run_order_literals: bool = false,
    run_inliner: bool = false,
    run_jumpdest_remover: bool = false,
    run_peephole: bool = false,
    run_deduplicate: bool = false,
    run_cse: bool = false,
    run_constant_optimiser: bool = false,
    simple_counter_for_loop_unchecked_increment: bool = false,
    optimize_stack_allocation: bool = false,
    run_yul_optimiser: bool = false,
    yul_optimiser_steps: []const u8 = default_yul_optimiser_steps,
    yul_optimiser_cleanup_steps: []const u8 = default_yul_optimiser_cleanup_steps,
    expected_executions_per_deployment: ExecutionCount = 200,

    pub fn none() OptimiserSettings {
        return .{};
    }

    pub fn minimal() OptimiserSettings {
        var result = none();
        result.run_jumpdest_remover = true;
        result.run_peephole = true;
        result.simple_counter_for_loop_unchecked_increment = true;
        return result;
    }

    pub fn standard() OptimiserSettings {
        var result: OptimiserSettings = .{};
        result.run_order_literals = true;
        result.run_inliner = true;
        result.run_jumpdest_remover = true;
        result.run_peephole = true;
        result.run_deduplicate = true;
        result.run_cse = true;
        result.run_constant_optimiser = true;
        result.simple_counter_for_loop_unchecked_increment = true;
        result.run_yul_optimiser = true;
        result.optimize_stack_allocation = true;
        return result;
    }

    pub fn full() OptimiserSettings {
        return standard();
    }

    pub fn preset(value: OptimisationPreset) OptimiserSettings {
        return switch (value) {
            .none => none(),
            .minimal => minimal(),
            .standard => standard(),
            .full => full(),
        };
    }

    pub fn eql(self: OptimiserSettings, other: OptimiserSettings) bool {
        return self.run_order_literals == other.run_order_literals and
            self.run_inliner == other.run_inliner and
            self.run_jumpdest_remover == other.run_jumpdest_remover and
            self.run_peephole == other.run_peephole and
            self.run_deduplicate == other.run_deduplicate and
            self.run_cse == other.run_cse and
            self.run_constant_optimiser == other.run_constant_optimiser and
            self.simple_counter_for_loop_unchecked_increment == other.simple_counter_for_loop_unchecked_increment and
            self.optimize_stack_allocation == other.optimize_stack_allocation and
            self.run_yul_optimiser == other.run_yul_optimiser and
            std.mem.eql(u8, self.yul_optimiser_steps, other.yul_optimiser_steps) and
            std.mem.eql(u8, self.yul_optimiser_cleanup_steps, other.yul_optimiser_cleanup_steps) and
            self.expected_executions_per_deployment == other.expected_executions_per_deployment;
    }

    pub fn assemblySettings(self: OptimiserSettings) Assembly.OptimiserSettings {
        return .{
            .run_inliner = self.run_inliner,
            .run_jumpdest_remover = self.run_jumpdest_remover,
            .run_peephole = self.run_peephole,
            .run_deduplicate = self.run_deduplicate,
            .run_cse = self.run_cse,
            .run_constant_optimiser = self.run_constant_optimiser,
            .expected_executions_per_deployment = self.expected_executions_per_deployment,
        };
    }
};

test "optimizer presets and assembly projection preserve upstream defaults" {
    const none_value = OptimiserSettings.none();
    const minimal_value = OptimiserSettings.minimal();
    const standard_value = OptimiserSettings.standard();
    try std.testing.expect(!none_value.run_yul_optimiser);
    try std.testing.expect(minimal_value.run_peephole);
    try std.testing.expect(!minimal_value.run_yul_optimiser);
    try std.testing.expect(standard_value.run_yul_optimiser);
    try std.testing.expect(standard_value.optimize_stack_allocation);
    try std.testing.expect(standard_value.eql(OptimiserSettings.full()));
    try std.testing.expectEqual(@as(u64, 200), standard_value.assemblySettings().expected_executions_per_deployment);
    try std.testing.expectEqualStrings(default_yul_optimiser_steps, standard_value.yul_optimiser_steps);
}
