// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Type-erased optimizer-step dispatch and the shared execution context.

const std = @import("std");
const AST = @import("../ast.zig");
const CallGraphModule = @import("call_graph_generator.zig");
const NameCollectorModule = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const Profiler = @import("../../libsolutil/profiler.zig").Profiler;
const Semantics = @import("semantics.zig");

/// Reuses function side-effect analysis across consecutive optimizer steps.
///
/// Cached data is keyed by AST root identity and stored in an owned arena. Since
/// an in-place AST mutation preserves that identity, callers must invalidate the
/// cache after any step that may change call or side-effect semantics. The call
/// graph used to build the cached result remains temporary scratch data.
///
/// A cache belongs to one optimizer suite and is not thread-safe. Pointers
/// returned by `get` remain valid only until invalidation or deinitialization.
pub const FunctionAnalysisCache = struct {
    const Lookup = struct {
        side_effects: *const Semantics.FunctionSideEffects,
        reused: bool,
    };

    arena: std.heap.ArenaAllocator,
    ast: ?*const AST.Block = null,
    side_effects: ?Semantics.FunctionSideEffects = null,

    pub fn init(allocator: std.mem.Allocator) FunctionAnalysisCache {
        return .{ .arena = std.heap.ArenaAllocator.init(allocator) };
    }

    pub fn deinit(self: *FunctionAnalysisCache) void {
        self.arena.deinit();
        self.* = undefined;
    }

    pub fn invalidate(self: *FunctionAnalysisCache) void {
        if (self.ast == null) return;
        _ = self.arena.reset(.free_all);
        self.ast = null;
        self.side_effects = null;
    }

    pub fn get(
        self: *FunctionAnalysisCache,
        scratch_allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        ast: *const AST.Block,
    ) anyerror!Lookup {
        if (self.ast) |cached_ast|
            if (cached_ast != ast) self.invalidate();
        if (self.side_effects) |*side_effects|
            return .{ .side_effects = side_effects, .reused = true };

        var graph = try CallGraphModule.CallGraphGenerator.callGraph(scratch_allocator, ast);
        defer graph.deinit();
        self.side_effects = try Semantics.SideEffectsPropagator.sideEffects(
            self.arena.allocator(),
            dialect,
            &graph,
        );
        self.ast = ast;
        return .{ .side_effects = &self.side_effects.?, .reused = false };
    }
};

/// Scoped result of a function side-effect analysis request.
///
/// The cached form borrows side effects from `FunctionAnalysisCache`. The owned
/// form keeps the transient call graph and side effects allocated from the
/// optimizer step's scratch allocator when no cache is available. Call `deinit`
/// for both forms: it is a no-op for borrowed data and releases owned data.
/// Neither form may outlive cache invalidation or the corresponding scratch reset.
pub const FunctionAnalysis = union(enum) {
    const Owned = struct {
        allocator: std.mem.Allocator,
        graph: CallGraphModule.CallGraph,
        side_effects: Semantics.FunctionSideEffects,
    };

    cached: *const Semantics.FunctionSideEffects,
    owned: Owned,

    pub fn sideEffects(self: *const FunctionAnalysis) *const Semantics.FunctionSideEffects {
        return switch (self.*) {
            .cached => |side_effects| side_effects,
            .owned => |*owned| &owned.side_effects,
        };
    }

    pub fn deinit(self: *FunctionAnalysis) void {
        switch (self.*) {
            .cached => {},
            .owned => |*owned| {
                owned.side_effects.deinit(owned.allocator);
                owned.graph.deinit();
            },
        }
        self.* = undefined;
    }
};

pub const OptimiserStepContext = struct {
    dialect: AST.Dialect,
    dispenser: *NameDispenser,
    reserved_identifiers: *const NameCollectorModule.NameSet,
    expected_executions_per_deployment: ?usize = null,
    profiler: ?*Profiler = null,
    scratch_arena: ?*std.heap.ArenaAllocator = null,
    function_analysis_cache: ?*FunctionAnalysisCache = null,

    pub fn recordCounter(self: *const @This(), name: []const u8, value: u64) void {
        if (self.profiler) |profiler| profiler.recordCounter(name, value);
    }

    pub fn scratchAllocator(self: *const @This()) std.mem.Allocator {
        const arena = self.scratch_arena orelse return self.dispenser.allocator;
        return arena.allocator();
    }

    pub fn functionAnalysis(
        self: *const @This(),
        ast: *const AST.Block,
    ) anyerror!FunctionAnalysis {
        const scratch_allocator = self.scratchAllocator();
        if (self.function_analysis_cache) |cache| {
            const lookup = try cache.get(scratch_allocator, self.dialect, ast);
            self.recordCounter(
                if (lookup.reused)
                    "Optimizer function analysis cache hits"
                else
                    "Optimizer function analysis cache misses",
                1,
            );
            return .{ .cached = lookup.side_effects };
        }

        var graph = try CallGraphModule.CallGraphGenerator.callGraph(scratch_allocator, ast);
        errdefer graph.deinit();
        const side_effects = try Semantics.SideEffectsPropagator.sideEffects(
            scratch_allocator,
            self.dialect,
            &graph,
        );
        return .{ .owned = .{
            .allocator = scratch_allocator,
            .graph = graph,
            .side_effects = side_effects,
        } };
    }

    pub fn invalidateFunctionAnalysis(self: *@This()) void {
        if (self.function_analysis_cache) |cache| cache.invalidate();
    }

    pub fn resetScratch(self: *@This(), pass_name: []const u8) void {
        const arena = self.scratch_arena orelse return;
        if (self.profiler) |profiler| {
            profiler.recordCounter("Optimizer pass scratch capacity bytes", arena.queryCapacity());
            profiler.recordCounter(pass_name, arena.queryCapacity());
        }
        _ = arena.reset(.retain_capacity);
    }
};

pub const OptimiserStep = struct {
    instance: *const anyopaque,
    name: []const u8,
    vtable: *const VTable,

    pub const VTable = struct {
        run: *const fn (*const anyopaque, *OptimiserStepContext, *AST.Block) anyerror!void,
        invalid_in_current_environment: *const fn (*const anyopaque) ?[]const u8,
    };

    pub fn run(self: OptimiserStep, context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        return self.vtable.run(self.instance, context, ast);
    }

    pub fn invalidInCurrentEnvironment(self: OptimiserStep) ?[]const u8 {
        return self.vtable.invalid_in_current_environment(self.instance);
    }
};

pub fn OptimiserStepInstance(comptime Step: type) type {
    return struct {
        const Self = @This();

        pub fn optimiserStep(self: *const Self) OptimiserStep {
            return .{
                .instance = self,
                .name = Step.name,
                .vtable = &vtable,
            };
        }

        fn run(
            _: *const anyopaque,
            context: *OptimiserStepContext,
            ast: *AST.Block,
        ) anyerror!void {
            return Step.run(context, ast);
        }

        fn invalidInCurrentEnvironment(_: *const anyopaque) ?[]const u8 {
            if (@hasDecl(Step, "invalidInCurrentEnvironment"))
                return Step.invalidInCurrentEnvironment();
            return null;
        }

        const vtable: OptimiserStep.VTable = .{
            .run = run,
            .invalid_in_current_environment = invalidInCurrentEnvironment,
        };
    };
}

test "optimizer step instance dispatches through the erased interface" {
    const MockStep = struct {
        pub const name = "Mock";
        pub fn run(_: *OptimiserStepContext, ast: *AST.Block) !void {
            ast.debug_data = .{};
        }
    };
    const Instance = OptimiserStepInstance(MockStep);
    const instance: Instance = .{};
    const step = instance.optimiserStep();
    try @import("std").testing.expectEqualStrings("Mock", step.name);
    try @import("std").testing.expect(step.invalidInCurrentEnvironment() == null);
}
