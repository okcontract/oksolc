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
    /// Reuse ordinary pass storage without carrying an unusually large pass's
    /// entire arena through every subsequent pass and nested object.
    pub const scratch_retention_limit: usize = 8 * 1024 * 1024;

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

    /// Branch snapshots have many shorter lifetimes within one pass. Bypass
    /// the pass arena so its backing allocator can reclaim them individually.
    pub fn scratchBackingAllocator(self: *const @This()) std.mem.Allocator {
        const arena = self.scratch_arena orelse return self.dispenser.allocator;
        return arena.child_allocator;
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
        resetScratchArena(arena);
    }

    pub fn resetScratchArena(arena: *std.heap.ArenaAllocator) void {
        // Retention is optional. A failed shrink can leave the previous large
        // allocation alive, so release it rather than exceeding the bound.
        if (!arena.reset(.{ .retain_with_limit = scratch_retention_limit }))
            _ = arena.reset(.free_all);
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

test "function analysis cache owns results separately from recursive graph scratch" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const Parser = @import("../asm_parser.zig").Parser;
    const YulName = @import("../yul_name.zig").YulName;
    const Encoding = @import("../ast_encoding.zig");
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator,
        \\{ left() single() looped()
        \\  function left() { right() }
        \\  function right() { left() sstore(0, 1) }
        \\  function single() { single() }
        \\  function looped() { for {} 1 {} {} }
        \\  function leaf() { pop(1) }
        \\}
    , "recursive-cache-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer ast.deinit();
    const before = try Encoding.hashBlock(ast.root());
    const Check = struct {
        fn run(failing: std.mem.Allocator, input: *const AST.AST) !void {
            var scratch = std.heap.ArenaAllocator.init(failing);
            defer scratch.deinit();
            var cache = FunctionAnalysisCache.init(failing);
            defer cache.deinit();
            const first = cache.get(scratch.allocator(), input.dialect().*, input.root()) catch |err| {
                try std.testing.expect(cache.ast == null);
                try std.testing.expect(cache.side_effects == null);
                return err;
            };
            try std.testing.expect(!first.reused);
            _ = scratch.reset(.free_all);
            for ([_][]const u8{ "left", "right", "single", "looped" }) |name| {
                const effects = first.side_effects.get(.{ .user = try YulName.init(name) }).?;
                try std.testing.expect(!effects.cannot_loop);
            }
            try std.testing.expect(first.side_effects.get(.{ .user = try YulName.init("leaf") }).?.cannot_loop);
            try std.testing.expectEqual(.write, first.side_effects.get(.{ .user = try YulName.init("left") }).?.storage);
            const second = try cache.get(scratch.allocator(), input.dialect().*, input.root());
            try std.testing.expect(second.reused);
            try std.testing.expectEqual(first.side_effects, second.side_effects);
            cache.invalidate();
            try std.testing.expect(cache.ast == null);
            try std.testing.expect(cache.side_effects == null);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{&ast});
    try std.testing.expectEqualDeep(before, try Encoding.hashBlock(ast.root()));
}

test "optimizer scratch retention remains bounded after large passes" {
    const allocator = std.testing.allocator;
    var scratch = std.heap.ArenaAllocator.init(allocator);
    defer scratch.deinit();
    var reserved: NameCollectorModule.NameSet = .{};
    defer reserved.deinit(allocator);
    const ast: AST.Block = .{};
    var dispenser = try NameDispenser.initFromAst(allocator, .{}, &ast, &reserved);
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = .{},
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
        .scratch_arena = &scratch,
    };
    for ([_]usize{ 64, 2 * OptimiserStepContext.scratch_retention_limit, 128 }) |size| {
        const bytes = try context.scratchAllocator().alloc(u8, size);
        @memset(bytes, 0xab);
        context.resetScratch("test");
        try std.testing.expect(scratch.queryCapacity() <= OptimiserStepContext.scratch_retention_limit);
        const after = try context.scratchAllocator().alloc(u8, 1);
        after[0] = 0xcd;
        try std.testing.expectEqual(@as(u8, 0xcd), after[0]);
    }

    var failing = std.testing.FailingAllocator.init(allocator, .{});
    var failed_scratch = std.heap.ArenaAllocator.init(failing.allocator());
    defer failed_scratch.deinit();
    _ = try failed_scratch.allocator().alloc(u8, 2 * OptimiserStepContext.scratch_retention_limit);
    failing.fail_index = failing.alloc_index;
    failing.resize_fail_index = failing.resize_index;
    OptimiserStepContext.resetScratchArena(&failed_scratch);
    try std.testing.expect(failing.has_induced_failure);
    try std.testing.expectEqual(@as(usize, 0), failed_scratch.queryCapacity());
}
