// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Recursive lowering of analyzed Yul object/data trees into EVM assembly.
//!
//! Supports classic and optimized stack layouts. SSA-CFG code generation
//! returns `SSACFGBackendUnavailable`.

const std = @import("std");
const AbstractModule = @import("abstract_assembly.zig");
const BuiltinContext = @import("evm_builtins.zig").BuiltinContext;
const CodeTransformModule = @import("evm_code_transform.zig");
const EVMDialect = @import("evm_dialect.zig").EVMDialect;
const OptimizedTransformModule = @import("optimized_evm_code_transform.zig");
const ObjectModule = @import("../../object.zig");
const Object = ObjectModule.Object;
const AST = @import("../../ast.zig");
const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
const StackTooDeepError = @import("../../exceptions.zig").StackTooDeepError;
const FunctionCallFinder = @import("../../optimiser/function_call_finder.zig");

pub const EVMObjectCompiler = struct {
    pub fn compile(
        allocator: std.mem.Allocator,
        object: *Object,
        assembly: AbstractModule.AbstractAssembly,
        optimize: bool,
        via_ssa_cfg: bool,
    ) anyerror!void {
        return compileWithScratch(allocator, null, object, assembly, optimize, via_ssa_cfg);
    }

    /// The adapter owns emitted assembly. When supplied, the borrowed backing
    /// allocator gives each object an independent arena for backend temporaries;
    /// no graph, layout, lookup table or diagnostic survives this call. Child
    /// objects use the same backing allocator, never their parent's arena.
    /// Without one, preserve the caller's existing allocation policy.
    pub fn compileWithScratch(
        allocator: std.mem.Allocator,
        scratch_backing_allocator: ?std.mem.Allocator,
        object: *Object,
        assembly: AbstractModule.AbstractAssembly,
        optimize: bool,
        via_ssa_cfg: bool,
    ) anyerror!void {
        return compileWithDiagnostics(allocator, scratch_backing_allocator, object, assembly, optimize, via_ssa_cfg, null);
    }

    /// Copies diagnostic messages to the reporter before backend temporaries
    /// are destroyed. Locations borrow the input object's source table.
    pub fn compileWithDiagnostics(
        allocator: std.mem.Allocator,
        scratch_backing_allocator: ?std.mem.Allocator,
        object: *Object,
        assembly: AbstractModule.AbstractAssembly,
        optimize: bool,
        via_ssa_cfg: bool,
        reporter: ?*Diagnostics.ErrorReporter,
    ) anyerror!void {
        const dialect = try objectEVMDialect(object);
        if (optimize and dialect.evmVersion().canOverchargeGasForCall() and via_ssa_cfg)
            return error.SSACFGBackendUnavailable;
        var scratch_arena = if (scratch_backing_allocator) |backing|
            std.heap.ArenaAllocator.init(backing)
        else
            null;
        defer if (scratch_arena) |*arena| arena.deinit();
        var compiler: Compiler = .{
            .allocator = if (scratch_arena) |*arena| arena.allocator() else allocator,
            .scratch_backing_allocator = scratch_backing_allocator,
            .assembly = assembly,
            .reporter = reporter,
        };
        try compiler.run(object, optimize, via_ssa_cfg);
    }
};

const Compiler = struct {
    allocator: std.mem.Allocator,
    scratch_backing_allocator: ?std.mem.Allocator,
    assembly: AbstractModule.AbstractAssembly,
    reporter: ?*Diagnostics.ErrorReporter,

    fn run(self: *Compiler, object: *Object, optimize: bool, via_ssa_cfg: bool) anyerror!void {
        const dialect = try objectEVMDialect(object);
        var context = BuiltinContext.init(self.allocator);
        defer context.deinit();
        context.current_object = object;

        for (object.sub_objects.items) |*sub_node| switch (sub_node.*) {
            .object => |sub_object| {
                const is_creation = !std.mem.endsWith(u8, sub_object.name, "_deployed");
                const created = try self.assembly.createSubAssembly(is_creation, sub_object.name);
                try context.putSubId(sub_object.name, created.sub_id);
                sub_object.sub_id = created.sub_id;
                try EVMObjectCompiler.compileWithDiagnostics(
                    self.allocator,
                    self.scratch_backing_allocator,
                    sub_object,
                    created.assembly,
                    optimize,
                    via_ssa_cfg,
                    self.reporter,
                );
            },
            .data => |*data| {
                if (std.mem.eql(u8, data.name, Object.metadataName())) {
                    try self.assembly.appendToAuxiliaryData(data.data);
                } else {
                    try context.putSubId(data.name, try self.assembly.appendData(data.data));
                }
            },
        };

        const analysis_info = if (object.analysis_info != null)
            &object.analysis_info.?
        else
            return error.MissingAnalysisInfo;
        const code = object.code() orelse return error.MissingCode;
        if (optimize and dialect.evmVersion().canOverchargeGasForCall()) {
            var stack_errors = try OptimizedTransformModule.OptimizedEVMCodeTransform.run(
                self.allocator,
                self.assembly,
                analysis_info,
                code.root(),
                dialect,
                &context,
                .for_first_function_of_each_name,
            );
            defer OptimizedTransformModule.deinitStackErrors(self.allocator, &stack_errors);
            if (stack_errors.items.len != 0) {
                try self.reportStackError(&stack_errors.items[0], code.root(), dialect, true);
                return error.StackTooDeep;
            }
            return;
        }
        var transform = try CodeTransformModule.CodeTransform.init(
            self.allocator,
            self.assembly,
            analysis_info,
            code.root(),
            dialect,
            &context,
            optimize,
            .{},
            .for_first_function_of_each_name,
        );
        defer transform.deinit();
        try transform.apply(code.root());
        if (transform.stackErrors().len != 0) {
            try self.reportStackError(&transform.stackErrors()[0], code.root(), dialect, false);
            return error.StackTooDeep;
        }
    }

    fn reportStackError(
        self: *Compiler,
        stack_error: *const StackTooDeepError,
        code: *const AST.Block,
        dialect: *const EVMDialect,
        optimized: bool,
    ) !void {
        const reporter = self.reporter orelse return;
        const suffix = if (optimized) suffix: {
            const handle = dialect.dialect().findBuiltin("memoryguard") orelse
                return error.MissingMemoryGuardBuiltin;
            var calls = try FunctionCallFinder.findFunctionCallsConst(self.allocator, code, .{ .builtin = handle });
            defer calls.deinit(self.allocator);
            break :suffix if (calls.items.len == 0)
                "\nNo memoryguard was present. Consider using memory-safe assembly only and annotating it via 'assembly (\"memory-safe\") { ... }'."
            else
                "\nmemoryguard was present.";
        } else "";
        const message = try std.fmt.allocPrint(self.allocator, "{s}{s}", .{ stack_error.message, suffix });
        defer self.allocator.free(message);
        try reporter.report(.{ .value = 0 }, .YulException, stack_error.location, message);
    }
};

fn objectEVMDialect(object: *const Object) !*const EVMDialect {
    const dialect = object.dialect() orelse return error.MissingDialect;
    const context = dialect.context orelse return error.NonEVMDialect;
    return @ptrCast(@alignCast(context));
}

test "stack diagnostic messages survive backend scratch release and allocation failures" {
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const ObjectParser = @import("../../object_parser.zig").ObjectParser;
    const Check = struct {
        fn run(allocator: std.mem.Allocator, block: *const AST.Block, dialect: *const EVMDialect, optimized: bool, guarded: bool) !void {
            var reporter = Diagnostics.ErrorReporter.init(allocator);
            defer reporter.deinit();
            const location: Diagnostics.SourceLocation = .{ .start = 2, .end = 8, .source_name = "C.sol" };
            {
                var scratch = std.heap.ArenaAllocator.init(allocator);
                defer scratch.deinit();
                var compiler: Compiler = .{
                    .allocator = scratch.allocator(),
                    .scratch_backing_allocator = null,
                    .assembly = undefined, // Diagnostic publication does not use the adapter.
                    .reporter = &reporter,
                };
                var failure = try StackTooDeepError.init(scratch.allocator(), .{}, 2, "stack failure");
                defer failure.deinit();
                failure.location = location;
                try compiler.reportStackError(&failure, block, dialect, optimized);
            }
            try std.testing.expectEqual(@as(usize, 1), reporter.diagnostics().len);
            const diagnostic = reporter.diagnostics()[0];
            try std.testing.expect(diagnostic.location.?.eql(location));
            const expected = if (!optimized) "stack failure" else if (guarded)
                "stack failure\nmemoryguard was present."
            else
                "stack failure\nNo memoryguard was present. Consider using memory-safe assembly only and annotating it via 'assembly (\"memory-safe\") { ... }'.";
            try std.testing.expectEqualStrings(expected, diagnostic.description);
        }
    };
    var dialect = try EVMDialect.init(std.testing.allocator, EVMVersion.current(), true);
    defer dialect.deinit();
    for ([_]bool{ false, true }) |guarded| {
        var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
        defer reporter.deinit();
        const source = if (guarded) "object \"C\" { code { pop(memoryguard(128)) } }" else "object \"C\" { code {} }";
        const object = (try ObjectParser.parseSource(std.testing.allocator, source, "C.yul", &reporter, dialect.dialect())).?;
        defer object.destroy();
        for ([_]bool{ false, true }) |optimized|
            try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{ object.code().?.root(), &dialect, optimized, guarded });
    }
}

test "object compiler emits nested objects, data references, metadata, and bytecode" {
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialectModule = @import("evm_dialect.zig");
    const ObjectParser = @import("../../object_parser.zig").ObjectParser;
    const Assembly = @import("../../../libevmasm/assembly.zig").Assembly;
    const Adapter = @import("eth_assembly_adapter.zig").EthAssemblyAdapter;
    const allocator = std.testing.allocator;
    const version = EVMVersion.init(.Cancun);
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, version, true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const object = (try ObjectParser.parseSource(
        allocator,
        "object \"Root\" { code { datacopy(0, dataoffset(\"blob\"), datasize(\"blob\")) } data \"blob\" hex\"0102\" object \"Root_deployed\" { code { mstore(0, 42) return(0, 32) } data \".metadata\" hex\"aabb\" } }",
        "object.yul",
        &reporter,
        dialect.dialect(),
    )).?;
    defer object.destroy();
    try analyzeObjectTree(allocator, object, &reporter, &dialect);
    var assembly = try Assembly.init(allocator, version, true, "Root");
    defer assembly.deinit();
    var adapter = Adapter.init(allocator, &assembly);
    defer adapter.deinit();
    try EVMObjectCompiler.compile(allocator, object, adapter.abstractAssembly(), false, false);
    try std.testing.expect(!object.sub_objects.items[1].object.sub_id.empty());
    const linker_object = try assembly.assemble();
    try std.testing.expect(linker_object.bytecode.items.len != 0);
    const text = try assembly.assemblyStringAlloc(allocator, .{}, &.{});
    defer allocator.free(text);
    try std.testing.expect(std.mem.find(u8, text, "data_") != null);
    try std.testing.expect(std.mem.find(u8, text, "sub_0: assembly") != null);
    try std.testing.expect(std.mem.find(u8, text, "auxdata: 0xaabb") != null);

    var optimized_assembly = try Assembly.init(allocator, version, true, "Root");
    defer optimized_assembly.deinit();
    var optimized_adapter = Adapter.init(allocator, &optimized_assembly);
    defer optimized_adapter.deinit();
    try EVMObjectCompiler.compile(
        allocator,
        object,
        optimized_adapter.abstractAssembly(),
        true,
        false,
    );
    const optimized_linker_object = try optimized_assembly.assemble();
    try std.testing.expect(optimized_linker_object.bytecode.items.len != 0);
    try std.testing.expectError(
        error.SSACFGBackendUnavailable,
        EVMObjectCompiler.compile(allocator, object, optimized_adapter.abstractAssembly(), true, true),
    );
}

fn analyzeObjectTree(
    allocator: std.mem.Allocator,
    object: *Object,
    reporter: *@import("../../../liblangutil/diagnostics.zig").ErrorReporter,
    dialect: *const EVMDialect,
) !void {
    for (object.sub_objects.items) |sub_node| switch (sub_node) {
        .object => |child| try analyzeObjectTree(allocator, child, reporter, dialect),
        .data => {},
    };
    if (!try @import("../../asm_analysis.zig").analyzeObject(
        allocator,
        object,
        reporter,
        .{},
        @import("../../asm_analysis.zig").instructionValidatorForEVMDialect(dialect),
    )) return error.AnalysisFailed;
}

test "backend scratch arenas release nested intermediates before assembly use" {
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialectModule = @import("evm_dialect.zig");
    const ObjectParser = @import("../../object_parser.zig").ObjectParser;
    const Assembly = @import("../../../libevmasm/assembly.zig").Assembly;
    const Adapter = @import("eth_assembly_adapter.zig").EthAssemblyAdapter;
    const source =
        \\object "Root" {
        \\  code {
        \\    function f(x) -> r { r := add(x, 1) if gt(r, 3) { r := mul(r, 2) } }
        \\    mstore(0, f(5))
        \\    datacopy(32, dataoffset("blob"), datasize("blob"))
        \\    datacopy(64, dataoffset("Root_deployed"), datasize("Root_deployed"))
        \\  }
        \\  data "blob" hex"010203"
        \\  object "Root_deployed" {
        \\    code {
        \\      function g(x) -> r {
        \\        for { let i := 0 } lt(i, x) { i := add(i, 1) } { r := add(r, i) }
        \\      }
        \\      mstore(0, g(3)) return(0, 32)
        \\    }
        \\    data ".metadata" hex"aabb"
        \\    object "Nested" { code { mstore(0, 1) } }
        \\  }
        \\}
    ;
    const Check = struct {
        fn run(
            failing: std.mem.Allocator,
            object: *Object,
            version: EVMVersion,
            optimize: bool,
            expected_text: []const u8,
            expected_bytes: []const u8,
        ) !void {
            var assembly = try Assembly.init(failing, version, true, "Root");
            defer assembly.deinit();
            var adapter = Adapter.init(failing, &assembly);
            defer adapter.deinit();
            // Count only arena backing storage, independently of the emitted
            // assembly. The outer failing allocator still sees both owners.
            var backing = std.testing.FailingAllocator.init(failing, .{});
            const result = EVMObjectCompiler.compileWithScratch(
                failing,
                backing.allocator(),
                object,
                adapter.abstractAssembly(),
                optimize,
                false,
            );
            // Check successful and partial construction teardown alike.
            try std.testing.expectEqual(backing.allocated_bytes, backing.freed_bytes);
            try result;
            try std.testing.expect(backing.allocated_bytes > 0);
            // Every backend arena is gone before assembling or rendering output.
            const linker = try assembly.assemble();
            try std.testing.expectEqualSlices(u8, expected_bytes, linker.bytecode.items);
            const text = try assembly.assemblyStringAlloc(failing, .{}, &.{});
            defer failing.free(text);
            try std.testing.expectEqualStrings(expected_text, text);
        }
    };
    const allocator = std.testing.allocator;
    for ([_]EVMVersion{ .init(.Cancun), .init(.Homestead) }) |version| {
        var dialect = try EVMDialectModule.EVMDialect.init(allocator, version, true);
        defer dialect.deinit();
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        const object = (try ObjectParser.parseSource(allocator, source, "backend-scratch.yul", &reporter, dialect.dialect())).?;
        defer object.destroy();
        try analyzeObjectTree(allocator, object, &reporter, &dialect);
        for ([_]bool{ false, true }) |optimize| {
            var reference = try Assembly.init(allocator, version, true, "Root");
            defer reference.deinit();
            var adapter = Adapter.init(allocator, &reference);
            defer adapter.deinit();
            try EVMObjectCompiler.compile(allocator, object, adapter.abstractAssembly(), optimize, false);
            const linker = try reference.assemble();
            const text = try reference.assemblyStringAlloc(allocator, .{}, &.{});
            defer allocator.free(text);
            try std.testing.checkAllAllocationFailures(allocator, Check.run, .{
                object, version, optimize, text, linker.bytecode.items,
            });
        }
    }
}
