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

pub const EVMObjectCompiler = struct {
    pub fn compile(
        allocator: std.mem.Allocator,
        object: *Object,
        assembly: AbstractModule.AbstractAssembly,
        optimize: bool,
        via_ssa_cfg: bool,
    ) anyerror!void {
        const dialect = try objectEVMDialect(object);
        if (optimize and dialect.evmVersion().canOverchargeGasForCall() and via_ssa_cfg)
            return error.SSACFGBackendUnavailable;
        var compiler: Compiler = .{
            .allocator = allocator,
            .assembly = assembly,
        };
        try compiler.run(object, optimize, via_ssa_cfg);
    }
};

const Compiler = struct {
    allocator: std.mem.Allocator,
    assembly: AbstractModule.AbstractAssembly,

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
                try EVMObjectCompiler.compile(
                    self.allocator,
                    sub_object,
                    created.assembly,
                    optimize,
                    via_ssa_cfg,
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
            if (stack_errors.items.len != 0) return error.StackTooDeep;
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
        if (transform.stackErrors().len != 0) return error.StackTooDeep;
    }
};

fn objectEVMDialect(object: *const Object) !*const EVMDialect {
    const dialect = object.dialect() orelse return error.MissingDialect;
    const context = dialect.context orelse return error.NonEVMDialect;
    return @ptrCast(@alignCast(context));
}

test "object compiler emits nested objects, data references, metadata, and bytecode" {
    const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
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
