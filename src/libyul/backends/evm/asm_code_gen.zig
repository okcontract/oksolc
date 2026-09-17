// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Public inline-assembly code-generation entry point backed by the classic
//! Yul EVM transform.

const std = @import("std");
const AST = @import("../../ast.zig");
const AsmAnalysisInfo = @import("../../asm_analysis_info.zig").AsmAnalysisInfo;
const AbstractModule = @import("abstract_assembly.zig");
const Assembly = @import("../../../libevmasm/assembly.zig").Assembly;
const BuiltinContext = @import("evm_builtins.zig").BuiltinContext;
const CodeTransformModule = @import("evm_code_transform.zig");
const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
const EVMDialect = @import("evm_dialect.zig");
const EthAssemblyAdapter = @import("eth_assembly_adapter.zig").EthAssemblyAdapter;

pub const CodeGenerator = struct {
    pub fn assemble(
        allocator: std.mem.Allocator,
        parsed_data: *const AST.Block,
        analysis_info: *AsmAnalysisInfo,
        assembly: *Assembly,
        evm_version: EVMVersion,
        identifier_access: AbstractModule.ExternalIdentifierAccess,
        use_named_labels_for_functions: bool,
        optimize_stack_allocation: bool,
    ) !void {
        var assembly_adapter = EthAssemblyAdapter.init(allocator, assembly);
        defer assembly_adapter.deinit();
        var builtin_context = BuiltinContext.init(allocator);
        defer builtin_context.deinit();
        var transform = try CodeTransformModule.CodeTransform.init(
            allocator,
            assembly_adapter.abstractAssembly(),
            analysis_info,
            parsed_data,
            try EVMDialect.strictAssemblyForEVM(evm_version),
            &builtin_context,
            optimize_stack_allocation,
            identifier_access,
            if (use_named_labels_for_functions)
                .yes_and_force_unique
            else
                .never,
        );
        defer transform.deinit();
        try transform.apply(parsed_data);
        if (transform.stackErrors().len != 0) return error.StackTooDeep;
    }
};

test "code generator lowers analyzed inline Yul through libevmasm" {
    const Parser = @import("../../asm_parser.zig").Parser;
    const AsmAnalysis = @import("../../asm_analysis.zig");
    const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
    const allocator = std.testing.allocator;
    const version = EVMVersion.init(.Cancun);
    const dialect = try EVMDialect.strictAssemblyForEVM(version);
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function twice(a) -> r { r := add(a, a) } pop(twice(4)) }",
        "inline.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    defer info.deinit();
    var analyzer = AsmAnalysis.AsmAnalyzer.init(
        allocator,
        &info,
        &reporter,
        dialect.dialect(),
        .{},
        .{},
        AsmAnalysis.instructionValidatorForEVMDialect(dialect),
    );
    defer analyzer.deinit();
    try std.testing.expect(try analyzer.analyze(ast.root()));
    var assembly = try Assembly.init(allocator, version, false, "inline");
    defer assembly.deinit();
    try CodeGenerator.assemble(
        allocator,
        ast.root(),
        &info,
        &assembly,
        version,
        .{},
        true,
        true,
    );
    const object = try assembly.assemble();
    try std.testing.expect(object.bytecode.items.len != 0);
    try std.testing.expectEqual(@as(i32, 0), assembly.deposit());
}
