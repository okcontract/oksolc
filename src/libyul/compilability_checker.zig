// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Dry-run classic EVM lowering used to report stack-unreachable variables.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("ast.zig");
const AsmAnalysis = @import("asm_analysis.zig");
const EVMCodeTransform = @import("backends/evm/evm_code_transform.zig");
const EVMBuiltins = @import("backends/evm/evm_builtins.zig");
const EVMDialectModule = @import("backends/evm/evm_dialect.zig");
const NoOutput = @import("backends/evm/no_output_assembly.zig");
const Object = @import("object.zig").Object;
const SubAssemblyID = @import("../libevmasm/sub_assembly_id.zig").SubAssemblyID;
const YulName = @import("yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

pub const UnreachableVariables = ordered.OrderedMap(
    YulName,
    std.ArrayList(YulName),
    lessYulName,
);
pub const StackDeficit = ordered.OrderedMap(YulName, i32, lessYulName);

pub const CompilabilityChecker = struct {
    allocator: std.mem.Allocator,
    unreachable_variables: UnreachableVariables = .{},
    stack_deficit: StackDeficit = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        object: *const Object,
        optimize_stack_allocation: bool,
    ) !CompilabilityChecker {
        const code = object.code() orelse return error.MissingObjectCode;
        return initWithBlock(allocator, object, code.root(), optimize_stack_allocation);
    }

    /// Internal form used by StackCompressor while repeatedly rewriting a
    /// cloned root block. Object structure and builtin object access still
    /// come from `object`, exactly as in the upstream temporary Object copy.
    pub fn initWithBlock(
        allocator: std.mem.Allocator,
        object: *const Object,
        block: *const AST.Block,
        optimize_stack_allocation: bool,
    ) !CompilabilityChecker {
        var result: CompilabilityChecker = .{ .allocator = allocator };
        errdefer result.deinit();

        const dialect_value = object.dialect() orelse return error.MissingDialect;
        const evm_dialect = EVMDialectModule.fromDialect(dialect_value.*) orelse return result;
        var no_output_dialect = NoOutput.NoOutputEVMDialect.init(evm_dialect);

        var structure = try object.summarizeStructure();
        defer structure.deinit();
        var analysis_info = try AsmAnalysis.analyzeStrictBlock(
            allocator,
            no_output_dialect.dialect(),
            block,
            &structure,
            AsmAnalysis.instructionValidatorForEVMDialect(evm_dialect),
        );
        defer analysis_info.deinit();

        var builtin_context = EVMBuiltins.BuiltinContext.init(allocator);
        defer builtin_context.deinit();
        builtin_context.current_object = object;
        if (object.name.len != 0)
            try builtin_context.putSubId(object.name, SubAssemblyID.init(1));
        for (object.sub_objects.items) |*sub_node|
            try builtin_context.putSubId(sub_node.name(), SubAssemblyID.init(1));

        var assembly = NoOutput.NoOutputAssembly.init(evm_dialect.evmVersion());
        var transform = try EVMCodeTransform.CodeTransform.initNoOutput(
            allocator,
            assembly.abstractAssembly(),
            &analysis_info,
            block,
            &no_output_dialect,
            &builtin_context,
            optimize_stack_allocation,
        );
        defer transform.deinit();
        try transform.apply(block);

        for (transform.stackErrors()) |stack_error| {
            if (!result.unreachable_variables.contains(stack_error.function_name))
                _ = try result.unreachable_variables.insert(
                    allocator,
                    stack_error.function_name,
                    .empty,
                );
            const unreachable_list = result.unreachable_variables.getPtr(
                stack_error.function_name,
            ).?;
            var already_present = false;
            for (unreachable_list.items) |name| {
                if (name.eql(stack_error.variable)) {
                    already_present = true;
                    break;
                }
            }
            if (!already_present)
                try unreachable_list.append(allocator, stack_error.variable);

            if (result.stack_deficit.getPtr(stack_error.function_name)) |deficit|
                deficit.* = @max(deficit.*, stack_error.depth)
            else
                _ = try result.stack_deficit.insert(
                    allocator,
                    stack_error.function_name,
                    @max(0, stack_error.depth),
                );
        }
        return result;
    }

    pub fn deinit(self: *CompilabilityChecker) void {
        for (self.unreachable_variables.mutableItems()) |*entry|
            entry.value.deinit(self.allocator);
        self.unreachable_variables.deinit(self.allocator);
        self.stack_deficit.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn unreachableVariables(self: *const CompilabilityChecker) *const UnreachableVariables {
        return &self.unreachable_variables;
    }

    pub fn stackDeficit(self: *const CompilabilityChecker) *const StackDeficit {
        return &self.stack_deficit;
    }
};
