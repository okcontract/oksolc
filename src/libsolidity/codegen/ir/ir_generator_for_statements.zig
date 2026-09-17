// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Solidity statement and expression lowering translated from
//! `libsolidity/codegen/ir/IRGeneratorForStatements.cpp`.
//!
//! Preserves upstream evaluation order and lowers scalar and reference values
//! through the shared Yul/ABI helper collectors.

const std = @import("std");
const AST = @import("../../ast/ast.zig");
const ASTImplementation = @import("../../ast/ast.zig");
const ASTAnnotations = @import("../../ast/ast_annotations.zig");
const ASTUtils = @import("../../ast/ast_utils.zig");
const CompatibilityIdResolver = @import("../../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Types = @import("../../ast/types.zig");
const TypeBehavior = @import("../../ast/types.zig");
const TypeProviderModule = @import("../../ast/type_provider.zig");
const TokenModule = @import("../../../liblangutil/token.zig");
const SourceLocation = @import("../../../liblangutil/source_location.zig").SourceLocation;
const CommonData = @import("../../../libsolutil/common_data.zig");
const Numeric = @import("../../../libsolutil/numeric.zig");
const Keccak256 = @import("../../../libsolutil/keccak256.zig");
const FunctionSelector = @import("../../../libsolutil/function_selector.zig");
const GasCosts = @import("../../../libevmasm/gas_meter.zig").GasCosts;
const OptimiserSettings = @import("../../interface/optimiser_settings.zig").OptimiserSettings;
const DebugSettings = @import("../../interface/debug_settings.zig");
const ContextModule = @import("ir_generation_context.zig");
const Common = @import("common.zig");
const IRVariableModule = @import("ir_variable.zig");
const IRLValueModule = @import("irl_value.zig");
const YulUtilFunctionsModule = @import("../yul_util_functions.zig");
const ReturnInfoModule = @import("../return_info.zig");
const YulAST = @import("../../../libyul/ast.zig");
const YulAsmPrinter = @import("../../../libyul/asm_printer.zig").AsmPrinter;
const YulASTCopier = @import("../../../libyul/optimiser/ast_copier.zig").ASTCopier;
const YulName = @import("../../../libyul/yul_name.zig").YulName;
const YulUtilities = @import("../../../libyul/utilities.zig");

const max_ast_depth = 4096;

pub const PlaceholderCallback = struct {
    context: *anyopaque,
    generate_fn: *const fn (
        *anyopaque,
        std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8,

    pub fn generate(
        self: PlaceholderCallback,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        return self.generate_fn(self.context, allocator);
    }
};

pub const GeneratorError = ASTImplementation.AstError ||
    ASTUtils.QueryError ||
    ContextModule.ContextError ||
    Common.CommonError ||
    IRVariableModule.VariableError ||
    YulUtilFunctionsModule.UtilError ||
    TypeProviderModule.ProviderError ||
    Numeric.FormatBigIntError ||
    error{
        InvalidAst,
        InvalidLiteral,
        InvalidTypeList,
        UnsupportedStatement,
        UnsupportedExpression,
        UnsupportedLValue,
        UnsupportedConversion,
        UnsupportedFunctionCall,
        StackLayoutMismatch,
        MissingPlaceholderCallback,
        AstTooDeep,
    };

const EvaluatedArguments = struct {
    allocator: std.mem.Allocator,
    nodes: AST.NodeList,
    values: []IRVariableModule.IRVariable,

    fn deinit(self: *EvaluatedArguments) void {
        for (self.values) |*value| value.deinit();
        self.allocator.free(self.values);
        self.* = undefined;
    }

    fn find(
        self: *EvaluatedArguments,
        node: *const AST.Node,
    ) GeneratorError!*IRVariableModule.IRVariable {
        for (self.nodes, self.values) |candidate, *value|
            if (candidate == node) return value;
        return error.InvalidAst;
    }
};

pub const IRGeneratorForStatements = struct {
    allocator: std.mem.Allocator,
    context: *ContextModule.IRGenerationContext,
    utils: *YulUtilFunctionsModule.YulUtilFunctions,
    optimiser_settings: OptimiserSettings,
    placeholder_callback: ?PlaceholderCallback,
    output: std.ArrayList(u8) = .empty,
    current_location: SourceLocation = .{},
    last_location: SourceLocation = .{},
    has_last_location: bool = false,

    pub fn init(
        allocator: std.mem.Allocator,
        context: *ContextModule.IRGenerationContext,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
        optimiser_settings: OptimiserSettings,
        placeholder_callback: ?PlaceholderCallback,
    ) IRGeneratorForStatements {
        return .{
            .allocator = allocator,
            .context = context,
            .utils = utils,
            .optimiser_settings = optimiser_settings,
            .placeholder_callback = placeholder_callback,
        };
    }

    pub fn deinit(self: *IRGeneratorForStatements) void {
        self.output.deinit(self.allocator);
        self.* = undefined;
    }

    fn compatibilityId(
        self: *const IRGeneratorForStatements,
        node: *const AST.Node,
    ) GeneratorError!i64 {
        return self.context.compatibility_ids.id(node) orelse error.InvalidAst;
    }

    fn variableFromExpression(
        self: *const IRGeneratorForStatements,
        expression: *const AST.Node,
    ) GeneratorError!IRVariableModule.IRVariable {
        return IRVariableModule.IRVariable.fromExpression(
            self.allocator,
            self.context.compatibility_ids,
            expression,
        );
    }

    pub fn codeBorrowed(self: *const IRGeneratorForStatements) []const u8 {
        return self.output.items;
    }

    pub fn codeAlloc(
        self: *const IRGeneratorForStatements,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        return allocator.dupe(u8, self.output.items);
    }

    pub fn generate(
        self: *IRGeneratorForStatements,
        block: *const AST.Node,
    ) GeneratorError!void {
        if (block.nodeKind() != .block) return error.InvalidAst;
        try self.emitStatement(block, 0);
    }

    pub fn evaluateExpression(
        self: *IRGeneratorForStatements,
        expression: *const AST.Node,
        target_type: *const Types.Type,
    ) GeneratorError!IRVariableModule.IRVariable {
        var value = try self.emitExpression(expression, 0);
        defer value.deinit();
        const raw_name = try self.context.newYulVariable();
        defer self.allocator.free(raw_name);
        var result = try IRVariableModule.IRVariable.init(
            self.allocator,
            raw_name,
            target_type,
        );
        errdefer result.deinit();
        try self.assignConverted(&result, &value, true);
        return result;
    }

    pub fn bindLocalValue(
        self: *IRGeneratorForStatements,
        declaration: *const AST.Node,
        value: *const IRVariableModule.IRVariable,
    ) GeneratorError!void {
        const local = try self.context.localVariable(declaration);
        try self.assignConverted(local, value, true);
    }

    pub fn constantValueFunction(
        self: *IRGeneratorForStatements,
        declaration: *const AST.Node,
    ) GeneratorError![]u8 {
        if (declaration.nodeKind() != .variable_declaration or
            declaration.payload.variable_declaration.mutability != .Constant)
            return error.InvalidAst;
        const initializer = declaration.payload.variable_declaration.value orelse
            return error.InvalidAst;
        const name = try Common.constantValueFunctionAlloc(
            self.allocator,
            self.context.compatibility_ids,
            declaration,
        );
        errdefer self.allocator.free(name);
        if (!(try self.context.functionCollector().beginFunction(name))) return name;
        errdefer self.context.functionCollector().abortFunction(name);

        const type_ref = try variableType(declaration);
        var generator = IRGeneratorForStatements.init(
            self.allocator,
            self.context,
            self.utils,
            self.optimiser_settings,
            null,
        );
        defer generator.deinit();
        var value = try generator.evaluateExpression(initializer, type_ref);
        defer value.deinit();
        const value_names = try value.commaSeparatedListAlloc();
        defer self.allocator.free(value_names);
        var result = try IRVariableModule.IRVariable.init(
            self.allocator,
            "ret",
            type_ref,
        );
        defer result.deinit();
        const result_names = try result.commaSeparatedListAlloc();
        defer self.allocator.free(result_names);
        const location = try Common.dispenseNodeLocationCommentAlloc(
            self.allocator,
            declaration,
            self.context.locationCommentContext(),
        );
        defer self.allocator.free(location);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n{s}\nfunction {s}() -> {s} {{\n{s}\n{s} := {s}\n}}\n",
            .{ location, name, result_names, generator.codeBorrowed(), result_names, value_names },
        );
        defer self.allocator.free(code);
        try self.context.functionCollector().finishFunction(name, code);
        return name;
    }

    pub fn initializeLocalVar(
        self: *IRGeneratorForStatements,
        declaration: *const AST.Node,
    ) GeneratorError!void {
        try self.setLocation(declaration);
        const local = try self.context.localVariable(declaration);
        if (local.type_ref.category() == .Mapping) return;
        if (local.type_ref.asReference()) |reference| {
            if (reference.location == .Storage and reference.isPointer()) return;
        }

        const raw_name = try self.context.newYulVariable();
        defer self.allocator.free(raw_name);
        const zero_name = try Common.zeroValueAlloc(
            self.allocator,
            self.context.compatibility_ids,
            local.type_ref,
            raw_name,
        );
        defer self.allocator.free(zero_name);
        var zero = try IRVariableModule.IRVariable.init(
            self.allocator,
            zero_name,
            local.type_ref,
        );
        defer zero.deinit();
        const zero_function = try self.utils.zeroValueFunction(local.type_ref, true);
        defer self.allocator.free(zero_function);
        const call = try std.fmt.allocPrint(self.allocator, "{s}()", .{zero_function});
        defer self.allocator.free(call);
        try self.defineText(&zero, call);
        try self.declareAssign(local, &zero, false);
    }

    pub fn initializeStateVar(
        self: *IRGeneratorForStatements,
        declaration: *const AST.Node,
    ) GeneratorError!void {
        if (declaration.nodeKind() != .variable_declaration) return error.InvalidAst;
        const immutable = declaration.payload.variable_declaration.mutability == .Immutable;
        if (!self.context.isStateVariable(declaration) and
            !(immutable and self.context.immutableRegistered(declaration)))
            return error.InvalidAst;
        try self.setLocation(declaration);
        const initializer = declaration.payload.variable_declaration.value orelse return;
        var value = try self.emitExpression(initializer, 0);
        defer value.deinit();
        var lvalue = if (immutable)
            IRLValueModule.IRLValue.initImmutable(
                self.allocator,
                try variableType(declaration),
                declaration,
            )
        else
            try self.stateVariableLValue(declaration);
        defer lvalue.deinit();
        try self.writeToLValue(&lvalue, &value);
    }

    fn emitStatement(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        if (depth >= max_ast_depth) return error.AstTooDeep;
        switch (node.payload) {
            .block => |block| {
                const previous = self.context.arithmetic;
                if (block.unchecked) self.context.setArithmetic(.Wrapping);
                defer self.context.setArithmetic(previous);
                for (block.statements) |statement|
                    try self.emitStatement(statement, depth + 1);
            },
            .expression_statement => |statement| {
                var value = try self.emitExpression(statement.expression, depth + 1);
                value.deinit();
            },
            .variable_declaration_statement => try self.emitVariableDeclarationStatement(node, depth + 1),
            .if_statement => try self.emitIfStatement(node, depth + 1),
            .while_statement => try self.emitWhileStatement(node, depth + 1),
            .for_statement => try self.emitForStatement(node, depth + 1),
            .continue_statement => {
                try self.setLocation(node);
                try self.append("continue\n");
            },
            .break_statement => {
                try self.setLocation(node);
                try self.append("break\n");
            },
            .return_statement => try self.emitReturn(node, depth + 1),
            .placeholder_statement => try self.emitPlaceholder(node),
            .emit_statement => {
                var value = try self.emitExpression(
                    node.payload.emit_statement.event_call,
                    depth + 1,
                );
                value.deinit();
            },
            .revert_statement => try self.emitCustomRevert(
                node.payload.revert_statement.error_call,
                depth + 1,
            ),
            .inline_assembly => try self.emitInlineAssembly(node),
            .try_statement => try self.emitTryStatement(node, depth + 1),
            .try_catch_clause => try self.emitStatement(
                node.payload.try_catch_clause.block,
                depth + 1,
            ),
            else => return error.UnsupportedStatement,
        }
    }

    fn emitInlineAssembly(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
    ) GeneratorError!void {
        if (node.nodeKind() != .inline_assembly) return error.InvalidAst;
        const assembly = node.payload.inline_assembly;
        const annotation_union = ASTAnnotations.annotationConst(node) orelse
            return error.InvalidAst;
        const annotation = switch (annotation_union.*) {
            .inline_assembly => |*value| value,
            else => return error.InvalidAst,
        };
        const has_memory_effects = (annotation.has_memory_effects.get() catch
            return error.InvalidAst).*;
        if (has_memory_effects and !annotation.marked_memory_safe)
            self.context.setMemoryUnsafeInlineAssemblySeen();

        const operations = assembly.operations orelse return error.InvalidAst;
        var translation_context: InlineAssemblyCopyContext = .{
            .allocator = self.allocator,
            .generation_context = self.context,
            .references = annotation.external_references.items,
        };
        var copier = YulASTCopier.initWithHooks(
            self.allocator,
            &translation_context,
            .{
                .translate_expression = InlineAssemblyCopyContext.translateExpression,
                .translate_identifier_node = InlineAssemblyCopyContext.translateIdentifierNode,
                .translate_identifier = InlineAssemblyCopyContext.translateIdentifierName,
            },
        );
        var translated = copier.translateAst(operations) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.InvalidAst,
        };
        defer translated.deinit();
        const rendered = YulAsmPrinter.formatDefault(
            self.allocator,
            &translated,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.InvalidAst,
        };
        defer self.allocator.free(rendered);
        try self.setLocation(node);
        try self.append(rendered);
        try self.append("\n");
    }

    fn emitTryStatement(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        if (depth >= max_ast_depth or node.nodeKind() != .try_statement)
            return error.InvalidAst;
        const statement = node.payload.try_statement;

        var external_call = try self.emitExpression(statement.external_call, depth + 1);
        defer external_call.deinit();
        const success_condition = try Common.trySuccessConditionVariableAlloc(
            self.allocator,
            self.context.compatibility_ids,
            statement.external_call,
        );
        defer self.allocator.free(success_condition);

        try self.setLocation(node);
        try self.appendFmt("switch iszero({s})\n", .{success_condition});
        try self.append("case 0 { // success case\n");

        const success_clause_node = try ASTImplementation.trySuccessClause(statement);
        const success_clause = success_clause_node.payload.try_catch_clause;
        if (success_clause.parameters) |parameters_node| {
            if (parameters_node.nodeKind() != .parameter_list)
                return error.InvalidAst;
            const parameters = parameters_node.payload.parameter_list.parameters;
            if (parameters.len == 1) {
                const local = try self.context.addLocalVariable(parameters[0]);
                try self.assignConverted(local, &external_call, true);
            } else {
                for (parameters, 0..) |parameter, index| {
                    const local = try self.context.addLocalVariable(parameter);
                    var component = try external_call.tupleComponent(index);
                    defer component.deinit();
                    try self.assignConverted(local, &component, true);
                }
            }
        }
        try self.emitStatement(success_clause.block, depth + 1);
        try self.setLocation(node);
        try self.append("}\n");

        try self.append("default { // failure case\n");
        try self.emitCatchClauses(node, depth + 1);
        try self.append("}\n");
    }

    fn emitCatchClauses(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        if (depth >= max_ast_depth or node.nodeKind() != .try_statement)
            return error.InvalidAst;
        const statement = node.payload.try_statement;
        const error_clause = ASTImplementation.tryErrorClause(statement);
        const panic_clause = ASTImplementation.tryPanicClause(statement);

        try self.setLocation(node);
        const run_fallback = try self.context.newYulVariable();
        defer self.allocator.free(run_fallback);
        try self.appendFmt("let {s} := 1\n", .{run_fallback});

        if (error_clause != null or panic_clause != null) {
            const selector = try self.utils.returnDataSelectorFunction();
            defer self.allocator.free(selector);
            try self.appendFmt("switch {s}()\n", .{selector});
        }

        if (error_clause) |clause_node| {
            const selector = FunctionSelector.selectorFromSignatureU32("Error(string)");
            try self.appendFmt("case {d} {{\n", .{selector});
            try self.setLocation(clause_node);
            const data_variable = try self.context.newYulVariable();
            defer self.allocator.free(data_variable);
            const decoder = try self.utils.tryDecodeErrorMessageFunction();
            defer self.allocator.free(decoder);
            try self.appendFmt("let {s} := {s}()\n", .{ data_variable, decoder });
            try self.appendFmt("if {s} {{\n", .{data_variable});
            try self.appendFmt("{s} := 0\n", .{run_fallback});
            const clause = clause_node.payload.try_catch_clause;
            if (clause.parameters) |parameters_node| {
                if (parameters_node.nodeKind() != .parameter_list or
                    parameters_node.payload.parameter_list.parameters.len != 1)
                    return error.InvalidAst;
                const local = try self.context.addLocalVariable(
                    parameters_node.payload.parameter_list.parameters[0],
                );
                try self.defineText(local, data_variable);
            }
            try self.emitStatement(clause.block, depth + 1);
            try self.setLocation(clause_node);
            try self.append("}\n");
            try self.setLocation(node);
            try self.append("}\n");
        }

        if (panic_clause) |clause_node| {
            const selector = FunctionSelector.selectorFromSignatureU32("Panic(uint256)");
            try self.appendFmt("case {d} {{\n", .{selector});
            try self.setLocation(clause_node);
            const success = try self.context.newYulVariable();
            defer self.allocator.free(success);
            const code = try self.context.newYulVariable();
            defer self.allocator.free(code);
            const decoder = try self.utils.tryDecodePanicDataFunction();
            defer self.allocator.free(decoder);
            try self.appendFmt(
                "let {s}, {s} := {s}()\n",
                .{ success, code, decoder },
            );
            try self.appendFmt("if {s} {{\n", .{success});
            try self.appendFmt("{s} := 0\n", .{run_fallback});
            const clause = clause_node.payload.try_catch_clause;
            if (clause.parameters) |parameters_node| {
                if (parameters_node.nodeKind() != .parameter_list or
                    parameters_node.payload.parameter_list.parameters.len != 1)
                    return error.InvalidAst;
                const local = try self.context.addLocalVariable(
                    parameters_node.payload.parameter_list.parameters[0],
                );
                try self.defineText(local, code);
            }
            try self.emitStatement(clause.block, depth + 1);
            try self.setLocation(clause_node);
            try self.append("}\n");
            try self.setLocation(node);
            try self.append("}\n");
        }

        try self.setLocation(node);
        try self.appendFmt("if {s} {{\n", .{run_fallback});
        if (ASTImplementation.tryFallbackClause(statement)) |fallback|
            try self.emitCatchFallback(fallback, depth + 1)
        else {
            const forwarding_revert = try self.utils.forwardingRevertFunction();
            defer self.allocator.free(forwarding_revert);
            try self.appendFmt("{s}()\n", .{forwarding_revert});
        }
        try self.setLocation(node);
        try self.append("}\n");
    }

    fn emitCatchFallback(
        self: *IRGeneratorForStatements,
        clause_node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        if (depth >= max_ast_depth or clause_node.nodeKind() != .try_catch_clause)
            return error.InvalidAst;
        const clause = clause_node.payload.try_catch_clause;
        try self.setLocation(clause_node);
        if (clause.parameters) |parameters_node| {
            if (!self.context.evm_version.supportsReturndata() or
                parameters_node.nodeKind() != .parameter_list or
                parameters_node.payload.parameter_list.parameters.len != 1)
                return error.InvalidAst;
            const parameter = parameters_node.payload.parameter_list.parameters[0];
            if (!TypeBehavior.equals(
                try variableType(parameter),
                self.context.type_provider.bytesMemory(),
            )) return error.InvalidAst;
            const local = try self.context.addLocalVariable(parameter);
            const extract = try self.utils.extractReturndataFunction();
            defer self.allocator.free(extract);
            const call = try std.fmt.allocPrint(self.allocator, "{s}()", .{extract});
            defer self.allocator.free(call);
            try self.defineText(local, call);
        }
        try self.emitStatement(clause.block, depth + 1);
    }

    fn emitVariableDeclarationStatement(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        const statement = node.payload.variable_declaration_statement;
        if (statement.initial_value) |initial_value| {
            var value = try self.emitExpression(initial_value, depth + 1);
            defer value.deinit();
            try self.setLocation(node);
            if (statement.declarations.len == 1) {
                const declaration = statement.declarations[0] orelse return error.InvalidAst;
                const local = try self.context.addLocalVariable(declaration);
                try self.assignConverted(local, &value, true);
                return;
            }
            if (value.type_ref.category() != .Tuple or
                value.type_ref.payload.Tuple.components.len != statement.declarations.len)
                return error.InvalidAst;
            for (statement.declarations, 0..) |declaration, index| {
                const present = declaration orelse continue;
                const local = try self.context.addLocalVariable(present);
                var component = try value.tupleComponent(index);
                defer component.deinit();
                try self.assignConverted(local, &component, true);
            }
            return;
        }

        try self.setLocation(node);
        for (statement.declarations) |declaration| {
            const present = declaration orelse continue;
            const local = try self.context.addLocalVariable(present);
            try self.declare(local);
            try self.initializeLocalVar(present);
        }
    }

    fn emitIfStatement(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        const statement = node.payload.if_statement;
        var condition = try self.emitExpression(statement.condition, depth + 1);
        defer condition.deinit();
        const condition_text = try condition.commaSeparatedListAlloc();
        defer self.allocator.free(condition_text);
        try self.setLocation(node);
        if (statement.false_body) |false_body| {
            try self.appendFmt("switch {s}\ncase 0 {{\n", .{condition_text});
            try self.emitStatement(false_body, depth + 1);
            try self.setLocation(node);
            try self.append("}\ndefault {\n");
            try self.emitStatement(statement.true_body, depth + 1);
            try self.setLocation(node);
            try self.append("}\n");
        } else {
            try self.appendFmt("if {s} {{\n", .{condition_text});
            try self.emitStatement(statement.true_body, depth + 1);
            try self.setLocation(node);
            try self.append("}\n");
        }
    }

    fn emitWhileStatement(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        const statement = node.payload.while_statement;
        try self.setLocation(node);
        if (statement.is_do_while) {
            const first_run = try self.context.newYulVariable();
            defer self.allocator.free(first_run);
            try self.appendFmt("let {s} := 1\nfor {{\n}} 1 {{\n}}\n{{\n", .{first_run});
            try self.appendFmt("if iszero({s}) {{\n", .{first_run});
            var condition = try self.emitExpression(statement.condition, depth + 1);
            defer condition.deinit();
            const condition_text = try condition.commaSeparatedListAlloc();
            defer self.allocator.free(condition_text);
            try self.appendFmt("if iszero({s}) {{ break }}\n}}\n{s} := 0\n", .{
                condition_text,
                first_run,
            });
            try self.emitStatement(statement.body, depth + 1);
            try self.append("}\n");
            return;
        }
        try self.append("for {\n} 1 {\n}\n{\n");
        var condition = try self.emitExpression(statement.condition, depth + 1);
        defer condition.deinit();
        const condition_text = try condition.commaSeparatedListAlloc();
        defer self.allocator.free(condition_text);
        try self.appendFmt("if iszero({s}) {{ break }}\n", .{condition_text});
        try self.emitStatement(statement.body, depth + 1);
        try self.append("}\n");
    }

    fn emitForStatement(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        const statement = node.payload.for_statement;
        try self.setLocation(node);
        try self.append("for {\n");
        if (statement.initialization_expression) |initialization|
            try self.emitStatement(initialization, depth + 1);
        try self.append("} 1 {\n");
        if (statement.loop_expression) |loop| {
            const previous = self.context.arithmetic;
            const annotation = ASTAnnotations.annotationConst(node);
            const simple_counter = if (annotation) |value| switch (value.*) {
                .for_statement => |entry| entry.is_simple_counter_loop.value orelse false,
                else => false,
            } else false;
            if (simple_counter and
                self.optimiser_settings.simple_counter_for_loop_unchecked_increment)
                self.context.setArithmetic(.Wrapping);
            defer self.context.setArithmetic(previous);
            try self.emitStatement(loop, depth + 1);
        }
        try self.append("}\n{\n");
        if (statement.condition) |condition_node| {
            var condition = try self.emitExpression(condition_node, depth + 1);
            defer condition.deinit();
            const condition_text = try condition.commaSeparatedListAlloc();
            defer self.allocator.free(condition_text);
            try self.appendFmt("if iszero({s}) {{ break }}\n", .{condition_text});
        }
        try self.emitStatement(statement.body, depth + 1);
        try self.append("}\n");
    }

    fn emitReturn(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        const statement = node.payload.return_statement;
        if (statement.expression) |expression| {
            var value = try self.emitExpression(expression, depth + 1);
            defer value.deinit();
            try self.setLocation(node);
            const annotation = ASTAnnotations.annotationConst(node) orelse
                return error.InvalidAst;
            const parameters_node = switch (annotation.*) {
                .return_statement => |entry| entry.function_return_parameters,
                else => null,
            } orelse return error.InvalidAst;
            if (parameters_node.nodeKind() != .parameter_list) return error.InvalidAst;
            const parameters = parameters_node.payload.parameter_list.parameters;
            if (parameters.len == 1) {
                const local = try self.context.localVariable(parameters[0]);
                try self.assignConverted(local, &value, false);
            } else {
                if (value.type_ref.category() != .Tuple or
                    value.type_ref.payload.Tuple.components.len != parameters.len)
                    return error.InvalidAst;
                for (parameters, 0..) |parameter, index| {
                    const local = try self.context.localVariable(parameter);
                    var component = try value.tupleComponent(index);
                    defer component.deinit();
                    try self.assignConverted(local, &component, false);
                }
            }
        }
        try self.setLocation(node);
        try self.append("leave\n");
    }

    fn emitPlaceholder(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
    ) GeneratorError!void {
        const callback = self.placeholder_callback orelse
            return error.MissingPlaceholderCallback;
        const code = try callback.generate(self.allocator);
        defer self.allocator.free(code);
        try self.setLocation(node);
        try self.append(code);
    }

    fn emitExpression(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth) return error.AstTooDeep;
        return switch (node.payload) {
            .identifier => self.emitIdentifier(node),
            .literal => self.emitLiteral(node),
            .binary_operation => self.emitBinaryOperation(node, depth + 1),
            .unary_operation => self.emitUnaryOperation(node, depth + 1),
            .assignment => self.emitAssignment(node, depth + 1),
            .conditional => self.emitConditional(node, depth + 1),
            .tuple_expression => self.emitTupleExpression(node, depth + 1),
            .function_call => self.emitFunctionCall(node, depth + 1),
            .function_call_options => self.emitFunctionCallOptions(node, depth + 1),
            .new_expression => self.variableFromExpression(
                node,
            ),
            .member_access => self.emitMemberAccess(node, depth + 1),
            .index_access => self.emitIndexAccess(node, depth + 1),
            .index_range_access => self.emitIndexRangeAccess(node, depth + 1),
            else => error.UnsupportedExpression,
        };
    }

    fn emitMemberAccess(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        return self.emitMemberAccessWithOptions(node, depth, true);
    }

    fn emitMemberAccessWithOptions(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
        convert_contract_owner: bool,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .member_access)
            return error.InvalidAst;
        const access = node.payload.member_access;
        const owner_type = try expressionType(access.expression);
        const result_type = try expressionType(node);
        if (result_type.asFunction()) |member_function| {
            if (member_function.options.has_bound_first_argument) {
                var owner = try self.emitExpression(access.expression, depth + 1);
                defer owner.deinit();
                var result = try self.variableFromExpression(
                    node,
                );
                errdefer result.deinit();
                var self_part = try result.part("self");
                defer self_part.deinit();
                try self.setLocation(node);
                try self.assignConverted(&self_part, &owner, true);
                if (member_function.kind == .Internal) {
                    const annotation = ASTAnnotations.annotationConst(node) orelse
                        return error.InvalidAst;
                    const member_annotation = switch (annotation.*) {
                        .member_access => |value| value,
                        else => return error.InvalidAst,
                    };
                    if (!member_annotation.expression.called_directly) {
                        const declaration = member_function.declaration orelse
                            return error.InvalidAst;
                        try self.assignInternalFunctionId(&result, declaration, node);
                    }
                } else if (member_function.kind == .DelegateCall) {
                    const declaration = member_function.declaration orelse
                        return error.InvalidAst;
                    if (declaration.nodeKind() != .function_definition)
                        return error.InvalidAst;
                    const library = ASTImplementation.scope(declaration) orelse
                        return error.InvalidAst;
                    const symbol = try self.linkerSymbolAlloc(library);
                    defer self.allocator.free(symbol);
                    var address = try result.part("address");
                    defer address.deinit();
                    try self.defineText(&address, symbol);
                    const selector_value = try TypeBehavior.externalIdentifier(
                        self.context.type_provider,
                        self.allocator,
                        member_function.*,
                    );
                    const selector_text = try Numeric.toCompactHexWithPrefixAlloc(
                        u256,
                        self.allocator,
                        selector_value,
                    );
                    defer self.allocator.free(selector_text);
                    var selector = try result.part("functionSelector");
                    defer selector.deinit();
                    try self.defineText(&selector, selector_text);
                } else if (member_function.kind != .ArrayPush and
                    member_function.kind != .ArrayPop)
                    return error.InvalidAst;
                return result;
            }
            if (member_function.kind == .Declaration)
                return self.variableFromExpression(
                    node,
                );
        }
        if (owner_type.category() == .TypeType and
            owner_type.payload.TypeType.actual_type.category() == .Enum)
        {
            const enum_type = owner_type.payload.TypeType.actual_type.payload.Enum;
            const members = enum_type.declaration.payload.enum_definition.members;
            for (members, 0..) |member, index| {
                const name = (member.declarationConst() orelse
                    return error.InvalidAst).name;
                if (!std.mem.eql(u8, name, access.member_name)) continue;
                const expression = try std.fmt.allocPrint(
                    self.allocator,
                    "{d}",
                    .{index},
                );
                defer self.allocator.free(expression);
                var result = try self.variableFromExpression(
                    node,
                );
                errdefer result.deinit();
                try self.setLocation(node);
                try self.defineText(&result, expression);
                return result;
            }
            return error.InvalidAst;
        }
        if (owner_type.category() == .Contract) {
            const function_type = result_type.asFunction() orelse
                return error.UnsupportedExpression;
            if (function_type.kind != .External and
                function_type.kind != .DelegateCall)
                return error.UnsupportedExpression;
            const declaration = function_type.declaration orelse
                try referencedDeclaration(node);
            var owner = try self.emitExpression(access.expression, depth + 1);
            defer owner.deinit();
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            var address_part = try result.part("address");
            defer address_part.deinit();
            const owner_text = try owner.commaSeparatedListAlloc();
            defer self.allocator.free(owner_text);
            const address_text = if (convert_contract_owner) blk: {
                const conversion = try self.utils.conversionFunction(
                    owner.type_ref,
                    address_part.type_ref,
                );
                defer self.allocator.free(conversion);
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "{s}({s})",
                    .{ conversion, owner_text },
                );
            } else try self.allocator.dupe(u8, owner_text);
            defer self.allocator.free(address_text);
            const signature = try callableSignatureAlloc(
                self.context.type_provider,
                self.allocator,
                declaration,
                function_type,
            );
            defer self.allocator.free(signature);
            const selector_text = try Numeric.toCompactHexWithPrefixAlloc(
                u32,
                self.allocator,
                FunctionSelector.selectorFromSignatureU32(signature),
            );
            defer self.allocator.free(selector_text);
            var selector_part = try result.part("functionSelector");
            defer selector_part.deinit();
            try self.setLocation(node);
            try self.defineText(&address_part, address_text);
            try self.defineText(&selector_part, selector_text);
            return result;
        }
        if (owner_type.category() == .Function and
            std.mem.eql(u8, access.member_name, "selector"))
        {
            const function_type = owner_type.asFunction() orelse
                return error.InvalidAst;
            if (function_type.kind == .External or
                function_type.kind == .DelegateCall)
            {
                var owner = try self.emitExpression(access.expression, depth + 1);
                defer owner.deinit();
                var selector_part = try owner.part("functionSelector");
                defer selector_part.deinit();
                var result = try self.variableFromExpression(
                    node,
                );
                errdefer result.deinit();
                try self.setLocation(node);
                try self.assignConverted(&result, &selector_part, true);
                return result;
            }
            const declaration = function_type.declaration orelse
                try referencedDeclaration(access.expression);
            const signature = try callableSignatureAlloc(
                self.context.type_provider,
                self.allocator,
                declaration,
                function_type,
            );
            defer self.allocator.free(signature);
            const selector_value = if (function_type.kind == .Event)
                Keccak256.keccak256(signature).toInteger()
            else
                FunctionSelector.selectorFromSignatureU256(signature);
            const expression = try Numeric.toCompactHexWithPrefixAlloc(
                u256,
                self.allocator,
                selector_value,
            );
            defer self.allocator.free(expression);
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (owner_type.category() == .Function and
            std.mem.eql(u8, access.member_name, "address"))
        {
            const function_type = owner_type.asFunction() orelse
                return error.InvalidAst;
            if (function_type.kind != .External)
                return error.InvalidAst;
            var owner = try self.emitExpression(access.expression, depth + 1);
            defer owner.deinit();
            var address = try owner.part("address");
            defer address.deinit();
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            const expression = try self.convertedValueTextAlloc(
                &address,
                result.type_ref,
            );
            defer self.allocator.free(expression);
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (owner_type.category() == .Address) {
            if (result_type.asFunction()) |address_function| switch (address_function.kind) {
                .Send,
                .Transfer,
                .BareCall,
                .BareCallCode,
                .BareDelegateCall,
                .BareStaticCall,
                => {
                    var owner = try self.emitExpression(access.expression, depth + 1);
                    defer owner.deinit();
                    var result = try self.variableFromExpression(
                        node,
                    );
                    errdefer result.deinit();
                    var address = try result.part("address");
                    defer address.deinit();
                    const converted_owner = try self.convertedValueTextAlloc(
                        &owner,
                        address.type_ref,
                    );
                    defer self.allocator.free(converted_owner);
                    try self.setLocation(node);
                    try self.defineText(&address, converted_owner);
                    return result;
                },
                else => {},
            };
            if (!std.mem.eql(u8, access.member_name, "balance") and
                !std.mem.eql(u8, access.member_name, "codehash") and
                !std.mem.eql(u8, access.member_name, "code"))
                return error.UnsupportedExpression;
            var owner = try self.emitExpression(access.expression, depth + 1);
            defer owner.deinit();
            const owner_text = try self.convertedValueTextAlloc(
                &owner,
                self.context.type_provider.address(),
            );
            defer self.allocator.free(owner_text);
            const expression = if (std.mem.eql(u8, access.member_name, "balance"))
                try std.fmt.allocPrint(self.allocator, "balance({s})", .{owner_text})
            else if (std.mem.eql(u8, access.member_name, "codehash"))
                try std.fmt.allocPrint(self.allocator, "extcodehash({s})", .{owner_text})
            else blk: {
                const external_code = try self.utils.externalCodeFunction();
                defer self.allocator.free(external_code);
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "{s}({s})",
                    .{ external_code, owner_text },
                );
            };
            defer self.allocator.free(expression);
            var result = try self.variableFromExpression(node);
            errdefer result.deinit();
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (owner_type.category() == .Struct) {
            const structure = owner_type.payload.Struct;
            if (structure.reference.location == .CallData)
                return self.emitCalldataStructMember(node, structure, depth + 1);
            var lvalue = try self.resolveStructMemberLValue(node, structure, depth + 1);
            defer lvalue.deinit();
            var value = try self.readFromLValue(&lvalue);
            defer value.deinit();
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            try self.declareAssign(&result, &value, true);
            return result;
        }
        if ((owner_type.category() == .Array or owner_type.category() == .ArraySlice) and
            std.mem.eql(u8, access.member_name, "length"))
        {
            if (owner_type.category() == .Array and
                access.expression.nodeKind() == .member_access)
            {
                const code_access = access.expression.payload.member_access;
                if (std.mem.eql(u8, code_access.member_name, "code") and
                    (try expressionType(code_access.expression)).category() == .Address)
                {
                    var owner = try self.emitExpression(code_access.expression, depth + 1);
                    defer owner.deinit();
                    const owner_text = try self.convertedValueTextAlloc(
                        &owner,
                        self.context.type_provider.address(),
                    );
                    defer self.allocator.free(owner_text);
                    const expression = try std.fmt.allocPrint(
                        self.allocator,
                        "extcodesize({s})",
                        .{owner_text},
                    );
                    defer self.allocator.free(expression);
                    var result = try self.variableFromExpression(
                        node,
                    );
                    errdefer result.deinit();
                    try self.setLocation(node);
                    try self.defineText(&result, expression);
                    return result;
                }
            }
            var owner = try self.emitExpression(access.expression, depth + 1);
            defer owner.deinit();
            const owner_text = try owner.commaSeparatedListAlloc();
            defer self.allocator.free(owner_text);
            const array_type = if (owner_type.category() == .Array)
                owner_type
            else
                owner_type.payload.ArraySlice.array_type;
            const length = try self.utils.arrayLengthFunction(array_type);
            defer self.allocator.free(length);
            const expression = try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})",
                .{ length, owner_text },
            );
            defer self.allocator.free(expression);
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (owner_type.category() == .FixedBytes and
            std.mem.eql(u8, access.member_name, "length"))
        {
            var owner = try self.emitExpression(access.expression, depth + 1);
            defer owner.deinit();
            const expression = try std.fmt.allocPrint(
                self.allocator,
                "{d}",
                .{owner_type.payload.FixedBytes.bytes},
            );
            defer self.allocator.free(expression);
            var result = try self.variableFromExpression(node);
            errdefer result.deinit();
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (owner_type.category() == .TypeType)
            return self.emitTypeTypeMemberAccess(node, depth + 1);
        if (owner_type.category() == .Module)
            return self.emitModuleMemberAccess(node, depth + 1);
        if (owner_type.category() != .Magic) return error.UnsupportedExpression;
        const magic = owner_type.payload.Magic;
        if (std.mem.eql(u8, access.member_name, "creationCode") or
            std.mem.eql(u8, access.member_name, "runtimeCode"))
        {
            const type_argument = magic.type_argument orelse return error.InvalidAst;
            const contract_type = switch (type_argument.payload) {
                .Contract => |value| value,
                else => return error.InvalidAst,
            };
            if (contract_type.is_super) return error.InvalidAst;
            const contract = contract_type.declaration;
            try self.context.addSubObject(contract);
            const creation_object = try Common.creationObjectAlloc(
                self.allocator,
                self.context.compatibility_ids,
                contract,
            );
            defer self.allocator.free(creation_object);
            const object_path = if (std.mem.eql(u8, access.member_name, "runtimeCode")) path: {
                const deployed_object = try Common.deployedObjectAlloc(
                    self.allocator,
                    self.context.compatibility_ids,
                    contract,
                );
                defer self.allocator.free(deployed_object);
                break :path try std.fmt.allocPrint(
                    self.allocator,
                    "{s}.{s}",
                    .{ creation_object, deployed_object },
                );
            } else try self.allocator.dupe(u8, creation_object);
            defer self.allocator.free(object_path);
            const quoted_object = try CommonData.escapeAndQuoteStringAlloc(
                self.allocator,
                object_path,
            );
            defer self.allocator.free(quoted_object);
            const allocation = try self.utils.allocationFunction();
            defer self.allocator.free(allocation);
            const size = try self.context.newYulVariable();
            defer self.allocator.free(size);
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            const result_text = try result.commaSeparatedListAlloc();
            defer self.allocator.free(result_text);
            if (result_text.len == 0) return error.InvalidAst;
            try self.setLocation(node);
            try self.appendFmt(
                "let {s} := datasize({s})\nlet {s} := {s}(add({s}, 32))\nmstore({s}, {s})\ndatacopy(add({s}, 32), dataoffset({s}), {s})\n",
                .{
                    size,
                    quoted_object,
                    result_text,
                    allocation,
                    size,
                    result_text,
                    size,
                    result_text,
                    quoted_object,
                    size,
                },
            );
            return result;
        }
        if (std.mem.eql(u8, access.member_name, "name")) {
            const type_argument = magic.type_argument orelse return error.InvalidAst;
            const contract = switch (type_argument.payload) {
                .Contract => |value| value.declaration,
                else => return error.InvalidAst,
            };
            const declaration = contract.declarationConst() orelse return error.InvalidAst;
            const copy = try self.utils.copyLiteralToMemoryFunction(declaration.name);
            defer self.allocator.free(copy);
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            const expression = try std.fmt.allocPrint(
                self.allocator,
                "{s}()",
                .{copy},
            );
            defer self.allocator.free(expression);
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (std.mem.eql(u8, access.member_name, "interfaceId")) {
            const type_argument = magic.type_argument orelse return error.InvalidAst;
            const contract_type = switch (type_argument.payload) {
                .Contract => |value| value,
                else => return error.InvalidAst,
            };
            if (contract_type.is_super) return error.InvalidAst;
            const interface_id = try ASTImplementation.contractInterfaceId(
                self.context.type_provider,
                self.allocator,
                contract_type.declaration,
            );
            const expression = try Numeric.toCompactHexWithPrefixAlloc(
                u256,
                self.allocator,
                @as(u256, interface_id) << 224,
            );
            defer self.allocator.free(expression);
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (std.mem.eql(u8, access.member_name, "min") or
            std.mem.eql(u8, access.member_name, "max"))
            return self.emitMetaTypeBound(node, magic, access.member_name);
        if (std.mem.eql(u8, access.member_name, "sig")) {
            const mask = @as(u256, 0xffffffff) << 224;
            const mask_text = try Numeric.toCompactHexWithPrefixAlloc(
                u256,
                self.allocator,
                mask,
            );
            defer self.allocator.free(mask_text);
            const expression = try std.fmt.allocPrint(
                self.allocator,
                "and(calldataload(0), {s})",
                .{mask_text},
            );
            defer self.allocator.free(expression);
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (std.mem.eql(u8, access.member_name, "data")) {
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            var offset = try result.part("offset");
            defer offset.deinit();
            var length = try result.part("length");
            defer length.deinit();
            try self.setLocation(node);
            try self.defineText(&offset, "0");
            try self.defineText(&length, "calldatasize()");
            return result;
        }
        const expression = if (std.mem.eql(u8, access.member_name, "coinbase"))
            "coinbase()"
        else if (std.mem.eql(u8, access.member_name, "timestamp"))
            "timestamp()"
        else if (std.mem.eql(u8, access.member_name, "difficulty") or
            std.mem.eql(u8, access.member_name, "prevrandao"))
            if (self.context.evm_version.hasPrevRandao())
                "prevrandao()"
            else
                "difficulty()"
        else if (std.mem.eql(u8, access.member_name, "number"))
            "number()"
        else if (std.mem.eql(u8, access.member_name, "gaslimit"))
            "gaslimit()"
        else if (std.mem.eql(u8, access.member_name, "sender"))
            "caller()"
        else if (std.mem.eql(u8, access.member_name, "value"))
            "callvalue()"
        else if (std.mem.eql(u8, access.member_name, "origin"))
            "origin()"
        else if (std.mem.eql(u8, access.member_name, "gasprice"))
            "gasprice()"
        else if (std.mem.eql(u8, access.member_name, "chainid"))
            "chainid()"
        else if (std.mem.eql(u8, access.member_name, "basefee"))
            "basefee()"
        else if (std.mem.eql(u8, access.member_name, "blobbasefee"))
            "blobbasefee()"
        else
            return error.UnsupportedExpression;
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        if (try TypeBehavior.sizeOnStack(result.type_ref) != 1)
            return error.UnsupportedExpression;
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitTypeTypeMemberAccess(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .member_access)
            return error.InvalidAst;
        const access = node.payload.member_access;
        const owner_type = (try expressionType(access.expression)).asTypeType() orelse
            return error.InvalidAst;
        const annotation = try memberAccessAnnotation(node);

        switch (owner_type.actual_type.payload) {
            .Contract => |contract_type| {
                const declaration = annotation.referenced_declaration;
                if (contract_type.is_super) {
                    const function = declaration orelse return error.InvalidAst;
                    if (function.nodeKind() != .function_definition)
                        return error.InvalidAst;
                    var result = try self.variableFromExpression(
                        node,
                    );
                    errdefer result.deinit();
                    if (!annotation.expression.called_directly) {
                        const most_derived = try self.context.mostDerivedContract();
                        const search_start = (try ASTImplementation.superContract(
                            contract_type.declaration,
                            most_derived,
                        )) orelse return error.InvalidAst;
                        const resolved = try ASTImplementation.resolveCallableVirtual(
                            self.context.type_provider,
                            function,
                            most_derived,
                            search_start,
                        );
                        try self.assignInternalFunctionId(&result, resolved, node);
                    } else try self.setLocation(node);
                    return result;
                }

                if (declaration) |referenced|
                    if (referenced.nodeKind() == .variable_declaration)
                        return self.emitVariableReference(node, referenced);

                const result_type = try expressionType(node);
                if (result_type.asFunction()) |function_type| {
                    var result = try self.variableFromExpression(
                        node,
                    );
                    errdefer result.deinit();
                    switch (function_type.kind) {
                        .Declaration, .Event, .Error => {
                            try self.setLocation(node);
                            return result;
                        },
                        .Internal => {
                            const function = declaration orelse return error.InvalidAst;
                            if (function.nodeKind() != .function_definition)
                                return error.InvalidAst;
                            if (!annotation.expression.called_directly)
                                try self.assignInternalFunctionId(&result, function, node)
                            else
                                try self.setLocation(node);
                            return result;
                        },
                        .DelegateCall => {
                            const function = declaration orelse return error.InvalidAst;
                            if (function.nodeKind() != .function_definition)
                                return error.InvalidAst;
                            var owner = try self.emitExpression(
                                access.expression,
                                depth + 1,
                            );
                            defer owner.deinit();
                            var address = try result.part("address");
                            defer address.deinit();
                            var selector = try result.part("functionSelector");
                            defer selector.deinit();
                            const owner_text = try self.convertedValueTextAlloc(
                                &owner,
                                address.type_ref,
                            );
                            defer self.allocator.free(owner_text);
                            const selector_value = try TypeBehavior.externalIdentifier(
                                self.context.type_provider,
                                self.allocator,
                                function_type.*,
                            );
                            const selector_text = try Numeric.toCompactHexWithPrefixAlloc(
                                u256,
                                self.allocator,
                                selector_value,
                            );
                            defer self.allocator.free(selector_text);
                            try self.setLocation(node);
                            try self.defineText(&address, owner_text);
                            try self.defineText(&selector, selector_text);
                            return result;
                        },
                        else => return error.InvalidAst,
                    }
                }
                if (result_type.category() == .TypeType) {
                    try self.setLocation(node);
                    return self.variableFromExpression(
                        node,
                    );
                }
                return error.InvalidAst;
            },
            .Enum => return error.InvalidAst,
            .UserDefinedValueType => {
                if (!std.mem.eql(u8, access.member_name, "wrap") and
                    !std.mem.eql(u8, access.member_name, "unwrap"))
                    return error.InvalidAst;
            },
            .Array => |array| {
                if (!array.isByteArrayOrString() or
                    !std.mem.eql(u8, access.member_name, "concat"))
                    return error.InvalidAst;
            },
            else => return error.InvalidAst,
        }
        try self.setLocation(node);
        return self.variableFromExpression(node);
    }

    fn emitModuleMemberAccess(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .member_access)
            return error.InvalidAst;
        const access = node.payload.member_access;
        var owner = try self.emitExpression(access.expression, depth + 1);
        defer owner.deinit();
        const annotation = try memberAccessAnnotation(node);
        const declaration = annotation.referenced_declaration;
        if (declaration) |referenced| switch (referenced.nodeKind()) {
            .variable_declaration => return self.emitVariableReference(node, referenced),
            .function_definition => {
                var result = try self.variableFromExpression(
                    node,
                );
                errdefer result.deinit();
                if (!annotation.expression.called_directly)
                    try self.assignInternalFunctionId(&result, referenced, node)
                else
                    try self.setLocation(node);
                return result;
            },
            .contract_definition => {
                var result = try self.variableFromExpression(
                    node,
                );
                errdefer result.deinit();
                if (referenced.payload.contract_definition.contract_kind == .Library) {
                    var address = try result.part("address");
                    defer address.deinit();
                    const symbol = try self.linkerSymbolAlloc(referenced);
                    defer self.allocator.free(symbol);
                    try self.setLocation(node);
                    try self.defineText(&address, symbol);
                } else try self.setLocation(node);
                return result;
            },
            .error_definition, .event_definition, .import_directive => {
                try self.setLocation(node);
                return self.variableFromExpression(
                    node,
                );
            },
            else => {},
        };
        const result_type = try expressionType(node);
        if (result_type.category() != .TypeType and
            result_type.category() != .Module)
            return error.InvalidAst;
        try self.setLocation(node);
        return self.variableFromExpression(node);
    }

    fn resolveStructMemberLValue(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        structure: Types.StructType,
        depth: usize,
    ) GeneratorError!IRLValueModule.IRLValue {
        if (depth >= max_ast_depth or node.nodeKind() != .member_access)
            return error.InvalidAst;
        const access = node.payload.member_access;
        var owner = try self.emitExpression(access.expression, depth + 1);
        defer owner.deinit();
        const member_type = try expressionType(node);
        switch (structure.reference.location) {
            .Storage => {
                var base = try owner.part("slot");
                defer base.deinit();
                const base_text = try base.nameAlloc();
                defer self.allocator.free(base_text);
                const member_offset = try TypeBehavior.structStorageOffsetOfMember(
                    self.allocator,
                    structure,
                    access.member_name,
                );
                const slot = try self.context.newYulVariable();
                defer self.allocator.free(slot);
                try self.setLocation(node);
                try self.appendFmt(
                    "let {s} := add({s}, {d})\n",
                    .{ slot, base_text, member_offset.slot },
                );
                return IRLValueModule.IRLValue.initStorage(
                    self.allocator,
                    member_type,
                    slot,
                    .{ .constant = member_offset.byte_offset },
                    false,
                );
            },
            .Memory => {
                var base = try owner.part("mpos");
                defer base.deinit();
                const base_text = try base.nameAlloc();
                defer self.allocator.free(base_text);
                const member_offset = try TypeBehavior.structMemoryOffsetOfMember(
                    structure,
                    access.member_name,
                );
                const address = try self.context.newYulVariable();
                defer self.allocator.free(address);
                try self.setLocation(node);
                try self.appendFmt(
                    "let {s} := add({s}, {d})\n",
                    .{ address, base_text, member_offset },
                );
                return IRLValueModule.IRLValue.initMemory(
                    self.allocator,
                    member_type,
                    address,
                    false,
                );
            },
            .CallData, .Transient => return error.UnsupportedLValue,
        }
    }

    fn emitCalldataStructMember(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        structure: Types.StructType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .member_access)
            return error.InvalidAst;
        const access = node.payload.member_access;
        var owner = try self.emitExpression(access.expression, depth + 1);
        defer owner.deinit();
        var base = try owner.part("offset");
        defer base.deinit();
        const base_text = try base.nameAlloc();
        defer self.allocator.free(base_text);
        const member_offset = try TypeBehavior.structCalldataOffsetOfMember(
            structure,
            access.member_name,
        );
        const address = try self.context.newYulVariable();
        defer self.allocator.free(address);
        try self.setLocation(node);
        try self.appendFmt(
            "let {s} := add({s}, {d})\n",
            .{ address, base_text, member_offset },
        );
        var result = try self.variableFromExpression(
            node,
        );
        errdefer result.deinit();
        const expression = if (TypeBehavior.isDynamicallyEncoded(result.type_ref)) blk: {
            const tail = try self.utils.accessCalldataTailFunction(result.type_ref);
            defer self.allocator.free(tail);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}({s}, {s})",
                .{ tail, base_text, address },
            );
        } else if (result.type_ref.category() == .Array or
            result.type_ref.category() == .Struct)
            try self.allocator.dupe(u8, address)
        else blk: {
            const read = try self.utils.readFromCalldata(result.type_ref);
            defer self.allocator.free(read);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})",
                .{ read, address },
            );
        };
        defer self.allocator.free(expression);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitMetaTypeBound(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        magic: Types.MagicType,
        member_name: []const u8,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (magic.kind != .MetaType) return error.UnsupportedExpression;
        const type_argument = magic.type_argument orelse return error.InvalidAst;
        const value: u256 = switch (type_argument.payload) {
            .Integer => |integer| blk: {
                const magnitude_bits = if (integer.isSigned())
                    integer.bits - 1
                else
                    integer.bits;
                const bit = if (magnitude_bits == 256)
                    @as(u256, 0)
                else
                    @as(u256, 1) << @intCast(magnitude_bits);
                if (std.mem.eql(u8, member_name, "max"))
                    break :blk if (magnitude_bits == 256)
                        std.math.maxInt(u256)
                    else
                        bit - 1;
                break :blk if (integer.isSigned())
                    @as(u256, 0) -% bit
                else
                    0;
            },
            .Enum => |enum_type| blk: {
                const members = enum_type.declaration.payload.enum_definition.members;
                if (members.len == 0) return error.InvalidAst;
                break :blk if (std.mem.eql(u8, member_name, "max"))
                    @as(u256, @intCast(members.len - 1))
                else
                    0;
            },
            else => return error.UnsupportedExpression,
        };
        const expression = try Numeric.toCompactHexWithPrefixAlloc(
            u256,
            self.allocator,
            value,
        );
        defer self.allocator.free(expression);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitIndexAccess(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .index_access)
            return error.InvalidAst;
        const access = node.payload.index_access;
        const base_type = try expressionType(access.base);
        if (underlyingArrayType(base_type)) |array_type| {
            if (array_type.payload.Array.reference.location == .CallData)
                return self.emitCalldataArrayIndex(node, array_type, depth + 1);
        }
        if (base_type.category() == .FixedBytes)
            return self.emitFixedBytesIndex(node, base_type.payload.FixedBytes, depth + 1);
        if (base_type.category() == .TypeType)
            return self.variableFromExpression(node);
        var lvalue = try self.resolveIndexLValue(node, depth + 1);
        defer lvalue.deinit();
        var temporary = try self.readFromLValue(&lvalue);
        defer temporary.deinit();
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        try self.declareAssign(&result, &temporary, true);
        return result;
    }

    fn emitCalldataArrayIndex(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        array_type: *const Types.Type,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .index_access)
            return error.InvalidAst;
        const access = node.payload.index_access;
        const index_node = access.index orelse return error.InvalidAst;
        const array = array_type.payload.Array;
        if (array.reference.location != .CallData) return error.InvalidAst;
        var base = try self.emitExpression(access.base, depth + 1);
        defer base.deinit();
        const base_text = try base.commaSeparatedListAlloc();
        defer self.allocator.free(base_text);
        var index = try self.emitExpression(index_node, depth + 1);
        defer index.deinit();
        // Upstream requests the bounds-checked access helper before rendering
        // the converted index expression. The collector preserves that order.
        const index_function = try self.utils.calldataArrayIndexAccessFunction(array_type);
        defer self.allocator.free(index_function);
        const index_text = try self.convertedValueTextAlloc(
            &index,
            self.context.type_provider.uint256(),
        );
        defer self.allocator.free(index_text);
        const address = try std.fmt.allocPrint(
            self.allocator,
            "{s}({s}, {s})",
            .{ index_function, base_text, index_text },
        );
        defer self.allocator.free(address);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        const expression = if (array.isByteArrayOrString()) blk: {
            const cleanup = try self.utils.cleanupFunction(array.base_type);
            defer self.allocator.free(cleanup);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}(calldataload({s}))",
                .{ cleanup, address },
            );
        } else if (TypeBehavior.isValueType(array.base_type)) blk: {
            const read = try self.utils.readFromCalldata(array.base_type);
            defer self.allocator.free(read);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})",
                .{ read, address },
            );
        } else try self.allocator.dupe(u8, address);
        defer self.allocator.free(expression);
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitFixedBytesIndex(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        fixed_bytes: Types.FixedBytesType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .index_access)
            return error.InvalidAst;
        const access = node.payload.index_access;
        const index_node = access.index orelse return error.InvalidAst;
        var base = try self.emitExpression(access.base, depth + 1);
        defer base.deinit();
        const base_text = try base.nameAlloc();
        defer self.allocator.free(base_text);
        var raw_index = try self.emitExpression(index_node, depth + 1);
        defer raw_index.deinit();
        const index_name = try self.context.newYulVariable();
        defer self.allocator.free(index_name);
        var index = try IRVariableModule.IRVariable.init(
            self.allocator,
            index_name,
            self.context.type_provider.uint256(),
        );
        defer index.deinit();
        try self.setLocation(node);
        try self.assignConverted(&index, &raw_index, true);
        const index_text = try index.nameAlloc();
        defer self.allocator.free(index_text);
        const panic = try self.utils.panicFunction(.array_out_of_bounds);
        defer self.allocator.free(panic);
        const shift = try self.utils.shiftLeftFunction(248);
        defer self.allocator.free(shift);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "{s}(byte({s}, {s}))",
            .{ shift, index_text, base_text },
        );
        defer self.allocator.free(expression);
        try self.appendFmt(
            "if iszero(lt({s}, {d})) {{ {s}() }}\n",
            .{ index_text, fixed_bytes.bytes, panic },
        );
        try self.defineText(&result, expression);
        return result;
    }

    fn emitIndexRangeAccess(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .index_range_access)
            return error.InvalidAst;
        const access = node.payload.index_range_access;
        const base_type = try expressionType(access.base);
        const array_type = underlyingArrayType(base_type) orelse
            return error.UnsupportedExpression;
        const array = array_type.payload.Array;
        if (array.reference.location != .CallData or !array.isDynamicallySized())
            return error.UnsupportedExpression;
        var base = try self.emitExpression(access.base, depth + 1);
        defer base.deinit();
        var start_value: ?IRVariableModule.IRVariable = null;
        defer if (start_value) |*value| value.deinit();
        if (access.start) |start_node|
            start_value = try self.emitExpression(start_node, depth + 1);
        var end_value: ?IRVariableModule.IRVariable = null;
        defer if (end_value) |*value| value.deinit();
        if (access.end) |end_node|
            end_value = try self.emitExpression(end_node, depth + 1);

        try self.setLocation(node);
        const uint256_type = self.context.type_provider.uint256();
        const start_name = try self.context.newYulVariable();
        defer self.allocator.free(start_name);
        var slice_start = try IRVariableModule.IRVariable.init(
            self.allocator,
            start_name,
            uint256_type,
        );
        defer slice_start.deinit();
        if (start_value) |*value|
            try self.assignConverted(&slice_start, value, true)
        else
            try self.defineText(&slice_start, "0");

        const end_name = try self.context.newYulVariable();
        defer self.allocator.free(end_name);
        var slice_end = try IRVariableModule.IRVariable.init(
            self.allocator,
            end_name,
            uint256_type,
        );
        defer slice_end.deinit();
        if (end_value) |*value| {
            try self.assignConverted(&slice_end, value, true);
        } else {
            var length = try base.part("length");
            defer length.deinit();
            try self.declareAssign(&slice_end, &length, true);
        }

        const base_text = try base.commaSeparatedListAlloc();
        defer self.allocator.free(base_text);
        const start_text = try slice_start.nameAlloc();
        defer self.allocator.free(start_text);
        const end_text = try slice_end.nameAlloc();
        defer self.allocator.free(end_text);
        const range = try self.utils.calldataArrayIndexRangeAccess(array_type);
        defer self.allocator.free(range);
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "{s}({s}, {s}, {s})",
            .{ range, base_text, start_text, end_text },
        );
        defer self.allocator.free(expression);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.defineText(&result, expression);
        return result;
    }

    fn emitIdentifier(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
    ) GeneratorError!IRVariableModule.IRVariable {
        const annotation = try identifierAnnotation(node);
        const declaration = annotation.referenced_declaration orelse
            return error.InvalidAst;
        try self.setLocation(node);
        if (declaration.nodeKind() == .magic_variable_declaration) {
            var result = try self.variableFromExpression(node);
            errdefer result.deinit();
            const name = node.payload.identifier.name;
            const expression = if (std.mem.eql(u8, name, "this"))
                "address()"
            else if (std.mem.eql(u8, name, "now"))
                "timestamp()"
            else if (try TypeBehavior.sizeOnStack(result.type_ref) == 0)
                return result
            else
                return error.InvalidAst;
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        if (declaration.nodeKind() == .function_definition) {
            var result = try self.variableFromExpression(node);
            errdefer result.deinit();
            if (annotation.expression.called_directly) return result;
            const lookup = annotation.required_lookup.value orelse return error.InvalidAst;
            const resolved = if (lookup == .Virtual)
                try ASTImplementation.resolveCallableVirtual(
                    self.context.type_provider,
                    declaration,
                    try self.context.mostDerivedContract(),
                    null,
                )
            else
                declaration;
            try self.assignInternalFunctionId(&result, resolved, node);
            return result;
        }
        if (declaration.nodeKind() == .contract_definition) {
            var result = try self.variableFromExpression(node);
            errdefer result.deinit();
            if (declaration.payload.contract_definition.contract_kind == .Library) {
                var address = try result.part("address");
                defer address.deinit();
                const symbol = try self.linkerSymbolAlloc(declaration);
                defer self.allocator.free(symbol);
                try self.setLocation(node);
                try self.defineText(&address, symbol);
            }
            return result;
        }
        if (declaration.nodeKind() == .event_definition or
            declaration.nodeKind() == .error_definition or
            declaration.nodeKind() == .enum_definition or
            declaration.nodeKind() == .struct_definition or
            declaration.nodeKind() == .import_directive or
            declaration.nodeKind() == .user_defined_value_type_definition)
            return self.variableFromExpression(node);
        if (declaration.nodeKind() != .variable_declaration)
            return error.InvalidAst;
        if (annotation.expression.will_be_written_to)
            return error.UnsupportedLValue;
        return self.emitVariableReference(node, declaration);
    }

    fn emitVariableReference(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        declaration: *const AST.Node,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (declaration.nodeKind() != .variable_declaration)
            return error.InvalidAst;
        try self.setLocation(node);

        if (declaration.payload.variable_declaration.mutability == .Constant and
            (ASTImplementation.isStateVariable(declaration) or
                !ASTImplementation.isLocalVariable(declaration)))
        {
            var result = try self.variableFromExpression(node);
            errdefer result.deinit();
            const function = try self.constantValueFunction(declaration);
            defer self.allocator.free(function);
            const call = try std.fmt.allocPrint(self.allocator, "{s}()", .{function});
            defer self.allocator.free(call);
            try self.defineText(&result, call);
            return result;
        }

        var temporary = if (self.context.isLocalVariable(declaration)) blk: {
            const local = try self.context.localVariable(declaration);
            const raw_name = try self.context.newYulVariable();
            defer self.allocator.free(raw_name);
            var value = try IRVariableModule.IRVariable.init(
                self.allocator,
                raw_name,
                local.type_ref,
            );
            errdefer value.deinit();
            try self.declareAssign(&value, local, true);
            break :blk value;
        } else if (self.context.isStateVariable(declaration)) blk: {
            var lvalue = try self.stateVariableLValue(declaration);
            defer lvalue.deinit();
            break :blk try self.readFromLValue(&lvalue);
        } else if (ASTImplementation.isStateVariable(declaration) and
            declaration.payload.variable_declaration.mutability == .Immutable)
        blk: {
            var lvalue = IRLValueModule.IRLValue.initImmutable(
                self.allocator,
                try variableType(declaration),
                declaration,
            );
            defer lvalue.deinit();
            break :blk try self.readFromLValue(&lvalue);
        } else return error.UnsupportedLValue;
        defer temporary.deinit();

        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.declareAssign(&result, &temporary, true);
        return result;
    }

    fn emitLiteral(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
    ) GeneratorError!IRVariableModule.IRVariable {
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        if (result.type_ref.category() == .StringLiteral)
            return result;
        const value = try literalValueAlloc(self.allocator, node, result.type_ref);
        defer self.allocator.free(value);
        try self.defineText(&result, value);
        return result;
    }

    fn emitBinaryOperation(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        const operation = node.payload.binary_operation;
        const annotation = try binaryOperationAnnotation(node);
        if (annotation.operation.user_defined_function.value orelse null) |function|
            return self.emitUserDefinedBinaryOperation(
                node,
                function,
                operation.left,
                operation.right,
                depth + 1,
            );
        const common_type = annotation.common_type orelse return error.InvalidAst;
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();

        if (common_type.category() == .RationalNumber) {
            const folded = try literalValueAlloc(self.allocator, node, result.type_ref);
            defer self.allocator.free(folded);
            try self.setLocation(node);
            try self.defineText(&result, folded);
            return result;
        }

        if (operation.operator == .And or operation.operator == .Or) {
            var left = try self.emitExpression(operation.left, depth + 1);
            defer left.deinit();
            try self.setLocation(node);
            try self.assignConverted(&result, &left, true);
            const result_name = try result.nameAlloc();
            defer self.allocator.free(result_name);
            if (operation.operator == .Or)
                try self.appendFmt("if iszero({s}) {{\n", .{result_name})
            else
                try self.appendFmt("if {s} {{\n", .{result_name});
            var right = try self.emitExpression(operation.right, depth + 1);
            defer right.deinit();
            try self.setLocation(node);
            try self.assignConverted(&result, &right, false);
            try self.append("}\n");
            return result;
        }

        var left = try self.emitExpression(operation.left, depth + 1);
        defer left.deinit();
        var right = try self.emitExpression(operation.right, depth + 1);
        defer right.deinit();
        if (operation.operator == .Exp) {
            try self.setLocation(node);

            var converted_left_storage: ?IRVariableModule.IRVariable = null;
            defer if (converted_left_storage) |*value| value.deinit();
            const converted_left = if (TypeBehavior.equals(left.type_ref, common_type))
                &left
            else blk: {
                const name = try self.context.newYulVariable();
                defer self.allocator.free(name);
                converted_left_storage = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    name,
                    common_type,
                );
                try self.assignConverted(&converted_left_storage.?, &left, true);
                break :blk &converted_left_storage.?;
            };

            const right_mobile_type = (try TypeBehavior.mobileType(
                self.context.type_provider,
                right.type_ref,
            )) orelse return error.InvalidAst;
            var converted_right_storage: ?IRVariableModule.IRVariable = null;
            defer if (converted_right_storage) |*value| value.deinit();
            const converted_right = if (TypeBehavior.equals(right.type_ref, right_mobile_type))
                &right
            else blk: {
                const name = try self.context.newYulVariable();
                defer self.allocator.free(name);
                converted_right_storage = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    name,
                    right_mobile_type,
                );
                try self.assignConverted(&converted_right_storage.?, &right, true);
                break :blk &converted_right_storage.?;
            };

            const base_integer = converted_left.type_ref.asInteger() orelse
                return error.UnsupportedExpression;
            const exponent_integer = converted_right.type_ref.asInteger() orelse
                return error.UnsupportedExpression;
            const base_source_type = try expressionType(operation.left);
            const function = if (self.context.arithmetic == .Wrapping)
                try self.utils.wrappingIntExpFunction(
                    base_integer.*,
                    exponent_integer.*,
                )
            else if (base_source_type.category() == .RationalNumber)
                try self.utils.overflowCheckedIntLiteralExpFunction(
                    base_source_type,
                    exponent_integer.*,
                    base_integer.*,
                )
            else
                try self.utils.overflowCheckedIntExpFunction(
                    base_integer.*,
                    exponent_integer.*,
                );
            defer self.allocator.free(function);
            const left_text = try converted_left.nameAlloc();
            defer self.allocator.free(left_text);
            const right_text = try converted_right.nameAlloc();
            defer self.allocator.free(right_text);
            const expression = if (self.context.arithmetic == .Checked and
                base_source_type.category() == .RationalNumber)
                try std.fmt.allocPrint(
                    self.allocator,
                    "{s}({s})",
                    .{ function, right_text },
                )
            else
                try std.fmt.allocPrint(
                    self.allocator,
                    "{s}({s}, {s})",
                    .{ function, left_text, right_text },
                );
            defer self.allocator.free(expression);
            try self.defineText(&result, expression);
            return result;
        }
        if (TokenModule.isShiftOp(operation.operator)) {
            try self.setLocation(node);

            var converted_left_storage: ?IRVariableModule.IRVariable = null;
            defer if (converted_left_storage) |*value| value.deinit();
            const converted_left = if (TypeBehavior.equals(left.type_ref, common_type))
                &left
            else blk: {
                const name = try self.context.newYulVariable();
                defer self.allocator.free(name);
                converted_left_storage = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    name,
                    common_type,
                );
                try self.assignConverted(&converted_left_storage.?, &left, true);
                break :blk &converted_left_storage.?;
            };

            const right_mobile_type = (try TypeBehavior.mobileType(
                self.context.type_provider,
                right.type_ref,
            )) orelse return error.InvalidAst;
            var converted_right_storage: ?IRVariableModule.IRVariable = null;
            defer if (converted_right_storage) |*value| value.deinit();
            const converted_right = if (TypeBehavior.equals(right.type_ref, right_mobile_type))
                &right
            else blk: {
                const name = try self.context.newYulVariable();
                defer self.allocator.free(name);
                converted_right_storage = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    name,
                    right_mobile_type,
                );
                try self.assignConverted(&converted_right_storage.?, &right, true);
                break :blk &converted_right_storage.?;
            };

            const expression = try self.shiftExpressionAlloc(
                operation.operator,
                converted_left,
                converted_right,
            );
            defer self.allocator.free(expression);
            try self.defineText(&result, expression);
            return result;
        }
        const expression = try self.binaryExpressionAlloc(
            operation.operator,
            common_type,
            &left,
            &right,
        );
        defer self.allocator.free(expression);
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitUnaryOperation(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        const operation = node.payload.unary_operation;
        const annotation = try operationAnnotation(node);
        if (annotation.user_defined_function.value orelse null) |function|
            return self.emitUserDefinedUnaryOperation(
                node,
                function,
                operation.sub_expression,
                depth + 1,
            );
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        if (result.type_ref.category() == .RationalNumber) {
            const folded = try literalValueAlloc(self.allocator, node, result.type_ref);
            defer self.allocator.free(folded);
            try self.setLocation(node);
            try self.defineText(&result, folded);
            return result;
        }
        if (operation.operator == .Inc or operation.operator == .Dec or
            operation.operator == .Delete)
        {
            var lvalue = try self.resolveLValue(operation.sub_expression, depth + 1);
            defer lvalue.deinit();
            try self.setLocation(node);
            if (operation.operator == .Delete) {
                switch (lvalue.kind) {
                    .storage => |*storage| {
                        const clear = try self.utils.storageSetToZeroFunction(lvalue.type_ref);
                        defer self.allocator.free(clear);
                        const offset = try storage.offsetStringAlloc(self.allocator);
                        defer self.allocator.free(offset);
                        try self.appendFmt(
                            "{s}({s}, {s})\n",
                            .{ clear, storage.slot, offset },
                        );
                        return result;
                    },
                    .transient_storage => |*storage| {
                        const clear = try self.utils.storageSetToZeroAtLocationFunction(
                            lvalue.type_ref,
                            .Transient,
                        );
                        defer self.allocator.free(clear);
                        const offset = try storage.offsetStringAlloc(self.allocator);
                        defer self.allocator.free(offset);
                        try self.appendFmt(
                            "{s}({s}, {s})\n",
                            .{ clear, storage.slot, offset },
                        );
                        return result;
                    },
                    .stack, .memory => {},
                    else => return error.UnsupportedLValue,
                }
                const raw_name = try self.context.newYulVariable();
                defer self.allocator.free(raw_name);
                var zero = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    raw_name,
                    lvalue.type_ref,
                );
                defer zero.deinit();
                const zero_function = try self.utils.zeroValueFunction(lvalue.type_ref, true);
                defer self.allocator.free(zero_function);
                const call = try std.fmt.allocPrint(
                    self.allocator,
                    "{s}()",
                    .{zero_function},
                );
                defer self.allocator.free(call);
                try self.defineText(&zero, call);
                try self.writeToLValue(&lvalue, &zero);
                return result;
            }

            const integer = result.type_ref.asInteger() orelse
                return error.UnsupportedExpression;
            const modified_name = try self.context.newYulVariable();
            defer self.allocator.free(modified_name);
            var modified = try IRVariableModule.IRVariable.init(
                self.allocator,
                modified_name,
                result.type_ref,
            );
            defer modified.deinit();
            var original = try self.readFromLValue(&lvalue);
            defer original.deinit();
            const function = if (operation.operator == .Inc)
                if (self.context.arithmetic == .Checked)
                    try self.utils.incrementCheckedFunction(integer.*)
                else
                    try self.utils.incrementWrappingFunction(integer.*)
            else if (self.context.arithmetic == .Checked)
                try self.utils.decrementCheckedFunction(integer.*)
            else
                try self.utils.decrementWrappingFunction(integer.*);
            defer self.allocator.free(function);
            const original_text = try original.commaSeparatedListAlloc();
            defer self.allocator.free(original_text);
            const call = try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})",
                .{ function, original_text },
            );
            defer self.allocator.free(call);
            try self.defineText(&modified, call);
            try self.writeToLValue(&lvalue, &modified);
            try self.declareAssign(
                &result,
                if (operation.is_prefix) &modified else &original,
                true,
            );
            return result;
        }
        var operand = try self.emitExpression(operation.sub_expression, depth + 1);
        defer operand.deinit();
        const operand_text = try operand.commaSeparatedListAlloc();
        defer self.allocator.free(operand_text);
        const expression = switch (operation.operator) {
            .Not => blk: {
                const cleanup = try self.utils.cleanupFunction(result.type_ref);
                defer self.allocator.free(cleanup);
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "{s}(iszero({s}))",
                    .{ cleanup, operand_text },
                );
            },
            .BitNot => blk: {
                const cleanup = try self.utils.cleanupFunction(result.type_ref);
                defer self.allocator.free(cleanup);
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "{s}(not({s}))",
                    .{ cleanup, operand_text },
                );
            },
            .Sub => blk: {
                const integer = result.type_ref.asInteger() orelse
                    return error.UnsupportedExpression;
                const function = if (self.context.arithmetic == .Checked)
                    try self.utils.negateNumberCheckedFunction(integer.*)
                else
                    try self.utils.negateNumberWrappingFunction(integer.*);
                defer self.allocator.free(function);
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "{s}({s})",
                    .{ function, operand_text },
                );
            },
            else => return error.UnsupportedExpression,
        };
        defer self.allocator.free(expression);
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitAssignment(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        const assignment = node.payload.assignment;
        var right = try self.emitExpression(assignment.right_hand_side, depth + 1);
        defer right.deinit();
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();

        const binary_operator = if (assignment.operator == .Assign)
            AST.Token.Assign
        else
            TokenModule.assignmentToBinaryOp(assignment.operator) catch
                return error.InvalidAst;
        const left_type = try expressionType(assignment.left_hand_side);
        const value_type = if (TypeBehavior.isValueType(left_type))
            if (TokenModule.isShiftOp(binary_operator))
                (try TypeBehavior.mobileType(
                    self.context.type_provider,
                    right.type_ref,
                )) orelse return error.InvalidAst
            else
                result.type_ref
        else
            right.type_ref;
        const needs_value_conversion = !TypeBehavior.equals(value_type, right.type_ref);
        if (!needs_value_conversion) try self.append("\n");
        try self.setLocation(node);
        var converted: IRVariableModule.IRVariable = undefined;
        var has_converted = false;
        defer if (has_converted) converted.deinit();
        const value = if (needs_value_conversion) blk: {
            const raw_name = try self.context.newYulVariable();
            defer self.allocator.free(raw_name);
            converted = try IRVariableModule.IRVariable.init(
                self.allocator,
                raw_name,
                value_type,
            );
            has_converted = true;
            try self.assignConverted(&converted, &right, true);
            break :blk &converted;
        } else &right;

        var lvalue = try self.resolveLValue(assignment.left_hand_side, depth + 1);
        defer lvalue.deinit();
        try self.setLocation(node);

        if (assignment.operator == .Assign) {
            try self.writeToLValue(&lvalue, value);
            if (lvalue.type_ref.asReference() != null) {
                var stored = try self.readFromLValue(&lvalue);
                defer stored.deinit();
                try self.assignConverted(&result, &stored, true);
            } else if (try TypeBehavior.sizeOnStack(result.type_ref) != 0)
                try self.assignConverted(&result, value, true);
            return result;
        }

        var left = try self.readFromLValue(&lvalue);
        defer left.deinit();
        const expression = try self.binaryExpressionAlloc(
            binary_operator,
            result.type_ref,
            &left,
            value,
        );
        defer self.allocator.free(expression);
        try self.defineText(&result, expression);
        try self.writeToLValue(&lvalue, &result);
        return result;
    }

    fn emitConditional(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        const conditional = node.payload.conditional;
        var condition = try self.emitExpression(conditional.condition, depth + 1);
        defer condition.deinit();
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.declare(&result);
        const condition_text = try self.convertedValueTextAlloc(
            &condition,
            self.context.type_provider.boolean(),
        );
        defer self.allocator.free(condition_text);
        try self.setLocation(node);
        try self.appendFmt("switch {s}\ncase 0 {{\n", .{condition_text});
        var false_value = try self.emitExpression(conditional.false_expression, depth + 1);
        defer false_value.deinit();
        try self.setLocation(node);
        try self.assignConverted(&result, &false_value, false);
        try self.append("}\ndefault {\n");
        var true_value = try self.emitExpression(conditional.true_expression, depth + 1);
        defer true_value.deinit();
        try self.setLocation(node);
        try self.assignConverted(&result, &true_value, false);
        try self.append("}\n");
        return result;
    }

    fn emitTupleExpression(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        const tuple = node.payload.tuple_expression;
        if (tuple.is_inline_array) {
            const result_type = try expressionType(node);
            const array = result_type.asArray() orelse return error.InvalidAst;
            if (array.reference.location != .Memory or array.isDynamicallySized())
                return error.InvalidAst;
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            const allocate = try self.utils.allocateMemoryArrayFunction(result_type);
            defer self.allocator.free(allocate);
            var position = try result.part("mpos");
            defer position.deinit();
            const position_text = try position.nameAlloc();
            defer self.allocator.free(position_text);
            const allocation = try std.fmt.allocPrint(
                self.allocator,
                "{s}({d})",
                .{ allocate, tuple.components.len },
            );
            defer self.allocator.free(allocation);
            try self.setLocation(node);
            try self.defineText(&result, allocation);
            const stride = try TypeBehavior.memoryStride(array.*);
            for (tuple.components, 0..) |maybe_component, index| {
                const component = maybe_component orelse return error.InvalidAst;
                var value = try self.emitExpression(component, depth + 1);
                defer value.deinit();
                var converted = try self.convert(&value, array.base_type);
                defer converted.deinit();
                const converted_text = try converted.commaSeparatedListAlloc();
                defer self.allocator.free(converted_text);
                const write = try self.utils.writeToMemoryFunction(array.base_type);
                defer self.allocator.free(write);
                try self.setLocation(node);
                try self.appendFmt(
                    "{s}(add({s}, {d}), {s})\n",
                    .{ write, position_text, @as(u256, index) * stride, converted_text },
                );
            }
            return result;
        }
        const annotation = try expressionAnnotation(node);
        if (annotation.will_be_written_to) return error.UnsupportedLValue;
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        for (tuple.components, 0..) |component, index| {
            const present = component orelse continue;
            var value = try self.emitExpression(present, depth + 1);
            defer value.deinit();
            var target = if (tuple.components.len == 1)
                try result.clone()
            else
                try result.tupleComponent(index);
            defer target.deinit();
            try self.setLocation(node);
            try self.assignConverted(&target, &value, true);
        }
        return result;
    }

    fn emitFunctionCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        const call = node.payload.function_call;
        const annotation = try functionCallAnnotation(node);
        const kind = annotation.kind.value orelse return error.InvalidAst;
        if (kind == .TypeConversion) {
            if (call.arguments.len != 1) return error.InvalidAst;
            var value = try self.emitExpression(call.arguments[0], depth + 1);
            defer value.deinit();
            var result = try self.variableFromExpression(node);
            errdefer result.deinit();
            try self.setLocation(node);
            try self.assignConverted(&result, &value, true);
            return result;
        }
        if (kind == .StructConstructorCall)
            return self.emitStructConstructorCall(node, depth + 1);
        if (kind != .FunctionCall) return error.UnsupportedFunctionCall;
        const callee_type = try expressionType(call.expression);
        const function_type = callee_type.asFunction() orelse
            return error.UnsupportedFunctionCall;
        if (function_type.kind == .Wrap or function_type.kind == .Unwrap) {
            if (call.arguments.len != 1) return error.InvalidAst;
            var value = try self.emitExpression(call.arguments[0], depth + 1);
            defer value.deinit();
            var result = try self.variableFromExpression(
                node,
            );
            errdefer result.deinit();
            if (try TypeBehavior.sizeOnStack(value.type_ref) !=
                try TypeBehavior.sizeOnStack(result.type_ref))
                return error.UnsupportedConversion;
            const conversion = try self.utils.conversionFunction(
                value.type_ref,
                result.type_ref,
            );
            defer self.allocator.free(conversion);
            const value_text = try value.commaSeparatedListAlloc();
            defer self.allocator.free(value_text);
            const expression = try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})",
                .{ conversion, value_text },
            );
            defer self.allocator.free(expression);
            try self.setLocation(node);
            try self.defineText(&result, expression);
            return result;
        }
        switch (function_type.kind) {
            .ObjectCreation => return self.emitMemoryArrayCreation(node, depth + 1),
            .BytesConcat, .StringConcat => return self.emitBytesOrStringConcat(
                node,
                function_type.kind,
                depth + 1,
            ),
            .ABIDecode => return self.emitAbiDecode(node, depth + 1),
            .ABIEncode,
            .ABIEncodePacked,
            .ABIEncodeWithSelector,
            .ABIEncodeCall,
            .ABIEncodeWithSignature,
            => return self.emitAbiEncode(node, function_type, depth + 1),
            .Assert, .Require => return self.emitRequireOrAssert(
                node,
                function_type,
                depth + 1,
            ),
            .Revert => return self.emitRevertCall(node, depth + 1),
            .Event => return self.emitEventCall(node, function_type, depth + 1),
            .AddMod,
            .MulMod,
            .GasLeft,
            .Selfdestruct,
            .BlockHash,
            .BlobHash,
            => return self.emitScalarBuiltinCall(node, function_type, depth + 1),
            .KECCAK256 => return self.emitKeccak256(node, depth + 1),
            .ERC7201 => return self.emitErc7201(node, depth + 1),
            .ArrayPop => return self.emitArrayPop(node, function_type, depth + 1),
            .ArrayPush => return self.emitArrayPush(node, function_type, depth + 1),
            .External, .DelegateCall => return self.emitExternalCall(
                node,
                function_type,
                depth + 1,
            ),
            .BareCall, .BareDelegateCall, .BareStaticCall => return self.emitBareCall(
                node,
                function_type,
                depth + 1,
            ),
            .Creation => return self.emitContractCreation(node, function_type, depth + 1),
            .Send, .Transfer => return self.emitSendOrTransfer(
                node,
                function_type,
                depth + 1,
            ),
            .ECRecover, .SHA256, .RIPEMD160 => return self.emitPrecompileCall(
                node,
                function_type,
                depth + 1,
            ),
            .Error, .MetaType => return self.emitMarkerCall(node, depth + 1),
            .Internal => {},
            .Declaration,
            .BareCallCode,
            .SetGas,
            .SetValue,
            .Wrap,
            .Unwrap,
            => return error.UnsupportedFunctionCall,
        }
        const declaration = try ASTImplementation.resolveFunctionCall(
            self.context.type_provider,
            node,
            try self.context.mostDerivedContract(),
        );
        if (declaration) |definition|
            if (definition.nodeKind() != .function_definition or
                !definition.payload.function_definition.implemented())
                return error.InvalidAst;

        var arguments: std.ArrayList([]u8) = .empty;
        defer {
            for (arguments.items) |argument| self.allocator.free(argument);
            arguments.deinit(self.allocator);
        }
        var bound_callee: ?IRVariableModule.IRVariable = null;
        defer if (bound_callee) |*callee| callee.deinit();
        if (function_type.options.has_bound_first_argument) {
            bound_callee = try self.emitExpression(call.expression, depth + 1);
            var self_value = try bound_callee.?.part("self");
            defer self_value.deinit();
            try self_value.appendStackSlots(self.allocator, &arguments);
        } else if (declaration == null) {
            bound_callee = try self.emitExpression(call.expression, depth + 1);
        }
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const sorted_arguments = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
            self.context.type_provider,
            self.allocator,
            node,
        );
        defer self.allocator.free(sorted_arguments);
        const parameter_types = function_type.parameterTypes();
        if (sorted_arguments.len != parameter_types.len)
            return error.InvalidAst;
        for (sorted_arguments, parameter_types) |argument_node, target_type| {
            const argument = try evaluated.find(argument_node);
            if (TypeBehavior.equals(argument.type_ref, target_type)) {
                try argument.appendStackSlots(self.allocator, &arguments);
                continue;
            }
            const converted_name = try self.context.newYulVariable();
            defer self.allocator.free(converted_name);
            var converted = try IRVariableModule.IRVariable.init(
                self.allocator,
                converted_name,
                target_type,
            );
            defer converted.deinit();
            try self.assignConverted(&converted, argument, true);
            try converted.appendStackSlots(self.allocator, &arguments);
        }
        const joined = try joinAlloc(self.allocator, arguments.items, ", ");
        defer self.allocator.free(joined);
        const expression = if (declaration) |definition| blk: {
            const function_name = try self.context.enqueueFunctionForCodeGeneration(definition);
            defer self.allocator.free(function_name);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})",
                .{ function_name, joined },
            );
        } else blk: {
            const callee = if (bound_callee) |*value| value else return error.InvalidAst;
            var function_identifier = try callee.part("functionIdentifier");
            defer function_identifier.deinit();
            const identifier = try function_identifier.nameAlloc();
            defer self.allocator.free(identifier);
            const arity = try Common.yulArityFromType(function_type.*);
            try self.context.internalFunctionCalledThroughDispatch(arity);
            const dispatch = try Common.internalDispatchAlloc(self.allocator, arity);
            defer self.allocator.free(dispatch);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}({s}{s}{s})",
                .{
                    dispatch,
                    identifier,
                    if (joined.len == 0) "" else ", ",
                    joined,
                },
            );
        };
        defer self.allocator.free(expression);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitMemoryArrayCreation(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (call.arguments.len != 1) return error.InvalidAst;
        var length = try self.emitExpression(call.arguments[0], depth + 1);
        defer length.deinit();
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        const array = result.type_ref.asArray() orelse return error.InvalidAst;
        if (array.reference.location != .Memory) return error.InvalidAst;
        try self.setLocation(node);
        const uint256_type = self.context.type_provider.uint256();
        var converted_length: IRVariableModule.IRVariable = undefined;
        var has_converted_length = false;
        defer if (has_converted_length) converted_length.deinit();
        const value = if (TypeBehavior.equals(length.type_ref, uint256_type))
            &length
        else blk: {
            const raw_name = try self.context.newYulVariable();
            defer self.allocator.free(raw_name);
            converted_length = try IRVariableModule.IRVariable.init(
                self.allocator,
                raw_name,
                uint256_type,
            );
            has_converted_length = true;
            try self.assignConverted(&converted_length, &length, true);
            break :blk &converted_length;
        };
        const length_text = try value.commaSeparatedListAlloc();
        defer self.allocator.free(length_text);
        const allocate = try self.utils.allocateAndInitializeMemoryArrayFunction(
            result.type_ref,
        );
        defer self.allocator.free(allocate);
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "{s}({s})",
            .{ allocate, length_text },
        );
        defer self.allocator.free(expression);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitBytesOrStringConcat(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_kind: Types.FunctionKind,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const argument_types = try self.allocator.alloc(
            *const Types.Type,
            evaluated.values.len,
        );
        defer self.allocator.free(argument_types);
        var argument_slots: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &argument_slots);
        for (evaluated.values, argument_types) |*value, *type_ref| {
            type_ref.* = value.type_ref;
            try value.appendStackSlots(self.allocator, &argument_slots);
        }
        const target_types = try concatTargetTypesAlloc(
            self.context.type_provider,
            self.allocator,
            argument_types,
            function_kind,
        );
        defer self.allocator.free(target_types);
        // Upstream requests these Whiskers substitutions before constructing
        // the packed ABI encoder. Pre-requesting them preserves collector order
        // while avoiding a Zig import cycle between the two helper modules.
        const allocate = try self.utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const finalize = try self.utils.finalizeAllocationFunction();
        defer self.allocator.free(finalize);
        var abi = self.context.abiFunctions();
        const packed_encoder = try abi.tupleEncoderPacked(
            argument_types,
            target_types,
            false,
        );
        defer self.allocator.free(packed_encoder);
        const concat = try self.utils.bytesOrStringConcatFunction(
            argument_types,
            function_kind,
            packed_encoder,
        );
        defer self.allocator.free(concat);
        const arguments = try joinAlloc(self.allocator, argument_slots.items, ", ");
        defer self.allocator.free(arguments);
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "{s}({s})",
            .{ concat, arguments },
        );
        defer self.allocator.free(expression);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitAbiEncode(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const is_packed = function_type.kind == .ABIEncodePacked;
        const has_selector = function_type.kind == .ABIEncodeWithSelector or
            function_type.kind == .ABIEncodeCall or
            function_type.kind == .ABIEncodeWithSignature;

        var encode_arguments: std.ArrayList(*const AST.Node) = .empty;
        defer encode_arguments.deinit(self.allocator);
        if (function_type.kind == .ABIEncodeCall) {
            if (call.arguments.len != 2) return error.InvalidAst;
            if ((try expressionType(call.arguments[1])).category() == .Tuple) {
                if (call.arguments[1].nodeKind() != .tuple_expression)
                    return error.InvalidAst;
                for (call.arguments[1].payload.tuple_expression.components) |component|
                    try encode_arguments.append(
                        self.allocator,
                        component orelse return error.InvalidAst,
                    );
            } else try encode_arguments.append(self.allocator, call.arguments[1]);
        } else {
            for (call.arguments, 0..) |argument, index|
                if (!has_selector or index != 0)
                    try encode_arguments.append(self.allocator, argument);
        }

        var argument_types: std.ArrayList(*const Types.Type) = .empty;
        defer argument_types.deinit(self.allocator);
        var target_types: std.ArrayList(*const Types.Type) = .empty;
        defer target_types.deinit(self.allocator);
        var argument_slots: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &argument_slots);
        for (encode_arguments.items) |argument_node| {
            const argument_type = try expressionType(argument_node);
            try argument_types.append(self.allocator, argument_type);
            var argument = try self.variableFromExpression(
                argument_node,
            );
            defer argument.deinit();
            try argument.appendStackSlots(self.allocator, &argument_slots);
        }
        if (function_type.kind == .ABIEncodeCall) {
            const encoded_function = (try expressionType(call.arguments[0])).asFunction() orelse
                return error.InvalidAst;
            const external_type = try TypeBehavior.asExternallyCallableFunction(
                self.context.type_provider,
                encoded_function.*,
                false,
            );
            const external_function = external_type.asFunction() orelse return error.InvalidAst;
            try target_types.appendSlice(
                self.allocator,
                external_function.parameterTypes(),
            );
        } else {
            for (encode_arguments.items) |argument_node| {
                const target = (try TypeBehavior.fullEncodingType(
                    self.context.type_provider,
                    try expressionType(argument_node),
                    false,
                    true,
                    is_packed,
                )) orelse return error.InvalidAst;
                try target_types.append(self.allocator, target);
            }
        }
        if (argument_types.items.len != target_types.items.len)
            return error.InvalidAst;

        var selector: ?[]u8 = null;
        defer if (selector) |value| self.allocator.free(value);
        if (function_type.kind == .ABIEncodeCall) {
            const selector_type = (try expressionType(call.arguments[0])).asFunction() orelse
                return error.InvalidAst;
            if (selector_type.kind == .Declaration) {
                const signature = try TypeBehavior.externalSignatureAlloc(
                    self.context.type_provider,
                    self.allocator,
                    selector_type.*,
                );
                defer self.allocator.free(signature);
                selector = try Numeric.toCompactHexWithPrefixAlloc(
                    u256,
                    self.allocator,
                    FunctionSelector.selectorFromSignatureU256(signature),
                );
            } else {
                const function_value = try evaluated.find(call.arguments[0]);
                var selector_part = try function_value.part("functionSelector");
                defer selector_part.deinit();
                selector = try self.convertedValueTextAlloc(
                    &selector_part,
                    try self.context.type_provider.fixedBytes(4),
                );
            }
        } else if (function_type.kind == .ABIEncodeWithSignature) {
            if (call.arguments.len == 0) return error.InvalidAst;
            const signature_type = try expressionType(call.arguments[0]);
            if (signature_type.category() == .StringLiteral) {
                selector = try Numeric.toCompactHexWithPrefixAlloc(
                    u256,
                    self.allocator,
                    FunctionSelector.selectorFromSignatureU256(
                        signature_type.payload.StringLiteral.value,
                    ),
                );
            } else {
                const checkpoint = try self.context.newYulVariable();
                defer self.allocator.free(checkpoint);
                const allocate_checkpoint = try self.utils.allocateUnboundedFunction();
                defer self.allocator.free(allocate_checkpoint);
                try self.setLocation(node);
                try self.appendFmt(
                    "let {s} := {s}()\n",
                    .{ checkpoint, allocate_checkpoint },
                );
                const signature_value = try evaluated.find(call.arguments[0]);
                const converted_name = try self.context.newYulVariable();
                defer self.allocator.free(converted_name);
                var converted = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    converted_name,
                    self.context.type_provider.bytesMemory(),
                );
                defer converted.deinit();
                try self.assignConverted(&converted, signature_value, true);
                var position = try converted.part("mpos");
                defer position.deinit();
                const position_text = try position.nameAlloc();
                defer self.allocator.free(position_text);
                const data_area = try self.utils.arrayDataAreaFunction(
                    self.context.type_provider.bytesMemory(),
                );
                defer self.allocator.free(data_area);
                const length = try self.utils.arrayLengthFunction(
                    self.context.type_provider.bytesMemory(),
                );
                defer self.allocator.free(length);
                const hash_name = try self.context.newYulVariable();
                defer self.allocator.free(hash_name);
                const bytes32 = try self.context.type_provider.fixedBytes(32);
                var hash = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    hash_name,
                    bytes32,
                );
                defer hash.deinit();
                const hash_expression = try std.fmt.allocPrint(
                    self.allocator,
                    "keccak256({s}({s}), {s}({s}))",
                    .{ data_area, position_text, length, position_text },
                );
                defer self.allocator.free(hash_expression);
                try self.defineText(&hash, hash_expression);
                const selector_name = try self.context.newYulVariable();
                defer self.allocator.free(selector_name);
                var selector_value = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    selector_name,
                    try self.context.type_provider.fixedBytes(4),
                );
                defer selector_value.deinit();
                try self.assignConverted(&selector_value, &hash, true);
                selector = try selector_value.nameAlloc();
                const finalize_checkpoint = try self.utils.finalizeAllocationFunction();
                defer self.allocator.free(finalize_checkpoint);
                try self.appendFmt(
                    "{s}({s}, 0)\n",
                    .{ finalize_checkpoint, checkpoint },
                );
            }
        } else if (function_type.kind == .ABIEncodeWithSelector) {
            if (call.arguments.len == 0) return error.InvalidAst;
            const selector_value = try evaluated.find(call.arguments[0]);
            selector = try self.convertedValueTextAlloc(
                selector_value,
                try self.context.type_provider.fixedBytes(4),
            );
        }

        const allocate = try self.utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const memory_position = try self.context.newYulVariable();
        defer self.allocator.free(memory_position);
        const memory_end = try self.context.newYulVariable();
        defer self.allocator.free(memory_end);
        var abi = self.context.abiFunctions();
        const encoder = if (is_packed)
            try abi.tupleEncoderPacked(
                argument_types.items,
                target_types.items,
                false,
            )
        else
            try abi.tupleEncoder(
                argument_types.items,
                target_types.items,
                false,
                false,
            );
        defer self.allocator.free(encoder);
        const finalize = try self.utils.finalizeAllocationFunction();
        defer self.allocator.free(finalize);
        const arguments = try joinAlloc(self.allocator, argument_slots.items, ", ");
        defer self.allocator.free(arguments);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        var result_position = try result.part("mpos");
        defer result_position.deinit();
        const data = try result_position.nameAlloc();
        defer self.allocator.free(data);
        try self.setLocation(node);
        try self.appendFmt(
            "let {s} := {s}()\nlet {s} := add({s}, 0x20)\n",
            .{ data, allocate, memory_position, data },
        );
        if (selector) |selector_text| try self.appendFmt(
            "mstore({s}, {s})\n{s} := add({s}, 4)\n",
            .{ memory_position, selector_text, memory_position, memory_position },
        );
        try self.appendFmt(
            "let {s} := {s}({s}{s}{s})\nmstore({s}, sub({s}, add({s}, 0x20)))\n{s}({s}, sub({s}, {s}))\n",
            .{
                memory_end,
                encoder,
                memory_position,
                if (arguments.len == 0) "" else ", ",
                arguments,
                data,
                memory_end,
                data,
                finalize,
                data,
                memory_end,
                data,
            },
        );
        return result;
    }

    fn emitMarkerCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        var arguments = try self.evaluateArguments(
            node.payload.function_call.arguments,
            depth + 1,
        );
        defer arguments.deinit();
        try self.setLocation(node);
        return self.variableFromExpression(node);
    }

    fn emitRequireOrAssert(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (call.arguments.len == 0 or call.arguments.len > 2)
            return error.InvalidAst;
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const condition = try evaluated.find(call.arguments[0]);
        const condition_name = try condition.nameAlloc();
        defer self.allocator.free(condition_name);
        try self.setLocation(node);

        if (call.arguments.len == 2) {
            const message_node = call.arguments[1];
            const message_type = try expressionType(message_node);
            if (message_type.asMagic()) |magic| if (magic.kind == .Error) {
                if (message_node.nodeKind() != .function_call)
                    return error.InvalidAst;
                const error_call = message_node.payload.function_call;
                const error_function = (try expressionType(error_call.expression)).asFunction() orelse
                    return error.InvalidAst;
                if (error_function.kind != .Error or
                    error_call.arguments.len != error_function.parameterTypes().len)
                    return error.InvalidAst;
                const declaration = error_function.declaration orelse
                    try referencedDeclaration(error_call.expression);
                if (declaration.nodeKind() != .error_definition)
                    return error.InvalidAst;
                const sorted_error_arguments = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
                    self.context.type_provider,
                    self.allocator,
                    message_node,
                );
                defer self.allocator.free(sorted_error_arguments);
                if (sorted_error_arguments.len != error_function.parameterTypes().len)
                    return error.InvalidAst;
                var sorted_argument_types: std.ArrayList(*const Types.Type) = .empty;
                defer sorted_argument_types.deinit(self.allocator);
                var sorted_argument_slots: std.ArrayList([]u8) = .empty;
                defer deinitStrings(self.allocator, &sorted_argument_slots);
                for (sorted_error_arguments) |argument_node| {
                    const argument_type = try expressionType(argument_node);
                    try sorted_argument_types.append(self.allocator, argument_type);
                    var argument = try self.variableFromExpression(
                        argument_node,
                    );
                    defer argument.deinit();
                    try argument.appendStackSlots(self.allocator, &sorted_argument_slots);
                }
                const sorted_arguments = try joinAlloc(
                    self.allocator,
                    sorted_argument_slots.items,
                    ", ",
                );
                defer self.allocator.free(sorted_arguments);
                var call_argument_slots: std.ArrayList([]u8) = .empty;
                defer deinitStrings(self.allocator, &call_argument_slots);
                for (error_call.arguments) |argument_node| {
                    var argument = try self.variableFromExpression(
                        argument_node,
                    );
                    defer argument.deinit();
                    try argument.appendStackSlots(self.allocator, &call_argument_slots);
                }
                const call_arguments = try joinAlloc(
                    self.allocator,
                    call_argument_slots.items,
                    ", ",
                );
                defer self.allocator.free(call_arguments);
                var abi = self.context.abiFunctions();
                const encoder = try abi.tupleEncoder(
                    sorted_argument_types.items,
                    error_function.parameterTypes(),
                    false,
                    false,
                );
                defer self.allocator.free(encoder);
                const signature = try TypeBehavior.externalSignatureAlloc(
                    self.context.type_provider,
                    self.allocator,
                    error_function.*,
                );
                defer self.allocator.free(signature);
                const helper = try self.utils.requireWithErrorFunction(
                    try self.compatibilityId(declaration),
                    declaration.payload.error_definition.callable.declaration.name,
                    signature,
                    sorted_argument_types.items,
                    error_function.parameterTypes(),
                    sorted_arguments,
                    encoder,
                );
                defer self.allocator.free(helper);
                // Preserve upstream 0.8.36 behavior: the generated helper's
                // parameters follow sorted named-argument order, but its call
                // site passes source-order values. ZIG-UPSTREAM-001 records
                // the resulting swapped custom-error payload as an upstream
                // defect, retained for compatibility.
                try self.appendFmt(
                    "{s}({s}{s}{s})\n",
                    .{
                        helper,
                        condition_name,
                        if (call_arguments.len == 0) "" else ", ",
                        call_arguments,
                    },
                );
                return self.variableFromExpression(node);
            };

            if (self.context.revert_strings != .Strip) {
                const message = try evaluated.find(message_node);
                var slots = try message.stackSlotsAlloc();
                defer slots.deinit();
                const arguments = try joinAlloc(
                    self.allocator,
                    slots.borrowed(),
                    ", ",
                );
                defer self.allocator.free(arguments);
                const given_types = [_]*const Types.Type{message_type};
                const target_types = [_]*const Types.Type{
                    self.context.type_provider.stringMemory(),
                };
                var abi = self.context.abiFunctions();
                const encoder = try abi.tupleEncoder(
                    &given_types,
                    &target_types,
                    false,
                    false,
                );
                defer self.allocator.free(encoder);
                const helper = try self.utils.requireOrAssertWithMessageFunction(
                    message_type,
                    arguments,
                    encoder,
                );
                defer self.allocator.free(helper);
                try self.appendFmt(
                    "{s}({s}{s}{s})\n",
                    .{
                        helper,
                        condition_name,
                        if (arguments.len == 0) "" else ", ",
                        arguments,
                    },
                );
                return self.variableFromExpression(node);
            }
        }

        const helper = try self.utils.requireOrAssertFunction(
            function_type.kind == .Assert,
        );
        defer self.allocator.free(helper);
        try self.appendFmt("{s}({s})\n", .{ helper, condition_name });
        return self.variableFromExpression(node);
    }

    fn emitRevertCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (call.arguments.len > 1) return error.InvalidAst;
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        try self.setLocation(node);
        if (call.arguments.len == 0 or self.context.revert_strings == .Strip) {
            try self.append("revert(0, 0)\n");
            return self.variableFromExpression(node);
        }
        const argument = try evaluated.find(call.arguments[0]);
        var slots = try argument.stackSlotsAlloc();
        defer slots.deinit();
        const argument_names = try joinAlloc(self.allocator, slots.borrowed(), ", ");
        defer self.allocator.free(argument_names);
        const given_types = [_]*const Types.Type{argument.type_ref};
        const target_types = [_]*const Types.Type{
            self.context.type_provider.stringMemory(),
        };
        var abi = self.context.abiFunctions();
        const encoder = try abi.tupleEncoder(
            &given_types,
            &target_types,
            false,
            false,
        );
        defer self.allocator.free(encoder);
        const position = try self.context.newYulVariable();
        defer self.allocator.free(position);
        const end = try self.context.newYulVariable();
        defer self.allocator.free(end);
        const revert_code = try self.utils.revertWithError(
            "Error(string)",
            &target_types,
            argument_names,
            encoder,
            position,
            end,
        );
        defer self.allocator.free(revert_code);
        try self.append(revert_code);
        try self.append("\n");
        return self.variableFromExpression(node);
    }

    fn emitAbiDecode(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (call.arguments.len != 2) return error.InvalidAst;
        var input = try self.emitExpression(call.arguments[0], depth + 1);
        defer input.deinit();
        const reference = input.type_ref.asReference() orelse return error.InvalidAst;
        const canonical_type = if (reference.location == .CallData)
            self.context.type_provider.bytesCalldata()
        else
            self.context.type_provider.bytesMemory();
        const converted_name = try self.context.newYulVariable();
        defer self.allocator.free(converted_name);
        var converted = try IRVariableModule.IRVariable.init(
            self.allocator,
            converted_name,
            canonical_type,
        );
        defer converted.deinit();
        try self.assignConverted(&converted, &input, true);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        const target_types = try tupleTargetTypesAlloc(
            self.allocator,
            result.type_ref,
        );
        defer self.allocator.free(target_types);
        var abi = self.context.abiFunctions();
        const decoder = try abi.tupleDecoder(
            target_types,
            reference.location != .CallData,
        );
        defer self.allocator.free(decoder);
        const bounds = if (reference.location == .CallData) blk: {
            var offset = try converted.part("offset");
            defer offset.deinit();
            var length = try converted.part("length");
            defer length.deinit();
            const offset_text = try offset.nameAlloc();
            defer self.allocator.free(offset_text);
            const length_text = try length.nameAlloc();
            defer self.allocator.free(length_text);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}, add({s}, {s})",
                .{ offset_text, offset_text, length_text },
            );
        } else blk: {
            var position = try converted.part("mpos");
            defer position.deinit();
            const position_text = try position.nameAlloc();
            defer self.allocator.free(position_text);
            const length = try self.utils.arrayLengthFunction(canonical_type);
            defer self.allocator.free(length);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "add({s}, 32), add(add({s}, 32), {s}({s}))",
                .{ position_text, position_text, length, position_text },
            );
        };
        defer self.allocator.free(bounds);
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "{s}({s})",
            .{ decoder, bounds },
        );
        defer self.allocator.free(expression);
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn evaluateArguments(
        self: *IRGeneratorForStatements,
        nodes: AST.NodeList,
        depth: usize,
    ) GeneratorError!EvaluatedArguments {
        const values = try self.allocator.alloc(IRVariableModule.IRVariable, nodes.len);
        var initialized: usize = 0;
        errdefer {
            for (values[0..initialized]) |*value| value.deinit();
            self.allocator.free(values);
        }
        for (nodes, values) |argument, *value| {
            value.* = try self.emitExpression(argument, depth + 1);
            initialized += 1;
        }
        return .{
            .allocator = self.allocator,
            .nodes = nodes,
            .values = values,
        };
    }

    fn emitStructConstructorCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        const callee_type = try expressionType(call.expression);
        const actual_type = callee_type.asTypeType() orelse return error.InvalidAst;
        if (actual_type.actual_type.category() != .Struct) return error.InvalidAst;
        const constructor = (try TypeBehavior.structConstructorType(
            self.context.type_provider,
            actual_type.actual_type,
        )).asFunction() orelse return error.InvalidAst;
        const sorted = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
            self.context.type_provider,
            self.allocator,
            node,
        );
        defer self.allocator.free(sorted);
        if (sorted.len != constructor.parameterTypes().len)
            return error.InvalidAst;
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        const structure = switch (result.type_ref.payload) {
            .Struct => |value| value,
            else => return error.InvalidAst,
        };
        if (structure.reference.location != .Memory) return error.InvalidAst;
        const allocate = try self.utils.allocateMemoryStructFunction(
            actual_type.actual_type,
        );
        defer self.allocator.free(allocate);
        var result_position = try result.part("mpos");
        defer result_position.deinit();
        const result_text = try result_position.nameAlloc();
        defer self.allocator.free(result_text);
        const allocation = try std.fmt.allocPrint(self.allocator, "{s}()", .{allocate});
        defer self.allocator.free(allocation);
        try self.setLocation(node);
        try self.defineText(&result, allocation);
        const members = structure.declaration.payload.struct_definition.members;
        if (members.len != sorted.len) return error.InvalidAst;
        for (members, sorted, constructor.parameterTypes()) |member, argument_node, target_type| {
            const value = try evaluated.find(argument_node);
            var converted = try self.convert(value, target_type);
            defer converted.deinit();
            const converted_text = try converted.commaSeparatedListAlloc();
            defer self.allocator.free(converted_text);
            const write = try self.utils.writeToMemoryFunction(target_type);
            defer self.allocator.free(write);
            const member_name = member.payload.variable_declaration.declaration.name;
            const offset = try TypeBehavior.structMemoryOffsetOfMember(
                structure,
                member_name,
            );
            try self.appendFmt(
                "{s}(add({s}, {d}), {s})\n",
                .{ write, result_text, offset, converted_text },
            );
        }
        return result;
    }

    fn emitFunctionCallOptions(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call_options)
            return error.InvalidAst;
        const options = node.payload.function_call_options;
        if (options.names.len != options.options.len) return error.InvalidAst;
        var base = if (options.expression.nodeKind() == .member_access)
            try self.emitMemberAccessWithOptions(
                options.expression,
                depth + 1,
                true,
            )
        else
            try self.emitExpression(options.expression, depth + 1);
        defer base.deinit();
        var evaluated_options = try self.evaluateArguments(
            options.options,
            depth + 1,
        );
        defer evaluated_options.deinit();
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        var base_items = try TypeBehavior.stackItemsAlloc(self.allocator, base.type_ref);
        defer base_items.deinit();
        for (base_items.items) |item| {
            if (item.name.len == 0) return error.InvalidAst;
            var source = try base.part(item.name);
            defer source.deinit();
            var target = try result.part(item.name);
            defer target.deinit();
            try self.declareAssign(&target, &source, true);
        }
        for (options.names, options.options) |name, option_node| {
            if (!std.mem.eql(u8, name, "gas") and
                !std.mem.eql(u8, name, "value") and
                !std.mem.eql(u8, name, "salt")) return error.InvalidAst;
            const option = try evaluated_options.find(option_node);
            var target = try result.part(name);
            defer target.deinit();
            try self.assignConverted(&target, option, true);
        }
        return result;
    }

    fn emitExternalCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (function_type.options.arbitrary_parameters or
            function_type.options.salt_set or
            call.arguments.len != function_type.parameterTypes().len)
            return error.InvalidAst;
        var return_info = try ReturnInfoModule.ReturnInfo.init(
            self.allocator,
            self.context.evm_version,
            function_type,
        );
        defer return_info.deinit();
        const estimated_return_size = return_info.estimated_return_size;

        var callee = if (call.expression.nodeKind() == .member_access)
            try self.emitMemberAccessWithOptions(
                call.expression,
                depth + 1,
                true,
            )
        else
            try self.emitExpression(call.expression, depth + 1);
        defer callee.deinit();
        var address = try callee.part("address");
        defer address.deinit();
        var selector = try callee.part("functionSelector");
        defer selector.deinit();
        const address_text = try address.nameAlloc();
        defer self.allocator.free(address_text);
        const selector_text = try selector.nameAlloc();
        defer self.allocator.free(selector_text);

        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const sorted_arguments = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
            self.context.type_provider,
            self.allocator,
            node,
        );
        defer self.allocator.free(sorted_arguments);
        if (sorted_arguments.len != function_type.parameterTypes().len)
            return error.InvalidAst;
        var argument_types: std.ArrayList(*const Types.Type) = .empty;
        defer argument_types.deinit(self.allocator);
        var parameter_types: std.ArrayList(*const Types.Type) = .empty;
        defer parameter_types.deinit(self.allocator);
        var argument_slots: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &argument_slots);
        if (function_type.options.has_bound_first_argument) {
            const self_type = function_type.selfType() orelse return error.InvalidAst;
            try argument_types.append(self.allocator, self_type);
            try parameter_types.append(self.allocator, self_type);
            var self_value = try callee.part("self");
            defer self_value.deinit();
            try self_value.appendStackSlots(self.allocator, &argument_slots);
        }
        for (sorted_arguments, function_type.parameterTypes()) |argument_node, parameter_type| {
            const value = try evaluated.find(argument_node);
            try argument_types.append(self.allocator, value.type_ref);
            try parameter_types.append(self.allocator, parameter_type);
            try value.appendStackSlots(self.allocator, &argument_slots);
        }

        var result = try self.variableFromExpression(
            node,
        );
        errdefer result.deinit();
        if (try TypeBehavior.sizeOnStack(result.type_ref) !=
            try stackSize(return_info.return_types))
            return error.StackLayoutMismatch;

        var encoded_head_size: u32 = 0;
        for (return_info.return_types) |return_type| {
            const decoding = (try TypeBehavior.decodingType(
                self.context.type_provider,
                return_type,
            )) orelse return error.InvalidAst;
            encoded_head_size = std.math.add(
                u32,
                encoded_head_size,
                try TypeBehavior.calldataHeadSize(decoding),
            ) catch return error.Overflow;
        }
        const check_extcodesize = encoded_head_size == 0 or
            !self.context.evm_version.supportsReturndata() or
            @intFromEnum(self.context.revert_strings) >=
                @intFromEnum(DebugSettings.RevertStrings.Debug);
        const revert_no_code = try self.utils.revertReasonIfDebugFunction(
            "Target contract does not contain code",
        );
        defer self.allocator.free(revert_no_code);
        const allocate = try self.utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const finalize = try self.utils.finalizeAllocationFunction();
        defer self.allocator.free(finalize);
        const shift_selector = try self.utils.shiftLeftFunction(224);
        defer self.allocator.free(shift_selector);
        var abi = self.context.abiFunctions();
        const decoder = try abi.tupleDecoder(
            return_info.return_types,
            true,
        );
        defer self.allocator.free(decoder);
        const encoder = try abi.tupleEncoder(
            argument_types.items,
            parameter_types.items,
            function_type.kind == .DelegateCall,
            false,
        );
        defer self.allocator.free(encoder);
        const forwarding_revert = try self.utils.forwardingRevertFunction();
        defer self.allocator.free(forwarding_revert);
        const arguments = try joinAlloc(
            self.allocator,
            argument_slots.items,
            ", ",
        );
        defer self.allocator.free(arguments);
        const return_values = try result.commaSeparatedListAlloc();
        defer self.allocator.free(return_values);
        const position = try self.context.newYulVariable();
        defer self.allocator.free(position);
        const end = try self.context.newYulVariable();
        defer self.allocator.free(end);
        const call_annotation = try functionCallAnnotation(node);
        const is_try_call = call_annotation.try_call;
        const success = if (is_try_call)
            try Common.trySuccessConditionVariableAlloc(
                self.allocator,
                self.context.compatibility_ids,
                node,
            )
        else
            try self.context.newYulVariable();
        defer self.allocator.free(success);
        const return_data_size = try self.context.newYulVariable();
        defer self.allocator.free(return_data_size);
        const use_static_call =
            @intFromEnum(function_type.state_mutability) <=
            @intFromEnum(Types.StateMutability.View) and
            self.context.evm_version.hasStaticCall();
        const opcode = if (function_type.kind == .DelegateCall)
            "delegatecall"
        else if (use_static_call)
            "staticcall"
        else
            "call";
        const gas = if (function_type.options.gas_set) blk: {
            var gas_part = try callee.part("gas");
            defer gas_part.deinit();
            break :blk try gas_part.nameAlloc();
        } else if (self.context.evm_version.canOverchargeGasForCall())
            try self.allocator.dupe(u8, "gas()")
        else blk: {
            var retained = GasCosts.callGas(self.context.evm_version) + 10;
            if (function_type.options.value_set)
                retained += GasCosts.call_value_transfer_gas;
            if (!check_extcodesize)
                retained += GasCosts.call_new_account_gas;
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "sub(gas(), {d})",
                .{retained},
            );
        };
        defer self.allocator.free(gas);
        const value = if (function_type.options.value_set) blk: {
            var value_part = try callee.part("value");
            defer value_part.deinit();
            break :blk try value_part.nameAlloc();
        } else try self.allocator.dupe(u8, "0");
        defer self.allocator.free(value);

        try self.setLocation(node);
        if (!self.context.evm_version.canOverchargeGasForCall() and
            !function_type.options.gas_set and estimated_return_size > 0)
            try self.appendFmt(
                "mstore(add({s}() , {d}), 0)\n",
                .{ allocate, estimated_return_size },
            );
        if (check_extcodesize)
            try self.appendFmt(
                "if iszero(extcodesize({s})) {{ {s}() }}\n",
                .{ address_text, revert_no_code },
            );
        try self.appendFmt(
            "let {s} := {s}()\nmstore({s}, {s}({s}))\nlet {s} := {s}(add({s}, 4){s}{s})\n",
            .{
                position,
                allocate,
                position,
                shift_selector,
                selector_text,
                end,
                encoder,
                position,
                if (arguments.len == 0) "" else ", ",
                arguments,
            },
        );
        if (function_type.kind == .DelegateCall or use_static_call)
            try self.appendFmt(
                "let {s} := {s}({s}, {s}, {s}, sub({s}, {s}), {s}, {d})\n",
                .{
                    success,
                    opcode,
                    gas,
                    address_text,
                    position,
                    end,
                    position,
                    position,
                    estimated_return_size,
                },
            )
        else
            try self.appendFmt(
                "let {s} := call({s}, {s}, {s}, {s}, sub({s}, {s}), {s}, {d})\n",
                .{
                    success,
                    gas,
                    address_text,
                    value,
                    position,
                    end,
                    position,
                    position,
                    estimated_return_size,
                },
            );
        if (!is_try_call)
            try self.appendFmt(
                "if iszero({s}) {{ {s}() }}\n",
                .{ success, forwarding_revert },
            );
        if (return_values.len != 0) try self.declare(&result);
        try self.appendFmt("if {s} {{\n", .{success});
        if (return_info.dynamic_return_size) {
            if (!self.context.evm_version.supportsReturndata())
                return error.InvalidAst;
            try self.appendFmt(
                "let {s} := returndatasize()\nreturndatacopy({s}, 0, {s})\n",
                .{ return_data_size, position, return_data_size },
            );
        } else {
            try self.appendFmt(
                "let {s} := {d}\n",
                .{ return_data_size, estimated_return_size },
            );
            if (self.context.evm_version.supportsReturndata())
                try self.appendFmt(
                    "if gt({s}, returndatasize()) {{ {s} := returndatasize() }}\n",
                    .{ return_data_size, return_data_size },
                );
        }
        try self.appendFmt(
            "{s}({s}, {s})\n",
            .{ finalize, position, return_data_size },
        );
        if (return_values.len == 0)
            try self.appendFmt(
                "{s}({s}, add({s}, {s}))\n",
                .{ decoder, position, position, return_data_size },
            )
        else
            try self.appendFmt(
                "{s} := {s}({s}, add({s}, {s}))\n",
                .{
                    return_values,
                    decoder,
                    position,
                    position,
                    return_data_size,
                },
            );
        try self.append("}\n");
        return result;
    }

    fn emitBareCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (function_type.options.has_bound_first_argument or
            function_type.options.arbitrary_parameters or
            function_type.options.salt_set or
            call.arguments.len != 1 or
            function_type.parameterTypes().len != 1 or
            (try functionCallAnnotation(node)).try_call)
            return error.InvalidAst;
        var callee = try self.emitExpression(call.expression, depth + 1);
        defer callee.deinit();
        var argument = try self.emitExpression(call.arguments[0], depth + 1);
        defer argument.deinit();
        const argument_text = try argument.commaSeparatedListAlloc();
        defer self.allocator.free(argument_text);
        const allocate = try self.utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const position = try self.context.newYulVariable();
        defer self.allocator.free(position);
        const length = try self.context.newYulVariable();
        defer self.allocator.free(length);
        const direct_memory = TypeBehavior.equals(
            argument.type_ref,
            self.context.type_provider.bytesMemory(),
        ) or TypeBehavior.equals(
            argument.type_ref,
            self.context.type_provider.stringMemory(),
        );
        const encoder = if (direct_memory)
            try self.allocator.alloc(u8, 0)
        else blk: {
            const given = [_]*const Types.Type{argument.type_ref};
            const target = [_]*const Types.Type{
                self.context.type_provider.bytesMemory(),
            };
            var abi = self.context.abiFunctions();
            break :blk try abi.tupleEncoderPacked(&given, &target, false);
        };
        defer self.allocator.free(encoder);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        var success_value = try result.tupleComponent(0);
        defer success_value.deinit();
        var return_data = try result.tupleComponent(1);
        defer return_data.deinit();
        const success = try success_value.nameAlloc();
        defer self.allocator.free(success);
        const return_data_text = try return_data.commaSeparatedListAlloc();
        defer self.allocator.free(return_data_text);
        const extract = try self.utils.extractReturndataFunction();
        defer self.allocator.free(extract);
        var address = try callee.part("address");
        defer address.deinit();
        const address_text = try address.nameAlloc();
        defer self.allocator.free(address_text);
        const gas = if (function_type.options.gas_set) blk: {
            var gas_part = try callee.part("gas");
            defer gas_part.deinit();
            break :blk try gas_part.nameAlloc();
        } else if (self.context.evm_version.canOverchargeGasForCall())
            try self.allocator.dupe(u8, "gas()")
        else blk: {
            var retained = GasCosts.callGas(self.context.evm_version) + 10 +
                GasCosts.call_new_account_gas;
            if (function_type.options.value_set)
                retained += GasCosts.call_value_transfer_gas;
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "sub(gas(), {d})",
                .{retained},
            );
        };
        defer self.allocator.free(gas);
        const value = if (function_type.options.value_set) blk: {
            var value_part = try callee.part("value");
            defer value_part.deinit();
            break :blk try value_part.nameAlloc();
        } else try self.allocator.dupe(u8, "0");
        defer self.allocator.free(value);
        try self.setLocation(node);
        if (direct_memory)
            try self.appendFmt(
                "let {s} := add({s}, 0x20)\nlet {s} := mload({s})\n",
                .{ position, argument_text, length, argument_text },
            )
        else
            try self.appendFmt(
                "let {s} := {s}()\nlet {s} := sub({s}({s}{s}{s}), {s})\n",
                .{
                    position,
                    allocate,
                    length,
                    encoder,
                    position,
                    if (argument_text.len == 0) "" else ", ",
                    argument_text,
                    position,
                },
            );
        switch (function_type.kind) {
            .BareCall => try self.appendFmt(
                "let {s} := call({s}, {s}, {s}, {s}, {s}, 0, 0)\n",
                .{ success, gas, address_text, value, position, length },
            ),
            .BareDelegateCall, .BareStaticCall => try self.appendFmt(
                "let {s} := {s}({s}, {s}, {s}, {s}, 0, 0)\n",
                .{
                    success,
                    if (function_type.kind == .BareStaticCall) "staticcall" else "delegatecall",
                    gas,
                    address_text,
                    position,
                    length,
                },
            ),
            else => return error.InvalidAst,
        }
        try self.appendFmt(
            "let {s} := {s}()\n",
            .{ return_data_text, extract },
        );
        return result;
    }

    fn emitArrayPop(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (node.nodeKind() != .function_call or
            node.payload.function_call.arguments.len != 0)
            return error.InvalidAst;
        var callee = try self.emitExpression(node.payload.function_call.expression, depth + 1);
        defer callee.deinit();
        const array_type = function_type.selfType() orelse return error.InvalidAst;
        if (array_type.asArray() == null) return error.InvalidAst;
        const helper = try self.utils.storageArrayPopFunction(array_type);
        defer self.allocator.free(helper);
        const self_text = try callee.commaSeparatedListAlloc();
        defer self.allocator.free(self_text);
        try self.setLocation(node);
        try self.appendFmt("{s}({s})\n", .{ helper, self_text });
        return self.variableFromExpression(node);
    }

    fn emitArrayPush(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (node.nodeKind() != .function_call) return error.InvalidAst;
        const call = node.payload.function_call;
        const array_type = function_type.selfType() orelse return error.InvalidAst;
        const array = array_type.asArray() orelse return error.InvalidAst;
        if (call.arguments.len == 0) {
            var lvalue = try self.emitArrayPushLValue(node, function_type, depth + 1);
            defer lvalue.deinit();
            return self.readFromLValue(&lvalue);
        }
        if (call.arguments.len != 1) return error.InvalidAst;
        var callee = try self.emitExpression(call.expression, depth + 1);
        defer callee.deinit();
        var argument = try self.emitExpression(call.arguments[0], depth + 1);
        defer argument.deinit();
        var converted: ?IRVariableModule.IRVariable = null;
        defer if (converted) |*value| value.deinit();
        if (TypeBehavior.isValueType(array.base_type) and
            !TypeBehavior.equals(argument.type_ref, array.base_type))
        {
            const prepared_name = try self.context.newYulVariable();
            defer self.allocator.free(prepared_name);
            converted = try IRVariableModule.IRVariable.init(
                self.allocator,
                prepared_name,
                array.base_type,
            );
            try self.assignConverted(&converted.?, &argument, true);
        }
        const prepared = if (converted) |*value| value else &argument;
        const helper = try self.utils.storageArrayPushFunction(
            array_type,
            prepared.type_ref,
        );
        defer self.allocator.free(helper);
        const self_text = try callee.commaSeparatedListAlloc();
        defer self.allocator.free(self_text);
        const argument_text = try prepared.commaSeparatedListAlloc();
        defer self.allocator.free(argument_text);
        try self.setLocation(node);
        try self.appendFmt(
            "{s}({s}{s}{s})\n",
            .{
                helper,
                self_text,
                if (argument_text.len == 0) "" else ", ",
                argument_text,
            },
        );
        return self.variableFromExpression(node);
    }

    fn emitArrayPushLValue(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRLValueModule.IRLValue {
        if (node.nodeKind() != .function_call or
            node.payload.function_call.arguments.len != 0)
            return error.InvalidAst;
        const array_type = function_type.selfType() orelse return error.InvalidAst;
        const array = array_type.asArray() orelse return error.InvalidAst;
        var callee = try self.emitExpression(node.payload.function_call.expression, depth + 1);
        defer callee.deinit();
        const self_text = try callee.commaSeparatedListAlloc();
        defer self.allocator.free(self_text);
        const slot = try self.context.newYulVariable();
        defer self.allocator.free(slot);
        const offset = try self.context.newYulVariable();
        defer self.allocator.free(offset);
        const helper = try self.utils.storageArrayPushZeroFunction(array_type);
        defer self.allocator.free(helper);
        try self.setLocation(node);
        try self.appendFmt(
            "let {s}, {s} := {s}({s})\n",
            .{ slot, offset, helper, self_text },
        );
        return IRLValueModule.IRLValue.initStorage(
            self.allocator,
            array.base_type,
            slot,
            try IRLValueModule.Offset.initRuntime(self.allocator, offset),
            false,
        );
    }

    fn emitSendOrTransfer(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (node.nodeKind() != .function_call or
            node.payload.function_call.arguments.len != 1 or
            function_type.parameterTypes().len != 1)
            return error.InvalidAst;
        const call = node.payload.function_call;
        var callee = try self.emitExpression(call.expression, depth + 1);
        defer callee.deinit();
        var argument = try self.emitExpression(call.arguments[0], depth + 1);
        defer argument.deinit();
        var address = try callee.part("address");
        defer address.deinit();
        const address_text = try address.nameAlloc();
        defer self.allocator.free(address_text);
        const value = try self.convertedValueTextAlloc(
            &argument,
            function_type.parameterTypes()[0],
        );
        defer self.allocator.free(value);
        const gas = try self.context.newYulVariable();
        defer self.allocator.free(gas);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        const success = if (function_type.kind == .Transfer)
            try self.context.newYulVariable()
        else
            try result.commaSeparatedListAlloc();
        defer self.allocator.free(success);
        const forwarding = try self.utils.forwardingRevertFunction();
        defer self.allocator.free(forwarding);
        try self.setLocation(node);
        try self.appendFmt(
            "let {s} := 0\nif iszero({s}) {{ {s} := {d} }}\nlet {s} := call({s}, {s}, {s}, 0, 0, 0, 0)\n",
            .{ gas, value, gas, GasCosts.call_stipend, success, gas, address_text, value },
        );
        if (function_type.kind == .Transfer)
            try self.appendFmt(
                "if iszero({s}) {{ {s}() }}\n",
                .{ success, forwarding },
            );
        return result;
    }

    fn emitKeccak256(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (node.nodeKind() != .function_call or
            node.payload.function_call.arguments.len != 1)
            return error.InvalidAst;
        const argument_node = node.payload.function_call.arguments[0];
        var argument = try self.emitExpression(argument_node, depth + 1);
        defer argument.deinit();
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        if (argument.type_ref.category() == .StringLiteral) {
            const digest = Keccak256.keccak256(
                argument.type_ref.payload.StringLiteral.value,
            );
            const expression = try std.fmt.allocPrint(
                self.allocator,
                "0x{s}",
                .{&digest.hex()},
            );
            defer self.allocator.free(expression);
            try self.defineText(&result, expression);
            return result;
        }
        var converted: ?IRVariableModule.IRVariable = null;
        defer if (converted) |*value| value.deinit();
        const bytes_memory = self.context.type_provider.bytesMemory();
        if (!TypeBehavior.equals(argument.type_ref, bytes_memory)) {
            const converted_name = try self.context.newYulVariable();
            defer self.allocator.free(converted_name);
            converted = try IRVariableModule.IRVariable.init(
                self.allocator,
                converted_name,
                bytes_memory,
            );
            try self.assignConverted(&converted.?, &argument, true);
        }
        const array_value = if (converted) |*value| value else &argument;
        var position = try array_value.part("mpos");
        defer position.deinit();
        const position_text = try position.nameAlloc();
        defer self.allocator.free(position_text);
        const data_area = try self.utils.arrayDataAreaFunction(
            self.context.type_provider.bytesMemory(),
        );
        defer self.allocator.free(data_area);
        const length = try self.utils.arrayLengthFunction(
            self.context.type_provider.bytesMemory(),
        );
        defer self.allocator.free(length);
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "keccak256({s}({s}), {s}({s}))",
            .{ data_area, position_text, length, position_text },
        );
        defer self.allocator.free(expression);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitErc7201(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (node.nodeKind() != .function_call or
            node.payload.function_call.arguments.len != 1)
            return error.InvalidAst;
        const argument_node = node.payload.function_call.arguments[0];
        var argument = try self.emitExpression(argument_node, depth + 1);
        defer argument.deinit();
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        if ((try expressionType(argument_node)).category() == .StringLiteral) {
            const value = (try ASTUtils.erc7201CompileTimeValue(
                self.allocator,
                self.context.type_provider,
                node,
            )) orelse return error.InvalidAst;
            const expression = try Numeric.toCompactHexWithPrefixAlloc(
                u256,
                self.allocator,
                value,
            );
            defer self.allocator.free(expression);
            try self.defineText(&result, expression);
            return result;
        }
        const converted_name = try self.context.newYulVariable();
        defer self.allocator.free(converted_name);
        var converted = try IRVariableModule.IRVariable.init(
            self.allocator,
            converted_name,
            self.context.type_provider.stringMemory(),
        );
        defer converted.deinit();
        try self.assignConverted(&converted, &argument, true);
        var position = try converted.part("mpos");
        defer position.deinit();
        const namespace = try position.nameAlloc();
        defer self.allocator.free(namespace);
        const data_area = try self.utils.arrayDataAreaFunction(
            self.context.type_provider.stringMemory(),
        );
        defer self.allocator.free(data_area);
        const length = try self.utils.arrayLengthFunction(
            self.context.type_provider.stringMemory(),
        );
        defer self.allocator.free(length);
        const erc7201 = try self.utils.erc7201();
        defer self.allocator.free(erc7201);
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "{s}({s}({s}), {s}({s}))",
            .{ erc7201, data_area, namespace, length, namespace },
        );
        defer self.allocator.free(expression);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitPrecompileCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (node.nodeKind() != .function_call or
            (try functionCallAnnotation(node)).try_call or
            function_type.options.value_set or
            function_type.options.gas_set or
            function_type.options.has_bound_first_argument)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (call.arguments.len != function_type.parameterTypes().len)
            return error.InvalidAst;
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const sorted_arguments = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
            self.context.type_provider,
            self.allocator,
            node,
        );
        defer self.allocator.free(sorted_arguments);
        if (sorted_arguments.len != function_type.parameterTypes().len)
            return error.InvalidAst;
        var argument_types: std.ArrayList(*const Types.Type) = .empty;
        defer argument_types.deinit(self.allocator);
        var argument_slots: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &argument_slots);
        for (sorted_arguments) |argument_node| {
            const argument = try evaluated.find(argument_node);
            try argument_types.append(self.allocator, argument.type_ref);
            try argument.appendStackSlots(self.allocator, &argument_slots);
        }
        const address: u8 = switch (function_type.kind) {
            .ECRecover => 1,
            .SHA256 => 2,
            .RIPEMD160 => 3,
            else => return error.InvalidAst,
        };
        const shift_bytes: usize = if (function_type.kind == .RIPEMD160) 12 else 0;
        const shift = try self.utils.shiftLeftFunction(shift_bytes * 8);
        defer self.allocator.free(shift);
        const allocate = try self.utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const position = try self.context.newYulVariable();
        defer self.allocator.free(position);
        const end = try self.context.newYulVariable();
        defer self.allocator.free(end);
        var abi = self.context.abiFunctions();
        const encoder = if (function_type.kind == .ECRecover)
            try abi.tupleEncoder(
                argument_types.items,
                function_type.parameterTypes(),
                false,
                false,
            )
        else
            try abi.tupleEncoderPacked(
                argument_types.items,
                function_type.parameterTypes(),
                false,
            );
        defer self.allocator.free(encoder);
        const arguments = try joinAlloc(self.allocator, argument_slots.items, ", ");
        defer self.allocator.free(arguments);
        const success = try self.context.newYulVariable();
        defer self.allocator.free(success);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        const result_text = try result.commaSeparatedListAlloc();
        defer self.allocator.free(result_text);
        const forwarding = try self.utils.forwardingRevertFunction();
        defer self.allocator.free(forwarding);
        const gas = if (self.context.evm_version.canOverchargeGasForCall())
            try self.allocator.dupe(u8, "gas()")
        else
            try std.fmt.allocPrint(
                self.allocator,
                "sub(gas(), {d})",
                .{
                    GasCosts.callGas(self.context.evm_version) + 10 +
                        GasCosts.call_new_account_gas,
                },
            );
        defer self.allocator.free(gas);
        try self.setLocation(node);
        try self.appendFmt(
            "let {s} := {s}()\nlet {s} := {s}({s}{s}{s})\n",
            .{
                position,
                allocate,
                end,
                encoder,
                position,
                if (arguments.len == 0) "" else ", ",
                arguments,
            },
        );
        if (function_type.kind == .ECRecover) try self.append("mstore(0, 0)\n");
        if (self.context.evm_version.hasStaticCall())
            try self.appendFmt(
                "let {s} := staticcall({s}, {d}, {s}, sub({s}, {s}), 0, 32)\n",
                .{ success, gas, address, position, end, position },
            )
        else
            try self.appendFmt(
                "let {s} := call({s}, {d}, 0, {s}, sub({s}, {s}), 0, 32)\n",
                .{ success, gas, address, position, end, position },
            );
        try self.appendFmt(
            "if iszero({s}) {{ {s}() }}\nlet {s} := {s}(mload(0))\n",
            .{ success, forwarding, result_text, shift },
        );
        return result;
    }

    fn emitContractCreation(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (node.nodeKind() != .function_call or
            function_type.options.gas_set or
            function_type.return_parameter_types.len != 1)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (call.arguments.len != function_type.parameterTypes().len)
            return error.InvalidAst;
        var callee = try self.emitExpression(call.expression, depth + 1);
        defer callee.deinit();
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const sorted_arguments = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
            self.context.type_provider,
            self.allocator,
            node,
        );
        defer self.allocator.free(sorted_arguments);
        if (sorted_arguments.len != function_type.parameterTypes().len)
            return error.InvalidAst;
        var argument_types: std.ArrayList(*const Types.Type) = .empty;
        defer argument_types.deinit(self.allocator);
        var argument_slots: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &argument_slots);
        for (sorted_arguments) |argument_node| {
            const argument = try evaluated.find(argument_node);
            try argument_types.append(self.allocator, argument.type_ref);
            try argument.appendStackSlots(self.allocator, &argument_slots);
        }
        const contract_type = switch (function_type.return_parameter_types[0].payload) {
            .Contract => |value| value,
            else => return error.InvalidAst,
        };
        const contract = contract_type.declaration;
        try self.context.addSubObject(contract);
        const object_name = try Common.creationObjectAlloc(
            self.allocator,
            self.context.compatibility_ids,
            contract,
        );
        defer self.allocator.free(object_name);
        const quoted_object = try CommonData.escapeAndQuoteStringAlloc(
            self.allocator,
            object_name,
        );
        defer self.allocator.free(quoted_object);
        const memory_position = try self.context.newYulVariable();
        defer self.allocator.free(memory_position);
        const memory_end = try self.context.newYulVariable();
        defer self.allocator.free(memory_end);
        const allocate = try self.utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const panic = try self.utils.panicFunction(.resource_error);
        defer self.allocator.free(panic);
        var abi = self.context.abiFunctions();
        const encoder = try abi.tupleEncoder(
            argument_types.items,
            function_type.parameterTypes(),
            false,
            false,
        );
        defer self.allocator.free(encoder);
        const arguments = try joinAlloc(self.allocator, argument_slots.items, ", ");
        defer self.allocator.free(arguments);
        const value = if (function_type.options.value_set) blk: {
            var part = try callee.part("value");
            defer part.deinit();
            break :blk try part.nameAlloc();
        } else try self.allocator.dupe(u8, "0");
        defer self.allocator.free(value);
        const salt = if (function_type.options.salt_set) blk: {
            var part = try callee.part("salt");
            defer part.deinit();
            break :blk try part.nameAlloc();
        } else try self.allocator.alloc(u8, 0);
        defer self.allocator.free(salt);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        const address = try result.commaSeparatedListAlloc();
        defer self.allocator.free(address);
        if (address.len == 0) return error.InvalidAst;
        const is_try_call = (try functionCallAnnotation(node)).try_call;
        const success = if (is_try_call)
            try Common.trySuccessConditionVariableAlloc(
                self.allocator,
                self.context.compatibility_ids,
                node,
            )
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(success);
        const forwarding = if (is_try_call)
            try self.allocator.alloc(u8, 0)
        else
            try self.utils.forwardingRevertFunction();
        defer self.allocator.free(forwarding);
        try self.setLocation(node);
        try self.appendFmt(
            "let {s} := {s}()\nlet {s} := add({s}, datasize({s}))\nif or(gt({s}, 0xffffffffffffffff), lt({s}, {s})) {{ {s}() }}\ndatacopy({s}, dataoffset({s}), datasize({s}))\n{s} := {s}({s}{s}{s})\n",
            .{
                memory_position,
                allocate,
                memory_end,
                memory_position,
                quoted_object,
                memory_end,
                memory_end,
                memory_position,
                panic,
                memory_position,
                quoted_object,
                quoted_object,
                memory_end,
                encoder,
                memory_end,
                if (arguments.len == 0) "" else ", ",
                arguments,
            },
        );
        if (function_type.options.salt_set)
            try self.appendFmt(
                "let {s} := create2({s}, {s}, sub({s}, {s}), {s})\n",
                .{ address, value, memory_position, memory_end, memory_position, salt },
            )
        else
            try self.appendFmt(
                "let {s} := create({s}, {s}, sub({s}, {s}))\n",
                .{ address, value, memory_position, memory_end, memory_position },
            );
        if (is_try_call)
            try self.appendFmt(
                "let {s} := iszero(iszero({s}))\n",
                .{ success, address },
            )
        else
            try self.appendFmt(
                "if iszero({s}) {{ {s}() }}\n",
                .{ address, forwarding },
            );
        return result;
    }

    fn emitScalarBuiltinCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        if (call.arguments.len != function_type.parameter_types.len)
            return error.InvalidAst;
        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const sorted_arguments = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
            self.context.type_provider,
            self.allocator,
            node,
        );
        defer self.allocator.free(sorted_arguments);
        if (sorted_arguments.len != function_type.parameter_types.len)
            return error.InvalidAst;
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        switch (function_type.kind) {
            .GasLeft => {
                if (sorted_arguments.len != 0) return error.InvalidAst;
                try self.defineText(&result, "gas()");
            },
            .BlockHash, .BlobHash => {
                if (sorted_arguments.len != 1) return error.InvalidAst;
                const argument = try self.convertedValueTextAlloc(
                    try evaluated.find(sorted_arguments[0]),
                    function_type.parameter_types[0],
                );
                defer self.allocator.free(argument);
                const expression = if (function_type.kind == .BlockHash)
                    try std.fmt.allocPrint(self.allocator, "blockhash({s})", .{argument})
                else
                    try std.fmt.allocPrint(self.allocator, "blobhash({s})", .{argument});
                defer self.allocator.free(expression);
                try self.defineText(&result, expression);
            },
            .Selfdestruct => {
                if (sorted_arguments.len != 1) return error.InvalidAst;
                const argument = try self.convertedValueTextAlloc(
                    try evaluated.find(sorted_arguments[0]),
                    function_type.parameterTypes()[0],
                );
                defer self.allocator.free(argument);
                const expression = try std.fmt.allocPrint(
                    self.allocator,
                    "selfdestruct({s})",
                    .{argument},
                );
                defer self.allocator.free(expression);
                try self.defineText(&result, expression);
            },
            .AddMod, .MulMod => {
                if (sorted_arguments.len != 3) return error.InvalidAst;
                const modulus_name = try self.context.newYulVariable();
                defer self.allocator.free(modulus_name);
                var modulus = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    modulus_name,
                    function_type.parameter_types[2],
                );
                defer modulus.deinit();
                try self.assignConverted(
                    &modulus,
                    try evaluated.find(sorted_arguments[2]),
                    true,
                );
                const modulus_text = try modulus.commaSeparatedListAlloc();
                defer self.allocator.free(modulus_text);
                const panic = try self.utils.panicFunction(.division_by_zero);
                defer self.allocator.free(panic);
                try self.appendFmt(
                    "if iszero({s}) {{ {s}() }}\n",
                    .{ modulus_text, panic },
                );
                const left = try self.convertedValueTextAlloc(
                    try evaluated.find(sorted_arguments[0]),
                    function_type.parameter_types[0],
                );
                defer self.allocator.free(left);
                const right = try self.convertedValueTextAlloc(
                    try evaluated.find(sorted_arguments[1]),
                    function_type.parameter_types[1],
                );
                defer self.allocator.free(right);
                const expression = if (function_type.kind == .AddMod)
                    try std.fmt.allocPrint(
                        self.allocator,
                        "addmod({s}, {s}, {s})",
                        .{ left, right, modulus_text },
                    )
                else
                    try std.fmt.allocPrint(
                        self.allocator,
                        "mulmod({s}, {s}, {s})",
                        .{ left, right, modulus_text },
                    );
                defer self.allocator.free(expression);
                try self.defineText(&result, expression);
            },
            else => return error.UnsupportedFunctionCall,
        }
        return result;
    }

    fn emitEventCall(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function_type: *const Types.FunctionType,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (depth >= max_ast_depth or node.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = node.payload.function_call;
        const declaration = function_type.declaration orelse return error.InvalidAst;
        if (declaration.nodeKind() != .event_definition)
            return error.InvalidAst;
        const event = declaration.payload.event_definition;
        const parameters_node = event.callable.parameters;
        if (parameters_node.nodeKind() != .parameter_list)
            return error.InvalidAst;
        const parameter_declarations = parameters_node.payload.parameter_list.parameters;
        if (call.arguments.len != parameter_declarations.len or
            call.arguments.len != function_type.parameter_types.len)
            return error.InvalidAst;

        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const sorted_arguments = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
            self.context.type_provider,
            self.allocator,
            node,
        );
        defer self.allocator.free(sorted_arguments);
        if (sorted_arguments.len != parameter_declarations.len)
            return error.InvalidAst;

        var indexed_arguments: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &indexed_arguments);
        if (!event.anonymous) {
            const signature = try callableSignatureAlloc(
                self.context.type_provider,
                self.allocator,
                declaration,
                function_type,
            );
            defer self.allocator.free(signature);
            const digest = Keccak256.keccak256(signature);
            const topic = try Numeric.toCompactHexWithPrefixAlloc(
                u256,
                self.allocator,
                digest.toInteger(),
            );
            defer self.allocator.free(topic);
            const topic_name = try self.context.newYulVariable();
            defer self.allocator.free(topic_name);
            try self.setLocation(node);
            try self.appendFmt("let {s} := {s}\n", .{ topic_name, topic });
            try indexed_arguments.append(
                self.allocator,
                try self.allocator.dupe(u8, topic_name),
            );
        }

        var non_indexed_arguments: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &non_indexed_arguments);
        var non_indexed_given_types: std.ArrayList(*const Types.Type) = .empty;
        defer non_indexed_given_types.deinit(self.allocator);
        var non_indexed_target_types: std.ArrayList(*const Types.Type) = .empty;
        defer non_indexed_target_types.deinit(self.allocator);
        for (
            parameter_declarations,
            function_type.parameter_types,
            sorted_arguments,
        ) |parameter, target_type, argument_node| {
            const value = try evaluated.find(argument_node);
            if (parameter.nodeKind() != .variable_declaration)
                return error.InvalidAst;
            if (parameter.payload.variable_declaration.indexed) {
                const value_text = try value.commaSeparatedListAlloc();
                defer self.allocator.free(value_text);
                const topic_name = try self.context.newYulVariable();
                defer self.allocator.free(topic_name);
                if (target_type.asReference() != null) {
                    // `YulUtilFunctions` cannot import `ABIFunctions` without
                    // creating a cycle. Request the upstream ABI packed
                    // encoder here and supply it to the hash wrapper.
                    const allocate = try self.utils.allocateUnboundedFunction();
                    defer self.allocator.free(allocate);
                    var abi = self.context.abiFunctions();
                    const packed_encoder = try abi.tupleEncoderPacked(
                        &.{value.type_ref},
                        &.{target_type},
                        false,
                    );
                    defer self.allocator.free(packed_encoder);
                    const hash = try self.utils.packedHashFunction(
                        &.{value.type_ref},
                        &.{target_type},
                        packed_encoder,
                    );
                    defer self.allocator.free(hash);
                    try self.appendFmt(
                        "let {s} := {s}({s})\n",
                        .{ topic_name, hash, value_text },
                    );
                } else if (target_type.asFunction()) |indexed_function| {
                    if (indexed_function.kind != .External or
                        indexed_function.options.has_bound_first_argument or
                        !TypeBehavior.equals(value.type_ref, target_type))
                        return error.InvalidAst;
                    const combine = try self.utils.combineExternalFunctionIdFunction();
                    defer self.allocator.free(combine);
                    try self.appendFmt(
                        "let {s} := {s}({s})\n",
                        .{ topic_name, combine, value_text },
                    );
                } else {
                    if (try TypeBehavior.sizeOnStack(target_type) != 1)
                        return error.InvalidAst;
                    const conversion = try self.utils.conversionFunction(
                        value.type_ref,
                        target_type,
                    );
                    defer self.allocator.free(conversion);
                    try self.appendFmt(
                        "let {s} := {s}({s})\n",
                        .{ topic_name, conversion, value_text },
                    );
                }
                try indexed_arguments.append(
                    self.allocator,
                    try self.allocator.dupe(u8, topic_name),
                );
                continue;
            }
            try value.appendStackSlots(self.allocator, &non_indexed_arguments);
            try non_indexed_given_types.append(self.allocator, value.type_ref);
            try non_indexed_target_types.append(self.allocator, target_type);
        }
        if (indexed_arguments.items.len > 4)
            return error.InvalidAst;
        const position = try self.context.newYulVariable();
        defer self.allocator.free(position);
        const end = try self.context.newYulVariable();
        defer self.allocator.free(end);
        // Preserve upstream Whiskers substitution order: the allocation
        // helper is requested before the tuple encoder.
        const allocate = try self.utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        var abi = self.context.abiFunctions();
        const encoder = try abi.tupleEncoder(
            non_indexed_given_types.items,
            non_indexed_target_types.items,
            false,
            false,
        );
        defer self.allocator.free(encoder);
        const data_arguments = try joinAlloc(
            self.allocator,
            non_indexed_arguments.items,
            ", ",
        );
        defer self.allocator.free(data_arguments);
        const topics = try joinAlloc(
            self.allocator,
            indexed_arguments.items,
            ", ",
        );
        defer self.allocator.free(topics);
        try self.setLocation(node);
        try self.appendFmt(
            "{{\nlet {s} := {s}()\nlet {s} := {s}({s}{s}{s})\nlog{d}({s}, sub({s}, {s}){s}{s})\n}}\n",
            .{
                position,
                allocate,
                end,
                encoder,
                position,
                if (data_arguments.len == 0) "" else ", ",
                data_arguments,
                indexed_arguments.items.len,
                position,
                end,
                position,
                if (topics.len == 0) "" else ", ",
                topics,
            },
        );
        return self.variableFromExpression(node);
    }

    fn emitCustomRevert(
        self: *IRGeneratorForStatements,
        error_call: *const AST.Node,
        depth: usize,
    ) GeneratorError!void {
        if (depth >= max_ast_depth or error_call.nodeKind() != .function_call)
            return error.InvalidAst;
        const call = error_call.payload.function_call;
        const function_type = (try expressionType(call.expression)).asFunction() orelse
            return error.InvalidAst;
        if (function_type.kind != .Error)
            return error.UnsupportedFunctionCall;
        const declaration = function_type.declaration orelse
            try referencedDeclaration(call.expression);
        if (declaration.nodeKind() != .error_definition or
            call.arguments.len != function_type.parameter_types.len)
            return error.InvalidAst;

        var evaluated = try self.evaluateArguments(call.arguments, depth + 1);
        defer evaluated.deinit();
        const sorted_arguments = try ASTImplementation.sortedFunctionCallArgumentsAlloc(
            self.context.type_provider,
            self.allocator,
            error_call,
        );
        defer self.allocator.free(sorted_arguments);
        if (sorted_arguments.len != function_type.parameter_types.len)
            return error.InvalidAst;
        var given_types: std.ArrayList(*const Types.Type) = .empty;
        defer given_types.deinit(self.allocator);
        var arguments: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &arguments);
        for (sorted_arguments) |argument| {
            const value = try evaluated.find(argument);
            try value.appendStackSlots(self.allocator, &arguments);
            try given_types.append(self.allocator, value.type_ref);
        }

        const signature = try callableSignatureAlloc(
            self.context.type_provider,
            self.allocator,
            declaration,
            function_type,
        );
        defer self.allocator.free(signature);
        const position = try self.context.newYulVariable();
        defer self.allocator.free(position);
        const end = try self.context.newYulVariable();
        defer self.allocator.free(end);
        const needs_allocation = try errorPayloadNeedsAllocation(
            function_type.parameter_types,
        );
        if (needs_allocation) {
            // `revertWithError` requests this internally too. Request it here
            // first so the separately supplied ABI encoder retains upstream's
            // dependency-registration order.
            const allocate = try self.utils.allocateUnboundedFunction();
            defer self.allocator.free(allocate);
        }
        var abi = self.context.abiFunctions();
        const encoder = try abi.tupleEncoder(
            given_types.items,
            function_type.parameter_types,
            false,
            false,
        );
        defer self.allocator.free(encoder);
        const argument_text = try joinAlloc(self.allocator, arguments.items, ", ");
        defer self.allocator.free(argument_text);
        const revert = try self.utils.revertWithError(
            signature,
            function_type.parameter_types,
            argument_text,
            encoder,
            position,
            end,
        );
        defer self.allocator.free(revert);
        try self.setLocation(error_call);
        try self.append(revert);
    }

    fn emitUserDefinedBinaryOperation(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function: *const AST.Node,
        left_node: *const AST.Node,
        right_node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (function.nodeKind() != .function_definition or
            !function.payload.function_definition.implemented())
            return error.InvalidAst;
        const parameters = callableParameters(function);
        const returns = callableReturns(function);
        if (parameters.len != 2 or returns.len != 1) return error.InvalidAst;

        var left = try self.emitExpression(left_node, depth + 1);
        defer left.deinit();
        var right = try self.emitExpression(right_node, depth + 1);
        defer right.deinit();
        const left_text = try self.convertedValueTextAlloc(
            &left,
            try variableType(parameters[0]),
        );
        defer self.allocator.free(left_text);
        const right_text = try self.convertedValueTextAlloc(
            &right,
            try variableType(parameters[1]),
        );
        defer self.allocator.free(right_text);
        const function_name = try self.context.enqueueFunctionForCodeGeneration(function);
        defer self.allocator.free(function_name);
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "{s}({s}, {s})",
            .{ function_name, left_text, right_text },
        );
        defer self.allocator.free(expression);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn emitUserDefinedUnaryOperation(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        function: *const AST.Node,
        operand_node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (function.nodeKind() != .function_definition or
            !function.payload.function_definition.implemented())
            return error.InvalidAst;
        const parameters = callableParameters(function);
        const returns = callableReturns(function);
        if (parameters.len != 1 or returns.len != 1) return error.InvalidAst;

        var operand = try self.emitExpression(operand_node, depth + 1);
        defer operand.deinit();
        const operand_text = try self.convertedValueTextAlloc(
            &operand,
            try variableType(parameters[0]),
        );
        defer self.allocator.free(operand_text);
        const function_name = try self.context.enqueueFunctionForCodeGeneration(function);
        defer self.allocator.free(function_name);
        const expression = try std.fmt.allocPrint(
            self.allocator,
            "{s}({s})",
            .{ function_name, operand_text },
        );
        defer self.allocator.free(expression);
        var result = try self.variableFromExpression(node);
        errdefer result.deinit();
        try self.setLocation(node);
        try self.defineText(&result, expression);
        return result;
    }

    fn resolveLValue(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRLValueModule.IRLValue {
        if (depth >= max_ast_depth) return error.AstTooDeep;
        return switch (node.payload) {
            .identifier => blk: {
                const declaration = (try identifierAnnotation(node)).referenced_declaration orelse
                    return error.InvalidAst;
                if (declaration.nodeKind() != .variable_declaration)
                    return error.UnsupportedLValue;
                if (self.context.isLocalVariable(declaration)) {
                    const local = try self.context.localVariable(declaration);
                    break :blk IRLValueModule.IRLValue.initStack(try local.clone());
                }
                if (self.context.isStateVariable(declaration))
                    break :blk try self.stateVariableLValue(declaration);
                if (ASTImplementation.isStateVariable(declaration) and
                    declaration.payload.variable_declaration.mutability == .Immutable)
                    break :blk IRLValueModule.IRLValue.initImmutable(
                        self.allocator,
                        try variableType(declaration),
                        declaration,
                    );
                return error.UnsupportedLValue;
            },
            .tuple_expression => |tuple| blk: {
                const type_ref = try expressionType(node);
                const components = try self.allocator.alloc(
                    ?*IRLValueModule.IRLValue,
                    tuple.components.len,
                );
                @memset(components, null);
                var initialized: usize = 0;
                errdefer {
                    for (components[0..initialized]) |component| if (component) |value| {
                        value.deinit();
                        self.allocator.destroy(value);
                    };
                    self.allocator.free(components);
                }
                for (tuple.components, 0..) |component, index| {
                    if (component) |present| {
                        const value = try self.allocator.create(IRLValueModule.IRLValue);
                        errdefer self.allocator.destroy(value);
                        value.* = try self.resolveLValue(present, depth + 1);
                        components[index] = value;
                    }
                    initialized = index + 1;
                }
                break :blk .{
                    .allocator = self.allocator,
                    .type_ref = type_ref,
                    .kind = .{ .tuple = .{ .components = components } },
                };
            },
            .index_access => self.resolveIndexLValue(node, depth + 1),
            .function_call => blk: {
                const call_type = (try expressionType(
                    node.payload.function_call.expression,
                )).asFunction() orelse return error.UnsupportedLValue;
                if (call_type.kind != .ArrayPush or
                    node.payload.function_call.arguments.len != 0)
                    return error.UnsupportedLValue;
                break :blk self.emitArrayPushLValue(node, call_type, depth + 1);
            },
            .member_access => blk: {
                const structure_type = try expressionType(
                    node.payload.member_access.expression,
                );
                const structure = switch (structure_type.payload) {
                    .Struct => |value| value,
                    else => return error.UnsupportedLValue,
                };
                break :blk self.resolveStructMemberLValue(
                    node,
                    structure,
                    depth + 1,
                );
            },
            else => error.UnsupportedLValue,
        };
    }

    fn resolveIndexLValue(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
        depth: usize,
    ) GeneratorError!IRLValueModule.IRLValue {
        if (depth >= max_ast_depth or node.nodeKind() != .index_access)
            return error.InvalidAst;
        const access = node.payload.index_access;
        const index = access.index orelse return error.UnsupportedLValue;
        const base_type = try expressionType(access.base);
        var base = try self.emitExpression(access.base, depth + 1);
        defer base.deinit();
        const base_text = try base.commaSeparatedListAlloc();
        defer self.allocator.free(base_text);
        var key = try self.emitExpression(index, depth + 1);
        defer key.deinit();
        const key_text = try key.commaSeparatedListAlloc();
        defer self.allocator.free(key_text);
        return switch (base_type.payload) {
            .Mapping => |mapping| blk: {
                const packed_encoder: ?[]u8 = if (TypeBehavior.isDynamicallySized(
                    mapping.key_type,
                )) dynamic: {
                    const allocate = try self.utils.allocateUnboundedFunction();
                    defer self.allocator.free(allocate);
                    const uint_type = self.context.type_provider.uint256();
                    var abi = self.context.abiFunctions();
                    break :dynamic try abi.tupleEncoderPacked(
                        &.{ key.type_ref, uint_type },
                        &.{ mapping.key_type, uint_type },
                        false,
                    );
                } else null;
                defer if (packed_encoder) |encoder| self.allocator.free(encoder);
                const index_function = try self.utils.mappingIndexAccessFunction(
                    base_type,
                    key.type_ref,
                    packed_encoder,
                );
                defer self.allocator.free(index_function);
                const slot = try self.context.newYulVariable();
                defer self.allocator.free(slot);
                try self.setLocation(node);
                try self.appendFmt(
                    "let {s} := {s}({s}, {s})\n",
                    .{ slot, index_function, base_text, key_text },
                );
                break :blk IRLValueModule.IRLValue.initStorage(
                    self.allocator,
                    mapping.value_type,
                    slot,
                    .{ .constant = 0 },
                    false,
                );
            },
            .Array => |array| switch (array.reference.location) {
                .Storage => blk: {
                    var base_slot = try base.part("slot");
                    defer base_slot.deinit();
                    const base_slot_text = try base_slot.nameAlloc();
                    defer self.allocator.free(base_slot_text);
                    const index_function = try self.utils.storageArrayIndexAccessFunction(
                        base_type,
                    );
                    defer self.allocator.free(index_function);
                    // Storage indexing uses the already-evaluated single Yul
                    // value directly. Upstream only applies expressionAsType
                    // conversion to memory and calldata array indices.
                    const index_text = try key.nameAlloc();
                    defer self.allocator.free(index_text);
                    const slot = try self.context.newYulVariable();
                    defer self.allocator.free(slot);
                    const offset = try self.context.newYulVariable();
                    defer self.allocator.free(offset);
                    try self.setLocation(node);
                    try self.appendFmt(
                        "let {s}, {s} := {s}({s}, {s})\n",
                        .{ slot, offset, index_function, base_slot_text, index_text },
                    );
                    break :blk IRLValueModule.IRLValue.initStorage(
                        self.allocator,
                        try expressionType(node),
                        slot,
                        try IRLValueModule.Offset.initRuntime(self.allocator, offset),
                        false,
                    );
                },
                .Memory => blk: {
                    var memory_position = try base.part("mpos");
                    defer memory_position.deinit();
                    const memory_text = try memory_position.nameAlloc();
                    defer self.allocator.free(memory_text);
                    const index_function = try self.utils.memoryArrayIndexAccessFunction(
                        base_type,
                    );
                    defer self.allocator.free(index_function);
                    const index_text = try self.convertedValueTextAlloc(
                        &key,
                        self.context.type_provider.uint256(),
                    );
                    defer self.allocator.free(index_text);
                    const address = try std.fmt.allocPrint(
                        self.allocator,
                        "{s}({s}, {s})",
                        .{ index_function, memory_text, index_text },
                    );
                    defer self.allocator.free(address);
                    break :blk IRLValueModule.IRLValue.initMemory(
                        self.allocator,
                        try expressionType(node),
                        address,
                        array.isByteArrayOrString(),
                    );
                },
                .CallData, .Transient => error.UnsupportedLValue,
            },
            else => error.UnsupportedLValue,
        };
    }

    fn readFromLValue(
        self: *IRGeneratorForStatements,
        lvalue: *const IRLValueModule.IRLValue,
    ) GeneratorError!IRVariableModule.IRVariable {
        const raw_name = try self.context.newYulVariable();
        defer self.allocator.free(raw_name);
        var result = try IRVariableModule.IRVariable.init(
            self.allocator,
            raw_name,
            lvalue.type_ref,
        );
        errdefer result.deinit();
        switch (lvalue.kind) {
            .stack => |*stack| try self.declareAssign(&result, stack, true),
            .storage => |*storage| {
                if (!TypeBehavior.isValueType(lvalue.type_ref)) {
                    try self.defineText(&result, storage.slot);
                    return result;
                }
                const reader = switch (storage.offset) {
                    .constant => |offset| try self.utils.readFromStorage(
                        lvalue.type_ref,
                        offset,
                        true,
                        .Unspecified,
                    ),
                    .runtime => try self.utils.readFromStorageDynamic(
                        lvalue.type_ref,
                        true,
                        .Unspecified,
                    ),
                };
                defer self.allocator.free(reader);
                const offset = try storage.offsetStringAlloc(self.allocator);
                defer self.allocator.free(offset);
                const expression = switch (storage.offset) {
                    .constant => try std.fmt.allocPrint(
                        self.allocator,
                        "{s}({s})",
                        .{ reader, storage.slot },
                    ),
                    .runtime => try std.fmt.allocPrint(
                        self.allocator,
                        "{s}({s}, {s})",
                        .{ reader, storage.slot, offset },
                    ),
                };
                defer self.allocator.free(expression);
                try self.defineText(&result, expression);
            },
            .transient_storage => |*storage| {
                if (!TypeBehavior.isValueType(lvalue.type_ref))
                    return error.UnsupportedLValue;
                const reader = switch (storage.offset) {
                    .constant => |offset| try self.utils.readFromStorage(
                        lvalue.type_ref,
                        offset,
                        true,
                        .Transient,
                    ),
                    .runtime => try self.utils.readFromStorageDynamic(
                        lvalue.type_ref,
                        true,
                        .Transient,
                    ),
                };
                defer self.allocator.free(reader);
                const offset = try storage.offsetStringAlloc(self.allocator);
                defer self.allocator.free(offset);
                const expression = switch (storage.offset) {
                    .constant => try std.fmt.allocPrint(
                        self.allocator,
                        "{s}({s})",
                        .{ reader, storage.slot },
                    ),
                    .runtime => try std.fmt.allocPrint(
                        self.allocator,
                        "{s}({s}, {s})",
                        .{ reader, storage.slot, offset },
                    ),
                };
                defer self.allocator.free(expression);
                try self.defineText(&result, expression);
            },
            .memory => |memory| {
                const expression = if (TypeBehavior.isValueType(lvalue.type_ref)) blk: {
                    const reader = try self.utils.readFromMemory(lvalue.type_ref);
                    defer self.allocator.free(reader);
                    break :blk try std.fmt.allocPrint(
                        self.allocator,
                        "{s}({s})",
                        .{ reader, memory.address },
                    );
                } else try std.fmt.allocPrint(
                    self.allocator,
                    "mload({s})",
                    .{memory.address},
                );
                defer self.allocator.free(expression);
                try self.defineText(&result, expression);
            },
            .immutable => |maybe_declaration| {
                const declaration = maybe_declaration orelse return error.InvalidAst;
                if (self.context.executionContext() == .Creation) {
                    const reader = try self.utils.readFromMemoryFunction(lvalue.type_ref);
                    defer self.allocator.free(reader);
                    const offset = try self.context.immutableMemoryOffset(declaration);
                    const expression = try std.fmt.allocPrint(
                        self.allocator,
                        "{s}({d})",
                        .{ reader, offset },
                    );
                    defer self.allocator.free(expression);
                    try self.defineText(&result, expression);
                } else {
                    const expression = try std.fmt.allocPrint(
                        self.allocator,
                        "loadimmutable(\"{d}\")",
                        .{try self.compatibilityId(declaration)},
                    );
                    defer self.allocator.free(expression);
                    try self.defineText(&result, expression);
                }
            },
            else => return error.UnsupportedLValue,
        }
        return result;
    }

    fn writeToLValue(
        self: *IRGeneratorForStatements,
        lvalue: *const IRLValueModule.IRLValue,
        value: *const IRVariableModule.IRVariable,
    ) GeneratorError!void {
        switch (lvalue.kind) {
            .stack => |*stack| try self.assignConverted(stack, value, false),
            .storage => |*storage| {
                const offset = switch (storage.offset) {
                    .constant => |constant| @as(?u32, constant),
                    .runtime => null,
                };
                const update = try self.utils.updateStorageValueAtLocationFunction(
                    value.type_ref,
                    lvalue.type_ref,
                    .Unspecified,
                    offset,
                );
                defer self.allocator.free(update);
                const value_arguments = try value.commaSeparatedListPrefixedAlloc();
                defer self.allocator.free(value_arguments);
                if (storage.offset == .runtime) {
                    const offset_text = try storage.offsetStringAlloc(self.allocator);
                    defer self.allocator.free(offset_text);
                    try self.appendFmt(
                        "{s}({s}, {s}{s})\n",
                        .{ update, storage.slot, offset_text, value_arguments },
                    );
                } else {
                    try self.appendFmt(
                        "{s}({s}{s})\n",
                        .{ update, storage.slot, value_arguments },
                    );
                }
            },
            .transient_storage => |*storage| {
                const offset = switch (storage.offset) {
                    .constant => |constant| @as(?u32, constant),
                    .runtime => null,
                };
                const update = try self.utils.updateStorageValueAtLocationFunction(
                    value.type_ref,
                    lvalue.type_ref,
                    .Transient,
                    offset,
                );
                defer self.allocator.free(update);
                const value_arguments = try value.commaSeparatedListPrefixedAlloc();
                defer self.allocator.free(value_arguments);
                if (storage.offset == .runtime) {
                    const offset_text = try storage.offsetStringAlloc(self.allocator);
                    defer self.allocator.free(offset_text);
                    try self.appendFmt(
                        "{s}({s}, {s}{s})\n",
                        .{ update, storage.slot, offset_text, value_arguments },
                    );
                } else {
                    try self.appendFmt(
                        "{s}({s}{s})\n",
                        .{ update, storage.slot, value_arguments },
                    );
                }
            },
            .memory => |memory| {
                if (TypeBehavior.isValueType(lvalue.type_ref)) {
                    const prepared_name = try self.context.newYulVariable();
                    defer self.allocator.free(prepared_name);
                    var prepared = try IRVariableModule.IRVariable.init(
                        self.allocator,
                        prepared_name,
                        lvalue.type_ref,
                    );
                    defer prepared.deinit();
                    try self.assignConverted(&prepared, value, true);
                    const prepared_text = try prepared.commaSeparatedListAlloc();
                    defer self.allocator.free(prepared_text);
                    if (memory.byte_array_element)
                        try self.appendFmt(
                            "mstore8({s}, byte(0, {s}))\n",
                            .{ memory.address, prepared_text },
                        )
                    else {
                        const write = try self.utils.writeToMemoryFunction(lvalue.type_ref);
                        defer self.allocator.free(write);
                        try self.appendFmt(
                            "{s}({s}, {s})\n",
                            .{ write, memory.address, prepared_text },
                        );
                    }
                } else if (value.type_ref.category() == .StringLiteral) {
                    const write = try self.utils.writeToMemoryFunction(
                        self.context.type_provider.uint256(),
                    );
                    defer self.allocator.free(write);
                    const copy = try self.utils.copyLiteralToMemoryFunction(
                        value.type_ref.payload.StringLiteral.value,
                    );
                    defer self.allocator.free(copy);
                    try self.appendFmt(
                        "{s}({s}, {s}())\n",
                        .{ write, memory.address, copy },
                    );
                } else {
                    const value_reference = value.type_ref.asReference() orelse
                        return error.UnsupportedLValue;
                    const value_text = if (value_reference.location == .Memory) blk: {
                        var position = try value.part("mpos");
                        defer position.deinit();
                        break :blk try position.nameAlloc();
                    } else blk: {
                        const conversion = try self.utils.conversionFunction(
                            value.type_ref,
                            lvalue.type_ref,
                        );
                        defer self.allocator.free(conversion);
                        const values = try value.commaSeparatedListAlloc();
                        defer self.allocator.free(values);
                        break :blk try std.fmt.allocPrint(
                            self.allocator,
                            "{s}({s})",
                            .{ conversion, values },
                        );
                    };
                    defer self.allocator.free(value_text);
                    try self.appendFmt(
                        "mstore({s}, {s})\n",
                        .{ memory.address, value_text },
                    );
                }
            },
            .immutable => |maybe_declaration| {
                const declaration = maybe_declaration orelse return error.InvalidAst;
                if (self.context.executionContext() != .Creation)
                    return error.UnsupportedLValue;
                const prepared_name = try self.context.newYulVariable();
                defer self.allocator.free(prepared_name);
                var prepared = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    prepared_name,
                    lvalue.type_ref,
                );
                defer prepared.deinit();
                try self.assignConverted(&prepared, value, true);
                const prepared_text = try prepared.commaSeparatedListAlloc();
                defer self.allocator.free(prepared_text);
                try self.appendFmt(
                    "mstore({d}, {s})\n",
                    .{
                        try self.context.immutableMemoryOffset(declaration),
                        prepared_text,
                    },
                );
            },
            .tuple => |tuple| {
                var index = tuple.components.len;
                while (index != 0) {
                    index -= 1;
                    const component = tuple.components[index] orelse continue;
                    var source = try value.tupleComponent(index);
                    defer source.deinit();
                    try self.writeToLValue(component, &source);
                }
            },
        }
    }

    fn stateVariableLValue(
        self: *IRGeneratorForStatements,
        declaration: *const AST.Node,
    ) GeneratorError!IRLValueModule.IRLValue {
        const type_ref = try variableType(declaration);
        if (declaration.nodeKind() != .variable_declaration)
            return error.InvalidAst;
        const location = try self.context.storageLocationOfStateVariable(declaration);
        const slot = try Numeric.toCompactHexWithPrefixAlloc(
            u256,
            self.allocator,
            location.storage_offset,
        );
        defer self.allocator.free(slot);
        return IRLValueModule.IRLValue.initStorage(
            self.allocator,
            type_ref,
            slot,
            .{ .constant = location.byte_offset },
            location.location == .Transient,
        );
    }

    fn binaryExpressionAlloc(
        self: *IRGeneratorForStatements,
        operator: AST.Token,
        common_type: *const Types.Type,
        left: *const IRVariableModule.IRVariable,
        right: *const IRVariableModule.IRVariable,
    ) GeneratorError![]u8 {
        if (TokenModule.isShiftOp(operator))
            return self.shiftExpressionAlloc(operator, left, right);
        if (TokenModule.isCompareOp(operator)) {
            const clean_left = try self.cleanedValueTextAlloc(left, common_type);
            defer self.allocator.free(clean_left);
            const clean_right = try self.cleanedValueTextAlloc(right, common_type);
            defer self.allocator.free(clean_right);
            if (common_type.asFunction()) |function_type| {
                if (function_type.kind == .External) {
                    if (operator != .Equal and operator != .NotEqual)
                        return error.InvalidAst;
                    var left_address = try left.part("address");
                    defer left_address.deinit();
                    var left_selector = try left.part("functionSelector");
                    defer left_selector.deinit();
                    var right_address = try right.part("address");
                    defer right_address.deinit();
                    var right_selector = try right.part("functionSelector");
                    defer right_selector.deinit();
                    const left_address_name = try left_address.nameAlloc();
                    defer self.allocator.free(left_address_name);
                    const left_selector_name = try left_selector.nameAlloc();
                    defer self.allocator.free(left_selector_name);
                    const right_address_name = try right_address.nameAlloc();
                    defer self.allocator.free(right_address_name);
                    const right_selector_name = try right_selector.nameAlloc();
                    defer self.allocator.free(right_selector_name);
                    const equal = try self.utils.externalFunctionPointersEqualFunction();
                    defer self.allocator.free(equal);
                    const comparison = try std.fmt.allocPrint(
                        self.allocator,
                        "{s}({s}, {s}, {s}, {s})",
                        .{
                            equal,
                            left_address_name,
                            left_selector_name,
                            right_address_name,
                            right_selector_name,
                        },
                    );
                    if (operator == .Equal) return comparison;
                    defer self.allocator.free(comparison);
                    return std.fmt.allocPrint(
                        self.allocator,
                        "iszero({s})",
                        .{comparison},
                    );
                }
            }
            const signed = common_type.asInteger() != null and
                common_type.payload.Integer.isSigned();
            return switch (operator) {
                .Equal => std.fmt.allocPrint(
                    self.allocator,
                    "eq({s}, {s})",
                    .{ clean_left, clean_right },
                ),
                .NotEqual => std.fmt.allocPrint(
                    self.allocator,
                    "iszero(eq({s}, {s}))",
                    .{ clean_left, clean_right },
                ),
                .GreaterThan => std.fmt.allocPrint(
                    self.allocator,
                    "{s}gt({s}, {s})",
                    .{ if (signed) "s" else "", clean_left, clean_right },
                ),
                .LessThan => std.fmt.allocPrint(
                    self.allocator,
                    "{s}lt({s}, {s})",
                    .{ if (signed) "s" else "", clean_left, clean_right },
                ),
                .GreaterThanOrEqual => std.fmt.allocPrint(
                    self.allocator,
                    "iszero({s}lt({s}, {s}))",
                    .{ if (signed) "s" else "", clean_left, clean_right },
                ),
                .LessThanOrEqual => std.fmt.allocPrint(
                    self.allocator,
                    "iszero({s}gt({s}, {s}))",
                    .{ if (signed) "s" else "", clean_left, clean_right },
                ),
                else => unreachable,
            };
        }
        const convert_operands = TokenModule.isArithmeticOp(operator) or
            operator == .BitOr or operator == .BitXor or operator == .BitAnd;
        const left_text = if (convert_operands)
            try self.convertedValueTextAlloc(left, common_type)
        else
            try left.commaSeparatedListAlloc();
        defer self.allocator.free(left_text);
        const right_text = if (convert_operands)
            try self.convertedValueTextAlloc(right, common_type)
        else
            try right.commaSeparatedListAlloc();
        defer self.allocator.free(right_text);
        if (TokenModule.isArithmeticOp(operator)) {
            const integer = common_type.asInteger() orelse
                return error.UnsupportedExpression;
            const function = switch (operator) {
                .Add => if (self.context.arithmetic == .Checked)
                    try self.utils.overflowCheckedIntAddFunction(integer.*)
                else
                    try self.utils.wrappingIntAddFunction(integer.*),
                .Sub => if (self.context.arithmetic == .Checked)
                    try self.utils.overflowCheckedIntSubFunction(integer.*)
                else
                    try self.utils.wrappingIntSubFunction(integer.*),
                .Mul => if (self.context.arithmetic == .Checked)
                    try self.utils.overflowCheckedIntMulFunction(integer.*)
                else
                    try self.utils.wrappingIntMulFunction(integer.*),
                .Div => if (self.context.arithmetic == .Checked)
                    try self.utils.overflowCheckedIntDivFunction(integer.*)
                else
                    try self.utils.wrappingIntDivFunction(integer.*),
                .Mod => try self.utils.intModFunction(integer.*),
                else => return error.UnsupportedExpression,
            };
            defer self.allocator.free(function);
            return std.fmt.allocPrint(
                self.allocator,
                "{s}({s}, {s})",
                .{ function, left_text, right_text },
            );
        }

        return switch (operator) {
            .BitOr => std.fmt.allocPrint(
                self.allocator,
                "or({s}, {s})",
                .{ left_text, right_text },
            ),
            .BitXor => std.fmt.allocPrint(
                self.allocator,
                "xor({s}, {s})",
                .{ left_text, right_text },
            ),
            .BitAnd => std.fmt.allocPrint(
                self.allocator,
                "and({s}, {s})",
                .{ left_text, right_text },
            ),
            else => error.UnsupportedExpression,
        };
    }

    fn shiftExpressionAlloc(
        self: *IRGeneratorForStatements,
        operator: AST.Token,
        value: *const IRVariableModule.IRVariable,
        amount: *const IRVariableModule.IRVariable,
    ) GeneratorError![]u8 {
        const amount_type = amount.type_ref.asInteger() orelse
            return error.UnsupportedExpression;
        if (amount_type.isSigned()) return error.InvalidAst;
        const helper = switch (operator) {
            .SHL => try self.utils.typedShiftLeftFunction(
                value.type_ref,
                amount.type_ref,
            ),
            .SAR => try self.utils.typedShiftRightFunction(
                value.type_ref,
                amount.type_ref,
            ),
            else => return error.UnsupportedExpression,
        };
        defer self.allocator.free(helper);
        const value_name = try value.nameAlloc();
        defer self.allocator.free(value_name);
        const amount_name = try amount.nameAlloc();
        defer self.allocator.free(amount_name);
        return std.fmt.allocPrint(
            self.allocator,
            "{s}({s}, {s})",
            .{ helper, value_name, amount_name },
        );
    }

    fn assignInternalFunctionId(
        self: *IRGeneratorForStatements,
        result: *IRVariableModule.IRVariable,
        function: *const AST.Node,
        location_node: *const AST.Node,
    ) GeneratorError!void {
        if (function.nodeKind() != .function_definition or
            !function.payload.function_definition.implemented())
            return error.InvalidAst;
        const function_type = result.type_ref.asFunction() orelse return error.InvalidAst;
        if (function_type.kind != .Internal) return error.InvalidAst;
        const contract = try self.context.mostDerivedContract();
        const annotation = ASTAnnotations.annotationConst(contract) orelse
            return error.InvalidAst;
        const contract_annotation = switch (annotation.*) {
            .contract_definition => |value| value,
            else => return error.InvalidAst,
        };
        const identifier = for (contract_annotation.internal_function_ids.items) |entry| {
            if (entry.function == function) break entry.id;
        } else return error.InvalidAst;
        var function_identifier = try result.part("functionIdentifier");
        defer function_identifier.deinit();
        const value = try std.fmt.allocPrint(self.allocator, "{d}", .{identifier});
        defer self.allocator.free(value);
        try self.setLocation(location_node);
        try self.defineText(&function_identifier, value);
        try self.context.addToInternalDispatch(function);
    }

    fn linkerSymbolAlloc(
        self: *IRGeneratorForStatements,
        library: *const AST.Node,
    ) GeneratorError![]u8 {
        if (library.nodeKind() != .contract_definition or
            library.payload.contract_definition.contract_kind != .Library)
            return error.InvalidAst;
        const qualified = try ASTImplementation.fullyQualifiedContractNameAlloc(
            self.allocator,
            library,
        );
        defer self.allocator.free(qualified);
        const quoted = try CommonData.escapeAndQuoteStringAlloc(
            self.allocator,
            qualified,
        );
        defer self.allocator.free(quoted);
        return std.fmt.allocPrint(self.allocator, "linkersymbol({s})", .{quoted});
    }

    fn convertedValueTextAlloc(
        self: *IRGeneratorForStatements,
        value: *const IRVariableModule.IRVariable,
        target_type: *const Types.Type,
    ) GeneratorError![]u8 {
        const text = try value.commaSeparatedListAlloc();
        defer self.allocator.free(text);
        if (TypeBehavior.equals(value.type_ref, target_type))
            return self.allocator.dupe(u8, text);
        if (try TypeBehavior.sizeOnStack(value.type_ref) != 1 or
            try TypeBehavior.sizeOnStack(target_type) != 1)
            return error.UnsupportedConversion;
        const conversion = try self.utils.conversionFunction(
            value.type_ref,
            target_type,
        );
        defer self.allocator.free(conversion);
        return std.fmt.allocPrint(
            self.allocator,
            "{s}({s})",
            .{ conversion, text },
        );
    }

    fn convert(
        self: *IRGeneratorForStatements,
        value: *const IRVariableModule.IRVariable,
        target_type: *const Types.Type,
    ) GeneratorError!IRVariableModule.IRVariable {
        if (TypeBehavior.equals(value.type_ref, target_type))
            return value.clone();
        const converted_name = try self.context.newYulVariable();
        defer self.allocator.free(converted_name);
        var converted = try IRVariableModule.IRVariable.init(
            self.allocator,
            converted_name,
            target_type,
        );
        errdefer converted.deinit();
        try self.assignConverted(&converted, value, true);
        return converted;
    }

    fn cleanedValueTextAlloc(
        self: *IRGeneratorForStatements,
        value: *const IRVariableModule.IRVariable,
        target_type: *const Types.Type,
    ) GeneratorError![]u8 {
        const text = try value.commaSeparatedListAlloc();
        defer self.allocator.free(text);
        const function = if (TypeBehavior.equals(value.type_ref, target_type))
            try self.utils.cleanupFunction(target_type)
        else
            try self.utils.conversionFunction(value.type_ref, target_type);
        defer self.allocator.free(function);
        return std.fmt.allocPrint(
            self.allocator,
            "{s}({s})",
            .{ function, text },
        );
    }

    fn declareAssign(
        self: *IRGeneratorForStatements,
        left: *const IRVariableModule.IRVariable,
        right: *const IRVariableModule.IRVariable,
        declare_value: bool,
    ) GeneratorError!void {
        var left_slots = try left.stackSlotsAlloc();
        defer left_slots.deinit();
        var right_slots = try right.stackSlotsAlloc();
        defer right_slots.deinit();
        if (left_slots.items.len != right_slots.items.len)
            return error.StackLayoutMismatch;
        for (left_slots.items, right_slots.items) |left_slot, right_slot|
            try self.appendFmt(
                "{s}{s} := {s}\n",
                .{ if (declare_value) "let " else "", left_slot, right_slot },
            );
    }

    fn assignConverted(
        self: *IRGeneratorForStatements,
        left: *const IRVariableModule.IRVariable,
        right: *const IRVariableModule.IRVariable,
        declare_value: bool,
    ) GeneratorError!void {
        if (TypeBehavior.equals(left.type_ref, right.type_ref))
            return self.declareAssign(left, right, declare_value);
        const conversion = try self.utils.conversionFunction(
            right.type_ref,
            left.type_ref,
        );
        defer self.allocator.free(conversion);
        const left_slots = try left.commaSeparatedListAlloc();
        defer self.allocator.free(left_slots);
        const right_slots = try right.commaSeparatedListAlloc();
        defer self.allocator.free(right_slots);
        try self.appendFmt(
            "{s}{s}{s}{s}({s})\n",
            .{
                if (left_slots.len == 0) "" else if (declare_value) "let " else "",
                left_slots,
                if (left_slots.len == 0) "" else " := ",
                conversion,
                right_slots,
            },
        );
    }

    fn declare(
        self: *IRGeneratorForStatements,
        variable: *const IRVariableModule.IRVariable,
    ) GeneratorError!void {
        const slots = try variable.commaSeparatedListAlloc();
        defer self.allocator.free(slots);
        if (slots.len != 0) try self.appendFmt("let {s}\n", .{slots});
    }

    fn defineText(
        self: *IRGeneratorForStatements,
        variable: *const IRVariableModule.IRVariable,
        expression: []const u8,
    ) GeneratorError!void {
        const slots = try variable.commaSeparatedListAlloc();
        defer self.allocator.free(slots);
        if (slots.len == 0) {
            try self.appendFmt("{s}\n", .{expression});
        } else {
            try self.appendFmt("let {s} := {s}\n", .{ slots, expression });
        }
    }

    fn setLocation(
        self: *IRGeneratorForStatements,
        node: *const AST.Node,
    ) GeneratorError!void {
        self.current_location = node.location;
    }

    fn append(self: *IRGeneratorForStatements, code: []const u8) !void {
        try self.appendLocationComment();
        try self.output.appendSlice(self.allocator, code);
    }

    fn appendFmt(
        self: *IRGeneratorForStatements,
        comptime format: []const u8,
        arguments: anytype,
    ) !void {
        try self.appendLocationComment();
        try self.output.print(self.allocator, format, arguments);
    }

    fn appendLocationComment(self: *IRGeneratorForStatements) GeneratorError!void {
        if (self.current_location.isValid() and
            (!self.has_last_location or !self.last_location.eql(self.current_location)))
        {
            const comment = try Common.dispenseLocationCommentAlloc(
                self.allocator,
                self.current_location,
                self.context.locationCommentContext(),
            );
            defer self.allocator.free(comment);
            try self.output.appendSlice(self.allocator, comment);
            try self.output.append(self.allocator, '\n');
        }
        self.last_location = self.current_location;
        self.has_last_location = true;
    }
};

fn errorPayloadNeedsAllocation(
    parameter_types: []const *const Types.Type,
) GeneratorError!bool {
    var static_size: usize = 0;
    for (parameter_types) |type_ref| {
        if (!TypeBehavior.isValueType(type_ref) or
            TypeBehavior.isDynamicallyEncoded(type_ref))
            return true;
        static_size = std.math.add(
            usize,
            static_size,
            try TypeBehavior.calldataEncodedSize(type_ref, true),
        ) catch return error.Overflow;
    }
    const encoded_size = std.math.add(usize, static_size, 4) catch
        return error.Overflow;
    return encoded_size > ContextModule.general_purpose_memory_start;
}

const InlineAssemblyCopyContext = struct {
    allocator: std.mem.Allocator,
    generation_context: *ContextModule.IRGenerationContext,
    references: []const ASTAnnotations.InlineAssemblyExternalReference,

    fn translateExpression(
        opaque_context: ?*anyopaque,
        _: *YulASTCopier,
        expression: *const YulAST.Expression,
    ) anyerror!?YulAST.Expression {
        const self: *InlineAssemblyCopyContext = @ptrCast(@alignCast(opaque_context.?));
        const identifier = switch (expression.*) {
            .identifier => |*value| value,
            else => return null,
        };
        return self.translateReference(identifier);
    }

    fn translateIdentifierNode(
        opaque_context: ?*anyopaque,
        _: *YulASTCopier,
        identifier: *const YulAST.Identifier,
    ) anyerror!?YulAST.Identifier {
        const self: *InlineAssemblyCopyContext = @ptrCast(@alignCast(opaque_context.?));
        var translated = (try self.translateReference(identifier)) orelse return null;
        return switch (translated) {
            .identifier => |value| value,
            else => {
                translated.deinit(self.allocator);
                return error.InvalidAst;
            },
        };
    }

    fn translateIdentifierName(
        opaque_context: ?*anyopaque,
        name: YulName,
    ) anyerror!YulName {
        const self: *InlineAssemblyCopyContext = @ptrCast(@alignCast(opaque_context.?));
        const original = try name.str();
        const prefixed = try std.fmt.allocPrint(self.allocator, "usr${s}", .{original});
        defer self.allocator.free(prefixed);
        return YulName.init(prefixed);
    }

    fn translateReference(
        self: *InlineAssemblyCopyContext,
        identifier: *const YulAST.Identifier,
    ) anyerror!?YulAST.Expression {
        const reference = for (self.references) |*candidate| {
            if (candidate.identifier == identifier) break candidate;
        } else return null;
        const value = try self.referenceValueAlloc(reference.info);
        defer self.allocator.free(value);
        if (value.len == 0) return error.InvalidAst;
        if (std.ascii.isDigit(value[0]))
            return .{ .literal = .{
                .debug_data = identifier.debug_data,
                .kind = .Number,
                .value = try YulUtilities.valueOfNumberLiteral(self.allocator, value),
            } };
        return .{ .identifier = .{
            .debug_data = identifier.debug_data,
            .name = try YulName.init(value),
        } };
    }

    fn referenceValueAlloc(
        self: *InlineAssemblyCopyContext,
        reference: ASTAnnotations.InlineAssemblyExternalIdentifierInfo,
    ) anyerror![]u8 {
        var declaration = reference.declaration orelse return error.InvalidAst;
        if (declaration.nodeKind() != .variable_declaration)
            return error.InvalidAst;
        var type_ref = try variableType(declaration);

        if (reference.suffix.len == 0 and ASTImplementation.isLocalVariable(declaration)) {
            const local = try self.generation_context.localVariable(declaration);
            if (try TypeBehavior.sizeOnStack(local.type_ref) != 1)
                return error.InvalidAst;
            return local.commaSeparatedListAlloc();
        }

        if (declaration.payload.variable_declaration.mutability == .Constant) {
            declaration = (try ASTUtils.rootConstVariableDeclaration(
                self.allocator,
                declaration,
            )) orelse return error.InvalidAst;
            const initializer = declaration.payload.variable_declaration.value orelse
                return error.InvalidAst;
            const initializer_type = try expressionType(initializer);
            type_ref = try variableType(declaration);
            if (initializer_type.category() == .RationalNumber) {
                var value = try TypeBehavior.literalValue(
                    self.generation_context.type_provider,
                    initializer_type,
                    null,
                );
                if (type_ref.asFixedBytes()) |fixed_bytes| {
                    const shift: u8 = @intCast(256 - 8 * @as(u16, fixed_bytes.bytes));
                    value <<= shift;
                } else if (type_ref.category() != .Integer) {
                    return error.InvalidAst;
                }
                return Numeric.formatNumberU256Alloc(self.allocator, value);
            }
            if (initializer.nodeKind() != .literal) return error.InvalidAst;
            return switch (initializer_type.payload) {
                .Bool, .Address => blk: {
                    const value = try TypeBehavior.literalValue(
                        self.generation_context.type_provider,
                        initializer_type,
                        initializer.payload.literal,
                    );
                    break :blk Numeric.toCompactHexWithPrefixAlloc(
                        u256,
                        self.allocator,
                        value,
                    );
                },
                .StringLiteral => |literal| blk: {
                    const fixed_bytes = type_ref.asFixedBytes() orelse
                        return error.InvalidAst;
                    if (literal.value.len > fixed_bytes.bytes or literal.value.len > 32)
                        return error.InvalidAst;
                    var bytes: [32]u8 = @splat(0);
                    @memcpy(bytes[0..literal.value.len], literal.value);
                    break :blk Numeric.formatNumberU256Alloc(
                        self.allocator,
                        std.mem.readInt(u256, &bytes, .big),
                    );
                },
                else => error.InvalidAst,
            };
        }

        if (ASTImplementation.isStateVariable(declaration)) {
            const location = try self.generation_context.storageLocationOfStateVariable(
                declaration,
            );
            if (std.mem.eql(u8, reference.suffix, "slot"))
                return std.fmt.allocPrint(self.allocator, "{d}", .{location.storage_offset});
            if (std.mem.eql(u8, reference.suffix, "offset"))
                return std.fmt.allocPrint(self.allocator, "{d}", .{location.byte_offset});
            return error.InvalidAst;
        }

        if (TypeBehavior.dataStoredIn(type_ref, .Storage)) {
            if (!ASTImplementation.isLocalVariable(declaration) or
                TypeBehavior.isValueType(type_ref)) return error.InvalidAst;
            const local = try self.generation_context.localVariable(declaration);
            if (std.mem.eql(u8, reference.suffix, "slot")) {
                var slot = try local.part("slot");
                defer slot.deinit();
                return slot.nameAlloc();
            }
            if (std.mem.eql(u8, reference.suffix, "offset") and
                !(try local.hasPart("offset")))
                return self.allocator.dupe(u8, "0");
            return error.InvalidAst;
        }

        if (TypeBehavior.dataStoredIn(type_ref, .CallData)) {
            if (!std.mem.eql(u8, reference.suffix, "offset") and
                !std.mem.eql(u8, reference.suffix, "length"))
                return error.InvalidAst;
            const local = try self.generation_context.localVariable(declaration);
            var part = try local.part(reference.suffix);
            defer part.deinit();
            return part.nameAlloc();
        }

        if (type_ref.asFunction()) |function_type| {
            if (function_type.kind != .External or
                try TypeBehavior.sizeOnStack(type_ref) != 2)
                return error.InvalidAst;
            const part_name = if (std.mem.eql(u8, reference.suffix, "selector"))
                "functionSelector"
            else if (std.mem.eql(u8, reference.suffix, "address"))
                "address"
            else
                return error.InvalidAst;
            const local = try self.generation_context.localVariable(declaration);
            var part = try local.part(part_name);
            defer part.deinit();
            return part.nameAlloc();
        }
        return error.InvalidAst;
    }
};

fn expressionAnnotation(
    node: *const AST.Node,
) GeneratorError!*const ASTAnnotations.ExpressionAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .expression => |*value| value,
        .identifier => |*value| &value.expression,
        .member_access => |*value| &value.expression,
        .operation => |*value| &value.expression,
        .binary_operation => |*value| &value.operation.expression,
        .function_call => |*value| &value.expression,
        else => error.InvalidAst,
    };
}

fn expressionType(node: *const AST.Node) GeneratorError!*const Types.Type {
    return (try expressionAnnotation(node)).type_ref orelse error.InvalidAst;
}

fn underlyingArrayType(type_ref: *const Types.Type) ?*const Types.Type {
    return switch (type_ref.payload) {
        .Array => type_ref,
        .ArraySlice => |slice| slice.array_type,
        else => null,
    };
}

fn tupleTargetTypesAlloc(
    allocator: std.mem.Allocator,
    type_ref: *const Types.Type,
) GeneratorError![]*const Types.Type {
    const tuple = type_ref.asTuple() orelse {
        const result = try allocator.alloc(*const Types.Type, 1);
        result[0] = type_ref;
        return result;
    };
    var count: usize = 0;
    for (tuple.components) |component| if (component != null) {
        count += 1;
    };
    const result = try allocator.alloc(*const Types.Type, count);
    var index: usize = 0;
    for (tuple.components) |component| if (component) |present| {
        result[index] = present;
        index += 1;
    };
    return result;
}

fn stackSize(types: []const *const Types.Type) TypeBehavior.QueryError!usize {
    var size: usize = 0;
    for (types) |type_ref|
        size = std.math.add(
            usize,
            size,
            try TypeBehavior.sizeOnStack(type_ref),
        ) catch return error.Overflow;
    return size;
}

fn concatTargetTypesAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    argument_types: []const *const Types.Type,
    function_kind: Types.FunctionKind,
) GeneratorError![]*const Types.Type {
    if (function_kind != .BytesConcat and function_kind != .StringConcat)
        return error.InvalidAst;
    const result = try allocator.alloc(*const Types.Type, argument_types.len);
    errdefer allocator.free(result);
    for (argument_types, result) |argument_type, *target_type| {
        if (argument_type.asFixedBytes() != null) {
            target_type.* = argument_type;
            continue;
        }
        if (argument_type.category() == .RationalNumber)
            return error.InvalidAst;
        switch (argument_type.payload) {
            .StringLiteral => |literal| if (literal.value.len != 0 and
                literal.value.len <= 32)
            {
                target_type.* = try provider.fixedBytes(@intCast(literal.value.len));
                continue;
            },
            else => {},
        }
        target_type.* = if (function_kind == .StringConcat)
            provider.stringMemory()
        else
            provider.bytesMemory();
    }
    return result;
}

fn identifierAnnotation(
    node: *const AST.Node,
) GeneratorError!*const ASTAnnotations.IdentifierAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier => |*value| value,
        else => error.InvalidAst,
    };
}

fn binaryOperationAnnotation(
    node: *const AST.Node,
) GeneratorError!*const ASTAnnotations.BinaryOperationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .binary_operation => |*value| value,
        else => error.InvalidAst,
    };
}

fn operationAnnotation(
    node: *const AST.Node,
) GeneratorError!*const ASTAnnotations.OperationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .operation => |*value| value,
        else => error.InvalidAst,
    };
}

fn functionCallAnnotation(
    node: *const AST.Node,
) GeneratorError!*const ASTAnnotations.FunctionCallAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .function_call => |*value| value,
        else => error.InvalidAst,
    };
}

fn memberAccessAnnotation(
    node: *const AST.Node,
) GeneratorError!*const ASTAnnotations.MemberAccessAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .member_access => |*value| value,
        else => error.InvalidAst,
    };
}

fn referencedDeclaration(node: *const AST.Node) GeneratorError!*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .identifier => |value| value.referenced_declaration,
        .member_access => |value| value.referenced_declaration,
        else => null,
    } orelse error.InvalidAst;
}

fn callableParameters(function: *const AST.Node) AST.NodeList {
    if (function.nodeKind() != .function_definition) return &.{};
    return function.payload.function_definition.callable.parameters
        .payload.parameter_list.parameters;
}

fn callableReturns(function: *const AST.Node) AST.NodeList {
    if (function.nodeKind() != .function_definition) return &.{};
    const returns = function.payload.function_definition.callable.return_parameters orelse
        return &.{};
    return returns.payload.parameter_list.parameters;
}

fn variableType(variable: *const AST.Node) GeneratorError!*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(variable) orelse
        return error.InvalidAst;
    return switch (annotation.*) {
        .variable_declaration => |value| value.type_ref,
        else => null,
    } orelse error.InvalidAst;
}

fn literalValueAlloc(
    allocator: std.mem.Allocator,
    node: *const AST.Node,
    type_ref: *const Types.Type,
) GeneratorError![]u8 {
    switch (type_ref.payload) {
        .RationalNumber => |rational| {
            if (rational.denominator.compareUnsigned(1) != .eq)
                return error.InvalidLiteral;
            return Numeric.toCompactHexWithPrefixAlloc(
                u256,
                allocator,
                rational.numerator.toU256Wrapping(),
            );
        },
        .Bool => return Numeric.toCompactHexWithPrefixAlloc(
            u256,
            allocator,
            if (node.nodeKind() == .literal and
                node.payload.literal.token == .TrueLiteral) 1 else 0,
        ),
        .Address, .Integer => if (node.nodeKind() == .literal)
            return duplicateWithoutUnderscores(allocator, node.payload.literal.value),
        else => {},
    }
    return error.InvalidLiteral;
}

fn duplicateWithoutUnderscores(
    allocator: std.mem.Allocator,
    value: []const u8,
) std.mem.Allocator.Error![]u8 {
    var output = try allocator.alloc(u8, value.len);
    errdefer allocator.free(output);
    var length: usize = 0;
    for (value) |byte| {
        if (byte == '_') continue;
        output[length] = byte;
        length += 1;
    }
    if (length == output.len) return output;
    return allocator.realloc(output, length);
}

fn joinAlloc(
    allocator: std.mem.Allocator,
    values: []const []const u8,
    separator: []const u8,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (values, 0..) |value, index| {
        if (index != 0) try output.appendSlice(allocator, separator);
        try output.appendSlice(allocator, value);
    }
    return output.toOwnedSlice(allocator);
}

fn deinitStrings(
    allocator: std.mem.Allocator,
    values: *std.ArrayList([]u8),
) void {
    for (values.items) |value| allocator.free(value);
    values.deinit(allocator);
}

fn callableSignatureAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    declaration: *const AST.Node,
    function_type: *const Types.FunctionType,
) GeneratorError![]u8 {
    var callable = function_type.*;
    callable.declaration = declaration;
    return TypeBehavior.externalSignatureAlloc(provider, allocator, callable);
}

test "inline array reuses an element that already has the target type" {
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const DebugInfoSelection = @import("../../../liblangutil/debug_info_selection.zig").DebugInfoSelection;

    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const array_type = Types.Type{ .payload = .{ .Array = .{
        .reference = .{ .location = .Memory },
        .base_type = &uint_type,
        .length = 1,
    } } };
    var literal_annotation = ASTAnnotations.Annotation{ .expression = .{
        .type_ref = &uint_type,
    } };
    var tuple_annotation = ASTAnnotations.Annotation{ .expression = .{
        .type_ref = &array_type,
    } };
    var literal = AST.Node{
        .id = 1,
        .location = .{},
        .payload = .{ .literal = .{ .token = .Number, .value = "4" } },
        .annotation = @ptrCast(&literal_annotation),
    };
    var tuple = AST.Node{
        .id = 2,
        .location = .{},
        .payload = .{ .tuple_expression = .{
            .components = &.{&literal},
            .is_inline_array = true,
        } },
        .annotation = @ptrCast(&tuple_annotation),
    };
    var expression_statement = AST.Node{
        .id = 3,
        .location = .{},
        .payload = .{ .expression_statement = .{ .expression = &tuple } },
    };
    var block = AST.Node{
        .id = 4,
        .location = .{},
        .payload = .{ .block = .{ .statements = &.{&expression_statement} } },
    };

    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var context = try ContextModule.IRGenerationContext.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Deployed,
        .Default,
        &.{},
        DebugInfoSelection.noneValue(),
        null,
    );
    defer context.deinit();
    var utils = context.utils();
    var generator = IRGeneratorForStatements.init(
        std.testing.allocator,
        &context,
        &utils,
        OptimiserSettings.standard(),
        null,
    );
    defer generator.deinit();
    try generator.generate(&block);

    const code = generator.codeBorrowed();
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "write_to_memory_t_uint256(add(expr_2_mpos, 0), expr_1)",
    ) != null);
    try std.testing.expect(std.mem.find(u8, code, "let _") == null);
}

test "scalar local assignment preserves upstream evaluation order" {
    const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
    const DebugInfoSelection = @import("../../../liblangutil/debug_info_selection.zig").DebugInfoSelection;

    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    var a_annotation = ASTAnnotations.Annotation{ .variable_declaration = .{
        .type_ref = &uint_type,
    } };
    var b_annotation = ASTAnnotations.Annotation{ .variable_declaration = .{
        .type_ref = &uint_type,
    } };
    var result_annotation = ASTAnnotations.Annotation{ .variable_declaration = .{
        .type_ref = &uint_type,
    } };
    var a = AST.Node{
        .id = 3,
        .location = .{},
        .payload = .{ .variable_declaration = .{
            .declaration = .{ .name = "a" },
        } },
        .annotation = @ptrCast(&a_annotation),
    };
    var b = AST.Node{
        .id = 5,
        .location = .{},
        .payload = .{ .variable_declaration = .{
            .declaration = .{ .name = "b" },
        } },
        .annotation = @ptrCast(&b_annotation),
    };
    var result_declaration = AST.Node{
        .id = 8,
        .location = .{},
        .payload = .{ .variable_declaration = .{
            .declaration = .{ .name = "result" },
        } },
        .annotation = @ptrCast(&result_annotation),
    };

    var left_annotation = ASTAnnotations.Annotation{ .identifier = .{
        .expression = .{ .type_ref = &uint_type },
        .referenced_declaration = &a,
    } };
    var right_annotation = ASTAnnotations.Annotation{ .identifier = .{
        .expression = .{ .type_ref = &uint_type },
        .referenced_declaration = &b,
    } };
    var target_annotation = ASTAnnotations.Annotation{ .identifier = .{
        .expression = .{ .type_ref = &uint_type, .will_be_written_to = true },
        .referenced_declaration = &result_declaration,
    } };
    var binary_annotation = ASTAnnotations.Annotation{ .binary_operation = .{
        .operation = .{ .expression = .{ .type_ref = &uint_type } },
        .common_type = &uint_type,
    } };
    var assignment_annotation = ASTAnnotations.Annotation{ .expression = .{
        .type_ref = &uint_type,
    } };
    var left = AST.Node{
        .id = 11,
        .location = .{},
        .payload = .{ .identifier = .{ .name = "a" } },
        .annotation = @ptrCast(&left_annotation),
    };
    var right = AST.Node{
        .id = 12,
        .location = .{},
        .payload = .{ .identifier = .{ .name = "b" } },
        .annotation = @ptrCast(&right_annotation),
    };
    var target = AST.Node{
        .id = 10,
        .location = .{},
        .payload = .{ .identifier = .{ .name = "result" } },
        .annotation = @ptrCast(&target_annotation),
    };
    var binary = AST.Node{
        .id = 13,
        .location = .{},
        .payload = .{ .binary_operation = .{
            .left = &left,
            .operator = .Add,
            .right = &right,
        } },
        .annotation = @ptrCast(&binary_annotation),
    };
    var assignment = AST.Node{
        .id = 14,
        .location = .{},
        .payload = .{ .assignment = .{
            .left_hand_side = &target,
            .operator = .Assign,
            .right_hand_side = &binary,
        } },
        .annotation = @ptrCast(&assignment_annotation),
    };
    var expression_statement = AST.Node{
        .id = 15,
        .location = .{},
        .payload = .{ .expression_statement = .{ .expression = &assignment } },
    };
    var block = AST.Node{
        .id = 16,
        .location = .{},
        .payload = .{ .block = .{ .statements = &.{&expression_statement} } },
    };

    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var context = try ContextModule.IRGenerationContext.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Deployed,
        .Default,
        &.{},
        DebugInfoSelection.noneValue(),
        null,
    );
    defer context.deinit();
    _ = try context.addLocalVariable(&a);
    _ = try context.addLocalVariable(&b);
    _ = try context.addLocalVariable(&result_declaration);
    var utils = context.utils();
    var generator = IRGeneratorForStatements.init(
        std.testing.allocator,
        &context,
        &utils,
        OptimiserSettings.standard(),
        null,
    );
    defer generator.deinit();
    try generator.generate(&block);

    try std.testing.expectEqualStrings(
        \\let _1 := var_a_3
        \\let expr_11 := _1
        \\let _2 := var_b_5
        \\let expr_12 := _2
        \\let expr_13 := checked_add_t_uint256(expr_11, expr_12)
        \\
        \\var_result_8 := expr_13
        \\let expr_14 := expr_13
        \\
    ,
        generator.codeBorrowed(),
    );
    const helpers = try context.functionCollector().requestedFunctionsAlloc();
    defer std.testing.allocator.free(helpers);
    try std.testing.expect(std.mem.find(
        u8,
        helpers,
        "function checked_add_t_uint256",
    ) != null);
}
