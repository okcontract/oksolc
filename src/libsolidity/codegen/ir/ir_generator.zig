// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Contract-level Solidity-to-Yul lowering translated from
//! `libsolidity/codegen/ir/IRGenerator.cpp`.
//!
//! Handles contract objects, inheritance, constructors, modifiers,
//! getters, dispatch, and subobject composition.

const std = @import("std");
const AST = @import("../../ast/ast.zig");
const ASTAnnotations = @import("../../ast/ast_annotations.zig");
const ConstructionArguments = @import("../../ast/construction_arguments.zig");
const CompatibilityIdResolver = @import("../../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const ASTImplementation = @import("../../ast/ast.zig");
const Types = @import("../../ast/types.zig");
const TypeBehavior = @import("../../ast/types.zig");
const TypeProviderModule = @import("../../ast/type_provider.zig");
const ContractLevelChecker = @import("../../analysis/contract_level_checker.zig");
const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
const CharStreamProvider = @import("../../../liblangutil/char_stream_provider.zig").CharStreamProvider;
const DebugInfoSelection = @import("../../../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const AsmPrinter = @import("../../../libyul/asm_printer.zig");
const YulUtilities = @import("../../../libyul/utilities.zig");
const CommonData = @import("../../../libsolutil/common_data.zig");
const FunctionSelector = @import("../../../libsolutil/function_selector.zig");
const DebugSettings = @import("../../interface/debug_settings.zig");
const OptimiserSettings = @import("../../interface/optimiser_settings.zig").OptimiserSettings;
const ABIFunctionsModule = @import("../abi_functions.zig");
const YulUtilFunctionsModule = @import("../yul_util_functions.zig");
const ContextModule = @import("ir_generation_context.zig");
const Common = @import("common.zig");
const IRVariableModule = @import("ir_variable.zig");
const StatementGeneratorModule = @import("ir_generator_for_statements.zig");

pub const OtherYulSources = std.AutoHashMapUnmanaged(*const AST.Node, []u8);

pub const GeneratorError = ContractLevelChecker.CheckError ||
    ContextModule.ContextError ||
    Common.CommonError ||
    TypeProviderModule.ProviderError ||
    TypeBehavior.QueryError ||
    IRVariableModule.VariableError ||
    YulUtilFunctionsModule.UtilError ||
    ABIFunctionsModule.ABIError ||
    StatementGeneratorModule.GeneratorError ||
    error{
        InvalidAst,
        UnsupportedContract,
        UnsupportedStateVariable,
        UnsupportedModifier,
        UnsupportedInheritance,
        DuplicateInterfaceSelector,
        MissingFunctionBody,
        FunctionQueueNotEmpty,
        FunctionCollectorNotEmpty,
        MissingSubObjectSource,
    };

const InterfaceFunction = struct {
    declaration: *AST.Node,
    signature: []u8,
    selector: u32,

    fn lessThan(_: void, left: InterfaceFunction, right: InterfaceFunction) bool {
        if (left.selector != right.selector) return left.selector < right.selector;
        return std.mem.order(u8, left.signature, right.signature) == .lt;
    }
};

const ConstructorParameterMap = std.AutoHashMapUnmanaged(
    *const AST.Node,
    std.ArrayList([]u8),
);

const ModifierPlaceholderContext = struct {
    next_function: []const u8,
    return_values: []const u8,
    arguments: []const u8,

    fn generate(
        raw: *anyopaque,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        const self: *ModifierPlaceholderContext = @ptrCast(@alignCast(raw));
        return std.fmt.allocPrint(
            allocator,
            "{s}{s}{s}({s})\n",
            .{
                self.return_values,
                if (self.return_values.len == 0) "" else " := ",
                self.next_function,
                self.arguments,
            },
        );
    }
};

pub const IRGenerator = struct {
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    evm_version: EVMVersion,
    revert_strings: DebugSettings.RevertStrings,
    source_index_to_name: []const AsmPrinter.SourceIndexName,
    debug_info_selection: DebugInfoSelection,
    solidity_source_provider: ?CharStreamProvider,
    optimiser_settings: OptimiserSettings,
    context: ContextModule.IRGenerationContext,

    pub fn init(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        compatibility_ids: CompatibilityIdResolver,
        evm_version: EVMVersion,
        revert_strings: DebugSettings.RevertStrings,
        source_index_to_name: []const AsmPrinter.SourceIndexName,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
        optimiser_settings: OptimiserSettings,
    ) std.mem.Allocator.Error!IRGenerator {
        return .{
            .allocator = allocator,
            .type_provider = type_provider,
            .compatibility_ids = compatibility_ids,
            .evm_version = evm_version,
            .revert_strings = revert_strings,
            .source_index_to_name = source_index_to_name,
            .debug_info_selection = debug_info_selection,
            .solidity_source_provider = solidity_source_provider,
            .optimiser_settings = optimiser_settings,
            .context = try ContextModule.IRGenerationContext.init(
                allocator,
                type_provider,
                compatibility_ids,
                evm_version,
                .Creation,
                revert_strings,
                source_index_to_name,
                debug_info_selection,
                solidity_source_provider,
            ),
        };
    }

    pub fn deinit(self: *IRGenerator) void {
        self.context.deinit();
        self.* = undefined;
    }

    fn compatibilityId(self: *const IRGenerator, node: *const AST.Node) GeneratorError!i64 {
        return self.compatibility_ids.id(node) orelse error.InvalidAst;
    }

    /// Returns allocator-owned, reindented, unoptimized Yul IR.
    pub fn run(
        self: *IRGenerator,
        tree: *AST.Tree,
        contract: *AST.Node,
        cbor_metadata: []const u8,
        other_yul_sources: *const OtherYulSources,
    ) GeneratorError![]u8 {
        const raw = try self.generate(
            tree,
            contract,
            cbor_metadata,
            other_yul_sources,
        );
        defer self.allocator.free(raw);
        return YulUtilities.reindent(self.allocator, raw);
    }

    fn generate(
        self: *IRGenerator,
        tree: *AST.Tree,
        contract: *AST.Node,
        cbor_metadata: []const u8,
        other_yul_sources: *const OtherYulSources,
    ) GeneratorError![]u8 {
        try validateContractBoundary(contract);
        const is_library = contract.payload.contract_definition.contract_kind == .Library;
        const creation_name = try Common.creationObjectAlloc(
            self.allocator,
            self.compatibility_ids,
            contract,
        );
        defer self.allocator.free(creation_name);
        const deployed_name = try Common.deployedObjectAlloc(
            self.allocator,
            self.compatibility_ids,
            contract,
        );
        defer self.allocator.free(deployed_name);
        const quoted_creation = try CommonData.escapeAndQuoteStringAlloc(
            self.allocator,
            creation_name,
        );
        defer self.allocator.free(quoted_creation);
        const quoted_deployed = try CommonData.escapeAndQuoteStringAlloc(
            self.allocator,
            deployed_name,
        );
        defer self.allocator.free(quoted_deployed);
        const metadata_hex = try CommonData.toHexAlloc(
            self.allocator,
            cbor_metadata,
            .dont_add,
            .lower,
        );
        defer self.allocator.free(metadata_hex);

        try self.resetContext(contract, .Creation);
        var creation_utils = self.context.utils();
        const allocate = try creation_utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const call_value_check = if (!constructorPayable(contract))
            try self.callValueCheckAlloc(&creation_utils)
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(call_value_check);
        const constructor = findConstructor(contract);
        const constructor_types = if (constructor) |definition|
            try callableTypesAlloc(self.allocator, self.type_provider, definition, false)
        else
            try self.allocator.alloc(*const Types.Type, 0);
        defer self.allocator.free(constructor_types);
        const constructor_words = try stackSize(constructor_types);
        var constructor_argument_names: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &constructor_argument_names);
        for (0..constructor_words) |_| {
            const variable = try self.context.newYulVariable();
            errdefer self.allocator.free(variable);
            try constructor_argument_names.append(self.allocator, variable);
        }
        const joined_constructor_arguments = try joinAlloc(
            self.allocator,
            constructor_argument_names.items,
            ", ",
        );
        defer self.allocator.free(joined_constructor_arguments);
        const constructor_argument_copy = if (constructor) |definition| blk: {
            if (constructor_words == 0) break :blk try self.allocator.alloc(u8, 0);
            const copy = try self.copyConstructorArgumentsFunction(
                contract,
                definition,
                creation_name,
                constructor_types,
                &creation_utils,
            );
            defer self.allocator.free(copy);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "let {s} := {s}()\n",
                .{ joined_constructor_arguments, copy },
            );
        } else try self.allocator.alloc(u8, 0);
        defer self.allocator.free(constructor_argument_copy);
        const constructor_name = try self.generateConstructors(contract, &creation_utils);
        defer self.allocator.free(constructor_name);
        try self.generateQueuedFunctions(&creation_utils);
        var creation_internal_dispatch = try self.generateInternalDispatchFunctions(
            contract,
            &creation_utils,
        );
        defer creation_internal_dispatch.deinit();
        const constructor_invocation = if (is_library)
            try self.allocator.alloc(u8, 0)
        else
            try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})",
                .{ constructor_name, joined_constructor_arguments },
            );
        defer self.allocator.free(constructor_invocation);
        const deploy_variable = try self.context.newYulVariable();
        defer self.allocator.free(deploy_variable);
        const immutable_patches = try self.immutablePatchesAlloc(
            contract,
            deploy_variable,
        );
        defer self.allocator.free(immutable_patches);
        const creation_location = try self.locationCommentAlloc(contract);
        defer self.allocator.free(creation_location);
        const creation_memory = try self.memoryInitAlloc(
            !self.context.memoryUnsafeInlineAssemblySeen(),
        );
        defer self.allocator.free(creation_memory);
        const creation_functions = try self.context.functionCollector().requestedFunctionsAlloc();
        defer self.allocator.free(creation_functions);
        const creation_sub_objects = try self.subObjectSourcesAlloc(other_yul_sources);
        defer self.allocator.free(creation_sub_objects);
        const creation_use_src = try self.useSrcMapAlloc();
        defer self.allocator.free(creation_use_src);

        try self.resetContext(contract, .Deployed);
        try self.context.initializeInternalDispatch(&creation_internal_dispatch);
        var deployed_utils = self.context.utils();
        const dispatch = try self.dispatchRoutineAlloc(tree, contract, &deployed_utils);
        defer self.allocator.free(dispatch);
        try self.generateQueuedFunctions(&deployed_utils);
        var deployed_internal_dispatch = try self.generateInternalDispatchFunctions(
            contract,
            &deployed_utils,
        );
        defer deployed_internal_dispatch.deinit();
        const deployed_functions = try self.context.functionCollector().requestedFunctionsAlloc();
        defer self.allocator.free(deployed_functions);
        const deployed_sub_objects = try self.subObjectSourcesAlloc(other_yul_sources);
        defer self.allocator.free(deployed_sub_objects);
        const deployed_location = try self.locationCommentAlloc(contract);
        defer self.allocator.free(deployed_location);
        const deployed_memory = try self.memoryInitAlloc(
            !self.context.memoryUnsafeInlineAssemblySeen(),
        );
        defer self.allocator.free(deployed_memory);
        const deployed_library_init = if (is_library)
            try std.fmt.allocPrint(
                self.allocator,
                "let called_via_delegatecall := iszero(eq(loadimmutable(\"{s}\"), address()))",
                .{Common.libraryAddressImmutable()},
            )
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(deployed_library_init);
        const deployed_use_src = try self.useSrcMapAlloc();
        defer self.allocator.free(deployed_use_src);

        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        if (self.debug_info_selection.ethdebug)
            try output.appendSlice(self.allocator, "/// ethdebug: enabled\n")
        else
            try output.append(self.allocator, '\n');
        try output.print(self.allocator,
            \\/// @use-src {s}
            \\object {s} {{
            \\code {{
            \\{s}
            \\{s}
            \\{s}
            \\
            \\{s}
            \\{s}
            \\
            \\let {s} := {s}()
            \\codecopy({s}, dataoffset({s}), datasize({s}))
            \\{s}
            \\
            \\return({s}, datasize({s}))
            \\
            \\{s}
            \\}}
            \\/// @use-src {s}
            \\object {s} {{
            \\code {{
            \\{s}
            \\{s}
            \\{s}
            \\
            \\{s}
            \\{s}
            \\}}
            \\{s}
            \\
            \\data ".metadata" hex"{s}"
            \\}}
            \\{s}
            \\
            \\}}
            \\
        , .{
            creation_use_src,
            quoted_creation,
            creation_location,
            creation_memory,
            call_value_check,
            constructor_argument_copy,
            constructor_invocation,
            deploy_variable,
            allocate,
            deploy_variable,
            quoted_deployed,
            quoted_deployed,
            immutable_patches,
            deploy_variable,
            quoted_deployed,
            creation_functions,
            deployed_use_src,
            quoted_deployed,
            deployed_location,
            deployed_memory,
            deployed_library_init,
            dispatch,
            deployed_functions,
            deployed_sub_objects,
            metadata_hex,
            creation_sub_objects,
        });
        return output.toOwnedSlice(self.allocator);
    }

    fn subObjectSourcesAlloc(
        self: *IRGenerator,
        other_yul_sources: *const OtherYulSources,
    ) GeneratorError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        for (self.context.sub_objects.items) |sub_object| {
            const source = other_yul_sources.get(sub_object) orelse
                return error.MissingSubObjectSource;
            try output.appendSlice(self.allocator, source);
        }
        return output.toOwnedSlice(self.allocator);
    }

    fn resetContext(
        self: *IRGenerator,
        contract: *AST.Node,
        execution_context: ContextModule.ExecutionContext,
    ) GeneratorError!void {
        if (!self.context.functionGenerationQueueEmpty())
            return error.FunctionQueueNotEmpty;
        if (self.context.functionCollector().code.items.len != 0)
            return error.FunctionCollectorNotEmpty;
        self.context.deinit();
        self.context = try ContextModule.IRGenerationContext.init(
            self.allocator,
            self.type_provider,
            self.compatibility_ids,
            self.evm_version,
            execution_context,
            self.revert_strings,
            self.source_index_to_name,
            self.debug_info_selection,
            self.solidity_source_provider,
        );
        try self.context.setMostDerivedContract(contract);
        try self.registerStateVariables(contract);
        if (execution_context == .Creation)
            try self.registerImmutableVariables(contract);
    }

    fn registerImmutableVariables(
        self: *IRGenerator,
        contract: *AST.Node,
    ) GeneratorError!void {
        var variables = try self.immutableVariablesAlloc(contract);
        defer variables.deinit(self.allocator);
        for (variables.items) |variable|
            try self.context.registerImmutableVariable(variable);
    }

    fn immutableVariablesAlloc(
        self: *IRGenerator,
        contract: *AST.Node,
    ) GeneratorError!std.ArrayList(*AST.Node) {
        var variables: std.ArrayList(*AST.Node) = .empty;
        errdefer variables.deinit(self.allocator);
        const annotation = try contractAnnotation(contract);
        const hierarchy = annotation.linearized_base_contracts;
        if (hierarchy.len == 0) {
            for (contract.payload.contract_definition.sub_nodes) |member|
                if (member.nodeKind() == .variable_declaration and
                    ASTImplementation.isStateVariable(member) and
                    member.payload.variable_declaration.mutability == .Immutable)
                    try variables.append(self.allocator, member);
            return variables;
        }
        var index = hierarchy.len;
        while (index != 0) {
            index -= 1;
            const base = hierarchy[index];
            if (base.nodeKind() != .contract_definition) return error.InvalidAst;
            for (base.payload.contract_definition.sub_nodes) |member|
                if (member.nodeKind() == .variable_declaration and
                    ASTImplementation.isStateVariable(member) and
                    member.payload.variable_declaration.mutability == .Immutable)
                    try variables.append(self.allocator, member);
        }
        return variables;
    }

    fn registerStateVariables(
        self: *IRGenerator,
        contract: *AST.Node,
    ) GeneratorError!void {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        for ([_]Types.DataLocation{ .Storage, .Transient }) |data_location| {
            const variables = try TypeBehavior.linearizedStateVariablesAlloc(
                self.allocator,
                .{ .declaration = contract },
                data_location,
            );
            defer self.allocator.free(variables);
            for (variables) |variable| try self.context.addStateVariable(
                variable.declaration,
                variable.slot,
                variable.byte_offset,
                if (data_location == .Transient) .Transient else .Unspecified,
            );
        }
    }

    fn generateConstructors(
        self: *IRGenerator,
        contract: *AST.Node,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError![]u8 {
        const annotation = try contractAnnotation(contract);
        var base_parameters: ConstructorParameterMap = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitConstructorParameterMap(self.allocator, &base_parameters);

        const singleton = [_]*AST.Node{contract};
        const hierarchy = if (annotation.linearized_base_contracts.len == 0) singleton[0..] else annotation.linearized_base_contracts;
        var arguments = try ConstructionArguments.Plan.initAlloc(self.allocator, hierarchy);
        defer arguments.deinit();

        var entry_name: ?[]u8 = null;
        errdefer if (entry_name) |name| self.allocator.free(name);
        for (hierarchy, 0..) |base_const, index| {
            const base = @constCast(base_const);
            if (base_parameters.fetchRemove(base)) |removed| {
                var values = removed.value;
                deinitStrings(self.allocator, &values);
            }
            const next = if (index + 1 < hierarchy.len)
                @constCast(hierarchy[index + 1])
            else
                null;
            const name = try self.generateConstructor(
                base,
                utils,
                next,
                hierarchy,
                &base_parameters,
                arguments.forScope(index),
            );
            if (index == 0)
                entry_name = name
            else
                self.allocator.free(name);
        }
        if (base_parameters.count() != 0) return error.InvalidAst;
        return entry_name orelse error.InvalidAst;
    }

    fn generateConstructor(
        self: *IRGenerator,
        contract: *AST.Node,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
        next_contract: ?*AST.Node,
        hierarchy: []const *AST.Node,
        base_parameters: *ConstructorParameterMap,
        bindings: []const ConstructionArguments.Binding,
    ) GeneratorError![]u8 {
        const name = try Common.constructorAlloc(
            self.allocator,
            self.compatibility_ids,
            contract,
        );
        errdefer self.allocator.free(name);
        if (!(try self.context.functionCollector().beginFunction(name))) return name;
        errdefer self.context.functionCollector().abortFunction(name);

        const constructor = findConstructor(contract);
        self.context.resetLocalVariables();
        var parameter_names: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &parameter_names);
        if (constructor) |definition_node| {
            const parameters = definition_node.payload.function_definition.callable.parameters
                .payload.parameter_list.parameters;
            for (parameters) |parameter| {
                const local = try self.context.addLocalVariable(parameter);
                try local.appendStackSlots(self.allocator, &parameter_names);
            }
        }
        const inherited_parameter_names = try constructorParametersTextAlloc(
            self.allocator,
            hierarchy,
            base_parameters,
        );
        defer self.allocator.free(inherited_parameter_names);
        const joined_parameters = try joinAlloc(
            self.allocator,
            parameter_names.items,
            ", ",
        );
        defer self.allocator.free(joined_parameters);

        var argument_evaluator = StatementGeneratorModule.IRGeneratorForStatements.init(
            self.allocator,
            &self.context,
            utils,
            self.optimiser_settings,
            null,
        );
        defer argument_evaluator.deinit();
        for (bindings) |binding| {
            const target = @constCast(binding.supplied.target);
            const supplied_arguments = binding.supplied.values;
            const target_constructor = findConstructor(target) orelse
                return error.InvalidAst;
            const target_parameters = target_constructor.payload.function_definition
                .callable.parameters.payload.parameter_list.parameters;
            if (supplied_arguments.len != target_parameters.len)
                return error.InvalidAst;

            var values: std.ArrayList([]u8) = .empty;
            errdefer deinitStrings(self.allocator, &values);
            for (supplied_arguments, target_parameters) |argument, parameter| {
                var value = try argument_evaluator.evaluateExpression(
                    argument,
                    try variableType(parameter),
                );
                defer value.deinit();
                try value.appendStackSlots(self.allocator, &values);
            }
            const result = try base_parameters.getOrPut(self.allocator, target);
            if (result.found_existing) {
                deinitStrings(self.allocator, &values);
                return error.InvalidAst;
            }
            result.value_ptr.* = values;
        }

        const next_invocation = if (next_contract) |next| next_call: {
            const next_name = try Common.constructorAlloc(
                self.allocator,
                self.compatibility_ids,
                next,
            );
            defer self.allocator.free(next_name);
            const next_arguments = try constructorParametersTextAlloc(
                self.allocator,
                hierarchy,
                base_parameters,
            );
            defer self.allocator.free(next_arguments);
            break :next_call try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})\n",
                .{ next_name, next_arguments },
            );
        } else try self.allocator.alloc(u8, 0);
        defer self.allocator.free(next_invocation);

        var state_initializer = StatementGeneratorModule.IRGeneratorForStatements.init(
            self.allocator,
            &self.context,
            utils,
            self.optimiser_settings,
            null,
        );
        defer state_initializer.deinit();
        for (contract.payload.contract_definition.sub_nodes) |member| {
            if (member.nodeKind() != .variable_declaration or
                !ASTImplementation.isStateVariable(member) or
                member.payload.variable_declaration.mutability == .Constant)
                continue;
            try state_initializer.initializeStateVar(member);
        }

        const user_body = if (constructor) |constructor_node| body: {
            const definition = constructor_node.payload.function_definition;
            const block = definition.body orelse return error.MissingFunctionBody;
            var real_modifiers: std.ArrayList(*AST.Node) = .empty;
            defer real_modifiers.deinit(self.allocator);
            for (definition.modifiers) |invocation| {
                if (invocation.nodeKind() != .modifier_invocation)
                    return error.InvalidAst;
                const declaration = try identifierPathOrIdentifierDeclaration(
                    invocation.payload.modifier_invocation.modifier_name,
                );
                if (declaration.nodeKind() == .modifier_definition)
                    try real_modifiers.append(self.allocator, invocation)
                else if (declaration.nodeKind() != .contract_definition)
                    return error.InvalidAst;
            }
            if (real_modifiers.items.len == 0) {
                var statement_generator = StatementGeneratorModule.IRGeneratorForStatements.init(
                    self.allocator,
                    &self.context,
                    utils,
                    self.optimiser_settings,
                    null,
                );
                defer statement_generator.deinit();
                try statement_generator.generate(block);
                break :body try statement_generator.codeAlloc(self.allocator);
            }

            for (real_modifiers.items, 0..) |invocation, index| {
                const next = if (index + 1 < real_modifiers.items.len)
                    try Common.modifierInvocationAlloc(
                        self.allocator,
                        self.compatibility_ids,
                        real_modifiers.items[index + 1],
                    )
                else
                    try Common.functionWithModifierInnerAlloc(
                        self.allocator,
                        self.compatibility_ids,
                        constructor_node,
                    );
                defer self.allocator.free(next);
                try self.generateModifier(
                    constructor_node,
                    invocation,
                    next,
                    utils,
                );
            }
            try self.generateFunctionWithModifierInner(constructor_node, utils);
            const first = try Common.modifierInvocationAlloc(
                self.allocator,
                self.compatibility_ids,
                real_modifiers.items[0],
            );
            defer self.allocator.free(first);
            break :body try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})\n",
                .{ first, joined_parameters },
            );
        } else try self.allocator.alloc(u8, 0);
        defer self.allocator.free(user_body);

        const location_node = constructor orelse contract;
        const location = try self.locationCommentAlloc(location_node);
        defer self.allocator.free(location);
        const contract_location = try self.locationCommentAlloc(
            try self.context.mostDerivedContract(),
        );
        defer self.allocator.free(contract_location);
        const ast_id_comment = if (self.debug_info_selection.ast_id and constructor != null)
            try std.fmt.allocPrint(
                self.allocator,
                "/// @ast-id {d}\n",
                .{try self.compatibilityId(constructor.?)},
            )
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(ast_id_comment);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n{s}{s}\nfunction {s}({s}{s}{s}) {{\n{s}\n{s}\n{s}{s}{s}\n}}\n{s}\n",
            .{
                ast_id_comment,
                location,
                name,
                joined_parameters,
                if (joined_parameters.len != 0 and inherited_parameter_names.len != 0)
                    ", "
                else
                    "",
                inherited_parameter_names,
                argument_evaluator.codeBorrowed(),
                location,
                next_invocation,
                state_initializer.codeBorrowed(),
                user_body,
                contract_location,
            },
        );
        defer self.allocator.free(code);
        try self.context.functionCollector().finishFunction(name, code);
        return name;
    }

    fn copyConstructorArgumentsFunction(
        self: *IRGenerator,
        contract: *AST.Node,
        constructor: *AST.Node,
        creation_object_name: []const u8,
        parameter_types: []const *const Types.Type,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError![]u8 {
        if (constructor.nodeKind() != .function_definition or
            constructor.payload.function_definition.kind != .Constructor)
            return error.InvalidAst;
        const contract_name = (contract.declarationConst() orelse
            return error.InvalidAst).name;
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_arguments_for_constructor_{d}_object_{s}_{d}",
            .{
                try self.compatibilityId(constructor),
                contract_name,
                try self.compatibilityId(contract),
            },
        );
        defer self.allocator.free(name);
        if (!(try self.context.functionCollector().beginFunction(name)))
            return self.context.functionCollector().copyFunctionName(name);
        errdefer self.context.functionCollector().abortFunction(name);
        const return_count = try stackSize(parameter_types);
        const returns = try variableListAlloc(
            self.allocator,
            "ret_param_",
            return_count,
        );
        defer self.allocator.free(returns);
        const allocate = try utils.allocationFunction();
        defer self.allocator.free(allocate);
        var abi = self.context.abiFunctions();
        const decoder = try abi.tupleDecoder(parameter_types, true);
        defer self.allocator.free(decoder);
        const quoted_object = try CommonData.escapeAndQuoteStringAlloc(
            self.allocator,
            creation_object_name,
        );
        defer self.allocator.free(quoted_object);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\nfunction {s}() -> {s} {{\nlet programSize := datasize({s})\nlet argSize := sub(codesize(), programSize)\n\nlet memoryDataOffset := {s}(argSize)\ncodecopy(memoryDataOffset, programSize, argSize)\n\n{s} := {s}(memoryDataOffset, add(memoryDataOffset, argSize))\n}}\n",
            .{ name, returns, quoted_object, allocate, returns, decoder },
        );
        defer self.allocator.free(code);
        try self.context.functionCollector().finishFunction(name, code);
        return self.context.functionCollector().copyFunctionName(name);
    }

    fn dispatchRoutineAlloc(
        self: *IRGenerator,
        tree: *AST.Tree,
        contract: *AST.Node,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError![]u8 {
        var functions = try self.interfaceFunctionsAlloc(tree, contract);
        defer {
            for (functions.items) |function| self.allocator.free(function.signature);
            functions.deinit(self.allocator);
        }
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        if (functions.items.len != 0) {
            const shift = try utils.shiftRightFunction(224);
            defer self.allocator.free(shift);
            try output.print(
                self.allocator,
                "if iszero(lt(calldatasize(), 4))\n{{\nlet selector := {s}(calldataload(0))\nswitch selector\n",
                .{shift},
            );
            for (functions.items) |function| {
                const delegatecall_check = if (contract.payload.contract_definition.contract_kind == .Library and
                    function.declaration.nodeKind() == .function_definition and
                    @intFromEnum(function.declaration.payload.function_definition.state_mutability) >
                        @intFromEnum(Types.StateMutability.View))
                blk: {
                    const revert = try utils.revertReasonIfDebugFunction(
                        "Non-view function of library called without DELEGATECALL",
                    );
                    defer self.allocator.free(revert);
                    break :blk try std.fmt.allocPrint(
                        self.allocator,
                        "if iszero(called_via_delegatecall) {{ {s}() }}",
                        .{revert},
                    );
                } else try self.allocator.alloc(u8, 0);
                defer self.allocator.free(delegatecall_check);
                const wrapper = try self.generateExternalFunction(
                    contract,
                    function.declaration,
                    utils,
                );
                defer self.allocator.free(wrapper);
                try output.print(
                    self.allocator,
                    "\ncase 0x{x:0>8}\n{{\n// {s}\n{s}\n{s}()\n}}\n",
                    .{
                        function.selector,
                        function.signature,
                        delegatecall_check,
                        wrapper,
                    },
                );
            }
            try output.appendSlice(self.allocator, "\ndefault {}\n}\n");
        }
        const receive_function = try resolveSpecialFunction(contract, .Receive);
        if (receive_function) |receive| {
            const receive_name = try self.context.enqueueFunctionForCodeGeneration(receive);
            defer self.allocator.free(receive_name);
            try output.print(
                self.allocator,
                "\nif iszero(calldatasize()) {{ {s}() stop() }}\n",
                .{receive_name},
            );
        }
        const fallback_function = try resolveSpecialFunction(contract, .Fallback);
        if (fallback_function) |fallback| {
            const definition = fallback.payload.function_definition;
            const parameters = definition.callable.parameters.payload.parameter_list.parameters;
            const returns = if (definition.callable.return_parameters) |return_parameters|
                return_parameters.payload.parameter_list.parameters
            else
                @as(AST.NodeList, &.{});
            if (!((parameters.len == 0 and returns.len == 0) or
                (parameters.len == 1 and returns.len == 1)))
                return error.InvalidAst;
            if (definition.state_mutability != .Payable) {
                const check = try self.callValueCheckAlloc(utils);
                defer self.allocator.free(check);
                try output.print(self.allocator, "\n{s}\n", .{check});
            }
            const fallback_name = try self.context.enqueueFunctionForCodeGeneration(fallback);
            defer self.allocator.free(fallback_name);
            if (parameters.len == 0)
                try output.print(self.allocator, "{s}()\nstop()\n", .{fallback_name})
            else
                try output.print(
                    self.allocator,
                    "let retval := {s}(0, calldatasize())\nreturn(add(retval, 0x20), mload(retval))\n",
                    .{fallback_name},
                );
        } else {
            const fallback_revert = try utils.revertReasonIfDebugFunction(
                if (receive_function != null)
                    "Unknown signature and no fallback defined"
                else
                    "Contract does not have fallback nor receive functions",
            );
            defer self.allocator.free(fallback_revert);
            try output.print(self.allocator, "\n{s}()\n", .{fallback_revert});
        }
        return output.toOwnedSlice(self.allocator);
    }

    fn generateExternalFunction(
        self: *IRGenerator,
        contract: *AST.Node,
        declaration: *AST.Node,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError![]u8 {
        const name = try Common.externalFunctionABIWrapperAlloc(
            self.allocator,
            self.compatibility_ids,
            declaration,
        );
        errdefer self.allocator.free(name);
        if (!(try self.context.functionCollector().beginFunction(name))) return name;
        errdefer self.context.functionCollector().abortFunction(name);

        const parameters = try callableTypesAlloc(
            self.allocator,
            self.type_provider,
            declaration,
            false,
        );
        defer self.allocator.free(parameters);
        const returns = try callableTypesAlloc(
            self.allocator,
            self.type_provider,
            declaration,
            true,
        );
        defer self.allocator.free(returns);
        const parameter_words = try stackSize(parameters);
        const return_words = try stackSize(returns);
        const parameter_names = try variableListAlloc(
            self.allocator,
            "param_",
            parameter_words,
        );
        defer self.allocator.free(parameter_names);
        const return_names = try variableListAlloc(self.allocator, "ret_", return_words);
        defer self.allocator.free(return_names);

        const allocate = try utils.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const payable = declaration.nodeKind() == .function_definition and
            declaration.payload.function_definition.state_mutability == .Payable;
        const call_value_check = if (!payable and
            contract.payload.contract_definition.contract_kind != .Library)
            try self.callValueCheckAlloc(utils)
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(call_value_check);
        var abi = self.context.abiFunctions();
        const decoder = try abi.tupleDecoder(parameters, false);
        defer self.allocator.free(decoder);
        const internal_name = switch (declaration.nodeKind()) {
            .function_definition => try self.context.enqueueFunctionForCodeGeneration(declaration),
            .variable_declaration => try self.generateGetter(declaration, utils),
            else => return error.InvalidAst,
        };
        defer self.allocator.free(internal_name);
        const encoder = try abi.tupleEncoder(
            returns,
            returns,
            contract.payload.contract_definition.contract_kind == .Library,
            false,
        );
        defer self.allocator.free(encoder);

        var body: std.ArrayList(u8) = .empty;
        defer body.deinit(self.allocator);
        if (call_value_check.len != 0)
            try body.print(self.allocator, "{s}\n", .{call_value_check});
        if (parameter_words == 0)
            try body.print(self.allocator, "{s}(4, calldatasize())\n", .{decoder})
        else
            try body.print(
                self.allocator,
                "let {s} :=  {s}(4, calldatasize())\n",
                .{ parameter_names, decoder },
            );
        if (return_words == 0)
            try body.print(self.allocator, "{s}({s})\n", .{ internal_name, parameter_names })
        else
            try body.print(
                self.allocator,
                "let {s} :=  {s}({s})\n",
                .{ return_names, internal_name, parameter_names },
            );
        try body.print(self.allocator, "let memPos := {s}()\n", .{allocate});
        try body.print(
            self.allocator,
            "let memEnd := {s}(memPos {s} {s})\nreturn(memPos, sub(memEnd, memPos))\n",
            .{
                encoder,
                if (return_names.len == 0) "" else ",",
                return_names,
            },
        );
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\nfunction {s}() {{\n\n{s}\n}}\n",
            .{ name, body.items },
        );
        defer self.allocator.free(code);
        try self.context.functionCollector().finishFunction(name, code);
        return name;
    }

    fn generateGetter(
        self: *IRGenerator,
        variable: *AST.Node,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError![]u8 {
        if (variable.nodeKind() != .variable_declaration or
            !ASTImplementation.isStateVariable(variable) or
            !ASTImplementation.isPublic(variable))
            return error.InvalidAst;
        const name = try Common.getterFunctionAlloc(
            self.allocator,
            self.compatibility_ids,
            variable,
        );
        errdefer self.allocator.free(name);
        if (!(try self.context.functionCollector().beginFunction(name))) return name;
        errdefer self.context.functionCollector().abortFunction(name);

        const type_ref = try variableType(variable);
        const getter_type = (try self.type_provider.functionFromVariable(variable))
            .asFunction() orelse return error.InvalidAst;
        const location = try self.locationCommentAlloc(variable);
        defer self.allocator.free(location);
        const contract_location = try self.locationCommentAlloc(
            try self.context.mostDerivedContract(),
        );
        defer self.allocator.free(contract_location);
        const ast_id_comment = if (self.debug_info_selection.ast_id)
            try std.fmt.allocPrint(
                self.allocator,
                "/// @ast-id {d}\n",
                .{try self.compatibilityId(variable)},
            )
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(ast_id_comment);

        const variable_data = variable.payload.variable_declaration;
        if (variable_data.mutability == .Immutable) {
            if (getter_type.parameter_types.len != 0 or
                try TypeBehavior.sizeOnStack(type_ref) != 1)
                return error.InvalidAst;
            const code = try std.fmt.allocPrint(
                self.allocator,
                "\n{s}{s}\nfunction {s}() -> rval {{\nrval := loadimmutable(\"{d}\")\n}}\n{s}\n",
                .{
                    ast_id_comment,
                    location,
                    name,
                    try self.compatibilityId(variable),
                    contract_location,
                },
            );
            defer self.allocator.free(code);
            try self.context.functionCollector().finishFunction(name, code);
            return name;
        }
        if (variable_data.mutability == .Constant) {
            if (getter_type.parameter_types.len != 0) return error.InvalidAst;
            var statements = StatementGeneratorModule.IRGeneratorForStatements.init(
                self.allocator,
                &self.context,
                utils,
                self.optimiser_settings,
                null,
            );
            defer statements.deinit();
            const constant = try statements.constantValueFunction(variable);
            defer self.allocator.free(constant);
            const return_names = try variableListAlloc(
                self.allocator,
                "ret_",
                try TypeBehavior.sizeOnStack(type_ref),
            );
            defer self.allocator.free(return_names);
            if (return_names.len == 0) return error.InvalidAst;
            const code = try std.fmt.allocPrint(
                self.allocator,
                "\n{s}{s}\nfunction {s}() -> {s} {{\n{s} := {s}()\n}}\n{s}\n",
                .{
                    ast_id_comment,
                    location,
                    name,
                    return_names,
                    return_names,
                    constant,
                    contract_location,
                },
            );
            defer self.allocator.free(code);
            try self.context.functionCollector().finishFunction(name, code);
            return name;
        }

        const storage = try self.context.storageLocationOfStateVariable(variable);
        if (getter_type.parameter_types.len != 0 and storage.byte_offset != 0)
            return error.InvalidAst;
        var parameters: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &parameters);
        var body: std.ArrayList(u8) = .empty;
        defer body.deinit(self.allocator);
        try body.print(
            self.allocator,
            "\nlet slot := {d}\nlet offset := {d}\n",
            .{ storage.storage_offset, storage.byte_offset },
        );

        var current_type = type_ref;
        for (getter_type.parameter_types, 0..) |parameter_type, index| {
            const key_name = try std.fmt.allocPrint(
                self.allocator,
                "key_{d}",
                .{index},
            );
            defer self.allocator.free(key_name);
            var key = try IRVariableModule.IRVariable.init(
                self.allocator,
                key_name,
                parameter_type,
            );
            defer key.deinit();
            try key.appendStackSlots(self.allocator, &parameters);
            const keys = try key.commaSeparatedListAlloc();
            defer self.allocator.free(keys);

            switch (current_type.payload) {
                .Mapping => |mapping| {
                    const packed_encoder: ?[]u8 = if (TypeBehavior.isDynamicallySized(
                        mapping.key_type,
                    )) dynamic: {
                        const allocate = try utils.allocateUnboundedFunction();
                        defer self.allocator.free(allocate);
                        const uint_type = self.type_provider.uint256();
                        var abi = self.context.abiFunctions();
                        break :dynamic try abi.tupleEncoderPacked(
                            &.{ parameter_type, uint_type },
                            &.{ mapping.key_type, uint_type },
                            false,
                        );
                    } else null;
                    defer if (packed_encoder) |encoder| self.allocator.free(encoder);
                    const index_function = try utils.mappingIndexAccessFunction(
                        current_type,
                        parameter_type,
                        packed_encoder,
                    );
                    defer self.allocator.free(index_function);
                    try body.print(
                        self.allocator,
                        "\nslot := {s}(slot, {s})\n",
                        .{ index_function, keys },
                    );
                    current_type = mapping.value_type;
                },
                .Array => |array| {
                    if (array.isByteArrayOrString()) return error.InvalidAst;
                    // Keep upstream Whiskers substitution order: the index
                    // helper is requested before the length helper even
                    // though the bounds check renders first.
                    const index_function = try utils.storageArrayIndexAccessFunction(
                        current_type,
                    );
                    defer self.allocator.free(index_function);
                    const length_function = try utils.arrayLengthFunction(current_type);
                    defer self.allocator.free(length_function);
                    try body.print(
                        self.allocator,
                        "\nif iszero(lt({s}, {s}(slot))) {{ revert(0, 0) }}\nslot, offset := {s}(slot, {s})\n",
                        .{ keys, length_function, index_function, keys },
                    );
                    current_type = array.base_type;
                },
                else => return error.InvalidAst,
            }
        }

        var return_variables: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &return_variables);
        if (current_type.asStruct()) |structure| {
            if (storage.byte_offset != 0 or
                getter_type.return_parameter_types.len !=
                    getter_type.return_parameter_names.len)
                return error.InvalidAst;
            for (
                getter_type.return_parameter_types,
                getter_type.return_parameter_names,
            ) |return_type, return_name| {
                const member_offset = try TypeBehavior.structStorageOffsetOfMember(
                    self.allocator,
                    structure.*,
                    return_name,
                );
                const result_name = try std.fmt.allocPrint(
                    self.allocator,
                    "ret_{d}",
                    .{return_variables.items.len},
                );
                defer self.allocator.free(result_name);
                var result = try IRVariableModule.IRVariable.init(
                    self.allocator,
                    result_name,
                    return_type,
                );
                defer result.deinit();
                const result_text = try result.commaSeparatedListAlloc();
                defer self.allocator.free(result_text);
                try result.appendStackSlots(self.allocator, &return_variables);
                const reader = try utils.readFromStorage(
                    return_type,
                    member_offset.byte_offset,
                    true,
                    storage.location,
                );
                defer self.allocator.free(reader);
                try body.print(
                    self.allocator,
                    "\n{s} := {s}(add(slot, {d}))\n",
                    .{ result_text, reader, member_offset.slot },
                );
            }
        } else {
            if (getter_type.return_parameter_types.len != 1)
                return error.InvalidAst;
            if (current_type.asArray()) |array|
                if (!array.isByteArrayOrString()) return error.InvalidAst;
            const return_type = getter_type.return_parameter_types[0];
            var result = try IRVariableModule.IRVariable.init(
                self.allocator,
                "ret",
                return_type,
            );
            defer result.deinit();
            const result_text = try result.commaSeparatedListAlloc();
            defer self.allocator.free(result_text);
            try result.appendStackSlots(self.allocator, &return_variables);
            const reader = try utils.readFromStorageDynamic(
                return_type,
                true,
                storage.location,
            );
            defer self.allocator.free(reader);
            try body.print(
                self.allocator,
                "\n{s} := {s}(slot, offset)\n",
                .{ result_text, reader },
            );
        }
        if (return_variables.items.len == 0) return error.InvalidAst;
        const parameter_names = try joinAlloc(
            self.allocator,
            parameters.items,
            ", ",
        );
        defer self.allocator.free(parameter_names);
        const return_names = try joinAlloc(
            self.allocator,
            return_variables.items,
            ", ",
        );
        defer self.allocator.free(return_names);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n{s}{s}\nfunction {s}({s}) -> {s} {{\n{s}\n}}\n{s}\n",
            .{
                ast_id_comment,
                location,
                name,
                parameter_names,
                return_names,
                body.items,
                contract_location,
            },
        );
        defer self.allocator.free(code);
        try self.context.functionCollector().finishFunction(name, code);
        return name;
    }

    fn generateQueuedFunctions(
        self: *IRGenerator,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError!void {
        while (!self.context.functionGenerationQueueEmpty()) {
            const function = try self.context.dequeueFunctionForCodeGeneration();
            try self.generateFunction(@constCast(function), utils);
        }
    }

    fn generateInternalDispatchFunctions(
        self: *IRGenerator,
        contract: *const AST.Node,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError!ContextModule.InternalDispatchMap {
        var dispatch_map = self.context.consumeInternalDispatchMap();
        errdefer dispatch_map.deinit();

        var arities: std.ArrayList(Common.YulArity) = .empty;
        defer arities.deinit(self.allocator);
        try arities.ensureTotalCapacity(
            self.allocator,
            dispatch_map.entries.count(),
        );
        var key_iterator = dispatch_map.entries.keyIterator();
        while (key_iterator.next()) |arity| arities.appendAssumeCapacity(arity.*);
        std.sort.insertion(
            Common.YulArity,
            arities.items,
            {},
            Common.YulArity.lessThan,
        );

        const annotation = try contractAnnotation(
            try self.context.mostDerivedContract(),
        );
        for (arities.items) |arity| {
            const name = try Common.internalDispatchAlloc(self.allocator, arity);
            defer self.allocator.free(name);
            if (!(try self.context.functionCollector().beginFunction(name))) continue;
            errdefer self.context.functionCollector().abortFunction(name);

            const panic = try utils.panicFunction(.invalid_internal_function);
            defer self.allocator.free(panic);
            const inputs = try variableListAlloc(self.allocator, "in_", arity.in);
            defer self.allocator.free(inputs);
            const outputs = try variableListAlloc(self.allocator, "out_", arity.out);
            defer self.allocator.free(outputs);
            const location = try self.locationCommentAlloc(contract);
            defer self.allocator.free(location);

            var code: std.ArrayList(u8) = .empty;
            defer code.deinit(self.allocator);
            try code.print(
                self.allocator,
                "\n{s}\nfunction {s}(fun{s}{s}){s}{s} {{\nswitch fun\n",
                .{
                    location,
                    name,
                    if (inputs.len == 0) "" else ", ",
                    inputs,
                    if (outputs.len == 0) "" else " -> ",
                    outputs,
                },
            );
            const functions = dispatch_map.entries.get(arity) orelse
                return error.InvalidAst;
            for (functions.items) |function| {
                if (function.nodeKind() != .function_definition or
                    function.payload.function_definition.kind == .Constructor)
                    return error.InvalidAst;
                const identifier = for (annotation.internal_function_ids.items) |entry| {
                    if (entry.function == function) break entry.id;
                } else return error.InvalidAst;
                const function_name = try Common.functionAlloc(
                    self.allocator,
                    self.compatibility_ids,
                    function,
                );
                defer self.allocator.free(function_name);
                try code.print(
                    self.allocator,
                    "case {d}\n{{\n{s}{s}{s}({s})\n}}\n",
                    .{
                        identifier,
                        outputs,
                        if (outputs.len == 0) "" else " := ",
                        function_name,
                        inputs,
                    },
                );
            }
            try code.print(
                self.allocator,
                "default {{ {s}() }}\n}}\n{s}\n",
                .{ panic, location },
            );
            try self.context.functionCollector().finishFunction(name, code.items);
        }
        return dispatch_map;
    }

    fn generateFunction(
        self: *IRGenerator,
        function: *AST.Node,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError!void {
        if (function.nodeKind() != .function_definition) return error.InvalidAst;
        const definition = function.payload.function_definition;
        const body_node = definition.body orelse return error.MissingFunctionBody;
        const name = try Common.functionAlloc(
            self.allocator,
            self.compatibility_ids,
            function,
        );
        defer self.allocator.free(name);
        if (!(try self.context.functionCollector().beginFunction(name))) return;
        errdefer self.context.functionCollector().abortFunction(name);
        self.context.resetLocalVariables();

        var parameter_names: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &parameter_names);
        const parameters_node = definition.callable.parameters;
        if (parameters_node.nodeKind() != .parameter_list) return error.InvalidAst;
        for (parameters_node.payload.parameter_list.parameters) |parameter| {
            const local = try self.context.addLocalVariable(parameter);
            try local.appendStackSlots(self.allocator, &parameter_names);
        }
        var return_names: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &return_names);
        var return_initialization: std.ArrayList(u8) = .empty;
        defer return_initialization.deinit(self.allocator);
        if (definition.callable.return_parameters) |return_parameters| {
            if (return_parameters.nodeKind() != .parameter_list) return error.InvalidAst;
            for (return_parameters.payload.parameter_list.parameters) |return_parameter| {
                const local = try self.context.addLocalVariable(return_parameter);
                try local.appendStackSlots(self.allocator, &return_names);
                var initializer = StatementGeneratorModule.IRGeneratorForStatements.init(
                    self.allocator,
                    &self.context,
                    utils,
                    self.optimiser_settings,
                    null,
                );
                defer initializer.deinit();
                try initializer.initializeLocalVar(return_parameter);
                try return_initialization.appendSlice(
                    self.allocator,
                    initializer.codeBorrowed(),
                );
            }
        }

        const function_body = if (definition.modifiers.len == 0) blk: {
            var statements = StatementGeneratorModule.IRGeneratorForStatements.init(
                self.allocator,
                &self.context,
                utils,
                self.optimiser_settings,
                null,
            );
            defer statements.deinit();
            try statements.generate(body_node);
            break :blk try statements.codeAlloc(self.allocator);
        } else blk: {
            for (definition.modifiers, 0..) |invocation, index| {
                const next = if (index + 1 < definition.modifiers.len)
                    try Common.modifierInvocationAlloc(
                        self.allocator,
                        self.compatibility_ids,
                        definition.modifiers[index + 1],
                    )
                else
                    try Common.functionWithModifierInnerAlloc(
                        self.allocator,
                        self.compatibility_ids,
                        function,
                    );
                defer self.allocator.free(next);
                try self.generateModifier(function, invocation, next, utils);
            }
            try self.generateFunctionWithModifierInner(function, utils);
            const first = try Common.modifierInvocationAlloc(
                self.allocator,
                self.compatibility_ids,
                definition.modifiers[0],
            );
            defer self.allocator.free(first);
            var call_arguments: std.ArrayList([]const u8) = .empty;
            defer call_arguments.deinit(self.allocator);
            try call_arguments.appendSlice(self.allocator, return_names.items);
            try call_arguments.appendSlice(self.allocator, parameter_names.items);
            const joined_call_arguments = try joinAlloc(
                self.allocator,
                call_arguments.items,
                ", ",
            );
            defer self.allocator.free(joined_call_arguments);
            const joined_call_returns = try joinAlloc(
                self.allocator,
                return_names.items,
                ", ",
            );
            defer self.allocator.free(joined_call_returns);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}{s}{s}({s})",
                .{
                    joined_call_returns,
                    if (joined_call_returns.len == 0) "" else " := ",
                    first,
                    joined_call_arguments,
                },
            );
        };
        defer self.allocator.free(function_body);
        const joined_parameters = try joinAlloc(
            self.allocator,
            parameter_names.items,
            ", ",
        );
        defer self.allocator.free(joined_parameters);
        const joined_returns = try joinAlloc(self.allocator, return_names.items, ", ");
        defer self.allocator.free(joined_returns);
        const source_location = try self.locationCommentAlloc(function);
        defer self.allocator.free(source_location);
        const contract_location = try self.locationCommentAlloc(
            try self.context.mostDerivedContract(),
        );
        defer self.allocator.free(contract_location);
        const ast_id_comment = if (self.debug_info_selection.ast_id)
            try std.fmt.allocPrint(
                self.allocator,
                "/// @ast-id {d}\n",
                .{try self.compatibilityId(function)},
            )
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(ast_id_comment);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n{s}{s}\nfunction {s}({s}){s}{s} {{\n{s}\n{s}\n}}\n{s}\n",
            .{
                ast_id_comment,
                source_location,
                name,
                joined_parameters,
                if (joined_returns.len == 0) "" else " -> ",
                joined_returns,
                return_initialization.items,
                function_body,
                contract_location,
            },
        );
        defer self.allocator.free(code);
        try self.context.functionCollector().finishFunction(name, code);
    }

    fn generateModifier(
        self: *IRGenerator,
        function: *AST.Node,
        invocation: *AST.Node,
        next_function: []const u8,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError!void {
        if (invocation.nodeKind() != .modifier_invocation)
            return error.UnsupportedModifier;
        const invocation_data = invocation.payload.modifier_invocation;
        const referenced = try identifierPathOrIdentifierDeclaration(
            invocation_data.modifier_name,
        );
        if (referenced.nodeKind() != .modifier_definition)
            return error.UnsupportedModifier;
        const lookup = try identifierPathOrIdentifierLookup(invocation_data.modifier_name);
        const modifier = switch (lookup) {
            .Static => referenced,
            .Virtual => try resolveVirtualCallable(
                referenced,
                try self.context.mostDerivedContract(),
            ),
            .Super => return error.UnsupportedModifier,
        };
        if (modifier.nodeKind() != .modifier_definition)
            return error.UnsupportedModifier;
        const modifier_body = modifier.payload.modifier_definition.body orelse
            return error.UnsupportedModifier;
        const modifier_parameters = modifier.payload.modifier_definition.callable.parameters
            .payload.parameter_list.parameters;
        const invocation_arguments = invocation_data.arguments orelse &.{};
        if (modifier_parameters.len != invocation_arguments.len)
            return error.UnsupportedModifier;

        const name = try Common.modifierInvocationAlloc(
            self.allocator,
            self.compatibility_ids,
            invocation,
        );
        defer self.allocator.free(name);
        if (!(try self.context.functionCollector().beginFunction(name))) return;
        errdefer self.context.functionCollector().abortFunction(name);
        self.context.resetLocalVariables();

        var parameter_names: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &parameter_names);
        var return_outputs: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &return_outputs);
        var return_assignments: std.ArrayList(u8) = .empty;
        defer return_assignments.deinit(self.allocator);

        if (function.payload.function_definition.callable.return_parameters) |returns| {
            for (returns.payload.parameter_list.parameters) |declaration| {
                const local = try self.context.addLocalVariable(declaration);
                var slots = try local.stackSlotsAlloc();
                defer slots.deinit();
                for (slots.items) |slot| {
                    try parameter_names.ensureUnusedCapacity(self.allocator, 1);
                    const parameter = try self.allocator.dupe(u8, slot);
                    parameter_names.appendAssumeCapacity(parameter);
                    try return_outputs.ensureUnusedCapacity(self.allocator, 1);
                    const output = try self.context.newYulVariable();
                    return_outputs.appendAssumeCapacity(output);
                    try return_assignments.print(
                        self.allocator,
                        "{s} := {s}\n",
                        .{ output, slot },
                    );
                }
            }
        }
        for (function.payload.function_definition.callable.parameters
            .payload.parameter_list.parameters) |declaration|
        {
            const local = try self.context.addLocalVariable(declaration);
            try local.appendStackSlots(self.allocator, &parameter_names);
        }

        var argument_evaluator = StatementGeneratorModule.IRGeneratorForStatements.init(
            self.allocator,
            &self.context,
            utils,
            self.optimiser_settings,
            null,
        );
        defer argument_evaluator.deinit();
        for (invocation_arguments, modifier_parameters) |argument, parameter| {
            var value = try argument_evaluator.evaluateExpression(
                argument,
                try variableType(parameter),
            );
            defer value.deinit();
            _ = try self.context.addLocalVariable(parameter);
            try argument_evaluator.bindLocalValue(parameter, &value);
        }

        const joined_parameters = try joinAlloc(
            self.allocator,
            parameter_names.items,
            ", ",
        );
        defer self.allocator.free(joined_parameters);
        const joined_returns = try joinAlloc(
            self.allocator,
            return_outputs.items,
            ", ",
        );
        defer self.allocator.free(joined_returns);
        var placeholder_context: ModifierPlaceholderContext = .{
            .next_function = next_function,
            .return_values = joined_returns,
            .arguments = joined_parameters,
        };
        var statements = StatementGeneratorModule.IRGeneratorForStatements.init(
            self.allocator,
            &self.context,
            utils,
            self.optimiser_settings,
            .{
                .context = &placeholder_context,
                .generate_fn = ModifierPlaceholderContext.generate,
            },
        );
        defer statements.deinit();
        try statements.generate(modifier_body);

        const source_location = try self.locationCommentAlloc(referenced);
        defer self.allocator.free(source_location);
        const contract_location = try self.locationCommentAlloc(
            try self.context.mostDerivedContract(),
        );
        defer self.allocator.free(contract_location);
        const ast_id_comment = if (self.debug_info_selection.ast_id)
            try std.fmt.allocPrint(
                self.allocator,
                "/// @ast-id {d}\n",
                .{try self.compatibilityId(referenced)},
            )
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(ast_id_comment);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n{s}{s}\nfunction {s}({s}){s}{s} {{\n{s}\n{s}\n{s}\n}}\n{s}\n",
            .{
                ast_id_comment,
                source_location,
                name,
                joined_parameters,
                if (joined_returns.len == 0) "" else " -> ",
                joined_returns,
                return_assignments.items,
                argument_evaluator.codeBorrowed(),
                statements.codeBorrowed(),
                contract_location,
            },
        );
        defer self.allocator.free(code);
        try self.context.functionCollector().finishFunction(name, code);
    }

    fn generateFunctionWithModifierInner(
        self: *IRGenerator,
        function: *AST.Node,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError!void {
        const name = try Common.functionWithModifierInnerAlloc(
            self.allocator,
            self.compatibility_ids,
            function,
        );
        defer self.allocator.free(name);
        if (!(try self.context.functionCollector().beginFunction(name))) return;
        errdefer self.context.functionCollector().abortFunction(name);
        self.context.resetLocalVariables();

        var parameter_names: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &parameter_names);
        var return_names: std.ArrayList([]u8) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        defer deinitStrings(self.allocator, &return_names);
        var assignments: std.ArrayList(u8) = .empty;
        defer assignments.deinit(self.allocator);

        if (function.payload.function_definition.callable.return_parameters) |returns| {
            for (returns.payload.parameter_list.parameters) |declaration| {
                const local = try self.context.addLocalVariable(declaration);
                var slots = try local.stackSlotsAlloc();
                defer slots.deinit();
                for (slots.items) |slot| {
                    try return_names.ensureUnusedCapacity(self.allocator, 1);
                    const output = try self.allocator.dupe(u8, slot);
                    return_names.appendAssumeCapacity(output);
                    try parameter_names.ensureUnusedCapacity(self.allocator, 1);
                    const input = try self.context.newYulVariable();
                    parameter_names.appendAssumeCapacity(input);
                    try assignments.print(
                        self.allocator,
                        "{s} := {s}\n",
                        .{ slot, input },
                    );
                }
            }
        }
        for (function.payload.function_definition.callable.parameters
            .payload.parameter_list.parameters) |declaration|
        {
            const local = try self.context.addLocalVariable(declaration);
            try local.appendStackSlots(self.allocator, &parameter_names);
        }
        var statements = StatementGeneratorModule.IRGeneratorForStatements.init(
            self.allocator,
            &self.context,
            utils,
            self.optimiser_settings,
            null,
        );
        defer statements.deinit();
        try statements.generate(
            function.payload.function_definition.body orelse return error.MissingFunctionBody,
        );
        const joined_parameters = try joinAlloc(
            self.allocator,
            parameter_names.items,
            ", ",
        );
        defer self.allocator.free(joined_parameters);
        const joined_returns = try joinAlloc(
            self.allocator,
            return_names.items,
            ", ",
        );
        defer self.allocator.free(joined_returns);
        const source_location = try self.locationCommentAlloc(function);
        defer self.allocator.free(source_location);
        const contract_location = try self.locationCommentAlloc(
            try self.context.mostDerivedContract(),
        );
        defer self.allocator.free(contract_location);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n{s}\nfunction {s}({s}){s}{s} {{\n{s}\n{s}\n}}\n{s}\n",
            .{
                source_location,
                name,
                joined_parameters,
                if (joined_returns.len == 0) "" else " -> ",
                joined_returns,
                assignments.items,
                statements.codeBorrowed(),
                contract_location,
            },
        );
        defer self.allocator.free(code);
        try self.context.functionCollector().finishFunction(name, code);
    }

    fn interfaceFunctionsAlloc(
        self: *IRGenerator,
        _: *AST.Tree,
        contract: *AST.Node,
    ) GeneratorError!std.ArrayList(InterfaceFunction) {
        var result: std.ArrayList(InterfaceFunction) = .empty;
        errdefer {
            for (result.items) |function| self.allocator.free(function.signature);
            result.deinit(self.allocator);
        }
        const functions = try ASTImplementation.contractInterfaceFunctionListAlloc(
            self.type_provider,
            self.allocator,
            contract,
            true,
        );
        defer self.allocator.free(functions);
        for (functions) |function| {
            const function_type = function.function_type.payload.Function;
            const member = @constCast(function_type.declaration orelse return error.InvalidAst);
            const signature = try TypeBehavior.externalSignatureAlloc(
                self.type_provider,
                self.allocator,
                function_type,
            );
            const selector = FunctionSelector.selectorFromSignatureU32(signature);
            for (result.items) |existing|
                if (existing.selector == selector) {
                    self.allocator.free(signature);
                    return error.DuplicateInterfaceSelector;
                };
            try result.append(self.allocator, .{
                .declaration = member,
                .signature = signature,
                .selector = selector,
            });
        }
        std.sort.insertion(InterfaceFunction, result.items, {}, InterfaceFunction.lessThan);
        return result;
    }

    fn callValueCheckAlloc(
        self: *IRGenerator,
        utils: *YulUtilFunctionsModule.YulUtilFunctions,
    ) GeneratorError![]u8 {
        const revert = try utils.revertReasonIfDebugFunction(
            "Ether sent to non-payable function",
        );
        defer self.allocator.free(revert);
        return std.fmt.allocPrint(
            self.allocator,
            "if callvalue() {{ {s}() }}",
            .{revert},
        );
    }

    fn immutablePatchesAlloc(
        self: *IRGenerator,
        contract: *AST.Node,
        code_offset: []const u8,
    ) GeneratorError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        if (contract.payload.contract_definition.contract_kind == .Library) {
            try output.print(
                self.allocator,
                "setimmutable({s}, \"{s}\", address())\n",
                .{ code_offset, Common.libraryAddressImmutable() },
            );
            return output.toOwnedSlice(self.allocator);
        }
        var variables = try self.immutableVariablesAlloc(contract);
        defer variables.deinit(self.allocator);
        for (variables.items) |variable|
            try output.print(
                self.allocator,
                "setimmutable({s}, \"{d}\", mload({d}))\n",
                .{
                    code_offset,
                    try self.compatibilityId(variable),
                    try self.context.immutableMemoryOffset(variable),
                },
            );
        return output.toOwnedSlice(self.allocator);
    }

    fn memoryInitAlloc(
        self: *IRGenerator,
        use_memory_guard: bool,
    ) GeneratorError![]u8 {
        const reserved = try self.context.reservedMemory();
        const free_memory_start = ContextModule.general_purpose_memory_start + reserved;
        return if (use_memory_guard)
            std.fmt.allocPrint(
                self.allocator,
                "mstore(64, memoryguard({d}))",
                .{free_memory_start},
            )
        else
            std.fmt.allocPrint(
                self.allocator,
                "mstore(64, {d})",
                .{free_memory_start},
            );
    }

    fn locationCommentAlloc(
        self: *IRGenerator,
        node: *const AST.Node,
    ) GeneratorError![]u8 {
        if (!node.location.isValid()) return self.allocator.alloc(u8, 0);
        return Common.dispenseNodeLocationCommentAlloc(
            self.allocator,
            node,
            self.context.locationCommentContext(),
        );
    }

    fn useSrcMapAlloc(self: *IRGenerator) GeneratorError![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        var first = true;
        for (self.source_index_to_name) |source| {
            if (!self.context.sourceUsed(source.name)) continue;
            const quoted = try CommonData.escapeAndQuoteStringAlloc(
                self.allocator,
                source.name,
            );
            defer self.allocator.free(quoted);
            if (!first) try output.appendSlice(self.allocator, ", ");
            try output.print(self.allocator, "{d}:{s}", .{ source.index, quoted });
            first = false;
        }
        return output.toOwnedSlice(self.allocator);
    }
};

fn validateContractBoundary(contract: *const AST.Node) GeneratorError!void {
    if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
    const definition = contract.payload.contract_definition;
    if ((definition.contract_kind != .Contract and
        definition.contract_kind != .Library) or definition.abstract)
        return error.UnsupportedContract;
    const annotation = try contractAnnotation(contract);
    const hierarchy = annotation.linearized_base_contracts;
    const contracts = if (hierarchy.len == 0)
        @as([]const *const AST.Node, &.{contract})
    else
        hierarchy;
    for (contracts) |base| {
        if (base.nodeKind() != .contract_definition) return error.InvalidAst;
        if (base.payload.contract_definition.contract_kind == .Library and
            !(definition.contract_kind == .Library and base == contract))
            return error.UnsupportedInheritance;
        // Interfaces participate in the linearized hierarchy for override and
        // external-interface selection, but contribute no constructor, state,
        // or executable body to a concrete contract's IR object.
        if (base.payload.contract_definition.contract_kind == .Interface)
            continue;
        for ([_]AST.Token{ .Fallback, .Receive }) |kind| {
            const special = findSpecialFunctionDirect(base, kind) orelse continue;
            const callable = special.payload.function_definition.callable;
            const parameter_count = callable.parameters.payload.parameter_list.parameters.len;
            const return_count = if (callable.return_parameters) |returns|
                returns.payload.parameter_list.parameters.len
            else
                0;
            if (kind == .Receive) {
                if (parameter_count != 0 or return_count != 0)
                    return error.InvalidAst;
            } else if (!((parameter_count == 0 and return_count == 0) or
                (parameter_count == 1 and return_count == 1)))
                return error.InvalidAst;
        }
        for (base.payload.contract_definition.sub_nodes) |member| {
            if (member.nodeKind() != .variable_declaration or
                !ASTImplementation.isStateVariable(member))
                continue;
            const variable = member.payload.variable_declaration;
            if (variable.mutability == .Constant) {
                // Constants are evaluated into their annotated type on demand.
                // In particular, string and bytes constants lower to memory
                // references and are not value types.
                continue;
            }
            if (variable.mutability == .Immutable) {
                if (!TypeBehavior.isValueType(try variableType(member)) or
                    try TypeBehavior.sizeOnStack(try variableType(member)) != 1)
                    return error.UnsupportedStateVariable;
                continue;
            }
            if (variable.mutability != .Mutable)
                return error.UnsupportedStateVariable;
        }
    }
}

fn findConstructor(contract: *const AST.Node) ?*AST.Node {
    for (contract.payload.contract_definition.sub_nodes) |member|
        if (member.nodeKind() == .function_definition and
            member.payload.function_definition.kind == .Constructor)
            return member;
    return null;
}

fn constructorPayable(contract: *const AST.Node) bool {
    const constructor = findConstructor(contract) orelse return false;
    return constructor.payload.function_definition.state_mutability == .Payable;
}

fn findSpecialFunctionDirect(
    contract: *const AST.Node,
    kind: AST.Token,
) ?*AST.Node {
    for (contract.payload.contract_definition.sub_nodes) |member|
        if (member.nodeKind() == .function_definition and
            member.payload.function_definition.kind == kind)
            return member;
    return null;
}

fn resolveSpecialFunction(
    contract: *const AST.Node,
    kind: AST.Token,
) GeneratorError!?*AST.Node {
    const annotation = try contractAnnotation(contract);
    if (annotation.linearized_base_contracts.len == 0)
        return findSpecialFunctionDirect(contract, kind);
    for (annotation.linearized_base_contracts) |base|
        if (findSpecialFunctionDirect(base, kind)) |function|
            return function;
    return null;
}

fn identifierPathOrIdentifierDeclaration(
    node: *const AST.Node,
) GeneratorError!*AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse
        return error.InvalidAst;
    const declaration = switch (annotation.*) {
        .identifier_path => |value| value.referenced_declaration,
        .identifier => |value| value.referenced_declaration,
        else => return error.InvalidAst,
    } orelse return error.InvalidAst;
    return @constCast(declaration);
}

fn identifierPathOrIdentifierLookup(
    node: *const AST.Node,
) GeneratorError!AST.VirtualLookup {
    const annotation = ASTAnnotations.annotationConst(node) orelse
        return error.InvalidAst;
    const field = switch (annotation.*) {
        .identifier_path => |*value| &value.required_lookup,
        .identifier => |*value| &value.required_lookup,
        else => return error.InvalidAst,
    };
    return (field.get() catch return error.InvalidAst).*;
}

fn resolveVirtualCallable(
    declaration: *const AST.Node,
    most_derived_contract: *const AST.Node,
) GeneratorError!*AST.Node {
    const annotation = try contractAnnotation(most_derived_contract);
    for (annotation.linearized_base_contracts) |base|
        for (base.payload.contract_definition.sub_nodes) |candidate| {
            if (candidate.nodeKind() != declaration.nodeKind()) continue;
            if (candidate == declaration or callableOverrides(candidate, declaration, 0))
                return candidate;
        };
    return @constCast(declaration);
}

fn callableOverrides(
    candidate: *const AST.Node,
    target: *const AST.Node,
    depth: usize,
) bool {
    if (depth >= 256) return false;
    const bases = callableBaseFunctions(candidate) orelse return false;
    for (bases) |base|
        if (base == target or callableOverrides(base, target, depth + 1)) return true;
    return false;
}

fn callableBaseFunctions(node: *const AST.Node) ?[]const *const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .documented_callable => |value| value.callable.base_functions.items,
        else => null,
    };
}

fn contractAnnotation(
    contract: *const AST.Node,
) GeneratorError!*const ASTAnnotations.ContractDefinitionAnnotation {
    const annotation = ASTAnnotations.annotationConst(contract) orelse
        return error.InvalidAst;
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => error.InvalidAst,
    };
}

fn variableType(variable: *const AST.Node) GeneratorError!*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(variable) orelse
        return error.InvalidAst;
    return switch (annotation.*) {
        .variable_declaration => |value| value.type_ref,
        else => null,
    } orelse error.InvalidAst;
}

fn callableTypesAlloc(
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    function: *const AST.Node,
    returns: bool,
) GeneratorError![]const *const Types.Type {
    if (function.nodeKind() == .variable_declaration) {
        const getter = (try type_provider.functionFromVariable(function)).asFunction() orelse
            return error.InvalidAst;
        return allocator.dupe(
            *const Types.Type,
            if (returns) getter.return_parameter_types else getter.parameter_types,
        );
    }
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    const callable = function.payload.function_definition.callable;
    const parameters = if (returns)
        callable.return_parameters orelse return allocator.alloc(*const Types.Type, 0)
    else
        callable.parameters;
    if (parameters.nodeKind() != .parameter_list) return error.InvalidAst;
    const declarations = parameters.payload.parameter_list.parameters;
    const result = try allocator.alloc(*const Types.Type, declarations.len);
    errdefer allocator.free(result);
    for (declarations, result) |declaration, *target|
        target.* = try variableType(declaration);
    return result;
}

fn stackSize(types: []const *const Types.Type) GeneratorError!usize {
    var result: usize = 0;
    for (types) |type_ref|
        result = std.math.add(
            usize,
            result,
            try TypeBehavior.sizeOnStack(type_ref),
        ) catch return error.Overflow;
    return result;
}

fn constructorParametersTextAlloc(
    allocator: std.mem.Allocator,
    hierarchy: []const *AST.Node,
    parameters: *const ConstructorParameterMap,
) std.mem.Allocator.Error![]u8 {
    var ordered: std.ArrayList([]const u8) = .empty;
    defer ordered.deinit(allocator);
    for (hierarchy) |contract|
        if (parameters.get(contract)) |values|
            try ordered.appendSlice(allocator, values.items);
    return joinAlloc(allocator, ordered.items, ", ");
}

fn deinitConstructorParameterMap(
    allocator: std.mem.Allocator,
    parameters: *ConstructorParameterMap,
) void {
    var iterator = parameters.valueIterator();
    while (iterator.next()) |values| deinitStrings(allocator, values);
    parameters.deinit(allocator);
}

fn deinitStrings(
    allocator: std.mem.Allocator,
    values: *std.ArrayList([]u8),
) void {
    for (values.items) |value| allocator.free(value);
    values.deinit(allocator);
}

fn variableListAlloc(
    allocator: std.mem.Allocator,
    prefix: []const u8,
    count: usize,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (0..count) |index| {
        if (index != 0) try output.appendSlice(allocator, ", ");
        try output.print(allocator, "{s}{d}", .{ prefix, index });
    }
    return output.toOwnedSlice(allocator);
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

test "external wrapper variable lists retain upstream numbering" {
    const empty = try variableListAlloc(std.testing.allocator, "param_", 0);
    defer std.testing.allocator.free(empty);
    try std.testing.expectEqualStrings("", empty);
    const values = try variableListAlloc(std.testing.allocator, "param_", 3);
    defer std.testing.allocator.free(values);
    try std.testing.expectEqualStrings("param_0, param_1, param_2", values);
}
