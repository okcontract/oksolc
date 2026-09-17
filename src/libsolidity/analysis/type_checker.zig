// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Solidity expression and body typing translated from `TypeChecker.cpp`.
//!
//! Populates expression annotations and checks statement and expression types.
//! Unsupported expression families report a diagnostic.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const ASTUtils = @import("../ast/ast_utils.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const TokenModule = @import("../../liblangutil/token.zig");
const SetOnce = @import("../../libsolutil/set_once.zig");
const YulAST = @import("../../libyul/ast.zig");
const YulAsmAnalysis = @import("../../libyul/asm_analysis.zig");

pub const CheckError = ASTImplementation.AstError ||
    TypeProviderModule.ProviderError ||
    TypeBehavior.BehaviorError ||
    Diagnostics.ReportError ||
    SetOnce.SetOnceError ||
    error{InvalidAst};

const max_ast_depth = 4096;

const ResolvedMember = struct {
    type_ref: *const Types.Type,
    declaration: ?*const AST.Node = null,
    lookup: AST.VirtualLookup = .Static,
    is_lvalue: bool = false,
    is_pure: bool = false,
};

pub const TypeChecker = struct {
    allocator: std.mem.Allocator,
    tree: *AST.Tree,
    type_provider: *TypeProviderModule.TypeProvider,
    evm_version: EVMVersion,
    reporter: *Diagnostics.ErrorReporter,
    compatibility_ids: CompatibilityIdResolver = .legacyNodeIds(),
    current_source_unit: ?*const AST.Node = null,
    current_contract: ?*const AST.Node = null,

    pub fn init(
        allocator: std.mem.Allocator,
        tree: *AST.Tree,
        type_provider: *TypeProviderModule.TypeProvider,
        evm_version: EVMVersion,
        reporter: *Diagnostics.ErrorReporter,
    ) TypeChecker {
        return .{
            .allocator = allocator,
            .tree = tree,
            .type_provider = type_provider,
            .evm_version = evm_version,
            .reporter = reporter,
        };
    }

    pub fn checkTypeRequirements(
        self: *TypeChecker,
        source_unit: *AST.Node,
    ) CheckError!bool {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        self.current_source_unit = source_unit;
        defer self.current_source_unit = null;
        try self.checkNode(source_unit, 0);
        return watcher.ok();
    }

    pub fn setCompatibilityIds(
        self: *TypeChecker,
        compatibility_ids: CompatibilityIdResolver,
    ) void {
        self.compatibility_ids = compatibility_ids;
    }

    fn checkNode(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        if (node.isExpression()) return self.checkExpression(node, depth);

        switch (node.payload) {
            .import_directive => return,
            .function_definition => return self.visitFunctionDefinition(node, depth),
            .if_statement => return self.visitIfStatement(node, depth),
            .while_statement => return self.visitWhileStatement(node, depth),
            .for_statement => return self.visitForStatement(node, depth),
            .variable_declaration_statement => return self.visitVariableDeclarationStatement(
                node,
                depth,
            ),
            .event_definition => try self.endEventDefinition(node),
            .error_definition => try self.endErrorDefinition(node),
            else => {},
        }

        const previous_contract = self.current_contract;
        if (node.nodeKind() == .contract_definition) self.current_contract = node;
        defer self.current_contract = previous_contract;

        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.allocator);
        try ASTImplementation.appendChildren(self.allocator, &children, node);
        for (children.items) |child|
            try self.checkNode(@constCast(child), depth + 1);

        switch (node.payload) {
            .variable_declaration => try self.endVariableDeclaration(node),
            .inheritance_specifier => try self.endInheritanceSpecifier(node),
            .modifier_definition => try self.endModifierDefinition(node),
            .function_type_name => try self.endFunctionTypeName(node),
            .using_for_directive => try self.endUsingForDirective(node),
            .return_statement => try self.endReturn(node),
            .inline_assembly => try self.endInlineAssembly(node),
            .try_statement => try self.endTryStatement(node),
            .emit_statement => try self.endEmitStatement(node),
            .revert_statement => try self.endRevertStatement(node),
            .expression_statement => try self.endExpressionStatement(node),
            .identifier_path => try self.endIdentifierPath(node),
            else => {},
        }
    }

    fn endInheritanceSpecifier(
        self: *TypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const value = node.payload.inheritance_specifier;
        const base = try referencedDeclarationForName(self.tree, value.base_name);
        if (base.nodeKind() != .contract_definition) return error.InvalidAst;
        const current = self.current_contract orelse return error.InvalidAst;
        if (current.payload.contract_definition.contract_kind == .Interface and
            base.payload.contract_definition.contract_kind != .Interface)
            try self.reporter.typeError(
                errorId(6536),
                node.location,
                "Interfaces can only inherit from other interfaces.",
            );
        const arguments = value.arguments orelse return;
        const parameters = if (base.payload.contract_definition.contract_kind == .Interface)
            &[_]*AST.Node{}
        else if (findConstructor(base)) |constructor|
            constructor.payload.function_definition.callable.parameters.payload.parameter_list.parameters
        else
            &[_]*AST.Node{};
        if (arguments.len != parameters.len) {
            const suffix: []const u8 = if (arguments.len == 0)
                " Remove parentheses if you do not want to provide arguments here."
            else
                "";
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Wrong argument count for constructor call: {d} arguments given but expected {d}.{s}",
                .{ arguments.len, parameters.len, suffix },
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(7927), node.location, message);
        }
        const count = @min(arguments.len, parameters.len);
        for (arguments[0..count], parameters[0..count]) |argument, parameter| {
            const actual = (try expressionAnnotation(self.tree, argument)).type_ref orelse
                return error.InvalidAst;
            const expected = (try variableAnnotation(self.tree, parameter)).type_ref orelse
                return error.InvalidAst;
            if (TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) continue;
            const actual_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, actual);
            defer self.allocator.free(actual_name);
            const expected_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, expected);
            defer self.allocator.free(expected_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Invalid type for argument in constructor call. Invalid implicit conversion from {s} to {s} requested.",
                .{ actual_name, expected_name },
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(9827), argument.location, message);
        }
    }

    fn visitFunctionDefinition(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const function = node.payload.function_definition;
        const contract = self.current_contract;
        const constructor = function.kind == .Constructor;
        const fallback = function.kind == .Fallback;
        const receive = function.kind == .Receive;
        // Upstream never calls `visibility()` for constructors: each use
        // below is guarded by a constructor/special-function check. Preserve
        // that control flow without inventing a constructor default.
        const visibility = ASTImplementation.effectiveVisibility(node) orelse .Default;
        if (function.callable.marked_virtual) {
            if (function.free)
                try self.reporter.syntaxError(
                    errorId(4493),
                    node.location,
                    "Free functions cannot be virtual.",
                )
            else if (constructor)
                try self.reporter.typeError(
                    errorId(7001),
                    node.location,
                    "Constructors cannot be virtual.",
                )
            else if (contract != null and
                contract.?.payload.contract_definition.contract_kind == .Interface)
                try self.reporter.warning(
                    errorId(5815),
                    node.location,
                    "Interface functions are implicitly \"virtual\"",
                )
            else if (visibility == .Private)
                try self.reporter.typeError(
                    errorId(3942),
                    node.location,
                    "\"virtual\" and \"private\" cannot be used together.",
                )
            else if (contract != null and
                contract.?.payload.contract_definition.contract_kind == .Library)
                try self.reporter.typeError(
                    errorId(7801),
                    node.location,
                    "Library functions cannot be \"virtual\".",
                );
        }
        if (function.callable.overrides != null and function.free)
            try self.reporter.syntaxError(
                errorId(1750),
                node.location,
                "Free functions cannot override.",
            );
        if (function.modifiers.len != 0 and function.free)
            try self.reporter.syntaxError(
                errorId(5811),
                node.location,
                "Free functions cannot have modifiers.",
            );
        if (function.state_mutability == .Payable) {
            if (contract != null and
                contract.?.payload.contract_definition.contract_kind == .Library)
                try self.reporter.typeError(
                    errorId(7708),
                    node.location,
                    "Library functions cannot be payable.",
                )
            else if (function.free)
                try self.reporter.typeError(
                    errorId(9559),
                    node.location,
                    "Free functions cannot be payable.",
                )
            else if (function.ordinary() and visibility != .Public and visibility != .External)
                try self.reporter.typeError(
                    errorId(5587),
                    node.location,
                    "\"internal\" and \"private\" functions cannot be payable.",
                );
        }

        const parameters = function.callable.parameters.payload.parameter_list.parameters;
        for (parameters) |parameter| {
            try self.checkFunctionArgumentOrReturn(node, parameter);
            try self.checkNode(parameter, depth + 1);
        }
        const return_parameters = if (function.callable.return_parameters) |returns|
            returns.payload.parameter_list.parameters
        else
            &[_]*AST.Node{};
        for (return_parameters) |parameter| {
            try self.checkFunctionArgumentOrReturn(node, parameter);
            try self.checkNode(parameter, depth + 1);
        }

        var constructor_bases: AST.NodeList = &.{};
        if (constructor and contract != null) {
            const annotation = ASTAnnotations.annotationConst(contract.?) orelse
                return error.InvalidAst;
            const contract_annotation = switch (annotation.*) {
                .contract_definition => |value| value,
                else => return error.InvalidAst,
            };
            if (contract_annotation.linearized_base_contracts.len != 0)
                constructor_bases = contract_annotation.linearized_base_contracts[1..];
        }
        var seen_modifiers = std.AutoHashMap(*const AST.Node, void).init(self.allocator);
        defer seen_modifiers.deinit();
        for (function.modifiers) |modifier| {
            try self.visitModifierInvocation(modifier, constructor_bases, depth + 1);
            const declaration = try referencedDeclarationForName(
                self.tree,
                modifier.payload.modifier_invocation.modifier_name,
            );
            if (seen_modifiers.contains(declaration)) {
                if (declaration.nodeKind() == .contract_definition)
                    try self.reporter.declarationError(
                        errorId(1697),
                        modifier.location,
                        "Base constructor already provided.",
                    );
            } else {
                try seen_modifiers.put(declaration, {});
            }
        }

        if (contract) |present| {
            const contract_data = present.payload.contract_definition;
            if (contract_data.contract_kind == .Interface) {
                if (function.implemented())
                    try self.reporter.typeError(
                        errorId(4726),
                        node.location,
                        "Functions in interfaces cannot have an implementation.",
                    );
                if (constructor)
                    try self.reporter.typeError(
                        errorId(6482),
                        node.location,
                        "Constructor cannot be defined in interfaces.",
                    )
                else if (visibility != .External)
                    try self.reporter.typeError(
                        errorId(1560),
                        node.location,
                        "Functions in interfaces must be declared external.",
                    );
            } else if (contract_data.contract_kind == .Library and constructor) {
                try self.reporter.typeError(
                    errorId(7634),
                    node.location,
                    "Constructor cannot be defined in libraries.",
                );
            }
        }
        if (function.body) |body| {
            try self.checkNode(body, depth + 1);
        } else {
            if (constructor)
                try self.reporter.typeError(
                    errorId(5700),
                    node.location,
                    "Constructor must be implemented if declared.",
                )
            else if (contract != null and
                contract.?.payload.contract_definition.contract_kind == .Library)
                try self.reporter.typeError(
                    errorId(9231),
                    node.location,
                    "Library functions must be implemented if declared.",
                )
            else if (!function.callable.marked_virtual and
                !function.free and
                (contract == null or
                    contract.?.payload.contract_definition.contract_kind != .Interface))
                try self.reporter.typeError(
                    errorId(5424),
                    node.location,
                    "Functions without implementation must be marked virtual.",
                );
        }
        if (fallback) try self.checkFallbackFunction(node);
        if (constructor) try self.checkConstructor(node);
        if (receive and function.callable.return_parameters != null and
            function.callable.return_parameters.?.payload.parameter_list.parameters.len != 0)
            try self.reporter.typeError(
                errorId(6239),
                function.callable.return_parameters.?.location,
                "Receive ether function cannot return values.",
            );
    }

    fn checkFunctionArgumentOrReturn(
        self: *TypeChecker,
        function_node: *const AST.Node,
        parameter: *const AST.Node,
    ) CheckError!void {
        const function = function_node.payload.function_definition;
        const constructor = function.kind == .Constructor;
        const contract = self.current_contract;
        const parameter_value = parameter.payload.variable_declaration;
        const parameter_type = (try variableAnnotation(
            self.tree,
            @constCast(parameter),
        )).type_ref orelse return error.InvalidAst;
        const externally_visible = (!constructor and ASTImplementation.isPublic(function_node)) or
            (constructor and contract != null and !contract.?.payload.contract_definition.abstract);

        if (constructor and parameter_value.reference_location == .Storage and
            contract != null and !contract.?.payload.contract_definition.abstract)
        {
            try self.reporter.fatal(
                errorId(3644),
                .TypeError,
                parameter.location,
                null,
                "This parameter has a type that can only be used internally. You can make the contract abstract to avoid this problem.",
            );
        } else if (externally_visible) {
            const in_library = ASTImplementation.functionIsLibrary(function_node);
            if ((try TypeBehavior.interfaceType(
                self.type_provider,
                parameter_type,
                in_library,
            )) == null) {
                const base_reason = interfaceTypeFailureReason(parameter_type, in_library);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "{s}{s}",
                    .{
                        base_reason,
                        if (constructor)
                            " You can make the contract abstract to avoid this problem."
                        else
                            "",
                    },
                );
                defer self.allocator.free(message);
                try self.reporter.fatal(
                    errorId(4103),
                    .TypeError,
                    parameter.location,
                    null,
                    message,
                );
            } else if (!(try self.useAbiCoderV2()) and
                !typeSupportedByOldABIEncoder(parameter_type, in_library))
            {
                const message = if (constructor)
                    "This type is only supported in ABI coder v2. Use \"pragma abicoder v2;\" to enable the feature. Alternatively, make the contract abstract and supply the constructor arguments from a derived contract."
                else
                    "This type is only supported in ABI coder v2. Use \"pragma abicoder v2;\" to enable the feature.";
                try self.reporter.typeError(errorId(4957), parameter.location, message);
            }
        }
    }

    fn checkFallbackFunction(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const function = node.payload.function_definition;
        const contract = self.current_contract orelse return error.InvalidAst;
        if (contract.payload.contract_definition.contract_kind == .Library)
            try self.reporter.typeError(
                errorId(5982),
                node.location,
                "Libraries cannot have fallback functions.",
            );
        if (function.state_mutability != .NonPayable and function.state_mutability != .Payable) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Fallback function must be payable or non-payable, but is \"{s}\".",
                .{stateMutabilityName(function.state_mutability)},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(4575), node.location, message);
        }
        if (ASTImplementation.effectiveVisibility(node) != .External)
            try self.reporter.typeError(
                errorId(1159),
                node.location,
                "Fallback function must be defined as \"external\".",
            );
        const parameters = function.callable.parameters.payload.parameter_list.parameters;
        const returns = if (function.callable.return_parameters) |list|
            list.payload.parameter_list.parameters
        else
            &[_]*AST.Node{};
        if (parameters.len != 0 or returns.len != 0) {
            const valid = parameters.len == 1 and returns.len == 1 and
                TypeBehavior.equals(
                    (try variableAnnotation(self.tree, parameters[0])).type_ref orelse
                        return error.InvalidAst,
                    self.type_provider.bytesCalldata(),
                ) and
                TypeBehavior.equals(
                    (try variableAnnotation(self.tree, returns[0])).type_ref orelse
                        return error.InvalidAst,
                    self.type_provider.bytesMemory(),
                );
            if (!valid)
                try self.reporter.typeError(
                    errorId(5570),
                    if (function.callable.return_parameters) |list| list.location else node.location,
                    "Fallback function either has to have the signature \"fallback()\" or \"fallback(bytes calldata) returns (bytes memory)\".",
                );
        }
    }

    fn checkConstructor(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const function = node.payload.function_definition;
        if (function.callable.overrides != null)
            try self.reporter.typeError(
                errorId(1209),
                node.location,
                "Constructors cannot override.",
            );
        if (function.callable.return_parameters) |returns|
            if (returns.payload.parameter_list.parameters.len != 0)
                try self.reporter.typeError(
                    errorId(9712),
                    returns.location,
                    "Non-empty \"returns\" directive for constructor.",
                );
        if (function.state_mutability != .NonPayable and function.state_mutability != .Payable) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Constructor must be payable or non-payable, but is \"{s}\".",
                .{stateMutabilityName(function.state_mutability)},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(1558), node.location, message);
        }
        const visibility = function.callable.declaration.visibility;
        if (visibility != .Default) {
            const contract = self.current_contract orelse return error.InvalidAst;
            const abstract = contract.payload.contract_definition.abstract;
            if (visibility != .Public and visibility != .Internal) {
                try self.reporter.typeError(
                    errorId(9239),
                    node.location,
                    "Constructor cannot have visibility.",
                );
            } else if (visibility == .Public and abstract) {
                try self.reporter.declarationError(
                    errorId(8295),
                    node.location,
                    "Abstract contracts cannot have public constructors. Remove the \"public\" keyword to fix this.",
                );
            } else if (visibility == .Internal and !abstract) {
                try self.reporter.declarationError(
                    errorId(1845),
                    node.location,
                    "Non-abstract contracts cannot have internal constructors. Remove the \"internal\" keyword and make the contract abstract to fix this.",
                );
            } else {
                try self.reporter.warning(
                    errorId(2462),
                    node.location,
                    "Visibility for constructor is ignored. If you want the contract to be non-deployable, making it \"abstract\" is sufficient.",
                );
            }
        }
    }

    fn endModifierDefinition(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const modifier = node.payload.modifier_definition;
        if (self.current_contract) |contract| {
            if (modifier.callable.marked_virtual and
                contract.payload.contract_definition.contract_kind == .Library)
                try self.reporter.typeError(
                    errorId(3275),
                    node.location,
                    "Modifiers in a library cannot be virtual.",
                );
            if (contract.payload.contract_definition.contract_kind == .Interface)
                try self.reporter.typeError(
                    errorId(6408),
                    node.location,
                    "Modifiers cannot be defined or declared in interfaces.",
                );
        }
        if (!modifier.implemented() and !modifier.callable.marked_virtual)
            try self.reporter.typeError(
                errorId(8063),
                node.location,
                "Modifiers without implementation must be marked virtual.",
            );
    }

    fn visitModifierInvocation(
        self: *TypeChecker,
        node: *AST.Node,
        constructor_bases: AST.NodeList,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.modifier_invocation;
        const arguments = value.arguments orelse &.{};
        for (arguments) |argument| try self.checkExpression(argument, depth + 1);
        try self.checkNode(value.modifier_name, depth + 1);

        const declaration = try referencedDeclarationForName(self.tree, value.modifier_name);
        var parameters: ?AST.NodeList = null;
        switch (declaration.payload) {
            .modifier_definition => |modifier| {
                parameters = modifier.callable.parameters.payload.parameter_list.parameters;
                if (ASTImplementation.scope(declaration)) |modifier_contract|
                    if (modifier_contract.nodeKind() == .contract_definition)
                        if (self.current_contract) |current|
                            if (!(try contractHierarchyContains(
                                self.tree,
                                current,
                                modifier_contract,
                            )))
                                try self.reporter.typeError(
                                    errorId(9428),
                                    node.location,
                                    "Can only use modifiers defined in the current contract or in base contracts.",
                                );
                if ((try requiredLookupForName(self.tree, value.modifier_name)) == .Static and
                    !modifier.implemented())
                    try self.reporter.typeError(
                        errorId(1835),
                        node.location,
                        "Cannot call unimplemented modifier. The modifier has no implementation in the referenced contract. Refer to it by its unqualified name if you want to call the implementation from the most derived contract.",
                    );
            },
            .contract_definition => if (containsConstNode(constructor_bases, declaration)) {
                parameters = if (findConstructor(declaration)) |constructor|
                    constructor.payload.function_definition.callable.parameters.payload.parameter_list.parameters
                else
                    &.{};
            },
            else => {},
        }
        const expected_parameters = parameters orelse {
            try self.reporter.typeError(
                errorId(4659),
                node.location,
                "Referenced declaration is neither modifier nor base class.",
            );
            return;
        };
        if (arguments.len != expected_parameters.len) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Wrong argument count for modifier invocation: {d} arguments given but expected {d}.",
                .{ arguments.len, expected_parameters.len },
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(2973), node.location, message);
            return;
        }
        for (arguments, expected_parameters) |argument, parameter| {
            const actual = (try expressionAnnotation(self.tree, argument)).type_ref orelse
                return error.InvalidAst;
            const expected = (try variableAnnotation(self.tree, parameter)).type_ref orelse
                return error.InvalidAst;
            if (TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) continue;
            const actual_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, actual);
            defer self.allocator.free(actual_name);
            const expected_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, expected);
            defer self.allocator.free(expected_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Invalid type for argument in modifier invocation. Invalid implicit conversion from {s} to {s} requested.{s}{s}",
                .{
                    actual_name,
                    expected_name,
                    if (implicitConversionReason(actual, expected) != null) " " else "",
                    implicitConversionReason(actual, expected) orelse "",
                },
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(4649), argument.location, message);
        }
    }

    fn endEventDefinition(self: *TypeChecker, node: *AST.Node) CheckError!void {
        try self.checkErrorAndEventParameters(node, "event");
        var indexed: usize = 0;
        for (node.payload.event_definition.callable.parameters.payload.parameter_list.parameters) |parameter|
            indexed += @intFromBool(parameter.payload.variable_declaration.indexed);
        if (node.payload.event_definition.anonymous and indexed > 4)
            try self.reporter.typeError(
                errorId(8598),
                node.location,
                "More than 4 indexed arguments for anonymous event.",
            )
        else if (!node.payload.event_definition.anonymous and indexed > 3)
            try self.reporter.typeError(
                errorId(7249),
                node.location,
                "More than 3 indexed arguments for event.",
            );
    }

    fn endErrorDefinition(self: *TypeChecker, node: *AST.Node) CheckError!void {
        try self.checkErrorAndEventParameters(node, "error");
    }

    fn checkErrorAndEventParameters(
        self: *TypeChecker,
        node: *AST.Node,
        kind: []const u8,
    ) CheckError!void {
        const callable = callableData(node) orelse return error.InvalidAst;
        for (callable.parameters.payload.parameter_list.parameters) |parameter| {
            const type_ref = (try variableAnnotation(self.tree, parameter)).type_ref orelse
                return error.InvalidAst;
            if (containsNestedMapping(type_ref, 0)) {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Type containing a (nested) mapping is not allowed as {s} parameter type.",
                    .{kind},
                );
                defer self.allocator.free(message);
                try self.reporter.fatal(
                    errorId(3448),
                    .TypeError,
                    parameter.location,
                    null,
                    message,
                );
            }
            if ((try TypeBehavior.interfaceType(
                self.type_provider,
                type_ref,
                false,
            )) == null) {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Internal or recursive type is not allowed as {s} parameter type.",
                    .{kind},
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(3417), parameter.location, message);
            }
            if (!(try self.useAbiCoderV2()) and
                !typeSupportedByOldABIEncoder(type_ref, false))
                try self.reporter.typeError(
                    errorId(3061),
                    parameter.location,
                    "This type is only supported in ABI coder v2. Use \"pragma abicoder v2;\" to enable the feature.",
                );
        }
    }

    fn endFunctionTypeName(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const type_ref = (try typeNameAnnotation(self.tree, node)).type_ref orelse
            return error.InvalidAst;
        const function = type_ref.asFunction() orelse return error.InvalidAst;
        if (function.kind != .External) return;
        const value = node.payload.function_type_name;
        const lists = [_]*AST.Node{ value.parameter_types, value.return_types };
        for (lists) |list|
            for (list.payload.parameter_list.parameters) |parameter| {
                const parameter_type = (try variableAnnotation(
                    self.tree,
                    parameter,
                )).type_ref orelse return error.InvalidAst;
                if ((try TypeBehavior.interfaceType(
                    self.type_provider,
                    parameter_type,
                    false,
                )) == null)
                    try self.reporter.fatal(
                        errorId(2582),
                        .TypeError,
                        parameter.location,
                        null,
                        "Internal type cannot be used for external function type.",
                    );
            };
    }

    fn endUsingForDirective(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const value = node.payload.using_for_directive;
        if (value.global) {
            if (self.current_contract != null or value.type_name == null) {
                if (!self.reporter.hasErrors()) return error.InvalidAst;
                return;
            }
            const global_type = (try typeNameAnnotation(
                self.tree,
                value.type_name.?,
            )).type_ref orelse return error.InvalidAst;
            if (TypeBehavior.typeDefinition(global_type)) |definition| {
                if (ASTImplementation.scope(definition) != self.current_source_unit)
                    try self.reporter.typeError(
                        errorId(4117),
                        node.location,
                        "Can only use \"global\" with types defined in the same source unit at file level.",
                    );
            } else {
                try self.reporter.typeError(
                    errorId(8841),
                    node.location,
                    "Can only use \"global\" with user-defined types.",
                );
            }
        }
        if (!value.uses_braces) return;
        const type_name = value.type_name orelse {
            if (!self.reporter.hasErrors()) return error.InvalidAst;
            return;
        };
        const attached_type = (try typeNameAnnotation(self.tree, type_name)).type_ref orelse
            return error.InvalidAst;
        const normalized_attached = try self.type_provider.withLocationIfReference(
            .Storage,
            attached_type,
            false,
        );
        for (value.functions_and_operators) |entry| {
            const declaration = try referencedDeclarationForName(
                self.tree,
                entry.function_or_library,
            );
            if (declaration.nodeKind() != .function_definition) continue;
            const function = declaration.payload.function_definition;
            const parameters = function.callable.parameters.payload.parameter_list.parameters;
            const path_name = try identifierPathNameAlloc(
                self.allocator,
                entry.function_or_library,
            );
            defer self.allocator.free(path_name);
            if (parameters.len == 0) {
                const type_string = try TypeBehavior.toStringAlloc(
                    self.allocator,
                    normalized_attached,
                    true,
                );
                defer self.allocator.free(type_string);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "The function \"{s}\" does not have any parameters, and therefore cannot be attached to the type \"{s}\".",
                    .{ path_name, type_string },
                );
                defer self.allocator.free(message);
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(self.allocator, "Function defined here:", declaration.location);
                try self.reporter.fatal(
                    errorId(4731),
                    .TypeError,
                    entry.function_or_library.location,
                    &secondary,
                    message,
                );
            }

            if (ASTImplementation.effectiveVisibility(declaration) == .Private and
                ASTImplementation.scope(declaration) != self.current_contract)
            {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Function \"{s}\" is private and therefore cannot be attached to a type outside of the library where it is defined.",
                    .{path_name},
                );
                defer self.allocator.free(message);
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(self.allocator, "Function defined here:", declaration.location);
                try self.reporter.reportWithSecondary(
                    errorId(6772),
                    .TypeError,
                    entry.function_or_library.location,
                    &secondary,
                    message,
                );
            }

            const function_type = try ASTImplementation.functionTypeWhenAttached(
                self.type_provider,
                declaration,
            );
            const bound_function_type = try self.type_provider.withBoundFirstArgument(
                function_type,
            );
            const self_type = bound_function_type.asFunction().?.selfType() orelse
                return error.InvalidAst;
            const normalized_self = try self.type_provider.withLocationIfReference(
                .Storage,
                self_type,
                false,
            );
            if (!TypeBehavior.isImplicitlyConvertibleTo(normalized_attached, normalized_self) and
                entry.operator == null)
            {
                const attached_name = try TypeBehavior.toStringAlloc(
                    self.allocator,
                    attached_type,
                    true,
                );
                defer self.allocator.free(attached_name);
                const first_name = try TypeBehavior.humanReadableNameAlloc(
                    self.allocator,
                    self_type,
                );
                defer self.allocator.free(first_name);
                const reason = implicitConversionReason(normalized_attached, normalized_self);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "The function \"{s}\" cannot be attached to the type \"{s}\" because the type cannot be implicitly converted to the first argument of the function (\"{s}\"){s}{s}",
                    .{
                        path_name,
                        attached_name,
                        first_name,
                        if (reason != null) ": " else ".",
                        reason orelse "",
                    },
                );
                defer self.allocator.free(message);
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(self.allocator, "Function defined here:", declaration.location);
                try self.reporter.reportWithSecondary(
                    errorId(3100),
                    .TypeError,
                    entry.function_or_library.location,
                    &secondary,
                    message,
                );
            }
            if (entry.operator) |operator| try self.checkUserDefinedOperator(
                entry.function_or_library,
                declaration,
                attached_type,
                function_type,
                path_name,
                operator,
                value.global,
            );
        }
    }

    fn checkUserDefinedOperator(
        self: *TypeChecker,
        path: *const AST.Node,
        declaration: *AST.Node,
        attached_type: *const Types.Type,
        function_type: *const Types.Type,
        path_name: []const u8,
        operator: AST.Token,
        global: bool,
    ) CheckError!void {
        const function = declaration.payload.function_definition;
        if (!global)
            try self.reporter.typeError(
                errorId(3320),
                path.location,
                "Operators can only be defined in a global 'using for' directive.",
            );
        if (!function.free or function.state_mutability != .Pure) {
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            try secondary.append(
                self.allocator,
                "Function defined as non-pure here:",
                declaration.location,
            );
            try self.reporter.reportWithSecondary(
                errorId(7775),
                .TypeError,
                path.location,
                &secondary,
                "Only pure free functions can be used to define operators.",
            );
        }
        if (attached_type.category() != .UserDefinedValueType) {
            try self.reporter.typeError(
                errorId(5332),
                path.location,
                "Operators can only be implemented for user-defined value types.",
            );
            return;
        }
        const function_value = function_type.asFunction() orelse return error.InvalidAst;
        const parameter_types = function_value.parameter_types;
        const parameter_count = parameter_types.len;
        const binary_only = TokenModule.isBinaryOp(operator) and !TokenModule.isUnaryOp(operator);
        const unary_only = TokenModule.isUnaryOp(operator) and !TokenModule.isBinaryOp(operator);
        const identical_first_two = parameter_count < 2 or
            TypeBehavior.equals(parameter_types[0], parameter_types[1]);
        const first_matches = parameter_count == 0 or
            TypeBehavior.equals(attached_type, parameter_types[0]);
        const canonical_name = try TypeBehavior.canonicalNameAlloc(
            self.allocator,
            attached_type,
        );
        defer self.allocator.free(canonical_name);
        const wrong_parameters: ?[]u8 = if (binary_only and
            (parameter_count != 2 or !identical_first_two))
            try std.fmt.allocPrint(
                self.allocator,
                "two parameters of type {s} and the same data location",
                .{canonical_name},
            )
        else if (unary_only and (parameter_count != 1 or !first_matches))
            try std.fmt.allocPrint(
                self.allocator,
                "exactly one parameter of type {s}",
                .{canonical_name},
            )
        else if (parameter_count >= 3 or !first_matches or !identical_first_two)
            try std.fmt.allocPrint(
                self.allocator,
                "one or two parameters of type {s} and the same data location",
                .{canonical_name},
            )
        else
            null;
        defer if (wrong_parameters) |message| self.allocator.free(message);
        if (wrong_parameters) |expected| {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Wrong parameters in operator definition. The function \"{s}\" needs to have {s} to be used for the operator {s}.",
                .{ path_name, expected, TokenModule.friendlyName(operator) },
            );
            defer self.allocator.free(message);
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            try secondary.append(
                self.allocator,
                "Function was used to implement an operator here:",
                path.location,
            );
            try self.reporter.reportWithSecondary(
                errorId(1884),
                .TypeError,
                function.callable.parameters.location,
                &secondary,
                message,
            );
        }

        const return_types = function_value.return_parameter_types;
        const wrong_returns: ?[]u8 = if (!TokenModule.isCompareOp(operator) and operator != .Not)
            if (return_types.len != 1 or !TypeBehavior.equals(attached_type, return_types[0]))
                try std.fmt.allocPrint(
                    self.allocator,
                    "exactly one value of type {s}",
                    .{canonical_name},
                )
            else if (!TypeBehavior.equals(return_types[0], parameter_types[0]))
                try self.allocator.dupe(
                    u8,
                    "a value of the same type and data location as its parameters",
                )
            else
                null
        else if (return_types.len != 1 or
            !TypeBehavior.equals(return_types[0], self.type_provider.boolean()))
            try self.allocator.dupe(u8, "exactly one value of type bool")
        else
            null;
        defer if (wrong_returns) |message| self.allocator.free(message);
        if (wrong_returns) |expected| {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Wrong return parameters in operator definition. The function \"{s}\" needs to return {s} to be used for the operator {s}.",
                .{ path_name, expected, TokenModule.friendlyName(operator) },
            );
            defer self.allocator.free(message);
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            try secondary.append(
                self.allocator,
                "Function was used to implement an operator here:",
                path.location,
            );
            try self.reporter.reportWithSecondary(
                errorId(7743),
                .TypeError,
                if (function.callable.return_parameters) |list| list.location else declaration.location,
                &secondary,
                message,
            );
        }

        if (parameter_count != 1 and parameter_count != 2) {
            if (!self.reporter.hasErrors()) return error.InvalidAst;
            return;
        }
        const scope = self.current_contract orelse self.current_source_unit orelse
            return error.InvalidAst;
        const definitions = try TypeBehavior.operatorDefinitionsWithCompatibilityIdsAlloc(
            self.type_provider,
            self.allocator,
            self.compatibility_ids,
            attached_type,
            operator,
            scope,
            parameter_count == 1,
        );
        defer self.allocator.free(definitions);
        if (definitions.len >= 2) {
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            for (definitions) |definition|
                if (definition != declaration)
                    try secondary.append(
                        self.allocator,
                        "Conflicting definition:",
                        definition.location,
                    );
            const message = try std.fmt.allocPrint(
                self.allocator,
                "User-defined {s} operator {s} has more than one definition matching the operand type visible in the current scope.",
                .{
                    if (parameter_count == 1) "unary" else "binary",
                    TokenModule.friendlyName(operator),
                },
            );
            defer self.allocator.free(message);
            try self.reporter.reportWithSecondary(
                errorId(4705),
                .TypeError,
                path.location,
                &secondary,
                message,
            );
        }
    }

    fn findUserDefinedOperator(
        self: *TypeChecker,
        operator: AST.Token,
        operand_types: []const *const Types.Type,
    ) CheckError!?*const AST.Node {
        if (operand_types.len == 0 or operand_types.len > 2 or
            operand_types[0].category() != .UserDefinedValueType) return null;
        const scope = self.current_contract orelse self.current_source_unit orelse return null;
        const matches = try TypeBehavior.operatorDefinitionsWithCompatibilityIdsAlloc(
            self.type_provider,
            self.allocator,
            self.compatibility_ids,
            operand_types[0],
            operator,
            scope,
            operand_types.len == 1,
        );
        defer self.allocator.free(matches);
        if (matches.len == 0) return null;
        if (matches.len != 1 and !self.reporter.hasErrors()) return error.InvalidAst;
        return matches[0];
    }

    fn checkExpression(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;
        switch (node.payload) {
            .literal => try self.endLiteral(node),
            .identifier => try self.visitIdentifier(node),
            .binary_operation => |value| {
                try self.checkExpression(value.left, depth + 1);
                try self.checkExpression(value.right, depth + 1);
                try self.endBinaryOperation(node);
            },
            .unary_operation => |value| {
                const annotation = try expressionAnnotation(self.tree, node);
                const modifying = value.operator == .Inc or
                    value.operator == .Dec or
                    value.operator == .Delete;
                if (modifying) {
                    try self.requireLValue(value.sub_expression, depth + 1);
                } else {
                    try self.checkExpression(value.sub_expression, depth + 1);
                }
                try self.endUnaryOperation(node, annotation, modifying);
            },
            .assignment => try self.visitAssignment(node, depth),
            .tuple_expression => try self.visitTupleExpression(node, depth),
            .conditional => try self.visitConditional(node, depth),
            .function_call => try self.visitFunctionCall(node, depth),
            .function_call_options => try self.visitFunctionCallOptions(node, depth),
            .new_expression => try self.endNewExpression(node),
            .member_access => try self.visitMemberAccess(node, depth),
            .index_access => try self.visitIndexAccess(node, depth),
            .index_range_access => try self.visitIndexRangeAccess(node, depth),
            .elementary_type_name_expression => try self.endElementaryTypeNameExpression(node),
            else => try self.unsupportedExpression(node),
        }
    }

    fn endVariableDeclaration(
        self: *TypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const value = node.payload.variable_declaration;
        const variable_type = (try variableAnnotation(
            self.tree,
            node,
        )).type_ref orelse return error.InvalidAst;
        if (value.value) |expression| {
            if (ASTImplementation.isStateVariable(node) and
                containsNestedMapping(variable_type, 0))
            {
                try self.reporter.typeError(
                    errorId(6280),
                    node.location,
                    "Types in storage containing (nested) mappings cannot be assigned to.",
                );
            } else {
                _ = try self.expectTypeAlready(expression, variable_type);
            }
        }
        if (value.mutability == .Constant) {
            if (value.value == null) {
                try self.reporter.typeError(
                    errorId(4266),
                    node.location,
                    "Uninitialized \"constant\" variable.",
                );
            } else {
                const expression = try expressionAnnotation(self.tree, value.value.?);
                if (!(try expression.is_pure.get()).*)
                    try self.reporter.typeError(
                        errorId(8349),
                        value.value.?.location,
                        "Initial value for constant variable has to be compile-time constant.",
                    );
            }
        } else if (value.mutability == .Immutable and
            !TypeBehavior.isValueType(variable_type))
            try self.reporter.typeError(
                errorId(6377),
                node.location,
                "Immutable variables cannot have a non-value type.",
            );
        if (value.mutability == .Immutable and variable_type.asFunction() != null and
            variable_type.asFunction().?.kind == .External)
            try self.reporter.typeError(
                errorId(3366),
                node.location,
                "Immutable variables of external function type are not yet supported.",
            );

        if (!ASTImplementation.isStateVariable(node) and
            (value.reference_location == .CallData or value.reference_location == .Memory) and
            containsNestedMapping(variable_type, 0))
        {
            const type_name = try TypeBehavior.humanReadableNameAlloc(
                self.allocator,
                variable_type,
            );
            defer self.allocator.free(type_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Type {s} is only valid in storage because it contains a (nested) mapping.",
                .{type_name},
            );
            defer self.allocator.free(message);
            try self.reporter.fatal(errorId(4061), .TypeError, node.location, null, message);
        }
        if (ASTImplementation.isStateVariable(node) and ASTImplementation.isPublic(node)) {
            const getter_type = (try self.publicGetterType(node)).asFunction() orelse
                return error.InvalidAst;
            if (!(try self.useAbiCoderV2())) {
                var unsupported: std.ArrayList([]const u8) = .empty;
                defer {
                    for (unsupported.items) |name| self.allocator.free(name);
                    unsupported.deinit(self.allocator);
                }
                for (getter_type.parameter_types) |parameter_type|
                    if (!typeSupportedByOldABIEncoder(parameter_type, false))
                        try unsupported.append(
                            self.allocator,
                            try TypeBehavior.humanReadableNameAlloc(
                                self.allocator,
                                parameter_type,
                            ),
                        );
                for (getter_type.return_parameter_types) |return_type|
                    if (!typeSupportedByOldABIEncoder(return_type, false))
                        try unsupported.append(
                            self.allocator,
                            try TypeBehavior.humanReadableNameAlloc(
                                self.allocator,
                                return_type,
                            ),
                        );
                if (unsupported.items.len != 0) {
                    const names = try std.mem.join(self.allocator, ", ", unsupported.items);
                    defer self.allocator.free(names);
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "The following types are only supported for getters in ABI coder v2: {s}. Either remove \"public\" or use \"pragma abicoder v2;\" to enable the feature.",
                        .{names},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.typeError(errorId(2763), node.location, message);
                }
            }

            var interface_valid = true;
            for (getter_type.parameter_types) |parameter_type|
                interface_valid = interface_valid and
                    (try TypeBehavior.interfaceType(
                        self.type_provider,
                        parameter_type,
                        false,
                    )) != null;
            for (getter_type.return_parameter_types) |return_type|
                interface_valid = interface_valid and
                    (try TypeBehavior.interfaceType(
                        self.type_provider,
                        return_type,
                        false,
                    )) != null;
            if (!interface_valid) {
                if (getter_type.parameter_types.len == 0 and
                    getter_type.return_parameter_types.len == 0)
                    try self.reporter.typeError(
                        errorId(5359),
                        node.location,
                        "The struct has all its members omitted, therefore the getter cannot return any values.",
                    )
                else
                    try self.reporter.typeError(
                        errorId(6744),
                        node.location,
                        "Internal or recursive type is not allowed for public state variables.",
                    );
            } else if (getter_type.parameter_types.len == 0 and
                getter_type.return_parameter_types.len == 0)
                try self.reporter.typeError(
                    errorId(5359),
                    node.location,
                    "The struct has all its members omitted, therefore the getter cannot return any values.",
                );
        }

        if (ASTImplementation.scope(node)) |scope|
            if (scope.nodeKind() == .struct_definition) return;

        if (variable_type.asReference()) |reference| {
            var checked_location = reference.location;
            var valid = try TypeBehavior.validForLocation(
                self.type_provider,
                variable_type,
                reference.location,
            );
            if (valid) {
                const library_storage_parameter =
                    ASTImplementation.isLibraryFunctionParameter(node) and
                    reference.location == .Storage;
                const abstract_constructor_parameter =
                    ASTImplementation.isConstructorParameter(node) and
                    self.current_contract != null and
                    self.current_contract.?.payload.contract_definition.abstract;
                const calldata_check_required = !abstract_constructor_parameter and
                    (ASTImplementation.isConstructorParameter(node) or
                        ASTImplementation.isPublicCallableParameter(node)) and
                    !library_storage_parameter;
                if (calldata_check_required) {
                    if ((try TypeBehavior.interfaceType(
                        self.type_provider,
                        variable_type,
                        false,
                    )) != null) {
                        checked_location = .CallData;
                        valid = try TypeBehavior.validForLocation(
                            self.type_provider,
                            variable_type,
                            .CallData,
                        );
                    }
                }
            }
            if (!valid)
                try self.reporter.typeError(
                    errorId(1534),
                    node.location,
                    validForLocationFailureReason(checked_location),
                );
        }
    }

    fn endReturn(
        self: *TypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const value = node.payload.return_statement;
        const annotation = try returnAnnotation(self.tree, node);
        const parameters_node = annotation.function_return_parameters;
        if (value.expression == null) {
            if (parameters_node) |parameters|
                if (parameters.payload.parameter_list.parameters.len != 0)
                    try self.reporter.typeError(
                        errorId(6777),
                        node.location,
                        "Return arguments required.",
                    );
            return;
        }
        const expression = value.expression.?;
        if (parameters_node == null) {
            try self.reporter.typeError(
                errorId(7552),
                node.location,
                "Return arguments not allowed.",
            );
            return;
        }
        const parameters = parameters_node.?.payload.parameter_list.parameters;
        const actual = (try expressionAnnotation(self.tree, expression)).type_ref orelse
            return error.InvalidAst;

        if (actual.asTuple()) |tuple| {
            if (tuple.components.len != parameters.len) {
                try self.reporter.typeError(
                    errorId(5132),
                    node.location,
                    "Different number of arguments in return statement than in returns declaration.",
                );
                return;
            }
            const expected_types = try self.allocator.alloc(*const Types.Type, parameters.len);
            defer self.allocator.free(expected_types);
            for (parameters, 0..) |parameter, index|
                expected_types[index] = (try variableAnnotation(
                    self.tree,
                    parameter,
                )).type_ref orelse return error.InvalidAst;
            const expected = try self.type_provider.tupleOfTypes(expected_types);
            if (!TypeBehavior.isImplicitlyConvertibleTo(actual, expected))
                try self.reportReturnConversionError(
                    errorId(5992),
                    expression,
                    actual,
                    expected,
                    false,
                );
        } else if (parameters.len != 1) {
            try self.reporter.typeError(
                errorId(8863),
                node.location,
                "Different number of arguments in return statement than in returns declaration.",
            );
        } else {
            const expected = (try variableAnnotation(
                self.tree,
                parameters[0],
            )).type_ref orelse return error.InvalidAst;
            if (!TypeBehavior.isImplicitlyConvertibleTo(actual, expected))
                try self.reportReturnConversionError(
                    errorId(6359),
                    expression,
                    actual,
                    expected,
                    true,
                );
        }
    }

    fn visitIfStatement(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.if_statement;
        try self.checkExpression(value.condition, depth + 1);
        _ = try self.expectTypeAlready(value.condition, self.type_provider.boolean());
        try self.checkNode(value.true_body, depth + 1);
        if (value.false_body) |false_body| try self.checkNode(false_body, depth + 1);
    }

    fn visitWhileStatement(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.while_statement;
        try self.checkExpression(value.condition, depth + 1);
        _ = try self.expectTypeAlready(value.condition, self.type_provider.boolean());
        try self.checkNode(value.body, depth + 1);
    }

    fn visitForStatement(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.for_statement;
        if (value.initialization_expression) |initialization|
            try self.checkNode(initialization, depth + 1);
        if (value.condition) |condition| {
            try self.checkExpression(condition, depth + 1);
            _ = try self.expectTypeAlready(condition, self.type_provider.boolean());
        }
        if (value.loop_expression) |loop_expression|
            try self.checkNode(loop_expression, depth + 1);
        try self.checkNode(value.body, depth + 1);
    }

    fn endTryStatement(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const value = node.payload.try_statement;
        if (value.external_call.nodeKind() != .function_call) {
            try self.reporter.typeError(
                errorId(5347),
                value.external_call.location,
                "Try can only be used with external function calls and contract creation calls.",
            );
            return;
        }
        const call = value.external_call;
        const call_value = call.payload.function_call;
        const call_annotation = try functionCallAnnotation(self.tree, call);
        if ((try call_annotation.kind.get()).* != .FunctionCall) {
            try self.reporter.typeError(
                errorId(5347),
                value.external_call.location,
                "Try can only be used with external function calls and contract creation calls.",
            );
            return;
        }
        const function_type = (try expressionAnnotation(
            self.tree,
            call_value.expression,
        )).type_ref.?.asFunction() orelse {
            try self.reporter.typeError(
                errorId(2536),
                value.external_call.location,
                "Try can only be used with external function calls and contract creation calls.",
            );
            return;
        };
        switch (function_type.kind) {
            .External, .Creation, .DelegateCall => {},
            else => {
                try self.reporter.typeError(
                    errorId(2536),
                    value.external_call.location,
                    "Try can only be used with external function calls and contract creation calls.",
                );
                return;
            },
        }
        call_annotation.try_call = true;
        if (value.clauses.len == 0) return error.InvalidAst;
        const success = value.clauses[0].payload.try_catch_clause;
        if (success.parameters) |parameter_list| {
            const parameters = parameter_list.payload.parameter_list.parameters;
            const return_types = if (self.evm_version.supportsReturndata())
                function_type.return_parameter_types
            else
                try TypeBehavior.returnParameterTypesWithoutDynamicTypesAlloc(
                    self.type_provider,
                    self.allocator,
                    function_type.*,
                );
            defer if (!self.evm_version.supportsReturndata()) self.allocator.free(return_types);
            if (parameters.len != return_types.len) {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Function returns {d} values, but returns clause has {d} variables.",
                    .{ function_type.return_parameter_types.len, parameters.len },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(2800), value.clauses[0].location, message);
            }
            const count = @min(parameters.len, return_types.len);
            for (parameters[0..count], return_types[0..count]) |parameter, expected| {
                const actual = (try variableAnnotation(self.tree, parameter)).type_ref orelse
                    return error.InvalidAst;
                if (TypeBehavior.equals(actual, expected)) continue;
                const expected_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, expected);
                defer self.allocator.free(expected_name);
                const actual_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, actual);
                defer self.allocator.free(actual_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Invalid type, expected {s} but got {s}.",
                    .{ expected_name, actual_name },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(6509), parameter.location, message);
            }
        }

        var error_clause: ?*AST.Node = null;
        var panic_clause: ?*AST.Node = null;
        var low_level_clause: ?*AST.Node = null;
        for (value.clauses[1..]) |clause_node| {
            const clause = clause_node.payload.try_catch_clause;
            if (clause.error_name.len == 0) {
                if (low_level_clause) |first|
                    try self.reportDuplicateCatch(
                        errorId(5320),
                        clause_node,
                        first,
                        "This try statement already has a low-level catch clause.",
                    );
                low_level_clause = clause_node;
                if (clause.parameters) |parameters_node| {
                    const parameters = parameters_node.payload.parameter_list.parameters;
                    if (parameters.len != 0) {
                        const valid = parameters.len == 1 and TypeBehavior.equals(
                            (try variableAnnotation(self.tree, parameters[0])).type_ref orelse
                                return error.InvalidAst,
                            self.type_provider.bytesMemory(),
                        );
                        if (!valid)
                            try self.reporter.typeError(
                                errorId(6231),
                                clause_node.location,
                                "Expected `catch (bytes memory ...) { ... }` or `catch { ... }`.",
                            );
                        if (!self.evm_version.supportsReturndata()) {
                            const message = try std.fmt.allocPrint(
                                self.allocator,
                                "This catch clause type cannot be used on the selected EVM version ({s}). You need at least a Byzantium-compatible EVM or use `catch {{ ... }}`.",
                                .{self.evm_version.name()},
                            );
                            defer self.allocator.free(message);
                            try self.reporter.typeError(errorId(9908), clause_node.location, message);
                        }
                    }
                }
            } else if (std.mem.eql(u8, clause.error_name, "Error")) {
                if (!self.evm_version.supportsReturndata())
                    try self.reportCatchReturndataVersionError(clause_node);
                if (error_clause) |first|
                    try self.reportDuplicateCatch(
                        errorId(1036),
                        clause_node,
                        first,
                        "This try statement already has an \"Error\" catch clause.",
                    );
                error_clause = clause_node;
                if (!try self.catchHasSingleType(clause, self.type_provider.stringMemory()))
                    try self.reporter.typeError(
                        errorId(2943),
                        clause_node.location,
                        "Expected `catch Error(string memory ...) { ... }`.",
                    );
            } else if (std.mem.eql(u8, clause.error_name, "Panic")) {
                if (!self.evm_version.supportsReturndata())
                    try self.reportCatchReturndataVersionError(clause_node);
                if (panic_clause) |first|
                    try self.reportDuplicateCatch(
                        errorId(6732),
                        clause_node,
                        first,
                        "This try statement already has a \"Panic\" catch clause.",
                    );
                panic_clause = clause_node;
                if (!try self.catchHasSingleType(clause, self.type_provider.uint256()))
                    try self.reporter.typeError(
                        errorId(1271),
                        clause_node.location,
                        "Expected `catch Panic(uint ...) { ... }`.",
                    );
            } else {
                try self.reporter.typeError(
                    errorId(3542),
                    clause_node.location,
                    "Invalid catch clause name. Expected either `catch (...)`, `catch Error(...)`, or `catch Panic(...)`.",
                );
            }
        }
    }

    fn reportCatchReturndataVersionError(
        self: *TypeChecker,
        clause: *const AST.Node,
    ) CheckError!void {
        const message = try std.fmt.allocPrint(
            self.allocator,
            "This catch clause type cannot be used on the selected EVM version ({s}). You need at least a Byzantium-compatible EVM or use `catch {{ ... }}`.",
            .{self.evm_version.name()},
        );
        defer self.allocator.free(message);
        try self.reporter.typeError(errorId(1812), clause.location, message);
    }

    fn endInlineAssembly(self: *TypeChecker, node: *AST.Node) CheckError!void {
        if (node.nodeKind() != .inline_assembly) return error.InvalidAst;
        const assembly = node.payload.inline_assembly;
        const operations = assembly.operations orelse return error.InvalidAst;
        const annotation = try inlineAssemblyAnnotation(self.tree, node);
        if (annotation.analysis_info != null) return error.InvalidAst;
        const analysis_info = try annotation.createAnalysisInfo(self.tree);

        var resolver_context: InlineAssemblyResolverContext = .{
            .checker = self,
            .annotation = annotation,
        };
        var analyzer = YulAsmAnalysis.AsmAnalyzer.init(
            self.allocator,
            analysis_info,
            self.reporter,
            operations.dialect().*,
            .{
                .context = &resolver_context,
                .resolve = InlineAssemblyResolverContext.resolve,
            },
            .{},
            .{},
        );
        defer analyzer.deinit();
        _ = analyzer.analyze(operations.root()) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.FatalDiagnostic => return error.FatalDiagnostic,
            else => return error.InvalidAst,
        };
        if (resolver_context.failure) |failure| return failure;
        try assignOnce(
            &annotation.has_memory_effects,
            resolver_context.lvalue_access_to_memory_variable or
                analyzer.sideEffects().memory != .none,
        );
    }

    fn catchHasSingleType(
        self: *TypeChecker,
        clause: AST.TryCatchClause,
        expected: *const Types.Type,
    ) CheckError!bool {
        const parameters_node = clause.parameters orelse return false;
        const parameters = parameters_node.payload.parameter_list.parameters;
        if (parameters.len != 1) return false;
        const actual = (try variableAnnotation(self.tree, parameters[0])).type_ref orelse
            return error.InvalidAst;
        return TypeBehavior.equals(actual, expected);
    }

    fn reportDuplicateCatch(
        self: *TypeChecker,
        id: Diagnostics.ErrorId,
        duplicate: *const AST.Node,
        first: *const AST.Node,
        message: []const u8,
    ) CheckError!void {
        var secondary: Diagnostics.SecondarySourceLocation = .{};
        defer secondary.deinit(self.allocator);
        try secondary.append(self.allocator, "The first clause is here:", first.location);
        try self.reporter.reportWithSecondary(
            id,
            .TypeError,
            duplicate.location,
            &secondary,
            message,
        );
    }

    fn endEmitStatement(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const event_call = node.payload.emit_statement.event_call;
        if (event_call.nodeKind() != .function_call) {
            try self.reporter.typeError(
                errorId(9292),
                event_call.location,
                "Expression has to be an event invocation.",
            );
            return;
        }
        const expression = event_call.payload.function_call.expression;
        const type_ref = (try expressionAnnotation(self.tree, expression)).type_ref orelse
            return error.InvalidAst;
        const function = type_ref.asFunction();
        if (function == null or function.?.kind != .Event)
            try self.reporter.typeError(
                errorId(9292),
                expression.location,
                "Expression has to be an event invocation.",
            );
    }

    fn endRevertStatement(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const error_call = node.payload.revert_statement.error_call;
        if (error_call.nodeKind() != .function_call) {
            try self.reporter.typeError(
                errorId(1885),
                error_call.location,
                "Expression has to be an error.",
            );
            return;
        }
        const expression = error_call.payload.function_call.expression;
        const type_ref = (try expressionAnnotation(self.tree, expression)).type_ref orelse
            return error.InvalidAst;
        const function = type_ref.asFunction();
        if (function == null or function.?.kind != .Error)
            try self.reporter.typeError(
                errorId(1885),
                expression.location,
                "Expression has to be an error.",
            );
    }

    fn visitVariableDeclarationStatement(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.variable_declaration_statement;
        if (value.initial_value == null) {
            if (value.declarations.len == 1 and value.declarations[0] != null) {
                const declaration = value.declarations[0].?;
                const type_ref = (try variableAnnotation(self.tree, declaration)).type_ref orelse
                    return error.InvalidAst;
                if (type_ref.category() == .Mapping)
                    try self.reporter.typeError(
                        errorId(4182),
                        declaration.location,
                        "Uninitialized mapping. Mappings cannot be created dynamically, you have to assign them from a state variable.",
                    );
                try self.checkNode(declaration, depth + 1);
            } else if (!self.reporter.hasErrors()) {
                return error.InvalidAst;
            }
            return;
        }
        const initial = value.initial_value.?;
        try self.checkExpression(initial, depth + 1);
        const initial_type = (try expressionAnnotation(self.tree, initial)).type_ref orelse
            return error.InvalidAst;
        var component_types: std.ArrayList(?*const Types.Type) = .empty;
        defer component_types.deinit(self.allocator);
        if (initial_type.asTuple()) |tuple|
            try component_types.appendSlice(self.allocator, tuple.components)
        else
            try component_types.append(self.allocator, initial_type);
        if (component_types.items.len != value.declarations.len) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Different number of components on the left hand side ({d}) than on the right hand side ({d}).",
                .{ value.declarations.len, component_types.items.len },
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(7364), node.location, message);
        }
        const count = @min(component_types.items.len, value.declarations.len);
        for (value.declarations[0..count], component_types.items[0..count]) |maybe_declaration, maybe_actual| {
            const declaration = maybe_declaration orelse continue;
            const actual = maybe_actual orelse continue;
            const expected = (try variableAnnotation(self.tree, declaration)).type_ref orelse
                return error.InvalidAst;
            try self.checkNode(declaration, depth + 1);
            if (TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) continue;
            const actual_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, actual);
            defer self.allocator.free(actual_name);
            const expected_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, expected);
            defer self.allocator.free(expected_name);
            const base_message = try std.fmt.allocPrint(
                self.allocator,
                "Type {s} is not implicitly convertible to expected type {s}",
                .{ actual_name, expected_name },
            );
            defer self.allocator.free(base_message);
            if (actual.category() == .RationalNumber) {
                const rational = actual.payload.RationalNumber;
                const mobile = try TypeBehavior.mobileType(self.type_provider, actual);
                if (rational.denominator.compareUnsigned(1) != .eq and mobile != null) {
                    if (TypeBehavior.equals(expected, mobile.?)) {
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "{s}, but it can be explicitly converted.",
                            .{base_message},
                        );
                        defer self.allocator.free(message);
                        try self.reporter.typeError(errorId(5107), node.location, message);
                    } else {
                        const mobile_name = try TypeBehavior.humanReadableNameAlloc(
                            self.allocator,
                            mobile.?,
                        );
                        defer self.allocator.free(mobile_name);
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "{s}. Try converting to type {s} or use an explicit conversion.",
                            .{ base_message, mobile_name },
                        );
                        defer self.allocator.free(message);
                        try self.reporter.typeError(errorId(4486), node.location, message);
                    }
                    continue;
                }
            }
            const reason = implicitConversionReason(actual, expected);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "{s}.{s}{s}",
                .{
                    base_message,
                    if (reason != null) " " else "",
                    reason orelse "",
                },
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(9574), node.location, message);
        }
    }

    fn endExpressionStatement(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const expression = node.payload.expression_statement.expression;
        const expression_type = (try expressionAnnotation(self.tree, expression)).type_ref orelse
            return error.InvalidAst;
        if (expression_type.category() == .RationalNumber and
            (try TypeBehavior.mobileType(self.type_provider, expression_type)) == null)
            try self.reporter.typeError(
                errorId(3757),
                expression.location,
                "Invalid rational number.",
            );
        if (expression.nodeKind() != .function_call) return;
        const callee = expression.payload.function_call.expression;
        const type_ref = (try expressionAnnotation(self.tree, callee)).type_ref orelse
            return error.InvalidAst;
        const function = type_ref.asFunction() orelse return;
        switch (function.kind) {
            .BareCall, .BareCallCode, .BareDelegateCall, .BareStaticCall => try self.reporter.warning(
                errorId(9302),
                node.location,
                "Return value of low-level calls not used.",
            ),
            .Send => try self.reporter.warning(
                errorId(5878),
                node.location,
                "Failure condition of 'send' ignored. Consider using 'transfer' instead.",
            ),
            else => {},
        }
    }

    fn reportReturnConversionError(
        self: *TypeChecker,
        id: Diagnostics.ErrorId,
        expression: *const AST.Node,
        actual: *const Types.Type,
        expected: *const Types.Type,
        first_return_variable: bool,
    ) CheckError!void {
        const actual_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, actual);
        defer self.allocator.free(actual_name);
        const expected_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, expected);
        defer self.allocator.free(expected_name);
        const message = if (first_return_variable)
            try std.fmt.allocPrint(
                self.allocator,
                "Return argument type {s} is not implicitly convertible to expected type (type of first return variable) {s}.",
                .{ actual_name, expected_name },
            )
        else
            try std.fmt.allocPrint(
                self.allocator,
                "Return argument type {s} is not implicitly convertible to expected type {s}.",
                .{ actual_name, expected_name },
            );
        defer self.allocator.free(message);
        try self.reporter.typeError(id, expression.location, message);
    }

    fn endLiteral(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const literal = node.payload.literal;
        const annotation = try expressionAnnotation(self.tree, node);
        if (ASTImplementation.literalLooksLikeAddress(literal)) {
            annotation.type_ref = self.type_provider.address();
            const cleaned = try ASTImplementation.literalValueWithoutUnderscoresAlloc(
                self.allocator,
                literal,
            );
            defer self.allocator.free(cleaned);
            var detail: ?[]u8 = null;
            defer if (detail) |message| self.allocator.free(message);
            if (cleaned.len != 42) {
                detail = try std.fmt.allocPrint(
                    self.allocator,
                    "This looks like an address but is not exactly 40 hex digits. It is {d} hex digits.",
                    .{cleaned.len -| 2},
                );
            } else if (!(try ASTImplementation.literalPassesAddressChecksum(
                self.allocator,
                literal,
            ))) {
                const checksummed = try ASTImplementation.literalChecksummedAddressAlloc(
                    self.allocator,
                    literal,
                );
                defer self.allocator.free(checksummed);
                detail = if (checksummed.len == 0)
                    try self.allocator.dupe(
                        u8,
                        "This looks like an address but has an invalid checksum.",
                    )
                else
                    try std.fmt.allocPrint(
                        self.allocator,
                        "This looks like an address but has an invalid checksum. Correct checksummed address: \"{s}\".",
                        .{checksummed},
                    );
            }
            if (detail) |message| {
                const full = try std.fmt.allocPrint(
                    self.allocator,
                    "{s} If this is not used as an address, please prepend '00'. For more information please see https://docs.soliditylang.org/en/develop/types.html#address-literals",
                    .{message},
                );
                defer self.allocator.free(full);
                try self.reporter.syntaxError(errorId(9429), node.location, full);
            }
        }
        if (ASTImplementation.literalIsHexNumber(literal) and
            literal.sub_denomination != .None)
            try self.reporter.fatal(
                errorId(5145),
                .TypeError,
                node.location,
                null,
                "Hexadecimal numbers cannot be used with unit denominations. You can use an expression of the form \"0x1234 * 1 days\" instead.",
            );
        if (literal.sub_denomination == .Year)
            try self.reporter.typeError(
                errorId(4820),
                node.location,
                "Using \"years\" as a unit denomination is deprecated.",
            );
        if (annotation.type_ref == null)
            annotation.type_ref = try self.type_provider.forLiteral(literal);
        if (annotation.type_ref == null)
            try self.reporter.fatal(
                errorId(2826),
                .TypeError,
                node.location,
                null,
                "Invalid literal value.",
            );
        try assignOnce(&annotation.is_pure, true);
        try assignOnce(&annotation.is_lvalue, false);
        try assignOnce(&annotation.is_constant, false);
    }

    fn visitIdentifier(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const annotation = try identifierAnnotation(self.tree, node);
        if (annotation.referenced_declaration == null) {
            annotation.overloaded_declarations.clearRetainingCapacity();
            for (annotation.candidate_declarations.items) |candidate| {
                if (try self.callableHasMissingType(candidate))
                    try self.reporter.fatal(
                        errorId(3893),
                        .DeclarationError,
                        node.location,
                        null,
                        "Function type can not be used in this context.",
                    );
                const candidate_type = try self.overloadFunctionType(candidate);
                const candidate_function = candidate_type.asFunction() orelse
                    return error.InvalidAst;
                var duplicate = false;
                for (annotation.overloaded_declarations.items) |existing| {
                    const existing_type = try self.overloadFunctionType(existing);
                    const existing_function = existing_type.asFunction() orelse
                        return error.InvalidAst;
                    if (TypeBehavior.functionHasEqualParameterTypes(
                        candidate_function.*,
                        existing_function.*,
                    )) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate)
                    try annotation.overloaded_declarations.append(
                        self.tree.allocator(),
                        candidate,
                    );
            }
            const declarations = annotation.overloaded_declarations.items;
            if (declarations.len == 1) {
                annotation.referenced_declaration = declarations[0];
            } else if (declarations.len == 0) {
                try self.reporter.fatal(
                    errorId(7593),
                    .TypeError,
                    node.location,
                    null,
                    "No candidates for overload resolution found.",
                );
            } else if (annotation.expression.arguments) |*arguments| {
                var matches: std.ArrayList(*const AST.Node) = .empty;
                defer matches.deinit(self.allocator);
                for (declarations) |candidate| {
                    if (try self.declarationCanTakeArguments(candidate, arguments))
                        try matches.append(self.allocator, candidate);
                }
                if (matches.items.len == 1) {
                    annotation.referenced_declaration = matches.items[0];
                } else {
                    var secondary: Diagnostics.SecondarySourceLocation = .{};
                    defer secondary.deinit(self.allocator);
                    for (declarations) |candidate|
                        try secondary.append(self.allocator, "Candidate:", candidate.location);
                    try self.reporter.fatal(
                        if (matches.items.len == 0) errorId(9322) else errorId(4487),
                        .TypeError,
                        node.location,
                        &secondary,
                        if (matches.items.len == 0)
                            "No matching declaration found after argument-dependent lookup."
                        else
                            "No unique declaration found after argument-dependent lookup.",
                    );
                }
            } else {
                var variables: std.ArrayList(*const AST.Node) = .empty;
                defer variables.deinit(self.allocator);
                for (declarations) |candidate|
                    if (candidate.nodeKind() == .variable_declaration)
                        try variables.append(self.allocator, candidate);
                if (variables.items.len == 1)
                    annotation.referenced_declaration = variables.items[0]
                else
                    try self.reporter.fatal(
                        if (variables.items.len == 0) errorId(2144) else errorId(7589),
                        .TypeError,
                        node.location,
                        null,
                        if (variables.items.len == 0)
                            "No matching declaration found after variable lookup."
                        else
                            "No unique declaration found after variable lookup.",
                    );
            }
        }
        const declaration = annotation.referenced_declaration orelse return error.InvalidAst;
        const type_ref = try self.declarationType(declaration);
        annotation.expression.type_ref = type_ref;
        const constant = declaration.nodeKind() == .variable_declaration and
            declaration.payload.variable_declaration.mutability == .Constant;
        try assignOnce(&annotation.expression.is_lvalue, declarationIsLValue(declaration));
        try assignOnce(
            &annotation.expression.is_pure,
            constant or isPureIdentifierDeclaration(declaration, type_ref),
        );
        try assignOnce(&annotation.expression.is_constant, constant);
        try assignLookup(&annotation.required_lookup, if (isCallableDeclaration(declaration))
            .Virtual
        else
            .Static);

        if (type_ref.asFunction()) |function_type| {
            const name = node.payload.identifier.name;
            if (std.mem.eql(u8, name, "sha3") and function_type.kind == .KECCAK256)
                try self.reporter.typeError(
                    errorId(3557),
                    node.location,
                    "\"sha3\" has been deprecated in favour of \"keccak256\".",
                )
            else if (std.mem.eql(u8, name, "suicide") and
                function_type.kind == .Selfdestruct)
                try self.reporter.typeError(
                    errorId(8050),
                    node.location,
                    "\"suicide\" has been deprecated in favour of \"selfdestruct\".",
                )
            else if (std.mem.eql(u8, name, "selfdestruct") and
                function_type.kind == .Selfdestruct)
                try self.reporter.warning(
                    errorId(5159),
                    node.location,
                    "\"selfdestruct\" has been deprecated. Note that, starting from the Cancun hard fork, the underlying opcode no longer deletes the code and data associated with an account and only transfers its Ether to the beneficiary, unless executed in the same transaction in which the contract was created (see EIP-6780). Any use in newly deployed contracts is strongly discouraged even if the new behavior is taken into account. Future changes to the EVM might further reduce the functionality of the opcode.",
                );
        }
        if (declaration.nodeKind() == .magic_variable_declaration and
            type_ref.category() == .Integer and
            std.mem.eql(u8, node.payload.identifier.name, "now"))
            try self.reporter.typeError(
                errorId(7359),
                node.location,
                "\"now\" has been deprecated. Use \"block.timestamp\" instead.",
            );
    }

    fn callableHasMissingType(
        self: *TypeChecker,
        declaration: *const AST.Node,
    ) CheckError!bool {
        const callable = callableData(declaration) orelse return false;
        for (callable.parameters.payload.parameter_list.parameters) |parameter|
            if ((try variableAnnotation(self.tree, parameter)).type_ref == null) return true;
        if (callable.return_parameters) |returns|
            for (returns.payload.parameter_list.parameters) |parameter|
                if ((try variableAnnotation(self.tree, parameter)).type_ref == null) return true;
        return false;
    }

    /// Mirrors C++ `cleanOverloadedDeclarations`: prefer the externally
    /// callable type when one exists, otherwise use the internal/event type.
    fn overloadFunctionType(
        self: *TypeChecker,
        declaration: *const AST.Node,
    ) CheckError!*const Types.Type {
        return switch (declaration.payload) {
            .function_definition => blk: {
                const visibility = ASTImplementation.effectiveVisibility(declaration) orelse
                    return error.InvalidAst;
                break :blk if (visibility == .Public or visibility == .External)
                    try self.contractMemberType(@constCast(declaration), true)
                else
                    try self.callableType(declaration, .Internal);
            },
            .event_definition => try self.callableType(declaration, .Event),
            .error_definition => try self.callableType(declaration, .Error),
            .variable_declaration => try self.contractMemberType(@constCast(declaration), true),
            .magic_variable_declaration => |value| @ptrCast(@alignCast(
                value.type_ref orelse return error.InvalidAst,
            )),
            else => error.InvalidAst,
        };
    }

    fn declarationType(
        self: *TypeChecker,
        declaration: *const AST.Node,
    ) CheckError!*const Types.Type {
        return switch (declaration.payload) {
            .variable_declaration => (try variableAnnotation(
                self.tree,
                @constCast(declaration),
            )).type_ref orelse return error.InvalidAst,
            .magic_variable_declaration => |value| @ptrCast(@alignCast(
                value.type_ref orelse return error.InvalidAst,
            )),
            .function_definition => try self.callableType(declaration, .Internal),
            .modifier_definition => |value| blk: {
                const parameters = value.callable.parameters.payload.parameter_list.parameters;
                const parameter_types = try self.allocator.alloc(*const Types.Type, parameters.len);
                defer self.allocator.free(parameter_types);
                for (parameters, parameter_types) |parameter, *target|
                    target.* = (try variableAnnotation(
                        self.tree,
                        parameter,
                    )).type_ref orelse return error.InvalidAst;
                break :blk try self.type_provider.modifier(parameter_types);
            },
            .event_definition => try self.callableType(declaration, .Event),
            .error_definition => try self.callableType(declaration, .Error),
            .contract_definition => try self.type_provider.typeType(
                try self.type_provider.contract(declaration, false),
            ),
            .struct_definition => try self.type_provider.typeType(
                try self.type_provider.structType(declaration, .Storage),
            ),
            .enum_definition => try self.type_provider.typeType(
                try self.type_provider.enumType(declaration),
            ),
            .enum_value => blk: {
                const enclosing = ASTImplementation.scope(declaration) orelse
                    return error.InvalidAst;
                break :blk try self.type_provider.enumType(enclosing);
            },
            .user_defined_value_type_definition => |value| blk: {
                const underlying = (try typeNameAnnotation(
                    self.tree,
                    value.underlying_type,
                )).type_ref;
                break :blk try self.type_provider.typeType(
                    try self.type_provider.userDefinedValueType(declaration, underlying),
                );
            },
            .import_directive => blk: {
                const annotation = ASTAnnotations.annotationConst(declaration) orelse
                    return error.InvalidAst;
                const source_unit = switch (annotation.*) {
                    .import => |value| value.source_unit,
                    else => null,
                } orelse return error.InvalidAst;
                break :blk try self.type_provider.module(source_unit);
            },
            else => return error.InvalidAst,
        };
    }

    fn callableType(
        self: *TypeChecker,
        declaration: *const AST.Node,
        kind: Types.FunctionKind,
    ) CheckError!*const Types.Type {
        return switch (declaration.payload) {
            .function_definition => self.type_provider.functionFromDefinition(
                declaration,
                kind,
            ),
            .event_definition => if (kind == .Event)
                self.type_provider.functionFromEvent(declaration)
            else
                error.InvalidAst,
            .error_definition => if (kind == .Error)
                self.type_provider.functionFromError(declaration)
            else
                error.InvalidAst,
            else => error.InvalidAst,
        };
    }

    const ParameterTypesAndNames = struct {
        types: []const *const Types.Type,
        names: []const []const u8,
    };

    fn parameterTypesAndNames(
        self: *TypeChecker,
        list: *const AST.Node,
    ) CheckError!ParameterTypesAndNames {
        if (list.nodeKind() != .parameter_list) return error.InvalidAst;
        const parameters = list.payload.parameter_list.parameters;
        const types = try self.allocator.alloc(*const Types.Type, parameters.len);
        errdefer self.allocator.free(types);
        const names = try self.allocator.alloc([]const u8, parameters.len);
        errdefer self.allocator.free(names);
        for (parameters, 0..) |parameter, index| {
            types[index] = (try variableAnnotation(
                self.tree,
                parameter,
            )).type_ref orelse return error.InvalidAst;
            names[index] = parameter.payload.variable_declaration.declaration.name;
        }
        return .{ .types = types, .names = names };
    }

    fn endBinaryOperation(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const value = node.payload.binary_operation;
        const left_annotation = try expressionAnnotation(self.tree, value.left);
        const right_annotation = try expressionAnnotation(self.tree, value.right);
        const left = left_annotation.type_ref orelse return error.InvalidAst;
        const right = right_annotation.type_ref orelse return error.InvalidAst;
        const operation_annotation = try binaryOperationAnnotation(self.tree, node);
        var result_type: *const Types.Type = if (TokenModule.isCompareOp(value.operator))
            self.type_provider.boolean()
        else
            left;
        const builtin_result = try TypeBehavior.binaryOperatorResult(
            self.type_provider,
            value.operator,
            left,
            right,
        );
        const user_function = try self.findUserDefinedOperator(
            value.operator,
            &.{ left, right },
        );
        if (builtin_result != null and user_function != null) return error.InvalidAst;
        var user_function_pure = true;
        if (user_function) |declaration| {
            operation_annotation.common_type = left;
            const function_type = try ASTImplementation.functionTypeWhenAttached(
                self.type_provider,
                declaration,
            );
            const function = function_type.asFunction() orelse return error.InvalidAst;
            user_function_pure = function.state_mutability == .Pure;
            if (function.parameter_types.len != 2 or
                !TypeBehavior.equals(left, function.parameter_types[0]))
                return error.InvalidAst;
            if (!TypeBehavior.equals(right, function.parameter_types[0])) {
                const parameter_name = try TypeBehavior.humanReadableNameAlloc(
                    self.allocator,
                    function.parameter_types[0],
                );
                defer self.allocator.free(parameter_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "The type of the second operand of this user-defined binary operator {s} does not match the type of the first operand, which is {s}.",
                    .{ TokenModule.friendlyName(value.operator), parameter_name },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(5653), node.location, message);
            }
            if (function.return_parameter_types.len != 0)
                result_type = function.return_parameter_types[0];
        } else {
            if (builtin_result) |present| {
                operation_annotation.common_type = present;
                result_type = if (TokenModule.isCompareOp(value.operator))
                    self.type_provider.boolean()
                else
                    present;
            } else {
                const left_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, left);
                defer self.allocator.free(left_name);
                const right_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, right);
                defer self.allocator.free(right_name);
                const failure_reason = try TypeBehavior.binaryOperatorFailureReason(
                    self.type_provider,
                    value.operator,
                    left,
                    right,
                );
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Built-in binary operator {s} cannot be applied to types {s} and {s}.{s}{s}{s}",
                    .{
                        TokenModule.friendlyName(value.operator),
                        left_name,
                        right_name,
                        if (failure_reason != null) " " else "",
                        failure_reason orelse "",
                        if (TypeBehavior.typeDefinition(left) != null and
                            isUserDefinableOperator(value.operator))
                            " No matching user-defined operator found."
                        else
                            "",
                    },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(2271), node.location, message);
                operation_annotation.common_type = left;
            }
        }
        operation_annotation.operation.expression.type_ref = result_type;
        try assignOnce(&operation_annotation.operation.user_defined_function, user_function);
        try assignOnce(
            &operation_annotation.operation.expression.is_pure,
            (try left_annotation.is_pure.get()).* and
                (try right_annotation.is_pure.get()).* and
                user_function_pure,
        );
        try assignOnce(&operation_annotation.operation.expression.is_lvalue, false);
        try assignOnce(&operation_annotation.operation.expression.is_constant, false);

        if ((value.operator == .Equal or value.operator == .NotEqual) and
            left.asFunction() != null and right.asFunction() != null and
            left.asFunction().?.kind == .Internal and right.asFunction().?.kind == .Internal)
            try self.reporter.warning(
                errorId(3075),
                node.location,
                "Comparison of internal function pointers can yield unexpected results in the legacy pipeline with the optimizer enabled, and will be disallowed entirely in the next breaking release.",
            );

        if ((value.operator == .Exp or value.operator == .SHL) and
            operation_annotation.common_type != null and
            operation_annotation.common_type.?.asInteger() != null and
            right.asInteger() != null and
            operation_annotation.common_type.?.asInteger().?.bits < right.asInteger().?.bits)
        {
            const operation = if (value.operator == .Exp) "exponentiation" else "shift";
            const common_name = try TypeBehavior.humanReadableNameAlloc(
                self.allocator,
                operation_annotation.common_type.?,
            );
            defer self.allocator.free(common_name);
            const right_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, right);
            defer self.allocator.free(right_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "The result type of the {s} operation is equal to the type of the first operand ({s}) ignoring the (larger) type of the second operand ({s}) which might be unexpected. Silence this warning by either converting the first or the second operand to the type of the other.",
                .{ operation, common_name, right_name },
            );
            defer self.allocator.free(message);
            try self.reporter.warning(errorId(3149), node.location, message);
        }
        if (TokenModule.isCompareOp(value.operator) and
            operation_annotation.common_type != null and
            operation_annotation.common_type.?.category() == .Contract)
            try self.reporter.warning(
                errorId(9170),
                node.location,
                "Comparison of variables of contract type is deprecated and scheduled for removal. Use an explicit cast to address type and compare the addresses instead.",
            );
    }

    fn endUnaryOperation(
        self: *TypeChecker,
        node: *AST.Node,
        annotation: *ASTAnnotations.ExpressionAnnotation,
        modifying: bool,
    ) CheckError!void {
        const value = node.payload.unary_operation;
        const operand_annotation = try expressionAnnotation(self.tree, value.sub_expression);
        const operand = operand_annotation.type_ref orelse return error.InvalidAst;
        const builtin_result = try TypeBehavior.unaryOperatorResult(
            self.type_provider,
            value.operator,
            operand,
        );
        const user_function = try self.findUserDefinedOperator(value.operator, &.{operand});
        if (builtin_result != null and user_function != null) return error.InvalidAst;
        var result: ?*const Types.Type = builtin_result;
        var user_function_pure = true;
        if (user_function) |declaration| {
            const function_type = try ASTImplementation.functionTypeWhenAttached(
                self.type_provider,
                declaration,
            );
            const function = function_type.asFunction() orelse return error.InvalidAst;
            user_function_pure = function.state_mutability == .Pure;
            if (function.return_parameter_types.len != 0)
                result = function.return_parameter_types[0]
            else
                result = operand;
        }
        if (result == null) {
            const type_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, operand);
            defer self.allocator.free(type_name);
            const failure_reason = unaryOperatorFailureReason(value.operator, operand);
            const no_match_reason: ?[]const u8 = if (TypeBehavior.typeDefinition(operand) != null and
                isUserDefinableOperator(value.operator))
                "No matching user-defined operator found."
            else
                null;
            const suffix = failure_reason orelse no_match_reason;
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Built-in unary operator {s} cannot be applied to type {s}.{s}{s}",
                .{
                    TokenModule.friendlyName(value.operator),
                    type_name,
                    if (suffix != null) " " else "",
                    suffix orelse "",
                },
            );
            defer self.allocator.free(message);
            if (modifying)
                try self.reporter.fatal(errorId(9767), .TypeError, node.location, null, message)
            else
                try self.reporter.typeError(errorId(4907), node.location, message);
        }
        annotation.type_ref = result orelse operand;
        try assignOnce(
            &annotation.is_pure,
            !modifying and (try operand_annotation.is_pure.get()).* and user_function_pure,
        );
        try assignOnce(&annotation.is_lvalue, false);
        try assignOnce(&annotation.is_constant, false);
        const full_annotation = try ASTAnnotations.ensure(self.tree, node);
        try assignOnce(&full_annotation.operation.user_defined_function, user_function);
    }

    fn visitAssignment(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.assignment;
        try self.requireLValue(value.left_hand_side, depth + 1);
        const left = (try expressionAnnotation(
            self.tree,
            value.left_hand_side,
        )).type_ref orelse return error.InvalidAst;
        const annotation = try expressionAnnotation(self.tree, node);
        annotation.type_ref = left;
        try assignOnce(&annotation.is_pure, false);
        try assignOnce(&annotation.is_lvalue, false);
        try assignOnce(&annotation.is_constant, false);
        try self.checkExpressionAssignment(left, value.left_hand_side);
        if (left.asTuple()) |tuple_type| {
            if (value.operator != .Assign)
                try self.reporter.typeError(
                    errorId(4289),
                    node.location,
                    "Compound assignment is not allowed for tuple types.",
                );
            annotation.type_ref = self.type_provider.emptyTuple();
            try self.checkExpression(value.right_hand_side, depth + 1);
            _ = try self.expectTypeAlready(value.right_hand_side, left);
            _ = tuple_type;
        } else if (value.operator == .Assign) {
            try self.checkExpression(value.right_hand_side, depth + 1);
            _ = try self.expectTypeAlready(value.right_hand_side, left);
        } else {
            try self.checkExpression(value.right_hand_side, depth + 1);
            const binary_operator = TokenModule.assignmentToBinaryOp(value.operator) catch
                return error.InvalidAst;
            const right = (try expressionAnnotation(
                self.tree,
                value.right_hand_side,
            )).type_ref orelse return error.InvalidAst;
            const result = try TypeBehavior.binaryOperatorResult(
                self.type_provider,
                binary_operator,
                left,
                right,
            );
            if (result == null or !TypeBehavior.equals(result.?, left)) {
                const left_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, left);
                defer self.allocator.free(left_name);
                const right_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, right);
                defer self.allocator.free(right_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Operator {s} not compatible with types {s} and {s}.",
                    .{ TokenModule.friendlyName(value.operator), left_name, right_name },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(7366), node.location, message);
            }
        }
    }

    fn checkExpressionAssignment(
        self: *TypeChecker,
        type_ref: *const Types.Type,
        expression: *const AST.Node,
    ) CheckError!void {
        if (expression.nodeKind() == .tuple_expression) {
            const tuple = expression.payload.tuple_expression;
            if (tuple.components.len == 0)
                try self.reporter.typeError(
                    errorId(5547),
                    expression.location,
                    "Empty tuple on the left hand side.",
                );
            const tuple_type = type_ref.asTuple();
            if (tuple_type != null and tuple.components.len != 1) {
                const count = @min(tuple.components.len, tuple_type.?.components.len);
                for (tuple.components[0..count], tuple_type.?.components[0..count]) |component, component_type|
                    if (component != null and component_type != null)
                        try self.checkExpressionAssignment(component_type.?, component.?);
            } else if (tuple.components.len != 0 and tuple.components[0] != null) {
                try self.checkExpressionAssignment(type_ref, tuple.components[0].?);
            }
            return;
        }
        if (!TypeBehavior.nameable(type_ref) or !containsNestedMapping(type_ref, 0)) return;
        var local_or_return = false;
        if (expression.nodeKind() == .identifier) {
            const annotation = try identifierAnnotation(self.tree, @constCast(expression));
            if (annotation.referenced_declaration) |declaration| {
                if (declaration.nodeKind() == .variable_declaration) {
                    local_or_return = ASTImplementation.isLocalOrReturn(declaration);
                }
            }
        }
        if (!local_or_return)
            try self.reporter.typeError(
                errorId(9214),
                expression.location,
                "Types in storage containing (nested) mappings cannot be assigned to.",
            );
    }

    fn visitTupleExpression(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.tuple_expression;
        const annotation = try expressionAnnotation(self.tree, node);
        const components = try self.allocator.alloc(?*const Types.Type, value.components.len);
        defer self.allocator.free(components);
        if (annotation.will_be_written_to) {
            if (value.is_inline_array)
                try self.reporter.fatal(
                    errorId(3025),
                    .TypeError,
                    node.location,
                    null,
                    "Inline array type cannot be declared as LValue.",
                );
            for (value.components, 0..) |component, index| {
                if (component) |present| {
                    try self.requireLValue(present, depth + 1);
                    components[index] = (try expressionAnnotation(
                        self.tree,
                        present,
                    )).type_ref orelse return error.InvalidAst;
                } else {
                    components[index] = null;
                }
            }
            if (components.len == 1) {
                annotation.type_ref = components[0] orelse return error.InvalidAst;
            } else {
                annotation.type_ref = try self.type_provider.tuple(components);
            }
            try assignOnce(&annotation.is_pure, false);
            try assignOnce(&annotation.is_lvalue, true);
        } else {
            var pure = true;
            var inline_array_type: ?*const Types.Type = null;
            for (value.components, 0..) |component, index| {
                const present = component orelse {
                    try self.reporter.fatal(
                        errorId(8381),
                        .TypeError,
                        node.location,
                        null,
                        "Tuple component cannot be empty.",
                    );
                    unreachable;
                };
                try self.checkExpression(present, depth + 1);
                const component_annotation = try expressionAnnotation(self.tree, present);
                const component_type = component_annotation.type_ref orelse
                    return error.InvalidAst;
                components[index] = component_type;
                if (component_type.asTuple()) |tuple_type|
                    if (tuple_type.components.len == 0) {
                        if (value.is_inline_array)
                            try self.reporter.fatal(
                                errorId(5604),
                                .TypeError,
                                present.location,
                                null,
                                "Array component cannot be empty.",
                            );
                        try self.reporter.typeError(
                            errorId(6473),
                            present.location,
                            "Tuple component cannot be empty.",
                        );
                    };
                if (component_type.category() == .RationalNumber and components.len > 1 and
                    (try TypeBehavior.mobileType(self.type_provider, component_type)) == null)
                    try self.reporter.fatal(
                        errorId(3390),
                        .TypeError,
                        present.location,
                        null,
                        "Invalid rational number.",
                    );
                if (value.is_inline_array) {
                    const mobile = try TypeBehavior.mobileType(
                        self.type_provider,
                        component_type,
                    );
                    if ((index == 0 or inline_array_type != null) and mobile == null)
                        try self.reporter.fatal(
                            errorId(9563),
                            .TypeError,
                            present.location,
                            null,
                            "Invalid mobile type.",
                        );
                    if (index == 0) {
                        inline_array_type = mobile;
                    } else if (inline_array_type != null) {
                        inline_array_type = try TypeBehavior.commonTypeWithProvider(
                            self.type_provider,
                            inline_array_type,
                            component_type,
                        );
                    }
                }
                pure = pure and (try component_annotation.is_pure.get()).*;
            }
            try assignOnce(&annotation.is_pure, pure);
            if (value.is_inline_array) {
                const common = inline_array_type orelse {
                    try self.reporter.fatal(
                        errorId(6378),
                        .TypeError,
                        node.location,
                        null,
                        "Unable to deduce common type for array elements.",
                    );
                    unreachable;
                };
                if (!TypeBehavior.nameable(common))
                    try self.reporter.fatal(
                        errorId(9656),
                        .TypeError,
                        node.location,
                        null,
                        "Unable to deduce nameable type for array elements. Try adding explicit type conversion for the first element.",
                    );
                if (containsNestedMapping(common, 0)) {
                    const name = try TypeBehavior.humanReadableNameAlloc(
                        self.allocator,
                        common,
                    );
                    defer self.allocator.free(name);
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Type {s} is only valid in storage.",
                        .{name},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.fatal(
                        errorId(1545),
                        .TypeError,
                        node.location,
                        null,
                        message,
                    );
                }
                annotation.type_ref = try self.type_provider.arrayWithLength(
                    .Memory,
                    common,
                    components.len,
                );
            } else if (components.len == 1) {
                annotation.type_ref = components[0] orelse return error.InvalidAst;
            } else {
                annotation.type_ref = try self.type_provider.tuple(components);
            }
            try assignOnce(&annotation.is_lvalue, false);
        }
        try assignOnce(&annotation.is_constant, false);
    }

    fn visitConditional(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.conditional;
        try self.checkExpression(value.condition, depth + 1);
        _ = try self.expectTypeAlready(value.condition, self.type_provider.boolean());
        try self.checkExpression(value.true_expression, depth + 1);
        try self.checkExpression(value.false_expression, depth + 1);
        const condition = try expressionAnnotation(self.tree, value.condition);
        const true_annotation = try expressionAnnotation(self.tree, value.true_expression);
        const false_annotation = try expressionAnnotation(self.tree, value.false_expression);
        const true_raw = true_annotation.type_ref orelse return error.InvalidAst;
        const false_raw = false_annotation.type_ref orelse return error.InvalidAst;
        const true_type = try TypeBehavior.mobileType(self.type_provider, true_raw);
        const false_type = try TypeBehavior.mobileType(self.type_provider, false_raw);
        var common: ?*const Types.Type = null;
        if (true_type == null)
            try self.reporter.typeError(
                errorId(9717),
                value.true_expression.location,
                "Invalid mobile type in true expression.",
            )
        else
            common = true_type;
        if (false_type == null)
            try self.reporter.typeError(
                errorId(3703),
                value.false_expression.location,
                "Invalid mobile type in false expression.",
            )
        else
            common = false_type;
        if (true_type == null and false_type == null) return error.InvalidAst;
        if (true_type != null and false_type != null) {
            common = try TypeBehavior.commonTypeWithProvider(
                self.type_provider,
                true_type,
                false_type,
            );
            if (common == null) {
                const true_name = try TypeBehavior.humanReadableNameAlloc(
                    self.allocator,
                    true_type.?,
                );
                defer self.allocator.free(true_name);
                const false_name = try TypeBehavior.humanReadableNameAlloc(
                    self.allocator,
                    false_type.?,
                );
                defer self.allocator.free(false_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "True expression's type {s} does not match false expression's type {s}.",
                    .{ true_name, false_name },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(1080), node.location, message);
                common = true_type;
            }
        }
        const annotation = try expressionAnnotation(self.tree, node);
        annotation.type_ref = common.?;
        try assignOnce(
            &annotation.is_pure,
            (try condition.is_pure.get()).* and
                (try true_annotation.is_pure.get()).* and
                (try false_annotation.is_pure.get()).*,
        );
        try assignOnce(&annotation.is_lvalue, false);
        try assignOnce(&annotation.is_constant, false);
        if (annotation.will_be_written_to)
            try self.reporter.typeError(
                errorId(2212),
                node.location,
                "Conditional expression as left value is not supported yet.",
            );
    }

    fn visitFunctionCall(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.function_call;
        var arguments_are_pure = true;
        for (value.arguments) |argument| {
            try self.checkExpression(argument, depth + 1);
            arguments_are_pure = arguments_are_pure and
                (try (try expressionAnnotation(self.tree, argument)).is_pure.get()).*;
        }
        try self.attachCallArguments(value.expression, value.arguments, value.names);
        try self.checkExpression(value.expression, depth + 1);
        const callee_annotation = try expressionAnnotation(self.tree, value.expression);
        const callee = callee_annotation.type_ref orelse return error.InvalidAst;
        const annotation = try functionCallAnnotation(self.tree, node);
        try assignOnce(&annotation.expression.is_constant, false);

        if (callee.asTypeType()) |type_type| {
            if (type_type.actual_type.category() == .Struct) {
                if (containsNestedMapping(type_type.actual_type, 0))
                    try self.reporter.fatal(
                        errorId(9515),
                        .TypeError,
                        node.location,
                        null,
                        "Struct containing a (nested) mapping cannot be constructed.",
                    );
                try assignOnce(&annotation.kind, .StructConstructorCall);
                const constructor = try self.structConstructorType(type_type.actual_type);
                try self.checkFunctionGeneral(node, constructor, true);
                annotation.expression.type_ref = constructor.return_parameter_types[0];
            } else {
                if (type_type.actual_type.category() == .Contract and
                    type_type.actual_type.payload.Contract.is_super)
                    try self.reporter.fatal(
                        errorId(1744),
                        .TypeError,
                        node.location,
                        null,
                        "Cannot convert to the super type.",
                    );
                try assignOnce(&annotation.kind, .TypeConversion);
                annotation.expression.type_ref = try self.checkTypeConversion(
                    node,
                    type_type.actual_type,
                );
            }
            try assignOnce(&annotation.expression.is_pure, arguments_are_pure);
            try assignOnce(&annotation.expression.is_lvalue, false);
        } else if (callee.asFunction()) |function_type| {
            try assignOnce(&annotation.kind, .FunctionCall);
            switch (value.expression.payload) {
                .member_access => {
                    if ((try memberAccessAnnotation(
                        self.tree,
                        value.expression,
                    )).referenced_declaration) |declaration| {
                        if (declaration.nodeKind() == .function_definition)
                            callee_annotation.called_directly = true;
                    }
                },
                .identifier => {
                    if ((try identifierAnnotation(
                        self.tree,
                        value.expression,
                    )).referenced_declaration) |declaration| {
                        if (declaration.nodeKind() == .function_definition)
                            callee_annotation.called_directly = true;
                    }
                },
                else => {},
            }
            annotation.expression.type_ref = try self.checkFunctionByKind(node, function_type);
            try assignOnce(
                &annotation.expression.is_pure,
                arguments_are_pure and
                    (try callee_annotation.is_pure.get()).* and
                    TypeBehavior.functionIsPure(function_type.*),
            );
            try assignOnce(
                &annotation.expression.is_lvalue,
                function_type.kind == .ArrayPush and function_type.parameterTypes().len == 0,
            );
        } else {
            try self.reporter.fatal(
                errorId(5704),
                .TypeError,
                node.location,
                null,
                "This expression is not callable.",
            );
        }
    }

    fn structConstructorType(
        self: *TypeChecker,
        struct_type: *const Types.Type,
    ) CheckError!*const Types.FunctionType {
        const structure = switch (struct_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidAst,
        };
        const members = structure.declaration.payload.struct_definition.members;
        const parameter_types = try self.allocator.alloc(*const Types.Type, members.len);
        defer self.allocator.free(parameter_types);
        const parameter_names = try self.allocator.alloc([]const u8, members.len);
        defer self.allocator.free(parameter_names);
        for (members, 0..) |member, index| {
            const member_type = (try variableAnnotation(self.tree, member)).type_ref orelse
                return error.InvalidAst;
            parameter_types[index] = try self.type_provider.withLocationIfReference(
                .Memory,
                member_type,
                false,
            );
            parameter_names[index] = declarationName(member);
        }
        const result_type = try self.type_provider.withLocation(
            struct_type,
            .Memory,
            false,
        );
        const returns = [_]*const Types.Type{result_type};
        const return_names = [_][]const u8{""};
        const function_type = try self.type_provider.function(
            parameter_types,
            &returns,
            parameter_names,
            &return_names,
            .Internal,
            .Pure,
            structure.declaration,
            .{},
        );
        return function_type.asFunction() orelse return error.InvalidAst;
    }

    fn checkTypeConversion(
        self: *TypeChecker,
        node: *AST.Node,
        requested_type: *const Types.Type,
    ) CheckError!*const Types.Type {
        const value = node.payload.function_call;
        if (value.arguments.len != 1) {
            try self.reporter.typeError(
                errorId(2558),
                node.location,
                "Exactly one argument expected for explicit type conversion.",
            );
            return requested_type;
        }
        if (value.names.len != 0)
            try self.reporter.typeError(
                errorId(5153),
                node.location,
                "Type conversion cannot allow named arguments.",
            );
        const argument_type = (try expressionAnnotation(
            self.tree,
            value.arguments[0],
        )).type_ref orelse return error.InvalidAst;
        var result_type = requested_type;
        if (requested_type.asReference() != null) {
            const requested_reference = requested_type.asReference().?;
            const location: Types.DataLocation = if (argument_type.asReference()) |reference|
                reference.location
            else
                .Memory;
            result_type = try self.type_provider.withLocation(
                requested_type,
                location,
                requested_reference.isPointer(),
            );
        }
        if (!TypeBehavior.isExplicitlyConvertibleTo(argument_type, result_type)) {
            const argument_name = try TypeBehavior.humanReadableNameAlloc(
                self.allocator,
                argument_type,
            );
            defer self.allocator.free(argument_name);
            const result_name = try TypeBehavior.humanReadableNameAlloc(
                self.allocator,
                result_type,
            );
            defer self.allocator.free(result_name);
            if (result_type.category() == .Contract and
                argument_type.asAddress() != null and
                argument_type.asAddress().?.state_mutability != .Payable)
            {
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                const argument = value.arguments[0];
                if (argument.nodeKind() == .identifier) {
                    const identifier = try identifierAnnotation(self.tree, argument);
                    if (identifier.referenced_declaration) |declaration|
                        if (declaration.nodeKind() == .variable_declaration)
                            try secondary.append(
                                self.allocator,
                                "Did you mean to declare this variable as \"address payable\"?",
                                declaration.location,
                            );
                }
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Explicit type conversion not allowed from non-payable \"address\" to \"{s}\", which has a payable fallback function.",
                    .{result_name},
                );
                defer self.allocator.free(message);
                try self.reporter.reportWithSecondary(
                    errorId(7398),
                    .TypeError,
                    node.location,
                    &secondary,
                    message,
                );
            } else if (argument_type.asFunction() != null and
                argument_type.asFunction().?.kind == .External and
                result_type.category() == .Address)
            {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Explicit type conversion not allowed from \"{s}\" to \"{s}\". To obtain the address of the contract of the function, you can use the .address member of the function.",
                    .{ argument_name, result_name },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(5030), node.location, message);
            } else {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Explicit type conversion not allowed from \"{s}\" to \"{s}\".",
                    .{ argument_name, result_name },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(9640), node.location, message);
            }
        }
        return result_type;
    }

    fn checkFunctionByKind(
        self: *TypeChecker,
        node: *AST.Node,
        function_type: *const Types.FunctionType,
    ) CheckError!*const Types.Type {
        const return_types: []const *const Types.Type = switch (function_type.kind) {
            .ABIDecode => return self.checkAbiDecode(node),
            .ABIEncode,
            .ABIEncodePacked,
            .ABIEncodeWithSelector,
            .ABIEncodeCall,
            .ABIEncodeWithSignature,
            => blk: {
                try self.checkAbiEncode(node, function_type);
                break :blk function_type.return_parameter_types;
            },
            .MetaType => return self.checkMetaTypeCall(node),
            .StringConcat => blk: {
                try self.checkStringConcat(node, function_type);
                break :blk function_type.return_parameter_types;
            },
            .BytesConcat => blk: {
                try self.checkBytesConcat(node, function_type);
                break :blk function_type.return_parameter_types;
            },
            .ERC7201 => blk: {
                try self.checkErc7201(node, function_type);
                break :blk function_type.return_parameter_types;
            },
            .Declaration => blk: {
                const declaration = function_type.declaration orelse return error.InvalidAst;
                const defining_contract = ASTImplementation.scope(declaration) orelse
                    return error.InvalidAst;
                if (self.current_contract != null and
                    try contractHierarchyContains(
                        self.tree,
                        self.current_contract.?,
                        defining_contract,
                    ) and
                    declaration.nodeKind() == .function_definition and
                    !declaration.payload.function_definition.implemented())
                {
                    try self.reporter.typeError(
                        errorId(7501),
                        node.location,
                        "Cannot call unimplemented base function.",
                    );
                } else {
                    try self.reporter.typeError(
                        errorId(3419),
                        node.location,
                        "Cannot call function via contract type name.",
                    );
                }
                break :blk function_type.return_parameter_types;
            },
            else => blk: {
                if (function_type.kind == .BareStaticCall and !self.evm_version.hasStaticCall())
                    try self.reporter.typeError(
                        errorId(5052),
                        node.location,
                        "\"staticcall\" is not supported by the VM version.",
                    );
                try self.checkFunctionGeneral(node, function_type, false);
                break :blk function_type.return_parameter_types;
            },
        };
        return self.functionReturnType(return_types);
    }

    fn functionReturnType(
        self: *TypeChecker,
        return_types: []const *const Types.Type,
    ) CheckError!*const Types.Type {
        return if (return_types.len == 0)
            self.type_provider.emptyTuple()
        else if (return_types.len == 1)
            return_types[0]
        else
            try self.type_provider.tupleOfTypes(return_types);
    }

    fn checkFunctionGeneral(
        self: *TypeChecker,
        node: *AST.Node,
        function_type: *const Types.FunctionType,
        struct_constructor: bool,
    ) CheckError!void {
        const value = node.payload.function_call;
        const parameter_types = function_type.parameterTypes();
        const parameter_names = function_type.parameterNames();
        const variadic = function_type.options.arbitrary_parameters;
        if (value.arguments.len < parameter_types.len or
            (!variadic and value.arguments.len > parameter_types.len))
        {
            const message = if (variadic)
                try std.fmt.allocPrint(
                    self.allocator,
                    "Need at least {d} arguments for {s}, but provided only {d}.",
                    .{
                        parameter_types.len,
                        if (struct_constructor) "struct constructor" else "function call",
                        value.arguments.len,
                    },
                )
            else
                try std.fmt.allocPrint(
                    self.allocator,
                    "Wrong argument count for {s}: {d} arguments given but expected {d}.",
                    .{
                        if (struct_constructor) "struct constructor" else "function call",
                        value.arguments.len,
                        parameter_types.len,
                    },
                );
            defer self.allocator.free(message);
            if (isBareCallKind(function_type.kind)) {
                const suffix = if (value.arguments.len == 0)
                    " This function requires a single bytes argument. Use \"\" as argument to provide empty calldata."
                else
                    " This function requires a single bytes argument. If all your arguments are value types, you can use abi.encode(...) to properly generate it.";
                const full = try std.fmt.allocPrint(self.allocator, "{s}{s}", .{ message, suffix });
                defer self.allocator.free(full);
                try self.reporter.typeError(
                    if (value.arguments.len == 0) errorId(6138) else errorId(8922),
                    node.location,
                    full,
                );
            } else if (isHashFunctionKind(function_type.kind)) {
                const full = try std.fmt.allocPrint(
                    self.allocator,
                    "{s} This function requires a single bytes argument. Use abi.encodePacked(...) to obtain the pre-0.5.0 behaviour or abi.encode(...) to use ABI encoding.",
                    .{message},
                );
                defer self.allocator.free(full);
                try self.reporter.typeError(errorId(4323), node.location, full);
            } else {
                try self.reporter.typeError(
                    if (struct_constructor)
                        errorId(9755)
                    else if (variadic)
                        errorId(9308)
                    else
                        errorId(6160),
                    node.location,
                    message,
                );
            }
            return;
        }
        if (variadic and value.names.len != 0) {
            try self.reporter.typeError(
                errorId(2627),
                node.location,
                "Named arguments cannot be used for functions that take arbitrary parameters.",
            );
            return;
        }

        const mapped = try self.allocator.alloc(?*AST.Node, parameter_types.len);
        defer self.allocator.free(mapped);
        @memset(mapped, null);
        if (value.names.len == 0) {
            for (value.arguments[0..parameter_types.len], 0..) |argument, index|
                mapped[index] = argument;
        } else {
            var duplicate = false;
            for (value.names, 0..) |name, index|
                for (value.names[index + 1 ..]) |other|
                    if (std.mem.eql(u8, name, other)) {
                        duplicate = true;
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "Duplicate named argument \"{s}\".",
                            .{name},
                        );
                        defer self.allocator.free(message);
                        try self.reporter.typeError(
                            errorId(6995),
                            value.arguments[index].location,
                            message,
                        );
                    };
            if (duplicate) return;
            var not_all_mapped = false;
            for (value.names, value.arguments) |name, argument| {
                var found = false;
                for (parameter_names, 0..) |parameter_name, index| {
                    if (!std.mem.eql(u8, name, parameter_name)) continue;
                    mapped[index] = argument;
                    found = true;
                    break;
                }
                if (!found) {
                    not_all_mapped = true;
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Named argument \"{s}\" does not match function declaration.",
                        .{name},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.typeError(errorId(4974), node.location, message);
                }
            }
            if (not_all_mapped) return;
        }

        for (mapped, parameter_types) |maybe_argument, expected| {
            const argument = maybe_argument orelse return error.InvalidAst;
            const actual = (try expressionAnnotation(self.tree, argument)).type_ref orelse
                return error.InvalidAst;
            if (TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) continue;
            const actual_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, actual);
            defer self.allocator.free(actual_name);
            const expected_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, expected);
            defer self.allocator.free(expected_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Invalid type for argument in function call. Invalid implicit conversion from {s} to {s} requested.{s}{s}",
                .{
                    actual_name,
                    expected_name,
                    if (implicitConversionReason(actual, expected) != null) " " else "",
                    implicitConversionReason(actual, expected) orelse "",
                },
            );
            defer self.allocator.free(message);
            if (isBareCallKind(function_type.kind)) {
                const full = try std.fmt.allocPrint(
                    self.allocator,
                    "{s} This function requires a single bytes argument. If all your arguments are value types, you can use abi.encode(...) to properly generate it.",
                    .{message},
                );
                defer self.allocator.free(full);
                try self.reporter.typeError(errorId(8051), argument.location, full);
            } else if (isHashFunctionKind(function_type.kind)) {
                const full = try std.fmt.allocPrint(
                    self.allocator,
                    "{s} This function requires a single bytes argument. Use abi.encodePacked(...) to obtain the pre-0.5.0 behaviour or abi.encode(...) to use ABI encoding.",
                    .{message},
                );
                defer self.allocator.free(full);
                try self.reporter.typeError(errorId(7556), argument.location, full);
            } else {
                try self.reporter.typeError(errorId(9553), argument.location, message);
            }
        }

        const is_library_call = function_type.kind == .DelegateCall;
        const call_requires_abi_encoding = switch (function_type.kind) {
            .DelegateCall, .External, .Creation, .Event, .Error => true,
            else => false,
        };
        if (call_requires_abi_encoding and !(try self.useAbiCoderV2())) {
            for (mapped, parameter_types) |maybe_argument, parameter_type| {
                if (typeSupportedByOldABIEncoder(parameter_type, is_library_call)) continue;
                const argument = maybe_argument orelse return error.InvalidAst;
                const type_name = try TypeBehavior.humanReadableNameAlloc(
                    self.allocator,
                    parameter_type,
                );
                defer self.allocator.free(type_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "The type of this parameter, {s}, is only supported in ABI coder v2. Use \"pragma abicoder v2;\" to enable the feature.",
                    .{type_name},
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(2443), argument.location, message);
            }
            for (function_type.return_parameter_types, 1..) |return_type, index| {
                if (typeSupportedByOldABIEncoder(return_type, is_library_call)) continue;
                const type_name = try TypeBehavior.humanReadableNameAlloc(
                    self.allocator,
                    return_type,
                );
                defer self.allocator.free(type_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "The type of return parameter {d}, {s}, is only supported in ABI coder v2. Use \"pragma abicoder v2;\" to enable the feature.",
                    .{ index, type_name },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(2428), node.location, message);
            }
        }
    }

    fn checkAbiDecode(
        self: *TypeChecker,
        node: *AST.Node,
    ) CheckError!*const Types.Type {
        const value = node.payload.function_call;
        if (value.arguments.len != 2) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "This function takes two arguments, but {d} were provided.",
                .{value.arguments.len},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(5782), node.location, message);
        }
        if (value.arguments.len >= 1) {
            const first_type = (try expressionAnnotation(
                self.tree,
                value.arguments[0],
            )).type_ref orelse return error.InvalidAst;
            if (!TypeBehavior.isImplicitlyConvertibleTo(first_type, self.type_provider.bytesMemory()) and
                !TypeBehavior.isImplicitlyConvertibleTo(first_type, self.type_provider.bytesCalldata()))
            {
                const type_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, first_type);
                defer self.allocator.free(type_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "The first argument to \"abi.decode\" must be implicitly convertible to bytes memory or bytes calldata, but is of type {s}.",
                    .{type_name},
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(1956), value.arguments[0].location, message);
            }
        }
        if (value.arguments.len < 2) return self.type_provider.emptyTuple();
        const type_tuple = value.arguments[1];
        if (type_tuple.nodeKind() != .tuple_expression) {
            try self.reporter.typeError(
                errorId(6444),
                type_tuple.location,
                "The second argument to \"abi.decode\" has to be a tuple of types.",
            );
            return self.type_provider.emptyTuple();
        }
        var components: std.ArrayList(*const Types.Type) = .empty;
        defer components.deinit(self.allocator);
        for (type_tuple.payload.tuple_expression.components) |maybe_component| {
            const component = maybe_component orelse return error.InvalidAst;
            const component_type = (try expressionAnnotation(self.tree, component)).type_ref orelse
                return error.InvalidAst;
            const type_type = component_type.asTypeType() orelse {
                try self.reporter.typeError(
                    errorId(1039),
                    component.location,
                    "Argument has to be a type name.",
                );
                try components.append(self.allocator, self.type_provider.emptyTuple());
                continue;
            };
            var actual_type = try self.type_provider.withLocationIfReference(
                .Memory,
                type_type.actual_type,
                false,
            );
            if (actual_type.category() == .Address)
                actual_type = self.type_provider.payableAddress();
            if ((try TypeBehavior.fullEncodingType(
                self.type_provider,
                actual_type,
                false,
                try self.useAbiCoderV2(),
                false,
            )) == null) {
                const type_name = try TypeBehavior.humanReadableNameAlloc(
                    self.allocator,
                    actual_type,
                );
                defer self.allocator.free(type_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Decoding type {s} not supported.",
                    .{type_name},
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(9611), component.location, message);
            }
            if (actual_type.asReference()) |reference|
                if (!(try TypeBehavior.validForLocation(
                    self.type_provider,
                    actual_type,
                    reference.location,
                )))
                    try self.reporter.typeError(
                        errorId(6118),
                        component.location,
                        validForLocationFailureReason(reference.location),
                    );
            try components.append(self.allocator, actual_type);
        }
        return self.functionReturnType(components.items);
    }

    fn checkAbiEncode(
        self: *TypeChecker,
        node: *AST.Node,
        function_type: *const Types.FunctionType,
    ) CheckError!void {
        const value = node.payload.function_call;
        if (value.names.len != 0) {
            try self.reporter.typeError(
                errorId(2627),
                node.location,
                "Named arguments cannot be used for functions that take arbitrary parameters.",
            );
            return;
        }
        try self.checkFunctionGeneral(node, function_type, false);
        if (function_type.kind == .ABIEncodeCall) {
            try self.checkAbiEncodeCall(node);
            return;
        }
        const packed_mode = function_type.kind == .ABIEncodePacked;
        const abi_encoder_v2 = try self.useAbiCoderV2();
        for (value.arguments) |argument| {
            const argument_type = (try expressionAnnotation(self.tree, argument)).type_ref orelse
                return error.InvalidAst;
            if (argument_type.category() == .RationalNumber) {
                const rational = argument_type.payload.RationalNumber;
                if (rational.denominator.compareUnsigned(1) != .eq) {
                    try self.reporter.typeError(
                        errorId(6090),
                        argument.location,
                        "Fractional numbers cannot yet be encoded.",
                    );
                    continue;
                }
                if ((try TypeBehavior.mobileType(self.type_provider, argument_type)) == null) {
                    try self.reporter.typeError(
                        errorId(8009),
                        argument.location,
                        "Invalid rational number (too large or division by zero).",
                    );
                    continue;
                }
                if (packed_mode) {
                    try self.reporter.typeError(
                        errorId(7279),
                        argument.location,
                        "Cannot perform packed encoding for a literal. Please convert it to an explicit type first.",
                    );
                    continue;
                }
            }
            if (packed_mode and !typeSupportedByOldABIEncoder(argument_type, false)) {
                try self.reporter.typeError(
                    errorId(9578),
                    argument.location,
                    "Type not supported in packed mode.",
                );
                continue;
            }
            if ((try TypeBehavior.fullEncodingType(
                self.type_provider,
                argument_type,
                false,
                abi_encoder_v2,
                !TypeBehavior.functionPadsArguments(function_type.*),
            )) == null)
                try self.reporter.typeError(
                    errorId(2056),
                    argument.location,
                    "This type cannot be encoded.",
                );
        }
    }

    fn checkAbiEncodeCall(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const arguments = node.payload.function_call.arguments;
        if (arguments.len != 2) {
            try self.reporter.typeError(
                errorId(6219),
                node.location,
                "Expected two arguments: a function pointer followed by a tuple.",
            );
            return;
        }

        const first_type = (try expressionAnnotation(self.tree, arguments[0])).type_ref orelse
            return error.InvalidAst;
        const raw_function = first_type.asFunction() orelse {
            const type_name = try TypeBehavior.humanReadableNameAlloc(
                self.allocator,
                first_type,
            );
            defer self.allocator.free(type_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Expected first argument to be a function pointer, not \"{s}\".",
                .{type_name},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(5511), arguments[0].location, message);
            return;
        };
        const external_type = (try TypeBehavior.asExternallyCallableFunction(
            self.type_provider,
            raw_function.*,
            false,
        )).payload.Function;
        if (external_type.kind != .External and external_type.kind != .Declaration) {
            var message: std.ArrayList(u8) = .empty;
            defer message.deinit(self.allocator);
            try message.appendSlice(
                self.allocator,
                "Expected regular external function type, or external view on public function.",
            );
            try message.appendSlice(self.allocator, switch (external_type.kind) {
                .Internal => " Provided internal function.",
                .DelegateCall => " Cannot use library functions for abi.encodeCall.",
                .Creation => " Provided creation function.",
                .Event => " Cannot use events for abi.encodeCall.",
                .Error => " Cannot use errors for abi.encodeCall.",
                else => " Cannot use special function.",
            });
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            if (external_type.declaration) |declaration| {
                try secondary.append(
                    self.allocator,
                    "Function is declared here:",
                    declaration.location,
                );
                const scope = ASTImplementation.scope(declaration);
                if (ASTImplementation.effectiveVisibility(declaration) == .Public and
                    scope == self.current_contract)
                {
                    try message.appendSlice(
                        self.allocator,
                        " Did you forget to prefix \"this.\"?",
                    );
                } else if (self.current_contract) |current_contract| {
                    if (scope != current_contract and
                        try contractHierarchyContains(self.tree, current_contract, scope))
                        try message.appendSlice(
                            self.allocator,
                            " Functions from base contracts have to be external.",
                        );
                }
            }
            try self.reporter.reportWithSecondary(
                errorId(3509),
                .TypeError,
                arguments[0].location,
                &secondary,
                message.items,
            );
            return;
        }

        var call_arguments: std.ArrayList(*AST.Node) = .empty;
        defer call_arguments.deinit(self.allocator);
        const second_type = (try expressionAnnotation(self.tree, arguments[1])).type_ref orelse
            return error.InvalidAst;
        const tuple_type = second_type.asTuple();
        if (tuple_type != null) {
            if (arguments[1].nodeKind() != .tuple_expression) {
                try self.reporter.typeError(
                    errorId(9062),
                    arguments[1].location,
                    "Expected an inline tuple, not an expression of a tuple type.",
                );
                return;
            }
            for (arguments[1].payload.tuple_expression.components) |component|
                try call_arguments.append(
                    self.allocator,
                    component orelse return error.InvalidAst,
                );
        } else {
            try call_arguments.append(self.allocator, arguments[1]);
        }

        if (external_type.parameter_types.len != call_arguments.items.len) {
            const message = if (tuple_type != null)
                try std.fmt.allocPrint(
                    self.allocator,
                    "Expected {d} instead of {d} components for the tuple parameter.",
                    .{ external_type.parameter_types.len, call_arguments.items.len },
                )
            else
                try std.fmt.allocPrint(
                    self.allocator,
                    "Expected a tuple with {d} components instead of a single non-tuple parameter.",
                    .{external_type.parameter_types.len},
                );
            defer self.allocator.free(message);
            try self.reporter.typeError(
                if (tuple_type != null) errorId(7788) else errorId(7515),
                node.location,
                message,
            );
        }

        const count = @min(external_type.parameter_types.len, call_arguments.items.len);
        for (
            call_arguments.items[0..count],
            external_type.parameter_types[0..count],
            0..,
        ) |argument, expected, index| {
            const actual = (try expressionAnnotation(self.tree, argument)).type_ref orelse
                return error.InvalidAst;
            if (TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) continue;
            const actual_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, actual);
            defer self.allocator.free(actual_name);
            const expected_name = try TypeBehavior.humanReadableNameAlloc(
                self.allocator,
                expected,
            );
            defer self.allocator.free(expected_name);
            const reason = implicitConversionReason(actual, expected);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Cannot implicitly convert component at position {d} from \"{s}\" to \"{s}\"{s}{s}",
                .{
                    index,
                    actual_name,
                    expected_name,
                    if (reason != null) ": " else ".",
                    reason orelse "",
                },
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(5407), argument.location, message);
        }
    }

    fn checkMetaTypeCall(
        self: *TypeChecker,
        node: *AST.Node,
    ) CheckError!*const Types.Type {
        const value = node.payload.function_call;
        if (value.arguments.len != 1) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "This function takes one argument, but {d} were provided.",
                .{value.arguments.len},
            );
            defer self.allocator.free(message);
            try self.reporter.fatal(errorId(8885), .TypeError, node.location, null, message);
        }
        const argument_type = (try expressionAnnotation(
            self.tree,
            value.arguments[0],
        )).type_ref orelse return error.InvalidAst;
        const actual_type = if (argument_type.asTypeType()) |type_type|
            type_type.actual_type
        else
            null;
        const valid = if (actual_type) |present| switch (present.category()) {
            .Contract => !present.payload.Contract.is_super,
            .Integer, .Enum => true,
            else => false,
        } else false;
        if (!valid) {
            const type_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, argument_type);
            defer self.allocator.free(type_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Invalid type for argument in the function call. An enum type, contract type or an integer type is required, but {s} provided.",
                .{type_name},
            );
            defer self.allocator.free(message);
            try self.reporter.fatal(
                errorId(4259),
                .TypeError,
                value.arguments[0].location,
                null,
                message,
            );
        }
        return self.type_provider.meta(actual_type.?);
    }

    fn checkStringConcat(
        self: *TypeChecker,
        node: *AST.Node,
        function_type: *const Types.FunctionType,
    ) CheckError!void {
        try self.checkFunctionGeneral(node, function_type, false);
        for (node.payload.function_call.arguments) |argument| {
            const argument_type = (try expressionAnnotation(self.tree, argument)).type_ref orelse
                return error.InvalidAst;
            if (TypeBehavior.isImplicitlyConvertibleTo(
                argument_type,
                self.type_provider.stringMemory(),
            )) continue;
            const type_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, argument_type);
            defer self.allocator.free(type_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Invalid type for argument in the string.concat function call. string type is required, but {s} provided.",
                .{type_name},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(9977), argument.location, message);
        }
    }

    fn checkBytesConcat(
        self: *TypeChecker,
        node: *AST.Node,
        function_type: *const Types.FunctionType,
    ) CheckError!void {
        try self.checkFunctionGeneral(node, function_type, false);
        const bytes32 = try self.type_provider.fixedBytes(32);
        for (node.payload.function_call.arguments) |argument| {
            const argument_type = (try expressionAnnotation(self.tree, argument)).type_ref orelse
                return error.InvalidAst;
            const valid = argument_type.category() != .RationalNumber and
                (TypeBehavior.isImplicitlyConvertibleTo(argument_type, bytes32) or
                    TypeBehavior.isImplicitlyConvertibleTo(
                        argument_type,
                        self.type_provider.bytesMemory(),
                    ));
            if (valid) continue;
            const type_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, argument_type);
            defer self.allocator.free(type_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Invalid type for argument in the bytes.concat function call. bytes or fixed bytes type is required, but {s} provided.",
                .{type_name},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(8015), argument.location, message);
        }
    }

    fn checkErc7201(
        self: *TypeChecker,
        node: *AST.Node,
        function_type: *const Types.FunctionType,
    ) CheckError!void {
        const arguments = node.payload.function_call.arguments;
        if (arguments.len != 0) {
            const argument_type = (try expressionAnnotation(self.tree, arguments[0])).type_ref orelse
                return error.InvalidAst;
            const valid = argument_type.category() == .StringLiteral or
                (argument_type.asArray() != null and argument_type.payload.Array.kind == .String);
            if (!valid)
                try self.reporter.typeError(
                    errorId(6896),
                    arguments[0].location,
                    "The argument to erc7201 builtin must be a string.",
                );
        }
        try self.checkFunctionGeneral(node, function_type, false);
    }

    fn attachCallArguments(
        self: *TypeChecker,
        expression: *AST.Node,
        arguments: AST.NodeList,
        names: AST.StringList,
    ) CheckError!void {
        if (names.len != 0 and names.len != arguments.len) return error.InvalidAst;
        const annotation = try expressionAnnotation(self.tree, expression);
        if (annotation.arguments != null) return;
        var call_arguments: @import("../ast/ast_enums.zig").FuncCallArguments = .{};
        for (arguments) |argument| {
            const type_ref = (try expressionAnnotation(self.tree, argument)).type_ref orelse
                return error.InvalidAst;
            try call_arguments.types.append(self.tree.allocator(), @ptrCast(type_ref));
        }
        for (names) |name| try call_arguments.names.append(self.tree.allocator(), name);
        annotation.arguments = call_arguments;
    }

    fn declarationCanTakeArguments(
        self: *TypeChecker,
        declaration: *const AST.Node,
        arguments: *const @import("../ast/ast_enums.zig").FuncCallArguments,
    ) CheckError!bool {
        if (declaration.nodeKind() == .magic_variable_declaration) {
            const erased = declaration.payload.magic_variable_declaration.type_ref orelse
                return error.InvalidAst;
            const type_ref: *const Types.Type = @ptrCast(@alignCast(erased));
            const function = type_ref.asFunction() orelse return false;
            const parameters = function.parameterTypes();
            if (parameters.len != arguments.types.items.len or
                arguments.names.items.len != 0)
                return false;
            for (parameters, arguments.types.items) |expected, erased_type| {
                const actual: *const Types.Type = @ptrCast(@alignCast(erased_type));
                if (!TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) return false;
            }
            return true;
        }
        const callable = callableData(declaration) orelse return false;
        const parameters = callable.parameters.payload.parameter_list.parameters;
        if (parameters.len != arguments.types.items.len) return false;
        if (arguments.names.items.len == 0) {
            for (parameters, arguments.types.items) |parameter, erased_type| {
                const expected = (try variableAnnotation(self.tree, parameter)).type_ref orelse
                    return error.InvalidAst;
                const actual: *const Types.Type = @ptrCast(@alignCast(erased_type));
                if (!TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) return false;
            }
            return true;
        }
        if (arguments.names.items.len != parameters.len) return false;
        for (arguments.names.items, arguments.types.items) |name, erased_type| {
            var found = false;
            for (parameters) |parameter| {
                if (!std.mem.eql(
                    u8,
                    name,
                    parameter.payload.variable_declaration.declaration.name,
                )) continue;
                const expected = (try variableAnnotation(self.tree, parameter)).type_ref orelse
                    return error.InvalidAst;
                const actual: *const Types.Type = @ptrCast(@alignCast(erased_type));
                if (!TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) return false;
                found = true;
                break;
            }
            if (!found) return false;
        }
        return true;
    }

    fn visitFunctionCallOptions(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.function_call_options;
        if (value.options.len != value.names.len) return error.InvalidAst;
        // Overload resolution happens while visiting the expression beneath
        // `{gas:, value:, salt:}`. Forward the outer call's already inferred
        // argument types before that visit, as upstream does.
        (try expressionAnnotation(self.tree, value.expression)).arguments =
            (try expressionAnnotation(self.tree, node)).arguments;
        try self.checkExpression(value.expression, depth + 1);
        for (value.options) |option| try self.checkExpression(option, depth + 1);
        const expression_type = (try expressionAnnotation(
            self.tree,
            value.expression,
        )).type_ref orelse return error.InvalidAst;
        const function_type = expression_type.asFunction() orelse {
            try self.reporter.fatal(
                errorId(2622),
                .TypeError,
                node.location,
                null,
                "Expected callable expression before call options.",
            );
            unreachable;
        };
        const allowed = switch (function_type.kind) {
            .Creation,
            .External,
            .BareCall,
            .BareCallCode,
            .BareDelegateCall,
            .BareStaticCall,
            => true,
            else => false,
        };
        if (!allowed)
            try self.reporter.fatal(
                errorId(2193),
                .TypeError,
                node.location,
                null,
                "Function call options can only be set on external function calls or contract creations.",
            );
        if (function_type.options.value_set or function_type.options.gas_set or
            function_type.options.salt_set)
            try self.reporter.typeError(
                errorId(1645),
                node.location,
                "Function call options have already been set, you have to combine them into a single {...}-option.",
            );

        var set_salt = false;
        var set_value = false;
        var set_gas = false;
        for (value.names, value.options) |name, option| {
            if (std.mem.eql(u8, name, "salt")) {
                if (function_type.kind != .Creation) {
                    try self.reporter.typeError(
                        errorId(2721),
                        node.location,
                        "Function call option \"salt\" can only be used with \"new\".",
                    );
                } else {
                    try self.checkDuplicateCallOption(&set_salt, "salt", node.location);
                    _ = try self.expectTypeAlready(option, try self.type_provider.fixedBytes(32));
                }
            } else if (std.mem.eql(u8, name, "value")) {
                if (function_type.kind == .BareDelegateCall) {
                    try self.reporter.typeError(
                        errorId(6189),
                        node.location,
                        "Cannot set option \"value\" for delegatecall.",
                    );
                } else if (function_type.kind == .BareStaticCall) {
                    try self.reporter.typeError(
                        errorId(2842),
                        node.location,
                        "Cannot set option \"value\" for staticcall.",
                    );
                } else if (function_type.state_mutability != .Payable) {
                    try self.reporter.typeError(
                        errorId(7006),
                        node.location,
                        if (function_type.kind == .Creation)
                            "Cannot set option \"value\", since the constructor is not payable."
                        else
                            "Cannot set option \"value\" on a non-payable function type.",
                    );
                } else {
                    try self.checkDuplicateCallOption(&set_value, "value", node.location);
                    _ = try self.expectTypeAlready(option, self.type_provider.uint256());
                }
            } else if (std.mem.eql(u8, name, "gas")) {
                if (function_type.kind == .Creation) {
                    try self.reporter.typeError(
                        errorId(9903),
                        node.location,
                        "Function call option \"gas\" cannot be used with \"new\".",
                    );
                } else {
                    try self.checkDuplicateCallOption(&set_gas, "gas", node.location);
                    _ = try self.expectTypeAlready(option, self.type_provider.uint256());
                }
            } else {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Unknown call option \"{s}\". Valid options are \"salt\", \"value\" and \"gas\".",
                    .{name},
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(9318), node.location, message);
            }
        }
        if (set_salt and !self.evm_version.hasCreate2())
            try self.reporter.typeError(
                errorId(5189),
                node.location,
                "Unsupported call option \"salt\" (requires Constantinople-compatible VMs).",
            );
        const annotation = try expressionAnnotation(self.tree, node);
        annotation.type_ref = try self.type_provider.copyAndSetCallOptions(
            expression_type,
            set_gas,
            set_value,
            set_salt,
        );
        try assignOnce(&annotation.is_pure, false);
        try assignOnce(&annotation.is_lvalue, false);
        try assignOnce(&annotation.is_constant, false);
    }

    fn checkDuplicateCallOption(
        self: *TypeChecker,
        seen: *bool,
        name: []const u8,
        location: Diagnostics.SourceLocation,
    ) CheckError!void {
        if (seen.*) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Duplicate option \"{s}\".",
                .{name},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(9886), location, message);
        }
        seen.* = true;
    }

    fn endNewExpression(self: *TypeChecker, node: *AST.Node) CheckError!void {
        const type_name = node.payload.new_expression.type_name;
        const type_ref = (try typeNameAnnotation(self.tree, type_name)).type_ref orelse
            return error.InvalidAst;
        const annotation = try expressionAnnotation(self.tree, node);
        try assignOnce(&annotation.is_constant, false);
        try assignOnce(&annotation.is_lvalue, false);
        if (type_name.nodeKind() == .user_defined_type_name and
            type_ref.category() != .Contract)
            try self.reporter.fatal(
                errorId(5540),
                .TypeError,
                node.location,
                null,
                "Identifier is not a contract.",
            );
        switch (type_ref.payload) {
            .Contract => |contract_type| {
                const contract = @constCast(contract_type.declaration);
                const definition = contract.payload.contract_definition;
                if (definition.contract_kind == .Interface)
                    try self.reporter.fatal(
                        errorId(2971),
                        .TypeError,
                        node.location,
                        null,
                        "Cannot instantiate an interface.",
                    );
                const contract_annotation = try contractDefinitionAnnotation(self.tree, contract);
                const unresolved = contract_annotation.unimplemented_declarations;
                if (definition.abstract or (unresolved != null and unresolved.?.len != 0))
                    try self.reporter.typeError(
                        errorId(4614),
                        node.location,
                        "Cannot instantiate an abstract contract.",
                    );
                const constructor = findConstructor(contract);
                const parameters = if (constructor) |present|
                    try self.parameterTypesAndNames(
                        present.payload.function_definition.callable.parameters,
                    )
                else
                    ParameterTypesAndNames{ .types = &.{}, .names = &.{} };
                defer if (constructor != null) {
                    self.allocator.free(parameters.types);
                    self.allocator.free(parameters.names);
                };
                const return_types = [_]*const Types.Type{type_ref};
                const return_names = [_][]const u8{""};
                annotation.type_ref = try self.type_provider.function(
                    parameters.types,
                    &return_types,
                    parameters.names,
                    &return_names,
                    .Creation,
                    if (constructor) |present|
                        present.payload.function_definition.state_mutability
                    else
                        .NonPayable,
                    contract,
                    .{},
                );
                try assignOnce(&annotation.is_pure, false);
            },
            .Array => |array| {
                if (containsNestedMapping(type_ref, 0))
                    try self.reporter.fatal(
                        errorId(1164),
                        .TypeError,
                        type_name.location,
                        null,
                        "Array containing a (nested) mapping cannot be constructed in memory.",
                    );
                if (array.length != null)
                    try self.reporter.typeError(
                        errorId(3904),
                        type_name.location,
                        "Length has to be placed in parentheses after the array type for new expression.",
                    );
                const memory_type = try self.type_provider.withLocationIfReference(
                    .Memory,
                    type_ref,
                    true,
                );
                const parameters = [_]*const Types.Type{self.type_provider.uint256()};
                const returns = [_]*const Types.Type{memory_type};
                const names = [_][]const u8{""};
                annotation.type_ref = try self.type_provider.function(
                    &parameters,
                    &returns,
                    &names,
                    &names,
                    .ObjectCreation,
                    .Pure,
                    null,
                    .{},
                );
                try assignOnce(&annotation.is_pure, true);
            },
            else => {
                try assignOnce(&annotation.is_pure, false);
                try self.reporter.fatal(
                    errorId(8807),
                    .TypeError,
                    node.location,
                    null,
                    "Contract or array type expected.",
                );
            },
        }
    }

    fn visitMemberAccess(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.member_access;
        try self.checkExpression(value.expression, depth + 1);
        const owner_annotation = try expressionAnnotation(self.tree, value.expression);
        const owner_type = owner_annotation.type_ref orelse return error.InvalidAst;
        const annotation = try memberAccessAnnotation(self.tree, node);
        var resolved: ?ResolvedMember = null;

        switch (owner_type.payload) {
            .Struct => |structure| {
                for (structure.declaration.payload.struct_definition.members) |member| {
                    if (!std.mem.eql(u8, declarationName(member), value.member_name)) continue;
                    const raw_member_type = (try variableAnnotation(
                        self.tree,
                        member,
                    )).type_ref orelse return error.InvalidAst;
                    resolved = .{
                        .type_ref = try self.type_provider.withLocationIfReference(
                            structure.reference.location,
                            raw_member_type,
                            false,
                        ),
                        .declaration = member,
                        .is_lvalue = structure.reference.location != .CallData,
                        .is_pure = (try owner_annotation.is_pure.get()).*,
                    };
                    break;
                }
            },
            .Array => |array| resolved = try self.resolveArrayMember(
                node,
                owner_type,
                array,
                value.member_name,
                annotation.expression.arguments,
                (try owner_annotation.is_pure.get()).*,
            ),
            .FixedBytes => {
                if (std.mem.eql(u8, value.member_name, "length")) resolved = .{
                    .type_ref = try self.type_provider.uint(8),
                    .is_pure = (try owner_annotation.is_pure.get()).*,
                };
            },
            .Address => |address| resolved = try self.resolveAddressMember(
                value.member_name,
                address.state_mutability == .Payable,
            ),
            .Function => resolved = try self.resolveFunctionMember(
                owner_type,
                value.member_name,
            ),
            .Contract => |contract_type| resolved = try self.resolveContractMember(
                node,
                @constCast(contract_type.declaration),
                false,
                true,
            ),
            .TypeType => |type_type| resolved = try self.resolveTypeMember(
                node,
                type_type.actual_type,
            ),
            .Magic => |magic| resolved = try self.resolveMagicMember(
                magic,
                value.member_name,
            ),
            .Module => |module| resolved = try self.resolveModuleMember(
                module.source_unit,
                value.member_name,
            ),
            else => {},
        }
        if (resolved == null)
            resolved = try self.resolveAttachedMember(
                node,
                owner_type,
                value.member_name,
                annotation.expression.arguments,
                (try owner_annotation.is_pure.get()).*,
            );
        if (resolved == null) {
            if (owner_type.category() == .Contract and
                (std.mem.eql(u8, value.member_name, "balance") or
                    std.mem.eql(u8, value.member_name, "code") or
                    std.mem.eql(u8, value.member_name, "codehash")))
            {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Member \"{s}\" not found or not visible after argument-dependent lookup in {s}. Use \"address(...)\" to access this address member.",
                    .{ value.member_name, try self.typeNameTemporary(owner_type) },
                );
                defer self.allocator.free(message);
                try self.reporter.fatal(errorId(3125), .TypeError, node.location, null, message);
            }
            if (owner_type.asAddress() != null and
                owner_type.asAddress().?.state_mutability != .Payable and
                (std.mem.eql(u8, value.member_name, "send") or
                    std.mem.eql(u8, value.member_name, "transfer")))
            {
                const owner_name = try TypeBehavior.humanReadableNameAlloc(
                    self.allocator,
                    owner_type,
                );
                defer self.allocator.free(owner_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "\"send\" and \"transfer\" are only available for objects of type \"address payable\", not \"{s}\".",
                    .{owner_name},
                );
                defer self.allocator.free(message);
                try self.reporter.fatal(errorId(9862), .TypeError, node.location, null, message);
            }
            if (owner_type.asFunction()) |function_type| {
                if (std.mem.eql(u8, value.member_name, "value")) {
                    if (function_type.kind == .Creation) {
                        const result_name = if (function_type.return_parameter_types.len == 0)
                            "contract"
                        else
                            try self.typeNameTemporary(function_type.return_parameter_types[0]);
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "Constructor for {s} must be payable for member \"value\" to be available.",
                            .{result_name},
                        );
                        defer self.allocator.free(message);
                        try self.reporter.fatal(
                            errorId(8827),
                            .TypeError,
                            node.location,
                            null,
                            message,
                        );
                    } else if (function_type.kind == .DelegateCall or
                        function_type.kind == .BareDelegateCall)
                    {
                        try self.reporter.fatal(
                            errorId(8477),
                            .TypeError,
                            node.location,
                            null,
                            "Member \"value\" is not allowed in delegated calls due to \"msg.value\" persisting.",
                        );
                    } else {
                        try self.reporter.fatal(
                            errorId(8820),
                            .TypeError,
                            node.location,
                            null,
                            "Member \"value\" is only available for payable functions.",
                        );
                    }
                }
                if (function_type.return_parameter_types.len == 1 and
                    (function_type.return_parameter_types[0].category() == .Struct or
                        function_type.return_parameter_types[0].category() == .Contract))
                {
                    const owner_name = try TypeBehavior.humanReadableNameAlloc(
                        self.allocator,
                        owner_type,
                    );
                    defer self.allocator.free(owner_name);
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Member \"{s}\" not found or not visible after argument-dependent lookup in {s}. Did you intend to call the function?",
                        .{ value.member_name, owner_name },
                    );
                    defer self.allocator.free(message);
                    try self.reporter.fatal(errorId(6005), .TypeError, node.location, null, message);
                }
            }
            if (owner_type.asReference() != null and owner_type.category() != .ArraySlice) {
                const storage_type = try self.type_provider.withLocationIfReference(
                    .Storage,
                    owner_type,
                    true,
                );
                var storage_members = try TypeBehavior.nativeMembersAlloc(
                    self.type_provider,
                    self.allocator,
                    storage_type,
                    self.current_contract,
                );
                defer storage_members.deinit();
                for (storage_members.items) |storage_member|
                    if (std.mem.eql(u8, storage_member.name, value.member_name)) {
                        const owner_name = try TypeBehavior.humanReadableNameAlloc(
                            self.allocator,
                            owner_type,
                        );
                        defer self.allocator.free(owner_name);
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "Member \"{s}\" is not available in {s} outside of storage.",
                            .{ value.member_name, owner_name },
                        );
                        defer self.allocator.free(message);
                        try self.reporter.fatal(
                            errorId(4994),
                            .TypeError,
                            node.location,
                            null,
                            message,
                        );
                    };
            }
            const owner_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, owner_type);
            defer self.allocator.free(owner_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Member \"{s}\" not found or not visible after argument-dependent lookup in {s}.",
                .{ value.member_name, owner_name },
            );
            defer self.allocator.free(message);
            try self.reporter.fatal(errorId(9582), .TypeError, node.location, null, message);
        }
        const member = resolved.?;
        annotation.expression.type_ref = member.type_ref;
        annotation.referenced_declaration = member.declaration;
        try assignLookup(&annotation.required_lookup, member.lookup);
        try assignOnce(&annotation.expression.is_lvalue, member.is_lvalue);
        try assignOnce(&annotation.expression.is_pure, member.is_pure);
        try assignOnce(&annotation.expression.is_constant, false);
        if (member.type_ref.asFunction()) |member_function| {
            if (owner_type.asFunction() != null and member.declaration == null and
                (std.mem.eql(u8, value.member_name, "value") or
                    std.mem.eql(u8, value.member_name, "gas")))
            {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Using \".{s}(...)\" is deprecated. Use \"{{{s}: ...}}\" instead.",
                    .{ value.member_name, value.member_name },
                );
                defer self.allocator.free(message);
                try self.reporter.typeError(errorId(1621), node.location, message);
            }
            if (member_function.kind == .ArrayPush and
                annotation.expression.arguments != null and
                annotation.expression.arguments.?.types.items.len > 0 and
                containsNestedMapping(owner_type, 0))
                try self.reporter.typeError(
                    errorId(8871),
                    node.location,
                    "Storage arrays with nested mappings do not support .push(<arg>).",
                );
            switch (member_function.kind) {
                .Send => try self.reporter.warning(
                    errorId(9207),
                    node.location,
                    "'send' is deprecated and scheduled for removal. Use 'call{value: <amount>}(\"\")' instead.",
                ),
                .Transfer => try self.reporter.warning(
                    errorId(9207),
                    node.location,
                    "'transfer' is deprecated and scheduled for removal. Use 'call{value: <amount>}(\"\")' instead.",
                ),
                else => {},
            }
        }

        switch (owner_type.payload) {
            .Magic => |magic| switch (magic.kind) {
                .Block => {
                    if (std.mem.eql(u8, value.member_name, "chainid") and
                        !self.evm_version.hasChainID())
                        try self.reporter.typeError(
                            errorId(3081),
                            node.location,
                            "\"chainid\" is not supported by the VM version.",
                        )
                    else if (std.mem.eql(u8, value.member_name, "basefee") and
                        !self.evm_version.hasBaseFee())
                        try self.reporter.typeError(
                            errorId(5921),
                            node.location,
                            "\"basefee\" is not supported by the VM version.",
                        )
                    else if (std.mem.eql(u8, value.member_name, "blobbasefee") and
                        !self.evm_version.hasBlobBaseFee())
                        try self.reporter.typeError(
                            errorId(1006),
                            node.location,
                            "\"blobbasefee\" is not supported by the VM version.",
                        )
                    else if (std.mem.eql(u8, value.member_name, "prevrandao") and
                        !self.evm_version.hasPrevRandao())
                        try self.reporter.warning(
                            errorId(9432),
                            node.location,
                            "\"prevrandao\" is not supported by the VM version and will be treated as \"difficulty\".",
                        )
                    else if (std.mem.eql(u8, value.member_name, "difficulty") and
                        self.evm_version.hasPrevRandao())
                        try self.reporter.warning(
                            errorId(8417),
                            node.location,
                            "Since the VM version paris, \"difficulty\" was replaced by \"prevrandao\", which now returns a random number based on the beacon chain.",
                        );
                },
                .MetaType => if (std.mem.eql(u8, value.member_name, "runtimeCode")) {
                    const contract_type = switch ((magic.type_argument orelse
                        return error.InvalidAst).payload) {
                        .Contract => |present| present,
                        else => return error.InvalidAst,
                    };
                    const immutables = try TypeBehavior.immutableVariablesAlloc(
                        self.allocator,
                        contract_type,
                    );
                    defer self.allocator.free(immutables);
                    if (immutables.len != 0)
                        try self.reporter.typeError(
                            errorId(9274),
                            node.location,
                            "\"runtimeCode\" is not available for contracts containing immutable variables.",
                        );
                },
                else => {},
            },
            .Address => if (std.mem.eql(u8, value.member_name, "codehash") and
                !self.evm_version.hasExtCodeHash())
                try self.reporter.typeError(
                    errorId(7598),
                    node.location,
                    "\"codehash\" is not supported by the VM version.",
                ),
            else => {},
        }
    }

    fn resolveArrayMember(
        self: *TypeChecker,
        node: *AST.Node,
        owner_type: *const Types.Type,
        array: Types.ArrayType,
        name: []const u8,
        arguments: ?@import("../ast/ast_enums.zig").FuncCallArguments,
        owner_pure: bool,
    ) CheckError!?ResolvedMember {
        if (std.mem.eql(u8, name, "length"))
            return .{
                .type_ref = self.type_provider.uint256(),
                .is_pure = owner_pure,
            };
        if (array.reference.location != .Storage or array.length != null) return null;
        const self_pointer = try self.type_provider.withLocation(
            owner_type,
            .Storage,
            true,
        );
        if (std.mem.eql(u8, name, "pop")) {
            const unbound = try self.type_provider.function(
                &.{self_pointer},
                &.{},
                &.{""},
                &.{},
                .ArrayPop,
                .NonPayable,
                null,
                .{},
            );
            return .{
                .type_ref = try self.type_provider.withBoundFirstArgument(unbound),
                .is_pure = false,
            };
        }
        if (!std.mem.eql(u8, name, "push")) return null;
        const argument_count = if (arguments) |value| value.types.items.len else 0;
        if (argument_count == 0) {
            const returns = [_]*const Types.Type{array.base_type};
            const return_names = [_][]const u8{""};
            const unbound = try self.type_provider.function(
                &.{self_pointer},
                &returns,
                &.{""},
                &return_names,
                .ArrayPush,
                .NonPayable,
                null,
                .{},
            );
            return .{
                .type_ref = try self.type_provider.withBoundFirstArgument(unbound),
                .is_pure = false,
            };
        }
        const parameters = [_]*const Types.Type{ self_pointer, array.base_type };
        const parameter_names = [_][]const u8{ "", "" };
        const unbound = try self.type_provider.function(
            &parameters,
            &.{},
            &parameter_names,
            &.{},
            .ArrayPush,
            .NonPayable,
            null,
            .{},
        );
        _ = node;
        return .{
            .type_ref = try self.type_provider.withBoundFirstArgument(unbound),
            .is_pure = false,
        };
    }

    fn resolveAddressMember(
        self: *TypeChecker,
        name: []const u8,
        payable: bool,
    ) CheckError!?ResolvedMember {
        if (std.mem.eql(u8, name, "balance"))
            return .{ .type_ref = self.type_provider.uint256(), .is_pure = false };
        if (std.mem.eql(u8, name, "code"))
            return .{ .type_ref = self.type_provider.bytesMemory(), .is_pure = false };
        if (std.mem.eql(u8, name, "codehash"))
            return .{ .type_ref = try self.type_provider.fixedBytes(32), .is_pure = false };
        if (std.mem.eql(u8, name, "send") or std.mem.eql(u8, name, "transfer")) {
            if (!payable) return null;
            const parameters = [_]*const Types.Type{self.type_provider.uint256()};
            const parameter_names = [_][]const u8{""};
            const returns = if (std.mem.eql(u8, name, "send"))
                &[_]*const Types.Type{self.type_provider.boolean()}
            else
                &[_]*const Types.Type{};
            const return_names = if (returns.len == 1)
                &[_][]const u8{""}
            else
                &[_][]const u8{};
            return .{
                .type_ref = try self.type_provider.function(
                    &parameters,
                    returns,
                    &parameter_names,
                    return_names,
                    if (std.mem.eql(u8, name, "send")) .Send else .Transfer,
                    .NonPayable,
                    null,
                    .{},
                ),
                .is_pure = false,
            };
        }
        const kind: ?Types.FunctionKind = if (std.mem.eql(u8, name, "call"))
            .BareCall
        else if (std.mem.eql(u8, name, "callcode"))
            .BareCallCode
        else if (std.mem.eql(u8, name, "delegatecall"))
            .BareDelegateCall
        else if (std.mem.eql(u8, name, "staticcall"))
            .BareStaticCall
        else
            null;
        if (kind) |present| {
            const parameters = [_]*const Types.Type{self.type_provider.bytesMemory()};
            const returns = [_]*const Types.Type{
                self.type_provider.boolean(),
                self.type_provider.bytesMemory(),
            };
            const parameter_names = [_][]const u8{""};
            const return_names = [_][]const u8{ "", "" };
            return .{
                .type_ref = try self.type_provider.function(
                    &parameters,
                    &returns,
                    &parameter_names,
                    &return_names,
                    present,
                    if (present == .BareCall or present == .BareCallCode)
                        .Payable
                    else if (present == .BareStaticCall)
                        .View
                    else
                        .NonPayable,
                    null,
                    .{},
                ),
                .is_pure = false,
            };
        }
        return null;
    }

    fn resolveFunctionMember(
        self: *TypeChecker,
        owner_type: *const Types.Type,
        name: []const u8,
    ) CheckError!?ResolvedMember {
        const function = owner_type.asFunction() orelse return null;
        if (std.mem.eql(u8, name, "selector"))
            return .{
                .type_ref = try self.type_provider.fixedBytes(
                    if (function.kind == .Event) 32 else 4,
                ),
                .is_pure = function.declaration != null,
            };
        if (std.mem.eql(u8, name, "address") and function.kind == .External)
            return .{ .type_ref = self.type_provider.address(), .is_pure = false };
        if (std.mem.eql(u8, name, "value") and
            function.kind != .BareDelegateCall and
            function.state_mutability == .Payable)
        {
            const value_set = try self.type_provider.copyAndSetCallOptions(
                owner_type,
                false,
                true,
                false,
            );
            const names = [_][]const u8{""};
            return .{
                .type_ref = try self.type_provider.function(
                    &.{self.type_provider.uint256()},
                    &.{value_set},
                    &names,
                    &names,
                    .SetValue,
                    .Pure,
                    null,
                    function.options,
                ),
                .is_pure = false,
            };
        }
        if (std.mem.eql(u8, name, "gas") and function.kind != .Creation) {
            const gas_set = try self.type_provider.copyAndSetCallOptions(
                owner_type,
                true,
                false,
                false,
            );
            const names = [_][]const u8{""};
            return .{
                .type_ref = try self.type_provider.function(
                    &.{self.type_provider.uint256()},
                    &.{gas_set},
                    &names,
                    &names,
                    .SetGas,
                    .Pure,
                    null,
                    function.options,
                ),
                .is_pure = false,
            };
        }
        return null;
    }

    fn resolveContractMember(
        self: *TypeChecker,
        member_access: *AST.Node,
        contract: *AST.Node,
        super_lookup: bool,
        external: bool,
    ) CheckError!?ResolvedMember {
        const name = member_access.payload.member_access.member_name;
        const member_annotation = try memberAccessAnnotation(self.tree, member_access);
        const annotation = try contractDefinitionAnnotation(self.tree, contract);
        var candidates: std.ArrayList(*AST.Node) = .empty;
        defer candidates.deinit(self.allocator);
        for (annotation.linearized_base_contracts) |base| {
            // `super.f` starts lookup after the current contract. Keeping the
            // current override here resolves back to itself and changes both
            // the referenced declaration and virtual-dispatch semantics.
            if (super_lookup and base == contract) continue;
            for (base.payload.contract_definition.sub_nodes) |candidate| {
                if (!std.mem.eql(u8, declarationName(candidate), name)) continue;
                const visible = switch (candidate.payload) {
                    .function_definition => |function| function.kind == .Function and
                        if (external)
                            ASTImplementation.isPublic(candidate)
                        else
                            ASTImplementation.isVisibleInDerivedContracts(candidate),
                    .variable_declaration => external and ASTImplementation.isStateVariable(candidate) and
                        ASTImplementation.isPublic(candidate),
                    else => false,
                };
                if (!visible) continue;
                var duplicate = false;
                for (candidates.items) |present| {
                    const equal_parameters = if (external) blk: {
                        const present_type = try self.contractMemberType(present, true);
                        const candidate_type = try self.contractMemberType(candidate, true);
                        const present_function = present_type.asFunction() orelse
                            return error.InvalidAst;
                        const candidate_function = candidate_type.asFunction() orelse
                            return error.InvalidAst;
                        break :blk TypeBehavior.functionHasEqualParameterTypes(
                            present_function.*,
                            candidate_function.*,
                        );
                    } else try declarationsHaveEqualParameters(self.tree, present, candidate);
                    if (equal_parameters) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate) try candidates.append(self.allocator, candidate);
            }
        }
        if (member_annotation.expression.arguments) |*arguments| {
            var write_index: usize = 0;
            for (candidates.items) |candidate| {
                const type_ref = try self.contractMemberType(candidate, external);
                if (functionTypeCanTakeArguments(type_ref, arguments, null)) {
                    candidates.items[write_index] = candidate;
                    write_index += 1;
                }
            }
            candidates.shrinkRetainingCapacity(write_index);
        }
        if (candidates.items.len == 0) return null;
        if (candidates.items.len != 1) {
            const owner_name = contract.payload.contract_definition.declaration.name;
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Member \"{s}\" not unique after argument-dependent lookup in contract {s}.",
                .{ name, owner_name },
            );
            defer self.allocator.free(message);
            try self.reporter.fatal(errorId(6675), .TypeError, member_access.location, null, message);
        }
        const declaration = candidates.items[0];
        const type_ref = try self.contractMemberType(declaration, external);
        return .{
            .type_ref = type_ref,
            .declaration = declaration,
            .lookup = if (super_lookup) .Super else .Static,
            .is_lvalue = declaration.nodeKind() == .variable_declaration and !external,
            .is_pure = declaration.nodeKind() == .variable_declaration and
                declaration.payload.variable_declaration.mutability == .Constant,
        };
    }

    fn contractMemberType(
        self: *TypeChecker,
        declaration: *AST.Node,
        external: bool,
    ) CheckError!*const Types.Type {
        return switch (declaration.nodeKind()) {
            .function_definition => if (external) blk: {
                const raw = try self.callableType(declaration, .External);
                const function = raw.asFunction() orelse return error.InvalidAst;
                break :blk TypeBehavior.asExternallyCallableFunction(
                    self.type_provider,
                    function.*,
                    false,
                );
            } else self.callableType(declaration, .Internal),
            .variable_declaration => if (external) blk: {
                const raw = try self.publicGetterType(declaration);
                const function = raw.asFunction() orelse return error.InvalidAst;
                break :blk TypeBehavior.asExternallyCallableFunction(
                    self.type_provider,
                    function.*,
                    false,
                );
            } else (try variableAnnotation(self.tree, declaration)).type_ref orelse
                error.InvalidAst,
            else => error.InvalidAst,
        };
    }

    fn publicGetterType(
        self: *TypeChecker,
        variable: *AST.Node,
    ) CheckError!*const Types.Type {
        return self.type_provider.functionFromVariable(variable);
    }

    fn resolveTypeMember(
        self: *TypeChecker,
        member_access: *AST.Node,
        actual_type: *const Types.Type,
    ) CheckError!?ResolvedMember {
        const name = member_access.payload.member_access.member_name;
        switch (actual_type.payload) {
            .Contract => |contract_type| {
                if (contract_type.is_super)
                    return self.resolveContractMember(
                        member_access,
                        @constCast(contract_type.declaration),
                        true,
                        false,
                    );
                const meta_type = try self.type_provider.typeType(actual_type);
                var members = try TypeBehavior.nativeMembersAlloc(
                    self.type_provider,
                    self.allocator,
                    meta_type,
                    self.current_contract,
                );
                defer members.deinit();
                const annotation = try memberAccessAnnotation(self.tree, member_access);
                var selected: ?Types.Member = null;
                for (members.items) |member| {
                    if (!std.mem.eql(u8, member.name, name)) continue;
                    if (annotation.expression.arguments) |*arguments|
                        if (member.type_ref.category() == .Function and
                            !functionTypeCanTakeArguments(
                                member.type_ref,
                                arguments,
                                null,
                            )) continue;
                    if (selected != null) {
                        const owner = contract_type.declaration.payload.contract_definition.declaration.name;
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "Member \"{s}\" not unique after argument-dependent lookup in contract {s}.",
                            .{ name, owner },
                        );
                        defer self.allocator.free(message);
                        try self.reporter.fatal(
                            errorId(6675),
                            .TypeError,
                            member_access.location,
                            null,
                            message,
                        );
                    }
                    selected = member;
                }
                if (selected) |member| return .{
                    .type_ref = member.type_ref,
                    .declaration = member.declaration,
                    .lookup = .Static,
                    .is_pure = true,
                };
            },
            .Enum => |enum_type| {
                for (enum_type.declaration.payload.enum_definition.members) |member|
                    if (std.mem.eql(u8, declarationName(member), name))
                        return .{
                            .type_ref = actual_type,
                            .declaration = member,
                            .is_pure = true,
                        };
            },
            .UserDefinedValueType => |user_type| {
                const underlying = user_type.underlying_type orelse return error.InvalidAst;
                const parameter_names = [_][]const u8{""};
                if (std.mem.eql(u8, name, "wrap")) {
                    const parameters = [_]*const Types.Type{underlying};
                    const returns = [_]*const Types.Type{actual_type};
                    return .{
                        .type_ref = try self.type_provider.function(
                            &parameters,
                            &returns,
                            &parameter_names,
                            &parameter_names,
                            .Wrap,
                            .Pure,
                            user_type.declaration,
                            .{},
                        ),
                        .is_pure = true,
                    };
                }
                if (std.mem.eql(u8, name, "unwrap")) {
                    const parameters = [_]*const Types.Type{actual_type};
                    const returns = [_]*const Types.Type{underlying};
                    return .{
                        .type_ref = try self.type_provider.function(
                            &parameters,
                            &returns,
                            &parameter_names,
                            &parameter_names,
                            .Unwrap,
                            .Pure,
                            user_type.declaration,
                            .{},
                        ),
                        .is_pure = true,
                    };
                }
            },
            .Integer => if (std.mem.eql(u8, name, "min") or std.mem.eql(u8, name, "max"))
                return .{ .type_ref = actual_type, .is_pure = true },
            .Array => |array| if (array.kind != .Ordinary and std.mem.eql(u8, name, "concat")) {
                const returns = [_]*const Types.Type{try self.type_provider.withLocationIfReference(
                    .Memory,
                    actual_type,
                    true,
                )};
                const return_names = [_][]const u8{""};
                return .{
                    .type_ref = try self.type_provider.function(
                        &.{},
                        &returns,
                        &.{},
                        &return_names,
                        if (array.kind == .String) .StringConcat else .BytesConcat,
                        .Pure,
                        null,
                        Types.FunctionOptions.withArbitraryParameters(),
                    ),
                    .is_pure = true,
                };
            },
            else => {},
        }
        return null;
    }

    fn resolveMagicMember(
        self: *TypeChecker,
        magic: Types.MagicType,
        name: []const u8,
    ) CheckError!?ResolvedMember {
        const kind = magic.kind;
        const type_ref: ?*const Types.Type = switch (kind) {
            .Block => if (std.mem.eql(u8, name, "coinbase"))
                self.type_provider.payableAddress()
            else if (std.mem.eql(u8, name, "blockhash")) blk: {
                const parameters = [_]*const Types.Type{self.type_provider.uint256()};
                const returns = [_]*const Types.Type{try self.type_provider.fixedBytes(32)};
                const names = [_][]const u8{""};
                break :blk try self.type_provider.function(
                    &parameters,
                    &returns,
                    &names,
                    &names,
                    .BlockHash,
                    .View,
                    null,
                    .{},
                );
            } else if (std.mem.eql(u8, name, "difficulty") or
                std.mem.eql(u8, name, "prevrandao") or
                std.mem.eql(u8, name, "gaslimit") or
                std.mem.eql(u8, name, "number") or
                std.mem.eql(u8, name, "timestamp") or
                std.mem.eql(u8, name, "basefee") or
                std.mem.eql(u8, name, "blobbasefee") or
                std.mem.eql(u8, name, "chainid"))
                self.type_provider.uint256()
            else
                null,
            .Message => if (std.mem.eql(u8, name, "sender"))
                self.type_provider.address()
            else if (std.mem.eql(u8, name, "gas") or std.mem.eql(u8, name, "value"))
                self.type_provider.uint256()
            else if (std.mem.eql(u8, name, "data"))
                self.type_provider.bytesCalldata()
            else if (std.mem.eql(u8, name, "sig"))
                try self.type_provider.fixedBytes(4)
            else
                null,
            .Transaction => if (std.mem.eql(u8, name, "gasprice"))
                self.type_provider.uint256()
            else if (std.mem.eql(u8, name, "origin"))
                self.type_provider.address()
            else
                null,
            .ABI => try self.abiMemberType(name),
            .MetaType => try self.metaTypeMember(magic.type_argument, name),
            .Error => null,
        };
        return if (type_ref) |present|
            .{ .type_ref = present, .is_pure = kind == .ABI or kind == .MetaType }
        else
            null;
    }

    fn abiMemberType(self: *TypeChecker, name: []const u8) CheckError!?*const Types.Type {
        const kind: Types.FunctionKind = if (std.mem.eql(u8, name, "encode"))
            .ABIEncode
        else if (std.mem.eql(u8, name, "encodePacked"))
            .ABIEncodePacked
        else if (std.mem.eql(u8, name, "encodeWithSelector"))
            .ABIEncodeWithSelector
        else if (std.mem.eql(u8, name, "encodeCall"))
            .ABIEncodeCall
        else if (std.mem.eql(u8, name, "encodeWithSignature"))
            .ABIEncodeWithSignature
        else if (std.mem.eql(u8, name, "decode"))
            .ABIDecode
        else
            return null;
        const returns = if (kind == .ABIDecode)
            &[_]*const Types.Type{}
        else
            &[_]*const Types.Type{self.type_provider.bytesMemory()};
        const return_names = if (returns.len == 0)
            &[_][]const u8{}
        else
            &[_][]const u8{""};
        const parameters = if (kind == .ABIEncodeWithSelector)
            &[_]*const Types.Type{try self.type_provider.fixedBytes(4)}
        else if (kind == .ABIEncodeWithSignature)
            &[_]*const Types.Type{self.type_provider.stringMemory()}
        else
            &[_]*const Types.Type{};
        const parameter_names = if (parameters.len == 0)
            &[_][]const u8{}
        else
            &[_][]const u8{""};
        return try self.type_provider.function(
            parameters,
            returns,
            parameter_names,
            return_names,
            kind,
            .Pure,
            null,
            Types.FunctionOptions.withArbitraryParameters(),
        );
    }

    fn metaTypeMember(
        self: *TypeChecker,
        type_argument: ?*const Types.Type,
        name: []const u8,
    ) CheckError!?*const Types.Type {
        const actual_type = type_argument orelse return error.InvalidAst;
        return switch (actual_type.payload) {
            .Contract => |contract_type| blk: {
                const contract = contract_type.declaration.payload.contract_definition;
                if (std.mem.eql(u8, name, "name")) break :blk self.type_provider.stringMemory();
                if (contract.contract_kind == .Interface or contract.abstract) {
                    if (std.mem.eql(u8, name, "interfaceId"))
                        break :blk try self.type_provider.fixedBytes(4);
                } else if (std.mem.eql(u8, name, "creationCode") or
                    std.mem.eql(u8, name, "runtimeCode"))
                    break :blk self.type_provider.bytesMemory();
                break :blk null;
            },
            .Integer, .Enum => if (std.mem.eql(u8, name, "min") or
                std.mem.eql(u8, name, "max"))
                actual_type
            else
                null,
            else => null,
        };
    }

    fn resolveModuleMember(
        self: *TypeChecker,
        source_unit: *const AST.Node,
        name: []const u8,
    ) CheckError!?ResolvedMember {
        const annotation = ASTAnnotations.annotationConst(source_unit) orelse return error.InvalidAst;
        const exports = switch (annotation.*) {
            .source_unit => |*value| try value.exported_symbols.get(),
            else => return error.InvalidAst,
        };
        for (exports.*) |symbol| {
            if (!std.mem.eql(u8, symbol.name, name) or symbol.declarations.len != 1) continue;
            const declaration = symbol.declarations[0];
            return .{
                .type_ref = try self.declarationType(declaration),
                .declaration = declaration,
                .is_pure = true,
            };
        }
        return null;
    }

    fn resolveAttachedMember(
        self: *TypeChecker,
        member_access: *AST.Node,
        owner_type: *const Types.Type,
        name: []const u8,
        arguments: ?@import("../ast/ast_enums.zig").FuncCallArguments,
        owner_pure: bool,
    ) CheckError!?ResolvedMember {
        var directives: std.ArrayList(*AST.Node) = .empty;
        defer directives.deinit(self.allocator);
        if (self.current_contract) |contract|
            for (contract.payload.contract_definition.sub_nodes) |candidate|
                if (candidate.nodeKind() == .using_for_directive)
                    try directives.append(self.allocator, candidate);
        if (self.current_source_unit) |source_unit|
            for (source_unit.payload.source_unit.nodes) |candidate|
                if (candidate.nodeKind() == .using_for_directive)
                    try directives.append(self.allocator, candidate);
        // A global directive follows its user-defined type into every source
        // unit that imports that type. It is declared beside the type rather
        // than in the source currently being checked.
        if (TypeBehavior.typeDefinition(owner_type)) |definition|
            if (ASTImplementation.scope(definition)) |definition_scope|
                if (definition_scope.nodeKind() == .source_unit)
                    for (definition_scope.payload.source_unit.nodes) |candidate|
                        if (candidate.nodeKind() == .using_for_directive and
                            candidate.payload.using_for_directive.global and
                            candidate.payload.using_for_directive.type_name != null)
                            try directives.append(self.allocator, candidate);

        var declarations: std.ArrayList(*AST.Node) = .empty;
        defer declarations.deinit(self.allocator);
        for (directives.items) |directive_node| {
            const directive = directive_node.payload.using_for_directive;
            if (!(try self.usingDirectiveApplies(directive, owner_type))) continue;
            if (directive.uses_braces) {
                for (directive.functions_and_operators) |entry| {
                    if (entry.operator != null) continue;
                    const declaration = try referencedDeclarationForName(
                        self.tree,
                        entry.function_or_library,
                    );
                    if (declaration.nodeKind() != .function_definition or
                        !std.mem.eql(u8, declarationName(declaration), name)) continue;
                    if (!containsMutableNode(declarations.items, declaration))
                        try declarations.append(self.allocator, declaration);
                }
            } else if (directive.functions_and_operators.len != 0) {
                const library = try referencedDeclarationForName(
                    self.tree,
                    directive.functions_and_operators[0].function_or_library,
                );
                if (library.nodeKind() != .contract_definition) continue;
                for (library.payload.contract_definition.sub_nodes) |declaration| {
                    if (declaration.nodeKind() != .function_definition or
                        !std.mem.eql(u8, declarationName(declaration), name)) continue;
                    const visibility = ASTImplementation.effectiveVisibility(declaration) orelse
                        continue;
                    if (visibility == .Private) continue;
                    if (!containsMutableNode(declarations.items, declaration))
                        try declarations.append(self.allocator, declaration);
                }
            }
        }
        if (declarations.items.len == 0) return null;

        var matches: std.ArrayList(struct {
            declaration: *AST.Node,
            type_ref: *const Types.Type,
        }) = .empty;
        defer matches.deinit(self.allocator);
        for (declarations.items) |declaration| {
            const type_ref = try self.attachedFunctionType(declaration);
            const function = type_ref.asFunction() orelse return error.InvalidAst;
            const self_type = function.selfType() orelse return error.InvalidAst;
            // Directive applicability ignores location, but binding and call
            // compatibility must use the actual receiver (not a storage copy).
            if (!TypeBehavior.isImplicitlyConvertibleTo(owner_type, self_type)) continue;
            if (arguments) |*call_arguments|
                if (!functionTypeCanTakeArguments(
                    type_ref,
                    call_arguments,
                    owner_type,
                )) continue;
            try matches.append(self.allocator, .{
                .declaration = declaration,
                .type_ref = type_ref,
            });
        }
        if (matches.items.len == 0) return null;
        if (matches.items.len != 1) {
            const owner_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, owner_type);
            defer self.allocator.free(owner_name);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Member \"{s}\" not unique after argument-dependent lookup in {s}.",
                .{ name, owner_name },
            );
            defer self.allocator.free(message);
            try self.reporter.fatal(
                errorId(6675),
                .TypeError,
                member_access.location,
                null,
                message,
            );
        }
        return .{
            .type_ref = matches.items[0].type_ref,
            .declaration = matches.items[0].declaration,
            .is_pure = owner_pure,
        };
    }

    fn usingDirectiveApplies(
        self: *TypeChecker,
        directive: AST.UsingForDirective,
        owner_type: *const Types.Type,
    ) CheckError!bool {
        const type_name = directive.type_name orelse return true;
        const attached_type = (try typeNameAnnotation(self.tree, type_name)).type_ref orelse
            return error.InvalidAst;
        const normalized_owner = try self.type_provider.withLocationIfReference(
            .Storage,
            owner_type,
            true,
        );
        const normalized_attached = try self.type_provider.withLocationIfReference(
            .Storage,
            attached_type,
            true,
        );
        return TypeBehavior.equals(normalized_owner, normalized_attached);
    }

    fn attachedFunctionType(
        self: *TypeChecker,
        declaration: *AST.Node,
    ) CheckError!*const Types.Type {
        const function = declaration.payload.function_definition;
        const parameters = try self.parameterTypesAndNames(function.callable.parameters);
        defer self.allocator.free(parameters.types);
        defer self.allocator.free(parameters.names);
        if (parameters.types.len == 0) return error.InvalidAst;
        const returns = if (function.callable.return_parameters) |return_parameters|
            try self.parameterTypesAndNames(return_parameters)
        else
            ParameterTypesAndNames{ .types = &.{}, .names = &.{} };
        defer if (function.callable.return_parameters != null) {
            self.allocator.free(returns.types);
            self.allocator.free(returns.names);
        };
        const scope = ASTImplementation.scope(declaration);
        const library_function = scope != null and
            scope.?.nodeKind() == .contract_definition and
            scope.?.payload.contract_definition.contract_kind == .Library;
        const visibility = ASTImplementation.effectiveVisibility(declaration) orelse
            return error.InvalidAst;
        return self.type_provider.function(
            parameters.types,
            returns.types,
            parameters.names,
            returns.names,
            if (library_function and (visibility == .Public or visibility == .External))
                .DelegateCall
            else
                .Internal,
            function.state_mutability,
            declaration,
            .{ .has_bound_first_argument = true },
        );
    }

    fn typeNameTemporary(
        self: *TypeChecker,
        type_ref: *const Types.Type,
    ) CheckError![]const u8 {
        const value = try TypeBehavior.humanReadableNameAlloc(self.allocator, type_ref);
        defer self.allocator.free(value);
        return try self.tree.ownString(value);
    }

    fn visitIndexAccess(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.index_access;
        try self.checkExpression(value.base, depth + 1);
        const base_annotation = try expressionAnnotation(self.tree, value.base);
        var base_type = base_annotation.type_ref orelse return error.InvalidAst;
        const annotation = try expressionAnnotation(self.tree, node);
        var result_type: *const Types.Type = self.type_provider.emptyTuple();
        var is_lvalue = false;
        var pure = (try base_annotation.is_pure.get()).*;

        if (base_type.category() == .ArraySlice) {
            const slice_array = base_type.payload.ArraySlice.array_type;
            const array = slice_array.asArray() orelse return error.InvalidAst;
            if (array.reference.location != .CallData or !array.isDynamicallySized())
                try self.reporter.typeError(
                    errorId(4802),
                    node.location,
                    "Index access is only implemented for slices of dynamic calldata arrays.",
                );
            base_type = base_type.payload.ArraySlice.array_type;
        }
        switch (base_type.payload) {
            .Array => |array| {
                if (value.index == null) {
                    try self.reporter.typeError(
                        errorId(9689),
                        node.location,
                        "Index expression cannot be omitted.",
                    );
                } else if (array.kind == .String) {
                    try self.checkExpression(value.index.?, depth + 1);
                    try self.reporter.typeError(
                        errorId(9961),
                        node.location,
                        "Index access for string is not possible.",
                    );
                } else {
                    try self.checkExpression(value.index.?, depth + 1);
                    _ = try self.expectTypeAlready(value.index.?, self.type_provider.uint256());
                    if (array.length) |length|
                        if (try rationalValueU256(self.allocator, (try expressionAnnotation(
                            self.tree,
                            value.index.?,
                        )).type_ref)) |index_value|
                            if (index_value >= length)
                                try self.reporter.typeError(
                                    errorId(3383),
                                    node.location,
                                    "Out of bounds array access.",
                                );
                }
                result_type = array.base_type;
                is_lvalue = array.reference.location != .CallData;
            },
            .Mapping => |mapping| {
                if (value.index == null) {
                    try self.reporter.typeError(
                        errorId(1267),
                        node.location,
                        "Index expression cannot be omitted.",
                    );
                } else {
                    try self.checkExpression(value.index.?, depth + 1);
                    _ = try self.expectTypeAlready(value.index.?, mapping.key_type);
                }
                result_type = mapping.value_type;
                is_lvalue = true;
            },
            .TypeType => |type_type| {
                if (type_type.actual_type.category() == .Contract and
                    type_type.actual_type.payload.Contract.declaration
                        .payload.contract_definition.contract_kind == .Library)
                    try self.reporter.typeError(
                        errorId(2876),
                        node.location,
                        "Index access for library types and arrays of libraries are not possible.",
                    );
                var length: ?u256 = null;
                if (value.index) |index| {
                    try self.checkExpression(index, depth + 1);
                    _ = try self.expectTypeAlready(index, self.type_provider.uint256());
                    length = try rationalValueU256(
                        self.allocator,
                        (try expressionAnnotation(self.tree, index)).type_ref,
                    ) orelse {
                        try self.reporter.fatal(
                            errorId(3940),
                            .TypeError,
                            index.location,
                            null,
                            "Integer constant expected.",
                        );
                        unreachable;
                    };
                }
                result_type = try self.type_provider.typeType(
                    try self.type_provider.arrayWithLength(
                        .Memory,
                        type_type.actual_type,
                        length,
                    ),
                );
            },
            .FixedBytes => |fixed_bytes| {
                if (value.index == null) {
                    try self.reporter.typeError(
                        errorId(8830),
                        node.location,
                        "Index expression cannot be omitted.",
                    );
                } else {
                    try self.checkExpression(value.index.?, depth + 1);
                    if (!(try self.expectTypeAlready(value.index.?, self.type_provider.uint256())))
                        try self.reporter.fatal(
                            errorId(6318),
                            .TypeError,
                            node.location,
                            null,
                            "Index expression cannot be represented as an unsigned integer.",
                        );
                    if (try rationalValueU256(self.allocator, (try expressionAnnotation(
                        self.tree,
                        value.index.?,
                    )).type_ref)) |index_value|
                        if (index_value >= fixed_bytes.bytes)
                            try self.reporter.typeError(
                                errorId(1859),
                                node.location,
                                "Out of bounds array access.",
                            );
                }
                result_type = try self.type_provider.fixedBytes(1);
            },
            else => {
                const type_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, base_type);
                defer self.allocator.free(type_name);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Indexed expression has to be a type, mapping or array (is {s})",
                    .{type_name},
                );
                defer self.allocator.free(message);
                try self.reporter.fatal(
                    errorId(2614),
                    .TypeError,
                    value.base.location,
                    null,
                    message,
                );
            },
        }
        if (value.index) |index|
            pure = pure and (try (try expressionAnnotation(self.tree, index)).is_pure.get()).*;
        annotation.type_ref = result_type;
        try assignOnce(&annotation.is_lvalue, is_lvalue);
        try assignOnce(&annotation.is_pure, pure);
        try assignOnce(&annotation.is_constant, false);
    }

    fn visitIndexRangeAccess(
        self: *TypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.index_range_access;
        try self.checkExpression(value.base, depth + 1);
        const base_annotation = try expressionAnnotation(self.tree, value.base);
        var pure = (try base_annotation.is_pure.get()).*;
        if (value.start) |start| {
            try self.checkExpression(start, depth + 1);
            _ = try self.expectTypeAlready(start, self.type_provider.uint256());
            pure = pure and (try (try expressionAnnotation(self.tree, start)).is_pure.get()).*;
        }
        if (value.end) |end| {
            try self.checkExpression(end, depth + 1);
            _ = try self.expectTypeAlready(end, self.type_provider.uint256());
            pure = pure and (try (try expressionAnnotation(self.tree, end)).is_pure.get()).*;
        }
        const expression_type = base_annotation.type_ref orelse return error.InvalidAst;
        const annotation = try expressionAnnotation(self.tree, node);
        if (expression_type.category() == .TypeType) {
            try self.reporter.typeError(
                errorId(1760),
                node.location,
                "Types cannot be sliced.",
            );
            annotation.type_ref = expression_type;
        } else {
            const array_type = switch (expression_type.payload) {
                .Array => expression_type,
                .ArraySlice => |slice| slice.array_type,
                else => {
                    try self.reporter.fatal(
                        errorId(4781),
                        .TypeError,
                        node.location,
                        null,
                        "Index range access is only possible for arrays and array slices.",
                    );
                    unreachable;
                },
            };
            const array = array_type.payload.Array;
            if (array.reference.location != .CallData or array.length != null)
                try self.reporter.typeError(
                    errorId(1227),
                    node.location,
                    "Index range access is only supported for dynamic calldata arrays.",
                )
            else if (TypeBehavior.isDynamicallyEncoded(array.base_type))
                try self.reporter.typeError(
                    errorId(2148),
                    node.location,
                    "Index range access is not supported for arrays with dynamically encoded base types.",
                );
            annotation.type_ref = try self.type_provider.arraySlice(array_type);
        }
        try assignOnce(&annotation.is_lvalue, false);
        try assignOnce(&annotation.is_pure, pure);
        try assignOnce(&annotation.is_constant, false);
    }

    fn endElementaryTypeNameExpression(
        self: *TypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const type_name = node.payload.elementary_type_name_expression.type_name;
        if (type_name.nodeKind() != .elementary_type_name) return error.InvalidAst;
        const elementary = type_name.payload.elementary_type_name;
        // `ElementaryTypeNameExpression::accept` is a leaf upstream. Its
        // checker constructs the type directly instead of relying on the
        // embedded type-name node having been visited first.
        const actual = try self.type_provider.fromElementaryTypeToken(
            elementary.type_name,
            elementary.state_mutability,
        );
        const annotation = try expressionAnnotation(self.tree, node);
        annotation.type_ref = try self.type_provider.typeType(actual);
        try assignOnce(&annotation.is_pure, true);
        try assignOnce(&annotation.is_lvalue, false);
        try assignOnce(&annotation.is_constant, false);
    }

    fn unsupportedExpression(
        self: *TypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const message = try std.fmt.allocPrint(
            self.allocator,
            "Zig port: Solidity type checking for {s} expressions is not implemented.",
            .{@tagName(node.nodeKind())},
        );
        defer self.allocator.free(message);
        try self.reporter.unimplementedFeatureError(errorId(0), node.location, message);
        const annotation = try expressionAnnotation(self.tree, node);
        annotation.type_ref = self.type_provider.emptyTuple();
        try assignOnce(&annotation.is_pure, false);
        try assignOnce(&annotation.is_lvalue, false);
        try assignOnce(&annotation.is_constant, false);
    }

    fn requireLValue(
        self: *TypeChecker,
        expression: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const annotation = try expressionAnnotation(self.tree, expression);
        annotation.will_be_written_to = true;
        try self.checkExpression(expression, depth);
        if ((try annotation.is_lvalue.get()).*) return;
        var id = errorId(4247);
        var description: []const u8 = "Expression has to be an lvalue.";
        if ((try annotation.is_constant.get()).*) {
            id = errorId(6520);
            description = "Cannot assign to a constant variable.";
        } else if (expression.nodeKind() == .index_access) {
            const base = expression.payload.index_access.base;
            const base_type = (try expressionAnnotation(self.tree, base)).type_ref orelse
                return error.InvalidAst;
            if (base_type.category() == .FixedBytes) {
                id = errorId(4360);
                description = "Single bytes in fixed bytes arrays cannot be modified.";
            } else if (base_type.category() == .Array and
                TypeBehavior.dataStoredIn(base_type, .CallData))
            {
                id = errorId(6182);
                description = "Calldata arrays are read-only.";
            }
        } else if (expression.nodeKind() == .member_access) {
            const member = expression.payload.member_access;
            const owner_type = (try expressionAnnotation(self.tree, member.expression)).type_ref orelse
                return error.InvalidAst;
            if (owner_type.category() == .Struct and
                TypeBehavior.dataStoredIn(owner_type, .CallData))
            {
                id = errorId(4156);
                description = "Calldata structs are read-only.";
            } else if (owner_type.category() == .Array and
                std.mem.eql(u8, member.member_name, "length"))
            {
                id = errorId(7567);
                description = "Member \"length\" is read-only and cannot be used to resize arrays.";
            }
        } else if (expression.nodeKind() == .identifier) {
            const identifier = try identifierAnnotation(self.tree, expression);
            if (identifier.referenced_declaration) |declaration|
                if (declaration.nodeKind() == .variable_declaration and
                    ASTImplementation.isExternalCallableParameter(declaration) and
                    annotation.type_ref != null and
                    annotation.type_ref.?.asReference() != null)
                {
                    id = errorId(7128);
                    description = "External function arguments of reference type are read-only.";
                };
        }
        try self.reporter.typeError(id, expression.location, description);
    }

    fn expectTypeAlready(
        self: *TypeChecker,
        expression: *AST.Node,
        expected: *const Types.Type,
    ) CheckError!bool {
        const actual = (try expressionAnnotation(
            self.tree,
            expression,
        )).type_ref orelse return error.InvalidAst;
        if (TypeBehavior.isImplicitlyConvertibleTo(actual, expected)) return true;
        const actual_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, actual);
        defer self.allocator.free(actual_name);
        const expected_name = try TypeBehavior.humanReadableNameAlloc(self.allocator, expected);
        defer self.allocator.free(expected_name);
        const base_message = try std.fmt.allocPrint(
            self.allocator,
            "Type {s} is not implicitly convertible to expected type {s}",
            .{ actual_name, expected_name },
        );
        defer self.allocator.free(base_message);
        if (actual.category() == .RationalNumber) {
            const rational = actual.payload.RationalNumber;
            const mobile = try TypeBehavior.mobileType(self.type_provider, actual);
            if (rational.denominator.compareUnsigned(1) != .eq and mobile != null) {
                if (TypeBehavior.equals(expected, mobile.?)) {
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "{s}, but it can be explicitly converted.",
                        .{base_message},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.typeError(errorId(4426), expression.location, message);
                } else {
                    const mobile_name = try TypeBehavior.humanReadableNameAlloc(
                        self.allocator,
                        mobile.?,
                    );
                    defer self.allocator.free(mobile_name);
                    const reason = implicitConversionReason(actual, expected);
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "{s}. Try converting to type {s} or use an explicit conversion.{s}{s}",
                        .{
                            base_message,
                            mobile_name,
                            if (reason != null) " " else "",
                            reason orelse "",
                        },
                    );
                    defer self.allocator.free(message);
                    try self.reporter.typeError(errorId(2326), expression.location, message);
                }
                return false;
            }
        }
        const reason = implicitConversionReason(actual, expected);
        const message = try std.fmt.allocPrint(
            self.allocator,
            "{s}.{s}{s}",
            .{
                base_message,
                if (reason != null) " " else "",
                reason orelse "",
            },
        );
        defer self.allocator.free(message);
        try self.reporter.typeError(errorId(7407), expression.location, message);
        return false;
    }

    fn endIdentifierPath(
        self: *TypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const annotation = try identifierPathAnnotation(self.tree, node);
        const declaration = annotation.referenced_declaration orelse return error.InvalidAst;
        try assignLookup(&annotation.required_lookup, if (isCallableDeclaration(declaration) and
            node.payload.identifier_path.path.len == 1)
            .Virtual
        else
            .Static);
    }

    fn useAbiCoderV2(self: *TypeChecker) CheckError!bool {
        const source_unit = self.current_source_unit orelse return error.InvalidAst;
        const annotation = ASTAnnotations.annotationConst(source_unit) orelse
            return error.InvalidAst;
        return switch (annotation.*) {
            .source_unit => |*value| (try value.use_abi_coder_v2.get()).*,
            else => error.InvalidAst,
        };
    }
};

fn identifierPathNameAlloc(
    allocator: std.mem.Allocator,
    node: *const AST.Node,
) std.mem.Allocator.Error![]u8 {
    return switch (node.payload) {
        .identifier_path => |path| std.mem.join(allocator, ".", path.path),
        .identifier => |identifier| allocator.dupe(u8, identifier.name),
        else => allocator.dupe(u8, declarationName(node)),
    };
}

fn requiredLookupForName(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!AST.VirtualLookup {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .identifier => |*value| (try value.required_lookup.get()).*,
        .identifier_path => |*value| (try value.required_lookup.get()).*,
        .member_access => |*value| (try value.required_lookup.get()).*,
        else => error.InvalidAst,
    };
}

fn interfaceTypeFailureReason(
    type_ref: *const Types.Type,
    in_library: bool,
) []const u8 {
    return interfaceTypeFailureReasonInner(type_ref, in_library, 0) orelse
        "Internal type is not allowed for public or external functions.";
}

fn interfaceTypeFailureReasonInner(
    type_ref: *const Types.Type,
    in_library: bool,
    depth: usize,
) ?[]const u8 {
    if (depth >= 256) return "Invalid type!";
    return switch (type_ref.payload) {
        .Array => |array| interfaceTypeFailureReasonInner(
            array.base_type,
            in_library,
            depth + 1,
        ),
        .Struct => |structure| blk: {
            const annotation = ASTAnnotations.annotationConst(structure.declaration) orelse
                break :blk "Invalid type!";
            const recursive = switch (annotation.*) {
                .struct_declaration => |value| value.recursive orelse false,
                else => break :blk "Invalid type!",
            };
            if (recursive) {
                if (!in_library)
                    break :blk "Recursive type not allowed for public or external contract functions.";
                if (structure.reference.location != .Storage)
                    break :blk "Recursive structs can only be passed as storage pointers to libraries, not as memory objects to contract functions.";
            }
            for (structure.declaration.payload.struct_definition.members) |member| {
                const member_annotation = ASTAnnotations.annotationConst(member) orelse
                    break :blk "Invalid type!";
                const member_type = switch (member_annotation.*) {
                    .variable_declaration => |value| value.type_ref orelse
                        break :blk "Invalid type!",
                    else => break :blk "Invalid type!",
                };
                if (interfaceTypeFailureReasonInner(
                    member_type,
                    in_library,
                    depth + 1,
                )) |reason| break :blk reason;
            }
            break :blk null;
        },
        .Function => |function| if (function.kind != .External)
            "Internal type is not allowed for public or external functions."
        else
            null,
        .Mapping => |mapping| if (!in_library)
            "Types containing (nested) mappings can only be parameters or return variables of internal or library functions."
        else
            interfaceTypeFailureReasonInner(mapping.value_type, true, depth + 1),
        .Contract => |contract| if (contract.is_super)
            "Internal type is not allowed for public or external functions."
        else
            null,
        else => null,
    };
}

fn validForLocationFailureReason(location: Types.DataLocation) []const u8 {
    return switch (location) {
        .Memory => "Type too large for memory.",
        .CallData => "Type too large for calldata.",
        .Storage => "Type too large for storage.",
        .Transient => "Transient data location is only supported for value types.",
    };
}

fn isUserDefinableOperator(operator: AST.Token) bool {
    return switch (operator) {
        .BitOr,
        .BitAnd,
        .BitXor,
        .BitNot,
        .Add,
        .Sub,
        .Mul,
        .Div,
        .Mod,
        .Equal,
        .NotEqual,
        .LessThan,
        .GreaterThan,
        .LessThanOrEqual,
        .GreaterThanOrEqual,
        => true,
        else => false,
    };
}

fn unaryOperatorFailureReason(
    operator: AST.Token,
    operand: *const Types.Type,
) ?[]const u8 {
    return switch (operand.payload) {
        .Integer => |integer| if (operator == .Sub and !integer.isSigned())
            "Unary negation is only allowed for signed integers."
        else
            null,
        else => null,
    };
}

fn isBareCallKind(kind: Types.FunctionKind) bool {
    return switch (kind) {
        .BareCall, .BareCallCode, .BareDelegateCall, .BareStaticCall => true,
        else => false,
    };
}

fn isHashFunctionKind(kind: Types.FunctionKind) bool {
    return switch (kind) {
        .KECCAK256, .SHA256, .RIPEMD160 => true,
        else => false,
    };
}

fn implicitConversionReason(
    actual: *const Types.Type,
    expected: *const Types.Type,
) ?[]const u8 {
    const source = actual.asFunction() orelse return null;
    const target = expected.asFunction() orelse return null;
    if (source.options.has_bound_first_argument != target.options.has_bound_first_argument)
        return "Attached functions cannot be converted into unattached functions.";
    if (source.kind != target.kind)
        return "Special functions cannot be converted to function types.";
    if (source.kind == .Declaration and source.declaration != target.declaration)
        return "Function declaration types referring to different functions cannot be converted to each other.";
    return null;
}

fn contractHierarchyContains(
    tree: *AST.Tree,
    contract: *const AST.Node,
    candidate: ?*const AST.Node,
) CheckError!bool {
    const target = candidate orelse return false;
    const annotation = try ASTAnnotations.ensure(tree, @constCast(contract));
    const contract_annotation = switch (annotation.*) {
        .contract_definition => |*value| value,
        else => return error.InvalidAst,
    };
    for (contract_annotation.linearized_base_contracts) |base|
        if (base == target) return true;
    return false;
}

const InlineAssemblyResolverContext = struct {
    checker: *TypeChecker,
    annotation: *ASTAnnotations.InlineAssemblyAnnotation,
    lvalue_access_to_memory_variable: bool = false,
    failure: ?CheckError = null,

    fn resolve(
        opaque_context: ?*anyopaque,
        identifier: *const YulAST.Identifier,
        identifier_context: YulAsmAnalysis.IdentifierContext,
        _: bool,
    ) bool {
        const self: *InlineAssemblyResolverContext = @ptrCast(@alignCast(opaque_context.?));
        if (self.failure != null) return false;
        return self.resolveIdentifier(identifier, identifier_context) catch |err| {
            self.failure = err;
            return false;
        };
    }

    fn resolveIdentifier(
        self: *InlineAssemblyResolverContext,
        identifier: *const YulAST.Identifier,
        identifier_context: YulAsmAnalysis.IdentifierContext,
    ) CheckError!bool {
        if (identifier_context == .non_external) {
            for (self.annotation.external_references.items, 0..) |reference, index|
                if (reference.identifier == identifier) {
                    _ = self.annotation.external_references.orderedRemove(index);
                    break;
                };
            return false;
        }

        const reference = for (self.annotation.external_references.items) |*candidate| {
            if (candidate.identifier == identifier) break candidate;
        } else return false;
        var declaration = reference.info.declaration orelse return error.InvalidAst;
        const location = yulIdentifierLocation(identifier);

        if (declaration.nodeKind() == .variable_declaration) {
            var type_ref = (try variableAnnotation(
                self.checker.tree,
                @constCast(declaration),
            )).type_ref orelse return error.InvalidAst;
            if (identifier_context == .l_value and
                TypeBehavior.dataStoredIn(type_ref, .Memory))
                self.lvalue_access_to_memory_variable = true;

            if (declaration.payload.variable_declaration.mutability == .Immutable) {
                try self.checker.reporter.typeError(
                    errorId(3773),
                    location,
                    "Assembly access to immutable variables is not supported.",
                );
                return false;
            }

            if (declaration.payload.variable_declaration.mutability == .Constant) {
                if (try ASTUtils.isConstantVariableRecursive(
                    self.checker.allocator,
                    declaration,
                )) {
                    try self.checker.reporter.typeError(
                        errorId(3558),
                        location,
                        "Constant variable is circular.",
                    );
                    return false;
                }
                declaration = (try ASTUtils.rootConstVariableDeclaration(
                    self.checker.allocator,
                    declaration,
                )) orelse {
                    try self.checker.reporter.typeError(
                        errorId(3224),
                        location,
                        "Constant has no value.",
                    );
                    return false;
                };
                const initializer = declaration.payload.variable_declaration.value orelse {
                    try self.checker.reporter.typeError(
                        errorId(3224),
                        location,
                        "Constant has no value.",
                    );
                    return false;
                };
                if (identifier_context == .l_value) {
                    try self.checker.reporter.typeError(
                        errorId(6252),
                        location,
                        "Constant variables cannot be assigned to.",
                    );
                    return false;
                }
                if (std.mem.eql(u8, reference.info.suffix, "slot") or
                    std.mem.eql(u8, reference.info.suffix, "offset"))
                {
                    try self.checker.reporter.typeError(
                        errorId(6617),
                        location,
                        "The suffixes .offset and .slot can only be used on non-constant storage or transient storage variables.",
                    );
                    return false;
                }
                const initializer_type = expressionTypeIfSet(initializer);
                if (initializer_type == null and initializer.nodeKind() != .literal) {
                    try self.checker.reporter.typeError(
                        errorId(2249),
                        location,
                        "Constant variables with non-literal values cannot be forward referenced from inline assembly.",
                    );
                    return false;
                }
                type_ref = (try variableAnnotation(
                    self.checker.tree,
                    @constCast(declaration),
                )).type_ref orelse return error.InvalidAst;
                if (!TypeBehavior.isValueType(type_ref) or
                    (initializer.nodeKind() != .literal and
                        (initializer_type == null or
                            initializer_type.?.category() != .RationalNumber)))
                {
                    try self.checker.reporter.typeError(
                        errorId(7615),
                        location,
                        "Only direct number constants and references to such constants are supported by inline assembly.",
                    );
                    return false;
                }
            }

            if (type_ref.category() == .FixedPoint) return error.InvalidAst;
            const suffix = reference.info.suffix;
            if (suffix.len != 0) {
                if (declaration.payload.variable_declaration.mutability != .Constant and
                    (ASTImplementation.isStateVariable(declaration) or
                        TypeBehavior.dataStoredIn(type_ref, .Storage)))
                {
                    if (!std.mem.eql(u8, suffix, "slot") and
                        !std.mem.eql(u8, suffix, "offset"))
                    {
                        try self.checker.reporter.typeError(
                            errorId(4656),
                            location,
                            "State variables only support \".slot\" and \".offset\".",
                        );
                        return false;
                    }
                    if (identifier_context == .l_value) {
                        if (ASTImplementation.isStateVariable(declaration)) {
                            try self.checker.reporter.typeError(
                                errorId(4713),
                                location,
                                "State variables cannot be assigned to - you have to use \"sstore()\" or \"tstore()\".",
                            );
                            return false;
                        }
                        if (!std.mem.eql(u8, suffix, "slot")) {
                            try self.checker.reporter.typeError(
                                errorId(9739),
                                location,
                                "Only .slot can be assigned to.",
                            );
                            return false;
                        }
                    }
                } else if (type_ref.asArray()) |array_type| {
                    if (!array_type.isDynamicallySized() or
                        !TypeBehavior.dataStoredIn(type_ref, .CallData))
                    {
                        try self.reportUnsupportedSuffix(identifier, suffix);
                        return false;
                    }
                    if (!std.mem.eql(u8, suffix, "offset") and
                        !std.mem.eql(u8, suffix, "length"))
                    {
                        try self.checker.reporter.typeError(
                            errorId(1536),
                            location,
                            "Calldata variables only support \".offset\" and \".length\".",
                        );
                        return false;
                    }
                } else if (type_ref.asFunction()) |function_type| {
                    if (!std.mem.eql(u8, suffix, "selector") and
                        !std.mem.eql(u8, suffix, "address"))
                    {
                        try self.checker.reporter.typeError(
                            errorId(9272),
                            location,
                            "Variables of type function pointer only support \".selector\" and \".address\".",
                        );
                        return false;
                    }
                    if (function_type.kind != .External) {
                        try self.checker.reporter.typeError(
                            errorId(8533),
                            location,
                            "Only Variables of type external function pointer support \".selector\" and \".address\".",
                        );
                        return false;
                    }
                } else {
                    try self.reportUnsupportedSuffix(identifier, suffix);
                    return false;
                }
            } else if (declaration.payload.variable_declaration.mutability != .Constant and
                ASTImplementation.isStateVariable(declaration))
            {
                try self.checker.reporter.typeError(
                    errorId(1408),
                    location,
                    "Only local variables are supported. To access state variables, use the \".slot\" and \".offset\" suffixes.",
                );
                return false;
            } else if (TypeBehavior.dataStoredIn(type_ref, .Storage)) {
                try self.checker.reporter.typeError(
                    errorId(9068),
                    location,
                    "You have to use the \".slot\" or \".offset\" suffix to access storage reference variables.",
                );
                return false;
            } else if (try TypeBehavior.sizeOnStack(type_ref) != 1) {
                if (type_ref.asArray()) |array_type| {
                    if (array_type.isDynamicallySized() and
                        TypeBehavior.dataStoredIn(type_ref, .CallData))
                    {
                        try self.checker.reporter.typeError(
                            errorId(1397),
                            location,
                            "Call data elements cannot be accessed directly. Use \".offset\" and \".length\" to access the calldata offset and length of this array and then use \"calldatacopy\".",
                        );
                        return false;
                    }
                }
                try self.checker.reporter.typeError(
                    errorId(9857),
                    location,
                    "Only types that use one stack slot are supported.",
                );
                return false;
            }
        } else if (reference.info.suffix.len != 0) {
            try self.checker.reporter.typeError(
                errorId(7944),
                location,
                "The suffixes \".offset\", \".slot\" and \".length\" can only be used with variables.",
            );
            return false;
        } else if (identifier_context == .l_value) {
            if (declaration.nodeKind() == .magic_variable_declaration) return false;
            try self.checker.reporter.typeError(
                errorId(1990),
                location,
                "Only local variables can be assigned to in inline assembly.",
            );
            return false;
        }

        if (identifier_context == .r_value) switch (declaration.nodeKind()) {
            .function_definition => {
                try self.checker.reporter.declarationError(
                    errorId(2025),
                    location,
                    "Access to functions is not allowed in inline assembly.",
                );
                return false;
            },
            .variable_declaration => {},
            .contract_definition => if (declaration.payload.contract_definition.contract_kind != .Library) {
                try self.checker.reporter.typeError(
                    errorId(4977),
                    location,
                    "Expected a library.",
                );
                return false;
            },
            else => return false,
        };

        reference.info.value_size = 1;
        return true;
    }

    fn reportUnsupportedSuffix(
        self: *InlineAssemblyResolverContext,
        identifier: *const YulAST.Identifier,
        suffix: []const u8,
    ) CheckError!void {
        const message = try std.fmt.allocPrint(
            self.checker.allocator,
            "The suffix \".{s}\" is not supported by this variable or type.",
            .{suffix},
        );
        defer self.checker.allocator.free(message);
        try self.checker.reporter.typeError(
            errorId(3622),
            yulIdentifierLocation(identifier),
            message,
        );
    }
};

fn yulIdentifierLocation(identifier: *const YulAST.Identifier) Diagnostics.SourceLocation {
    return if (identifier.debug_data) |debug_data| debug_data.native_location else .{};
}

fn expressionTypeIfSet(node: *const AST.Node) ?*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .expression => |value| value.type_ref,
        .identifier => |value| value.expression.type_ref,
        .member_access => |value| value.expression.type_ref,
        .operation => |value| value.expression.type_ref,
        .binary_operation => |value| value.operation.expression.type_ref,
        .function_call => |value| value.expression.type_ref,
        else => null,
    };
}

pub fn typeSupportedByOldABIEncoder(
    type_ref: *const Types.Type,
    is_library_call: bool,
) bool {
    if (is_library_call and TypeBehavior.dataStoredIn(type_ref, .Storage)) return true;
    if (type_ref.category() == .Struct) return false;
    if (type_ref.asArray()) |array| {
        if (!typeSupportedByOldABIEncoder(array.base_type, is_library_call)) return false;
        if (array.base_type.asArray()) |base_array|
            if (base_array.isDynamicallySized()) return false;
    }
    return true;
}

fn rationalValueU256(
    allocator: std.mem.Allocator,
    type_ref: ?*const Types.Type,
) std.mem.Allocator.Error!?u256 {
    const rational = (type_ref orelse return null).payload;
    const value = switch (rational) {
        .RationalNumber => |entry| entry,
        else => return null,
    };
    if (value.numerator.isNegative() or
        value.denominator.compareUnsigned(1) != .eq or
        value.numerator.bitLength() > 256) return null;
    const bytes = try value.numerator.toMagnitudeBigEndianAlloc(allocator);
    defer allocator.free(bytes);
    var result: u256 = 0;
    for (bytes) |byte| result = (result << 8) | @as(u256, byte);
    return result;
}

fn containsNestedMapping(type_ref: *const Types.Type, depth: usize) bool {
    if (depth >= 256) return true;
    return switch (type_ref.payload) {
        .Mapping => true,
        .Array => |value| containsNestedMapping(value.base_type, depth + 1),
        .Struct => |value| blk: {
            for (value.declaration.payload.struct_definition.members) |member| {
                const annotation = ASTAnnotations.annotationConst(member) orelse continue;
                const member_type = switch (annotation.*) {
                    .variable_declaration => |entry| entry.type_ref,
                    else => null,
                } orelse continue;
                if (containsNestedMapping(member_type, depth + 1)) break :blk true;
            }
            break :blk false;
        },
        else => false,
    };
}

fn findConstructor(contract: *const AST.Node) ?*AST.Node {
    if (contract.nodeKind() != .contract_definition) return null;
    for (contract.payload.contract_definition.sub_nodes) |member|
        if (member.nodeKind() == .function_definition and
            member.payload.function_definition.kind == .Constructor)
            return member;
    return null;
}

fn declarationIsLValue(declaration: *const AST.Node) bool {
    return declaration.nodeKind() == .variable_declaration and
        declaration.payload.variable_declaration.mutability != .Constant;
}

fn isPureIdentifierDeclaration(
    declaration: *const AST.Node,
    type_ref: *const Types.Type,
) bool {
    return (declaration.nodeKind() == .magic_variable_declaration and
        type_ref.category() == .Function) or
        type_ref.category() == .TypeType or
        type_ref.category() == .Module;
}

fn isCallableDeclaration(declaration: *const AST.Node) bool {
    return switch (declaration.nodeKind()) {
        .function_definition, .modifier_definition, .event_definition, .error_definition => true,
        else => false,
    };
}

fn callableData(node: *const AST.Node) ?AST.CallableData {
    return switch (node.payload) {
        .function_definition => |value| value.callable,
        .modifier_definition => |value| value.callable,
        .event_definition => |value| value.callable,
        .error_definition => |value| value.callable,
        else => null,
    };
}

fn stateMutabilityName(value: AST.StateMutability) []const u8 {
    return switch (value) {
        .Pure => "pure",
        .View => "view",
        .NonPayable => "nonpayable",
        .Payable => "payable",
    };
}

fn referencedDeclarationForName(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*AST.Node {
    return switch (node.payload) {
        .identifier_path => @constCast((try identifierPathAnnotation(
            tree,
            node,
        )).referenced_declaration orelse return error.InvalidAst),
        .identifier => @constCast((try identifierAnnotation(
            tree,
            node,
        )).referenced_declaration orelse return error.InvalidAst),
        .user_defined_type_name => |value| referencedDeclarationForName(tree, value.path_node),
        else => error.InvalidAst,
    };
}

fn declarationName(node: *const AST.Node) []const u8 {
    const declaration = node.declarationConst() orelse return "";
    return declaration.name;
}

fn containsConstNode(
    nodes: []const *const AST.Node,
    wanted: *const AST.Node,
) bool {
    for (nodes) |node|
        if (node == wanted) return true;
    return false;
}

fn containsMutableNode(nodes: []const *AST.Node, wanted: *const AST.Node) bool {
    for (nodes) |node|
        if (node == wanted) return true;
    return false;
}

fn declarationsHaveEqualParameters(
    tree: *AST.Tree,
    left: *const AST.Node,
    right: *const AST.Node,
) CheckError!bool {
    const left_callable = callableData(left);
    const right_callable = callableData(right);
    if (left_callable == null or right_callable == null) {
        if (left.nodeKind() != .variable_declaration or
            right.nodeKind() != .variable_declaration) return false;
        const left_type = (try variableAnnotation(tree, @constCast(left))).type_ref orelse
            return error.InvalidAst;
        const right_type = (try variableAnnotation(tree, @constCast(right))).type_ref orelse
            return error.InvalidAst;
        return TypeBehavior.equals(left_type, right_type);
    }
    const left_parameters = left_callable.?.parameters.payload.parameter_list.parameters;
    const right_parameters = right_callable.?.parameters.payload.parameter_list.parameters;
    if (left_parameters.len != right_parameters.len) return false;
    for (left_parameters, right_parameters) |left_parameter, right_parameter| {
        const left_type = (try variableAnnotation(tree, left_parameter)).type_ref orelse
            return error.InvalidAst;
        const right_type = (try variableAnnotation(tree, right_parameter)).type_ref orelse
            return error.InvalidAst;
        if (!TypeBehavior.equals(left_type, right_type)) return false;
    }
    return true;
}

fn functionTypeCanTakeArguments(
    type_ref: *const Types.Type,
    arguments: *const @import("../ast/ast_enums.zig").FuncCallArguments,
    self_type: ?*const Types.Type,
) bool {
    const function = type_ref.asFunction() orelse return false;
    return TypeBehavior.functionCanTakeArguments(function.*, arguments, self_type);
}

fn assignOnce(field: anytype, value: anytype) CheckError!void {
    if (field.isSet()) {
        if ((try field.get()).* != value) return error.BadSetOnceReassignment;
        return;
    }
    try field.assign(value);
}

fn assignLookup(
    field: *SetOnce.SetOnce(AST.VirtualLookup),
    value: AST.VirtualLookup,
) CheckError!void {
    return assignOnce(field, value);
}

fn expressionAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.ExpressionAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
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

fn variableAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.VariableDeclarationAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .variable_declaration => |*value| value,
        else => error.InvalidAst,
    };
}

fn typeNameAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.TypeNameAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .type_name => |*value| value,
        else => error.InvalidAst,
    };
}

fn identifierAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.IdentifierAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .identifier => |*value| value,
        else => error.InvalidAst,
    };
}

fn identifierPathAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.IdentifierPathAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .identifier_path => |*value| value,
        else => error.InvalidAst,
    };
}

fn memberAccessAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.MemberAccessAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .member_access => |*value| value,
        else => error.InvalidAst,
    };
}

fn binaryOperationAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.BinaryOperationAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .binary_operation => |*value| value,
        else => error.InvalidAst,
    };
}

fn functionCallAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.FunctionCallAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .function_call => |*value| value,
        else => error.InvalidAst,
    };
}

fn contractDefinitionAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.ContractDefinitionAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => error.InvalidAst,
    };
}

fn returnAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.ReturnAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .return_statement => |*value| value,
        else => error.InvalidAst,
    };
}

fn inlineAssemblyAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.InlineAssemblyAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .inline_assembly => |*value| value,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}

test "body type checking matches the canonical return conversion diagnostic" {
    const Parser = @import("../parsing/parser.zig");
    const Scoper = @import("scoper.zig");
    const GlobalContext = @import("global_context.zig").GlobalContext;
    const NameResolver = @import("name_and_type_resolver.zig").NameAndTypeResolver;
    const ReferencesResolver = @import("references_resolver.zig");
    const DeclarationTypeChecker = @import("declaration_type_checker.zig").DeclarationTypeChecker;

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "interface Hook { function beforeInitialize(bytes calldata) external; }" ++
        "contract MockHook is Hook {" ++
        " function beforeInitialize(bytes memory) external override {}" ++
        " function selector() external view returns (bytes4) {" ++
        "  return this.beforeInitialize.selector;" ++
        " }" ++
        "}" ++
        "contract TypeError {" ++
        " bytes32 constant VALID = keccak256(\"valid\");" ++
        " function broken() external pure returns (uint256) { return true; }" ++
        " }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "TypeError.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
    const root = parsed.tree.root.?;
    try Scoper.assignScopes(&parsed.tree, root);
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var global = try GlobalContext.init(
        std.testing.allocator,
        &provider,
        EVMVersion.current(),
    );
    defer global.deinit();
    var resolver = try NameResolver.init(
        std.testing.allocator,
        &global,
        EVMVersion.current(),
        &reporter,
        false,
    );
    defer resolver.deinit();
    try std.testing.expect(try resolver.registerSource(&parsed.tree, root));
    try std.testing.expect(try ReferencesResolver.resolveSource(
        &parsed.tree,
        &resolver,
        root,
    ));
    var declaration_checker = DeclarationTypeChecker.init(
        std.testing.allocator,
        &parsed.tree,
        &reporter,
        &provider,
        EVMVersion.current(),
    );
    defer declaration_checker.deinit();
    try std.testing.expect(try declaration_checker.check(root));
    const source_annotation = try ASTAnnotations.ensure(&parsed.tree, root);
    switch (source_annotation.*) {
        .source_unit => |*value| try value.use_abi_coder_v2.assign(true),
        else => return error.InvalidAst,
    }

    var checker = TypeChecker.init(
        std.testing.allocator,
        &parsed.tree,
        &provider,
        EVMVersion.current(),
        &reporter,
    );
    try std.testing.expect(!(try checker.checkTypeRequirements(root)));
    try std.testing.expectEqual(@as(usize, 1), reporter.diagnostics().len);
    try std.testing.expectEqual(@as(u64, 6359), reporter.diagnostics()[0].error_id.value);
    try std.testing.expectEqualStrings(
        "Return argument type bool is not implicitly convertible to expected type (type of first return variable) uint256.",
        reporter.diagnostics()[0].description,
    );
}

test "address staticcall retains view mutability" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "StaticCall.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var checker = TypeChecker.init(
        std.testing.allocator,
        &tree,
        &provider,
        EVMVersion.current(),
        &reporter,
    );

    const resolved = (try checker.resolveAddressMember("staticcall", false)).?;
    try std.testing.expectEqual(
        Types.StateMutability.View,
        resolved.type_ref.asFunction().?.state_mutability,
    );
}
