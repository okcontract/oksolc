// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Contract-level semantic checks translated from `ContractLevelChecker.cpp`.
//!
//! This pass runs after declaration types are known and before expression
//! typing. It owns no syntax or types; contract annotations and diagnostic
//! payloads are allocated by their explicit compilation owners.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const OverrideCheckerModule = @import("override_checker.zig");
const TypeCheckerModule = @import("type_checker.zig");

pub const CheckError = ASTImplementation.AstError ||
    TypeProviderModule.ProviderError ||
    TypeBehavior.BehaviorError ||
    Diagnostics.ReportError ||
    std.mem.Allocator.Error ||
    error{
        BadSetOnceAccess,
        BadSetOnceReassignment,
        InvalidAst,
    };

const Proxy = struct {
    declaration: *AST.Node,
    implemented: bool,
};

pub const ContractLevelChecker = struct {
    allocator: std.mem.Allocator,
    tree: *AST.Tree,
    type_provider: *TypeProviderModule.TypeProvider,
    reporter: *Diagnostics.ErrorReporter,
    compatibility_ids: CompatibilityIdResolver,

    pub fn init(
        allocator: std.mem.Allocator,
        tree: *AST.Tree,
        type_provider: *TypeProviderModule.TypeProvider,
        reporter: *Diagnostics.ErrorReporter,
    ) ContractLevelChecker {
        return .{
            .allocator = allocator,
            .tree = tree,
            .type_provider = type_provider,
            .reporter = reporter,
            .compatibility_ids = .legacyNodeIds(),
        };
    }

    pub fn setCompatibilityIds(
        self: *ContractLevelChecker,
        compatibility_ids: CompatibilityIdResolver,
    ) void {
        self.compatibility_ids = compatibility_ids;
    }

    pub fn check(
        self: *ContractLevelChecker,
        source_unit: *AST.Node,
    ) CheckError!bool {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        try self.checkFreeDuplicates(source_unit);
        for (source_unit.payload.source_unit.nodes) |node|
            if (node.nodeKind() == .contract_definition)
                try self.checkContract(node);
        return watcher.ok();
    }

    fn checkContract(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const annotation = try contractAnnotation(self.tree, contract);
        annotation.unimplemented_declarations = &.{};
        try self.checkDuplicateFunctions(contract);
        try self.checkDuplicateEvents(contract);
        try self.checkReceiveFunction(contract);
        var override_checker = OverrideCheckerModule.OverrideChecker.init(
            self.allocator,
            self.tree,
            self.type_provider,
            self.reporter,
        );
        override_checker.setCompatibilityIds(self.compatibility_ids);
        try override_checker.check(contract);
        try self.checkBaseConstructorArguments(contract);
        try self.checkAbstractDefinitions(contract);
        try self.checkExternalTypeClashes(contract);
        try self.checkHashCollisions(contract);
        try self.checkLibraryRequirements(contract);
        try self.checkBaseAbiCompatibility(contract);
        try self.checkPayableFallbackWithoutReceive(contract);
        try self.checkStorageSize(contract);
        try self.checkStorageLayoutSpecifier(contract);
    }

    fn checkFreeDuplicates(
        self: *ContractLevelChecker,
        source_unit: *AST.Node,
    ) CheckError!void {
        const annotation = ASTAnnotations.annotation(source_unit) orelse return error.InvalidAst;
        const source_annotation = switch (annotation.*) {
            .source_unit => |*value| value,
            else => return error.InvalidAst,
        };
        const exported = (try source_annotation.exported_symbols.get()).*;
        const symbols = try self.allocator.alloc(
            *const ASTAnnotations.ExportedSymbol,
            exported.len,
        );
        defer self.allocator.free(symbols);
        for (exported, symbols) |*symbol, *target| target.* = symbol;
        stableSortExportedSymbols(symbols);
        for ([_]AST.Kind{ .function_definition, .event_definition }) |kind| {
            for (symbols) |symbol| {
                var declarations: std.ArrayList(*AST.Node) = .empty;
                defer declarations.deinit(self.allocator);
                for (symbol.declarations) |declaration|
                    if (declaration.nodeKind() == kind)
                        try declarations.append(self.allocator, declaration);
                try self.reportDuplicateGroup(declarations.items);
            }
        }
    }

    fn checkDuplicateFunctions(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        var constructor: ?*AST.Node = null;
        var fallback_function: ?*AST.Node = null;
        var receive_function: ?*AST.Node = null;
        const members = contract.payload.contract_definition.sub_nodes;
        var ordinary: std.ArrayList(*AST.Node) = .empty;
        defer ordinary.deinit(self.allocator);
        for (members) |function| {
            if (function.nodeKind() != .function_definition) continue;
            switch (function.payload.function_definition.kind) {
                .Constructor => {
                    if (constructor) |previous|
                        try self.reportDuplicateSpecial(
                            errorId(7997),
                            function,
                            previous,
                            "More than one constructor defined.",
                        );
                    constructor = function;
                },
                .Fallback => {
                    if (fallback_function) |previous|
                        try self.reportDuplicateSpecial(
                            errorId(7301),
                            function,
                            previous,
                            "Only one fallback function is allowed.",
                        );
                    fallback_function = function;
                },
                .Receive => {
                    if (receive_function) |previous|
                        try self.reportDuplicateSpecial(
                            errorId(4046),
                            function,
                            previous,
                            "Only one receive function is allowed.",
                        );
                    receive_function = function;
                },
                else => try ordinary.append(self.allocator, function),
            }
        }
        stableSortNodesByName(ordinary.items);
        var start: usize = 0;
        while (start < ordinary.items.len) {
            var end = start + 1;
            while (end < ordinary.items.len and std.mem.eql(
                u8,
                declarationName(ordinary.items[start]),
                declarationName(ordinary.items[end]),
            )) : (end += 1) {}
            try self.reportDuplicateGroup(ordinary.items[start..end]);
            start = end;
        }
    }

    fn checkDuplicateEvents(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const annotation = try contractAnnotation(self.tree, contract);
        const bases = if (annotation.linearized_base_contracts.len == 0)
            &.{contract}
        else
            annotation.linearized_base_contracts;
        var events: std.ArrayList(*AST.Node) = .empty;
        defer events.deinit(self.allocator);
        for (bases) |base|
            for (base.payload.contract_definition.sub_nodes) |member|
                if (member.nodeKind() == .event_definition)
                    try events.append(self.allocator, member);
        stableSortNodesByName(events.items);
        var start: usize = 0;
        while (start < events.items.len) {
            var end = start + 1;
            while (end < events.items.len and std.mem.eql(
                u8,
                declarationName(events.items[start]),
                declarationName(events.items[end]),
            )) : (end += 1) {}
            try self.reportDuplicateGroup(events.items[start..end]);
            start = end;
        }
    }

    fn reportDuplicateGroup(
        self: *ContractLevelChecker,
        declarations: []const *AST.Node,
    ) CheckError!void {
        const reported = try self.allocator.alloc(bool, declarations.len);
        defer self.allocator.free(reported);
        @memset(reported, false);
        for (declarations, 0..) |declaration, index| {
            if (reported[index]) continue;
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            for (declarations[index + 1 ..], index + 1..) |other, other_index|
                if (try self.externalCallableParametersEqual(declaration, other)) {
                    try secondary.append(
                        self.allocator,
                        "Other declaration is here:",
                        other.location,
                    );
                    reported[other_index] = true;
                };
            if (secondary.infos.items.len == 0) continue;
            const is_function = declaration.nodeKind() == .function_definition;
            var message = try self.allocator.dupe(
                u8,
                if (is_function)
                    "Function with same name and parameter types defined twice."
                else
                    "Event with same name and parameter types defined twice.",
            );
            defer self.allocator.free(message);
            try secondary.limitSize(self.allocator, &message);
            try self.reporter.reportWithSecondary(
                if (is_function) errorId(1686) else errorId(5883),
                .DeclarationError,
                declaration.location,
                &secondary,
                message,
            );
        }
    }

    fn externalCallableParametersEqual(
        self: *ContractLevelChecker,
        left: *AST.Node,
        right: *AST.Node,
    ) CheckError!bool {
        const left_function = (try self.externalCallableType(left)).payload.Function;
        const right_function = (try self.externalCallableType(right)).payload.Function;
        return typeSlicesEqual(left_function.parameter_types, right_function.parameter_types);
    }

    fn externalCallableType(
        self: *ContractLevelChecker,
        declaration: *AST.Node,
    ) CheckError!*const Types.Type {
        const raw = switch (declaration.nodeKind()) {
            .function_definition => try self.type_provider.functionFromDefinition(
                declaration,
                .Declaration,
            ),
            .event_definition => try self.type_provider.functionFromEvent(declaration),
            .variable_declaration => try self.type_provider.functionFromVariable(declaration),
            else => return error.InvalidAst,
        };
        return TypeBehavior.asExternallyCallableFunction(
            self.type_provider,
            raw.payload.Function,
            false,
        );
    }

    fn reportDuplicateSpecial(
        self: *ContractLevelChecker,
        id: Diagnostics.ErrorId,
        current: *const AST.Node,
        previous: *const AST.Node,
        message: []const u8,
    ) CheckError!void {
        var secondary: Diagnostics.SecondarySourceLocation = .{};
        defer secondary.deinit(self.allocator);
        try secondary.append(self.allocator, "Another declaration is here:", previous.location);
        try self.reporter.reportWithSecondary(
            id,
            .DeclarationError,
            current.location,
            &secondary,
            message,
        );
    }

    fn checkReceiveFunction(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        for (contract.payload.contract_definition.sub_nodes) |function| {
            if (function.nodeKind() != .function_definition or
                function.payload.function_definition.kind != .Receive) continue;
            const value = function.payload.function_definition;
            if (contract.payload.contract_definition.contract_kind == .Library)
                try self.reporter.declarationError(
                    errorId(4549),
                    function.location,
                    "Libraries cannot have receive ether functions.",
                );
            if (value.state_mutability != .Payable) {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Receive ether function must be payable, but is \"{s}\".",
                    .{@import("../ast/ast_enums.zig").stateMutabilityToString(value.state_mutability)},
                );
                defer self.allocator.free(message);
                try self.reporter.declarationError(errorId(7793), function.location, message);
            }
            if (ASTImplementation.effectiveVisibility(function) != .External)
                try self.reporter.declarationError(
                    errorId(4095),
                    function.location,
                    "Receive ether function must be defined as \"external\".",
                );
            if (value.callable.return_parameters) |returns|
                if (returns.payload.parameter_list.parameters.len != 0)
                    try self.reporter.fatal(
                        errorId(6899),
                        .DeclarationError,
                        returns.location,
                        null,
                        "Receive ether function cannot return values.",
                    );
            if (value.callable.parameters.payload.parameter_list.parameters.len != 0)
                try self.reporter.fatal(
                    errorId(6857),
                    .DeclarationError,
                    value.callable.parameters.location,
                    null,
                    "Receive ether function cannot take parameters.",
                );
        }
    }

    fn checkAbstractDefinitions(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const annotation = try contractAnnotation(self.tree, contract);
        const bases = if (annotation.linearized_base_contracts.len == 0)
            &.{contract}
        else
            annotation.linearized_base_contracts;
        var proxies: std.ArrayList(Proxy) = .empty;
        defer proxies.deinit(self.allocator);
        var override_checker = OverrideCheckerModule.OverrideChecker.init(
            self.allocator,
            self.tree,
            self.type_provider,
            self.reporter,
        );
        override_checker.setCompatibilityIds(self.compatibility_ids);

        var base_index = bases.len;
        while (base_index != 0) {
            base_index -= 1;
            const base = bases[base_index];
            for (base.payload.contract_definition.sub_nodes) |member| {
                const implemented = switch (member.payload) {
                    .variable_declaration => if (ASTImplementation.isStateVariable(member) and
                        ASTImplementation.isPartOfExternalInterface(member)) true else continue,
                    .function_definition => |value| if (value.kind == .Constructor)
                        continue
                    else
                        value.implemented(),
                    .modifier_definition => |value| value.implemented(),
                    else => continue,
                };
                const member_proxy = try OverrideCheckerModule.OverrideProxy.init(member);
                var matching: ?usize = null;
                for (proxies.items, 0..) |proxy, proxy_index|
                    if (try override_checker.signatureEqual(
                        member_proxy,
                        try OverrideCheckerModule.OverrideProxy.init(proxy.declaration),
                    )) {
                        matching = proxy_index;
                        break;
                    };
                if (matching) |proxy_index| {
                    if (implemented) proxies.items[proxy_index] = .{
                        .declaration = member,
                        .implemented = true,
                    };
                } else {
                    try proxies.append(self.allocator, .{
                        .declaration = member,
                        .implemented = implemented,
                    });
                }
            }
        }

        try self.sortAbstractProxies(&override_checker, proxies.items);
        var unresolved: std.ArrayList(*AST.Node) = .empty;
        defer unresolved.deinit(self.allocator);
        for (proxies.items) |proxy|
            if (!proxy.implemented)
                try unresolved.append(self.allocator, proxy.declaration);
        annotation.unimplemented_declarations = try self.tree.ownSlice(
            *AST.Node,
            unresolved.items,
        );

        const definition = contract.payload.contract_definition;
        if (definition.abstract) switch (definition.contract_kind) {
            .Interface => try self.reporter.typeError(
                errorId(9348),
                contract.location,
                "Interfaces do not need the \"abstract\" keyword, they are abstract implicitly.",
            ),
            .Library => try self.reporter.typeError(
                errorId(9571),
                contract.location,
                "Libraries cannot be abstract.",
            ),
            .Contract => {},
        };
        if (definition.contract_kind == .Contract and
            !definition.abstract and unresolved.items.len != 0)
        {
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            for (unresolved.items) |missing|
                try secondary.append(self.allocator, "Missing implementation: ", missing.location);
            const canonical = try annotation.type_declaration.canonical_name.get();
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Contract \"{s}\" should be marked as abstract.",
                .{canonical.*},
            );
            defer self.allocator.free(message);
            try self.reporter.reportWithSecondary(
                errorId(3656),
                .TypeError,
                contract.location,
                &secondary,
                message,
            );
        }
    }

    fn sortAbstractProxies(
        self: *ContractLevelChecker,
        override_checker: *OverrideCheckerModule.OverrideChecker,
        proxies: []Proxy,
    ) CheckError!void {
        _ = self;
        if (proxies.len < 2) return;
        for (1..proxies.len) |index| {
            const selected = proxies[index];
            const selected_proxy = try OverrideCheckerModule.OverrideProxy.init(
                selected.declaration,
            );
            var position = index;
            while (position != 0) {
                const previous_proxy = try OverrideCheckerModule.OverrideProxy.init(
                    proxies[position - 1].declaration,
                );
                if (try override_checker.signatureOrder(
                    selected_proxy,
                    previous_proxy,
                ) != .lt) break;
                proxies[position] = proxies[position - 1];
                position -= 1;
            }
            proxies[position] = selected;
        }
    }

    fn checkBaseConstructorArguments(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const annotation = try contractAnnotation(self.tree, contract);
        annotation.base_constructor_arguments.clearRetainingCapacity();
        const bases = if (annotation.linearized_base_contracts.len == 0)
            &.{contract}
        else
            annotation.linearized_base_contracts;

        for (bases) |base| {
            if (findConstructor(base)) |constructor|
                for (constructor.payload.function_definition.modifiers) |modifier| {
                    const invoked = referencedDeclaration(self.tree, modifier.payload
                        .modifier_invocation.modifier_name) catch continue;
                    if (invoked.nodeKind() != .contract_definition) continue;
                    if (modifier.payload.modifier_invocation.arguments != null) {
                        if (findConstructor(invoked)) |base_constructor|
                            try self.annotateBaseConstructorArguments(
                                contract,
                                base_constructor,
                                modifier,
                            );
                    } else {
                        try self.reporter.declarationError(
                            errorId(1563),
                            modifier.location,
                            "Modifier-style base constructor call without arguments.",
                        );
                    }
                };

            for (base.payload.contract_definition.base_contracts) |specifier| {
                const base_contract = try referencedDeclaration(
                    self.tree,
                    specifier.payload.inheritance_specifier.base_name,
                );
                const arguments = specifier.payload.inheritance_specifier.arguments;
                if (findConstructor(base_contract)) |base_constructor|
                    if (arguments != null and arguments.?.len != 0)
                        try self.annotateBaseConstructorArguments(
                            contract,
                            base_constructor,
                            specifier,
                        );
            }
        }

        const definition = contract.payload.contract_definition;
        if (definition.contract_kind == .Contract and !definition.abstract)
            for (bases) |base| {
                const constructor = findConstructor(base) orelse continue;
                if (base == contract or callableParameters(constructor).len == 0) continue;
                if (!hasBaseConstructorArguments(annotation, constructor)) {
                    var secondary: Diagnostics.SecondarySourceLocation = .{};
                    defer secondary.deinit(self.allocator);
                    try secondary.append(
                        self.allocator,
                        "Base constructor parameters:",
                        constructor.payload.function_definition.callable.parameters.location,
                    );
                    const canonical = try annotation.type_declaration.canonical_name.get();
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "No arguments passed to the base constructor. Specify the arguments or mark \"{s}\" as abstract.",
                        .{canonical.*},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.reportWithSecondary(
                        errorId(3415),
                        .TypeError,
                        contract.location,
                        &secondary,
                        message,
                    );
                }
            };
    }

    fn annotateBaseConstructorArguments(
        self: *ContractLevelChecker,
        contract: *AST.Node,
        base_constructor: *AST.Node,
        argument_node: *AST.Node,
    ) CheckError!void {
        const annotation = try contractAnnotation(self.tree, contract);
        for (annotation.base_constructor_arguments.items) |existing| {
            if (existing.function != base_constructor) continue;
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            var main_location = contract.location;
            if (contract.location.contains(existing.argument_node.location) or
                contract.location.contains(argument_node.location))
            {
                main_location = existing.argument_node.location;
                try secondary.append(
                    self.allocator,
                    "Second constructor call is here:",
                    argument_node.location,
                );
            } else {
                try secondary.append(
                    self.allocator,
                    "First constructor call is here:",
                    argument_node.location,
                );
                try secondary.append(
                    self.allocator,
                    "Second constructor call is here:",
                    existing.argument_node.location,
                );
            }
            try self.reporter.reportWithSecondary(
                errorId(3364),
                .DeclarationError,
                main_location,
                &secondary,
                "Base constructor arguments given twice.",
            );
            return;
        }
        try annotation.base_constructor_arguments.append(
            self.tree.allocator(),
            .{ .function = base_constructor, .argument_node = argument_node },
        );
    }

    fn checkLibraryRequirements(
        self: *ContractLevelChecker,
        contract: *const AST.Node,
    ) CheckError!void {
        const definition = contract.payload.contract_definition;
        if (definition.contract_kind != .Library) return;
        if (definition.base_contracts.len != 0)
            try self.reporter.typeError(
                errorId(9469),
                contract.location,
                "Library is not allowed to inherit.",
            );
        for (definition.sub_nodes) |member|
            if (member.nodeKind() == .variable_declaration and
                member.payload.variable_declaration.mutability != .Constant)
                try self.reporter.typeError(
                    errorId(9957),
                    member.location,
                    "Library cannot have non-constant state variables",
                );
    }

    fn checkExternalTypeClashes(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const annotation = try contractAnnotation(self.tree, contract);
        const bases = annotation.linearized_base_contracts;
        var declarations: std.ArrayList(ExternalDeclaration) = .empty;
        defer {
            for (declarations.items) |entry| self.allocator.free(entry.signature);
            declarations.deinit(self.allocator);
        }
        for (bases) |base|
            for (base.payload.contract_definition.sub_nodes) |member| {
                const raw_type = (try self.externalInterfaceType(member)) orelse continue;
                if ((try TypeBehavior.interfaceFunctionType(
                    self.type_provider,
                    raw_type.payload.Function,
                )) == null) continue;
                const signature = try TypeBehavior.externalSignatureAlloc(
                    self.type_provider,
                    self.allocator,
                    raw_type.payload.Function,
                );
                errdefer self.allocator.free(signature);
                const callable_type = try TypeBehavior.asExternallyCallableFunction(
                    self.type_provider,
                    raw_type.payload.Function,
                    false,
                );
                try declarations.append(self.allocator, .{
                    .declaration = member,
                    .signature = signature,
                    .callable_type = callable_type,
                });
            };
        stableSortExternalDeclarations(declarations.items);
        var group_start: usize = 0;
        while (group_start < declarations.items.len) {
            var group_end = group_start + 1;
            while (group_end < declarations.items.len and std.mem.eql(
                u8,
                declarations.items[group_start].signature,
                declarations.items[group_end].signature,
            )) : (group_end += 1) {}
            for (declarations.items[group_start..group_end], 0..) |left, left_index|
                for (declarations.items[group_start + left_index + 1 .. group_end]) |right|
                    if (!TypeBehavior.functionHasEqualParameterTypes(
                        left.callable_type.payload.Function,
                        right.callable_type.payload.Function,
                    ))
                        try self.reporter.typeError(
                            errorId(9914),
                            right.declaration.location,
                            "Function overload clash during conversion to external types for arguments.",
                        );
            group_start = group_end;
        }
    }

    fn checkHashCollisions(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const functions = try ASTImplementation.contractInterfaceFunctionListAlloc(
            self.type_provider,
            self.allocator,
            contract,
            true,
        );
        defer self.allocator.free(functions);
        for (functions, 0..) |function, index| {
            for (functions[0..index]) |previous|
                if (function.selector.eql(&previous.selector)) {
                    const signature = try TypeBehavior.externalSignatureAlloc(
                        self.type_provider,
                        self.allocator,
                        function.function_type.payload.Function,
                    );
                    defer self.allocator.free(signature);
                    const message = try std.fmt.allocPrint(
                        self.allocator,
                        "Function signature hash collision for {s}",
                        .{signature},
                    );
                    defer self.allocator.free(message);
                    try self.reporter.fatal(
                        errorId(1860),
                        .TypeError,
                        contract.location,
                        null,
                        message,
                    );
                };
        }
    }

    fn checkBaseAbiCompatibility(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        if (try usesAbiCoderV2(contract)) return;
        if (contract.payload.contract_definition.contract_kind == .Library) return;
        const functions = try ASTImplementation.contractInterfaceFunctionListAlloc(
            self.type_provider,
            self.allocator,
            contract,
            true,
        );
        defer self.allocator.free(functions);
        var secondary: Diagnostics.SecondarySourceLocation = .{};
        defer secondary.deinit(self.allocator);
        for (functions) |function| {
            const function_type = function.function_type.payload.Function;
            const declaration = function_type.declaration orelse return error.InvalidAst;
            if (!(try usesAbiCoderV2(declaration))) continue;
            var unsupported = false;
            for (function_type.parameter_types) |parameter_type|
                if (!TypeCheckerModule.typeSupportedByOldABIEncoder(parameter_type, false)) {
                    unsupported = true;
                    break;
                };
            if (!unsupported)
                for (function_type.return_parameter_types) |return_type|
                    if (!TypeCheckerModule.typeSupportedByOldABIEncoder(return_type, false)) {
                        unsupported = true;
                        break;
                    };
            if (unsupported)
                try secondary.append(
                    self.allocator,
                    "Type only supported by ABIEncoderV2",
                    declaration.location,
                );
        }
        if (secondary.infos.items.len == 0) return;
        const message = try std.fmt.allocPrint(
            self.allocator,
            "Contract \"{s}\" does not use ABI coder v2 but wants to inherit from a contract which uses types that require it. Use \"pragma abicoder v2;\" for the inheriting contract as well to enable the feature.",
            .{contract.payload.contract_definition.declaration.name},
        );
        defer self.allocator.free(message);
        try self.reporter.fatal(
            errorId(6594),
            .TypeError,
            contract.location,
            &secondary,
            message,
        );
    }

    fn checkStorageSize(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const annotation = try contractAnnotation(self.tree, contract);
        for ([_]AST.VariableLocation{ .Unspecified, .Transient }) |location| {
            var total: u256 = 0;
            var overflow = false;
            for (annotation.linearized_base_contracts) |base|
                for (base.payload.contract_definition.sub_nodes) |member| {
                    if (member.nodeKind() != .variable_declaration or
                        !ASTImplementation.isStateVariable(member)) continue;
                    const value = member.payload.variable_declaration;
                    if (value.mutability == .Constant or value.mutability == .Immutable or
                        value.reference_location != location) continue;
                    const type_ref = (try variableAnnotation(self.tree, member)).type_ref orelse
                        return error.InvalidAst;
                    const bound = TypeBehavior.storageSizeUpperBound(type_ref) catch |err| switch (err) {
                        error.Overflow => {
                            overflow = true;
                            continue;
                        },
                        else => return err,
                    };
                    total = std.math.add(u256, total, bound) catch {
                        overflow = true;
                        continue;
                    };
                };
            if (!overflow) continue;
            try self.reporter.typeError(
                if (location == .Transient) errorId(5026) else errorId(7676),
                contract.location,
                if (location == .Transient)
                    "Contract requires too much transient storage."
                else
                    "Contract requires too much storage.",
            );
        }
    }

    fn checkPayableFallbackWithoutReceive(
        self: *ContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const fallback_function = try self.findSpecialFunction(contract, .Fallback);
        const receive_function = try self.findSpecialFunction(contract, .Receive);
        const functions = try ASTImplementation.contractInterfaceFunctionListAlloc(
            self.type_provider,
            self.allocator,
            contract,
            true,
        );
        defer self.allocator.free(functions);
        if (fallback_function) |fallback|
            if (fallback.payload.function_definition.state_mutability == .Payable and
                functions.len != 0 and receive_function == null)
            {
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(
                    self.allocator,
                    "The payable fallback function is defined here.",
                    fallback.location,
                );
                try self.reporter.warningWithSecondary(
                    errorId(3628),
                    contract.location,
                    "This contract has a payable fallback function, but no receive ether function. Consider adding a receive ether function.",
                    &secondary,
                );
            };
    }

    fn externalInterfaceType(
        self: *ContractLevelChecker,
        declaration: *AST.Node,
    ) CheckError!?*const Types.Type {
        if (!declaration.isPartOfExternalInterface()) return null;
        return switch (declaration.nodeKind()) {
            .function_definition => try self.type_provider.functionFromDefinition(
                declaration,
                .External,
            ),
            .variable_declaration => try self.type_provider.functionFromVariable(declaration),
            else => null,
        };
    }

    fn findSpecialFunction(
        self: *ContractLevelChecker,
        contract: *AST.Node,
        kind: AST.Token,
    ) CheckError!?*AST.Node {
        const annotation = try contractAnnotation(self.tree, contract);
        for (annotation.linearized_base_contracts) |base|
            for (base.payload.contract_definition.sub_nodes) |member|
                if (member.nodeKind() == .function_definition and
                    member.payload.function_definition.kind == kind)
                    return member;
        return null;
    }

    fn checkStorageLayoutSpecifier(
        self: *ContractLevelChecker,
        contract: *const AST.Node,
    ) CheckError!void {
        const definition = contract.payload.contract_definition;
        if (definition.storage_layout_specifier) |layout|
            if (definition.abstract)
                try self.reporter.typeError(
                    errorId(7587),
                    layout.location,
                    "Storage layout cannot be specified for abstract contracts.",
                );
        for (definition.base_contracts) |specifier| {
            const base = try referencedDeclaration(
                self.tree,
                specifier.payload.inheritance_specifier.base_name,
            );
            if (base.payload.contract_definition.storage_layout_specifier) |layout| {
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(
                    self.allocator,
                    "Custom storage layout defined here:",
                    layout.location,
                );
                try self.reporter.reportWithSecondary(
                    errorId(8894),
                    .TypeError,
                    specifier.location,
                    &secondary,
                    "Cannot inherit from a contract with a custom storage layout.",
                );
            }
        }
    }
};

const ExternalDeclaration = struct {
    declaration: *AST.Node,
    signature: []u8,
    callable_type: *const Types.Type,
};

fn usesAbiCoderV2(node: *const AST.Node) CheckError!bool {
    var current: *const AST.Node = node;
    while (current.nodeKind() != .source_unit)
        current = ASTImplementation.scope(current) orelse return error.InvalidAst;
    const annotation = ASTAnnotations.annotationConst(current) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .source_unit => |*value| (try value.use_abi_coder_v2.get()).*,
        else => error.InvalidAst,
    };
}

fn callableParameters(node: *const AST.Node) AST.NodeList {
    const list = switch (node.payload) {
        .function_definition => |value| value.callable.parameters,
        .modifier_definition => |value| value.callable.parameters,
        .event_definition => |value| value.callable.parameters,
        .error_definition => |value| value.callable.parameters,
        else => return &.{},
    };
    return list.payload.parameter_list.parameters;
}

fn typeSlicesEqual(
    left: []const *const Types.Type,
    right: []const *const Types.Type,
) bool {
    if (left.len != right.len) return false;
    for (left, right) |left_type, right_type|
        if (!TypeBehavior.equals(left_type, right_type)) return false;
    return true;
}

fn stableSortNodesByName(nodes: []*AST.Node) void {
    if (nodes.len < 2) return;
    for (1..nodes.len) |index| {
        const selected = nodes[index];
        var position = index;
        while (position != 0 and std.mem.order(
            u8,
            declarationName(selected),
            declarationName(nodes[position - 1]),
        ) == .lt) {
            nodes[position] = nodes[position - 1];
            position -= 1;
        }
        nodes[position] = selected;
    }
}

fn stableSortExternalDeclarations(declarations: []ExternalDeclaration) void {
    if (declarations.len < 2) return;
    for (1..declarations.len) |index| {
        const selected = declarations[index];
        var position = index;
        while (position != 0 and std.mem.order(
            u8,
            selected.signature,
            declarations[position - 1].signature,
        ) == .lt) {
            declarations[position] = declarations[position - 1];
            position -= 1;
        }
        declarations[position] = selected;
    }
}

fn stableSortExportedSymbols(symbols: []*const ASTAnnotations.ExportedSymbol) void {
    if (symbols.len < 2) return;
    for (1..symbols.len) |index| {
        const selected = symbols[index];
        var position = index;
        while (position != 0 and std.mem.order(
            u8,
            selected.name,
            symbols[position - 1].name,
        ) == .lt) {
            symbols[position] = symbols[position - 1];
            position -= 1;
        }
        symbols[position] = selected;
    }
}

fn declarationName(node: *const AST.Node) []const u8 {
    const declaration = node.declarationConst() orelse return "";
    return declaration.name;
}

fn findConstructor(contract: *const AST.Node) ?*AST.Node {
    if (contract.nodeKind() != .contract_definition) return null;
    for (contract.payload.contract_definition.sub_nodes) |member|
        if (member.nodeKind() == .function_definition and
            member.payload.function_definition.kind == .Constructor)
            return member;
    return null;
}

fn hasBaseConstructorArguments(
    annotation: *const ASTAnnotations.ContractDefinitionAnnotation,
    constructor: *const AST.Node,
) bool {
    for (annotation.base_constructor_arguments.items) |entry|
        if (entry.function == constructor) return true;
    return false;
}

fn referencedDeclaration(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*AST.Node {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .identifier_path => |value| @constCast(value.referenced_declaration orelse
            return error.InvalidAst),
        .identifier => |value| @constCast(value.referenced_declaration orelse
            return error.InvalidAst),
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

fn contractAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.ContractDefinitionAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}

test "contract-level checker reports duplicate constructors with secondary location" {
    const Parser = @import("../parsing/parser.zig");
    const Scoper = @import("scoper.zig");
    const SyntaxChecker = @import("syntax_checker.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const GlobalContext = @import("global_context.zig").GlobalContext;
    const NameResolver = @import("name_and_type_resolver.zig").NameAndTypeResolver;
    const ReferencesResolver = @import("references_resolver.zig");
    const DeclarationTypeChecker = @import("declaration_type_checker.zig").DeclarationTypeChecker;

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "pragma solidity ^0.8.36;\n" ++
        "contract C { constructor() {} constructor(uint value) {} }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "Contract.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
    const root = parsed.tree.root.?;
    try Scoper.assignScopes(&parsed.tree, root);
    try std.testing.expect(try SyntaxChecker.checkSyntax(
        &parsed.tree,
        root,
        &reporter,
        .{},
    ));
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
    try std.testing.expect(try resolver.performImports(&parsed.tree, root, &.{}));
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

    var checker = ContractLevelChecker.init(
        std.testing.allocator,
        &parsed.tree,
        &provider,
        &reporter,
    );
    try std.testing.expect(!(try checker.check(root)));
    try std.testing.expectEqual(@as(usize, 1), reporter.diagnostics().len);
    try std.testing.expectEqual(@as(u64, 7997), reporter.diagnostics()[0].error_id.value);
    try std.testing.expectEqual(@as(usize, 1), reporter.diagnostics()[0].secondary.infos.items.len);
}
