// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Contract checks that require complete expression types and call graphs,
//! translated from `PostTypeContractLevelChecker.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const ConstantEvaluator = @import("constant_evaluator.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const FunctionSelector = @import("../../libsolutil/function_selector.zig");
const Numeric = @import("../../libsolutil/numeric.zig");
const SetOnce = @import("../../libsolutil/set_once.zig");
const StringUtils = @import("../../libsolutil/string_utils.zig");

pub const CheckError = ConstantEvaluator.EvaluateError ||
    std.mem.Allocator.Error ||
    Diagnostics.ReportError ||
    SetOnce.SetOnceError ||
    TypeBehavior.BehaviorError ||
    error{InvalidAst};

const ErrorHashEntry = struct {
    selector: u32,
    signature: []u8,
    location: Diagnostics.SourceLocation,
};

pub const PostTypeContractLevelChecker = struct {
    allocator: std.mem.Allocator,
    tree: *AST.Tree,
    reporter: *Diagnostics.ErrorReporter,
    type_provider: *TypeProviderModule.TypeProvider,

    pub fn init(
        allocator: std.mem.Allocator,
        tree: *AST.Tree,
        reporter: *Diagnostics.ErrorReporter,
        type_provider: *TypeProviderModule.TypeProvider,
    ) PostTypeContractLevelChecker {
        return .{
            .allocator = allocator,
            .tree = tree,
            .reporter = reporter,
            .type_provider = type_provider,
        };
    }

    pub fn check(
        self: *PostTypeContractLevelChecker,
        source_unit: *AST.Node,
    ) CheckError!bool {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
        const watcher = self.reporter.errorWatcher();
        for (source_unit.payload.source_unit.nodes) |contract| {
            if (contract.nodeKind() != .contract_definition) continue;
            try self.checkContract(contract);
        }
        return watcher.ok();
    }

    fn checkContract(
        self: *PostTypeContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const annotation = try contractAnnotation(contract);
        if (!annotation.creation_call_graph.isSet() or
            !annotation.deployed_call_graph.isSet()) return error.InvalidAst;
        try self.checkErrorHashCollisions(annotation);
        if (contract.payload.contract_definition.storage_layout_specifier != null)
            try self.checkStorageLayoutSpecifier(contract);
        try self.warnStorageLayoutBaseNearStorageEnd(contract);
    }

    fn checkErrorHashCollisions(
        self: *PostTypeContractLevelChecker,
        annotation: *const ASTAnnotations.ContractDefinitionAnnotation,
    ) CheckError!void {
        var errors: std.ArrayList(*const AST.Node) = .empty;
        defer errors.deinit(self.allocator);
        for (annotation.linearized_base_contracts) |base|
            for (base.payload.contract_definition.sub_nodes) |member|
                if (member.nodeKind() == .error_definition)
                    try appendUniqueNode(self.allocator, &errors, member);
        const creation = (try annotation.creation_call_graph.get()).*;
        const deployed = (try annotation.deployed_call_graph.get()).*;
        for (creation.used_errors.items) |used|
            try appendUniqueNode(self.allocator, &errors, used);
        for (deployed.used_errors.items) |used|
            try appendUniqueNode(self.allocator, &errors, used);
        std.sort.insertion(*const AST.Node, errors.items, {}, nodeLessThan);

        var entries: std.ArrayList(ErrorHashEntry) = .empty;
        defer {
            for (entries.items) |entry| self.allocator.free(entry.signature);
            entries.deinit(self.allocator);
        }
        for (errors.items) |error_definition| {
            const function_type = try self.type_provider.functionFromError(error_definition);
            const signature = try TypeBehavior.externalSignatureAlloc(
                self.type_provider,
                self.allocator,
                function_type.payload.Function,
            );
            var keep_signature = false;
            defer if (!keep_signature) self.allocator.free(signature);
            const selector = FunctionSelector.selectorFromSignatureU32(signature);
            var same_signature = false;
            var first_other: ?*const ErrorHashEntry = null;
            for (entries.items) |*entry| {
                if (entry.selector != selector) continue;
                if (std.mem.eql(u8, entry.signature, signature)) {
                    same_signature = true;
                    break;
                }
                if (first_other == null or
                    std.mem.order(u8, entry.signature, first_other.?.signature) == .lt)
                    first_other = entry;
            }
            if (!same_signature and first_other != null) {
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(
                    self.allocator,
                    "This error has a different signature but the same hash: ",
                    first_other.?.location,
                );
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Error signature hash collision for {s}",
                    .{signature},
                );
                defer self.allocator.free(message);
                const declaration = error_definition.declarationConst() orelse
                    return error.InvalidAst;
                try self.reporter.reportWithSecondary(
                    errorId(4883),
                    .TypeError,
                    declaration.name_location,
                    &secondary,
                    message,
                );
            } else if (!same_signature) {
                try entries.append(self.allocator, .{
                    .selector = selector,
                    .signature = signature,
                    .location = error_definition.location,
                });
                keep_signature = true;
            }
        }
    }

    fn checkStorageLayoutSpecifier(
        self: *PostTypeContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        const layout = contract.payload.contract_definition.storage_layout_specifier orelse
            return;
        const expression = layout.payload.storage_layout_specifier.base_slot_expression;
        const expression_annotation = try expressionAnnotation(expression);
        if (!(try expression_annotation.is_pure.get()).*) {
            try self.reporter.typeError(
                errorId(1139),
                expression.location,
                "The base slot of the storage layout must be a compile-time constant expression.",
            );
            return;
        }
        const expression_type = expression_annotation.type_ref orelse
            return error.InvalidAst;
        if (expression_type.category() != .Integer and
            expression_type.category() != .RationalNumber)
        {
            var message: std.ArrayList(u8) = .empty;
            defer message.deinit(self.allocator);
            try message.appendSlice(
                self.allocator,
                "The base slot of the storage layout must evaluate to an integer",
            );
            switch (expression_type.payload) {
                .Address => try message.appendSlice(
                    self.allocator,
                    " (the type is 'address' instead)",
                ),
                .FixedBytes => |fixed| {
                    const suffix = try std.fmt.allocPrint(
                        self.allocator,
                        " (the type is 'bytes{d}' instead)",
                        .{fixed.bytes},
                    );
                    defer self.allocator.free(suffix);
                    try message.appendSlice(self.allocator, suffix);
                },
                .UserDefinedValueType => {
                    const rendered = try TypeBehavior.toStringAlloc(
                        self.allocator,
                        expression_type,
                        true,
                    );
                    defer self.allocator.free(rendered);
                    const suffix = try std.fmt.allocPrint(
                        self.allocator,
                        " (the type is '{s}' instead)",
                        .{rendered},
                    );
                    defer self.allocator.free(suffix);
                    try message.appendSlice(self.allocator, suffix);
                },
                else => {},
            }
            try message.append(self.allocator, '.');
            try self.reporter.typeError(
                errorId(1763),
                expression.location,
                message.items,
            );
            return;
        }

        var rational: ConstantEvaluator.RationalValue = if (expression_type.category() == .Integer) blk: {
            var evaluated = try ConstantEvaluator.evaluate(
                self.allocator,
                self.reporter,
                self.type_provider,
                expression,
            );
            defer evaluated.deinit();
            if (evaluated.type_ref == null) {
                try self.reporter.typeError(
                    errorId(1505),
                    expression.location,
                    "The base slot expression contains elements that are not yet supported by the internal constant evaluator and therefore cannot be evaluated at compilation time.",
                );
                return;
            }
            const value = evaluated.rationalValue() orelse return error.InvalidAst;
            break :blk value.clone();
        } else blk: {
            const value = expression_type.payload.RationalNumber;
            if (value.denominator.compareUnsigned(1) != .eq) {
                try self.reporter.typeError(
                    errorId(1763),
                    expression.location,
                    "The base slot of the storage layout must evaluate to an integer.",
                );
                return;
            }
            break :blk .{
                .numerator = value.numerator.clone(),
                .denominator = value.denominator.clone(),
            };
        };
        defer rational.deinit();
        if (rational.denominator.compareUnsigned(1) != .eq) {
            try self.reporter.typeError(
                errorId(1763),
                expression.location,
                "The base slot of the storage layout must evaluate to an integer.",
            );
            return;
        }
        if (rational.numerator.isNegative() or rational.numerator.bitLength() > 256) {
            const rendered = StringUtils.formatNumberReadableAlloc(
                self.allocator,
                &rational.numerator,
                false,
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidBase => unreachable,
            };
            defer self.allocator.free(rendered);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "The base slot of the storage layout evaluates to {s}, which is outside the range of type uint256.",
                .{rendered},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(6753), expression.location, message);
            return;
        }
        if (!TypeBehavior.isImplicitlyConvertibleTo(
            expression_type,
            self.type_provider.uint256(),
        )) {
            const rendered = try TypeBehavior.humanReadableNameAlloc(
                self.allocator,
                expression_type,
            );
            defer self.allocator.free(rendered);
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Base slot expression of type '{s}' is not convertible to uint256.",
                .{rendered},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(1481), expression.location, message);
            return;
        }
        const base_slot = rational.numerator.toU256Wrapping();
        const layout_annotation = try storageLayoutAnnotation(layout);
        try layout_annotation.base_slot.assign(base_slot);

        const storage_size = try contractStorageSizeUpperBound(contract);
        if (storage_size > std.math.maxInt(u256) - base_slot) {
            try self.reporter.typeError(
                errorId(5015),
                expression.location,
                "Contract extends past the end of storage when this base slot value is specified.",
            );
        }
    }

    fn warnStorageLayoutBaseNearStorageEnd(
        self: *PostTypeContractLevelChecker,
        contract: *AST.Node,
    ) CheckError!void {
        if (self.reporter.hasErrors()) return;
        const storage_size = try contractStorageSizeUpperBound(contract);
        const definition = contract.payload.contract_definition;
        const base_slot: u256 = if (definition.storage_layout_specifier) |layout|
            (try (try storageLayoutAnnotation(layout)).base_slot.get()).*
        else
            0;
        if (storage_size > std.math.maxInt(u256) - base_slot)
            return error.InvalidAst;
        const slots_left = std.math.maxInt(u256) - base_slot - storage_size;
        if (slots_left > (@as(u256, 1) << 64)) return;
        const location = if (definition.storage_layout_specifier) |layout|
            layout.location
        else
            contract.location;
        const message = "This contract is very close to the end of storage. This limits its future upgradability.";
        if (try findLastStorageVariable(contract)) |last_variable| {
            var slots = Numeric.BigInt.fromU256(slots_left);
            defer slots.deinit();
            const rendered = StringUtils.formatNumberReadableAlloc(
                self.allocator,
                &slots,
                false,
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidBase => unreachable,
            };
            defer self.allocator.free(rendered);
            const secondary_message = try std.fmt.allocPrint(
                self.allocator,
                "There are {s} storage slots between this state variable and the end of storage.",
                .{rendered},
            );
            defer self.allocator.free(secondary_message);
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            try secondary.append(
                self.allocator,
                secondary_message,
                last_variable.location,
            );
            try self.reporter.warningWithSecondary(
                errorId(3495),
                location,
                message,
                &secondary,
            );
        } else try self.reporter.warning(errorId(3495), location, message);
    }
};

fn appendUniqueNode(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(*const AST.Node),
    node: *const AST.Node,
) std.mem.Allocator.Error!void {
    for (output.items) |existing| if (existing == node) return;
    try output.append(allocator, node);
}

fn nodeLessThan(_: void, left: *const AST.Node, right: *const AST.Node) bool {
    return ASTAnnotations.compatibilityId(left) < ASTAnnotations.compatibilityId(right);
}

fn contractStorageSizeUpperBound(contract: *const AST.Node) CheckError!u256 {
    const annotation = try contractAnnotationConst(contract);
    var size: u256 = 0;
    for (annotation.linearized_base_contracts) |base|
        for (base.payload.contract_definition.sub_nodes) |variable| {
            if (variable.nodeKind() != .variable_declaration or
                !ASTImplementation.isStateVariable(variable)) continue;
            const declaration = variable.payload.variable_declaration;
            if (declaration.mutability == .Constant or
                declaration.mutability == .Immutable or
                declaration.reference_location != .Unspecified) continue;
            const type_ref = (try variableAnnotationConst(variable)).type_ref orelse
                return error.InvalidAst;
            const bound = try TypeBehavior.storageSizeUpperBound(type_ref);
            size = std.math.add(u256, size, bound) catch return error.InvalidAst;
        };
    return size;
}

fn findLastStorageVariable(contract: *const AST.Node) CheckError!?*const AST.Node {
    const annotation = try contractAnnotationConst(contract);
    for (annotation.linearized_base_contracts) |base| {
        var index = base.payload.contract_definition.sub_nodes.len;
        while (index != 0) {
            index -= 1;
            const variable = base.payload.contract_definition.sub_nodes[index];
            if (variable.nodeKind() != .variable_declaration or
                !ASTImplementation.isStateVariable(variable)) continue;
            const declaration = variable.payload.variable_declaration;
            if (declaration.reference_location == .Unspecified and
                declaration.mutability != .Constant and
                declaration.mutability != .Immutable) return variable;
        }
    }
    return null;
}

fn expressionAnnotationConst(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.ExpressionAnnotation {
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

fn expressionAnnotation(node: *AST.Node) CheckError!*ASTAnnotations.ExpressionAnnotation {
    return @constCast(try expressionAnnotationConst(node));
}

fn variableAnnotationConst(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.VariableDeclarationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .variable_declaration => |*value| value,
        else => error.InvalidAst,
    };
}

fn contractAnnotation(
    node: *AST.Node,
) CheckError!*ASTAnnotations.ContractDefinitionAnnotation {
    const annotation = ASTAnnotations.annotation(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => error.InvalidAst,
    };
}

fn contractAnnotationConst(
    node: *const AST.Node,
) CheckError!*const ASTAnnotations.ContractDefinitionAnnotation {
    return contractAnnotation(@constCast(node));
}

fn storageLayoutAnnotation(
    node: *AST.Node,
) CheckError!*ASTAnnotations.StorageLayoutSpecifierAnnotation {
    const annotation = ASTAnnotations.annotation(node) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .storage_layout_specifier => |*value| value,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
