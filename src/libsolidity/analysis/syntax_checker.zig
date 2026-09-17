// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Ordinary Solidity syntax analysis translated from `SyntaxChecker.cpp`.
//!
//! The pass uses an explicit enter/leave stack. This retains upstream visitor
//! ordering while making temporary allocation and error propagation visible.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Features = @import("../ast/experimental_features.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;
const UTF8 = @import("../../libsolutil/utf8.zig");
const SetOnceError = @import("../../libsolutil/set_once.zig").SetOnceError;
const YulSemantics = @import("../../libyul/optimiser/semantics.zig");

pub const Options = struct {
    use_yul_optimizer: bool = false,
    experimental: bool = false,
};

pub const CheckError = std.mem.Allocator.Error ||
    Diagnostics.ReportError ||
    SetOnceError ||
    error{InvalidAst};

const Phase = enum { enter, leave };
const Frame = struct { node: *AST.Node, phase: Phase };

const SyntaxChecker = struct {
    tree: *AST.Tree,
    reporter: *Diagnostics.ErrorReporter,
    options: Options,
    frames: std.ArrayList(Frame) = .empty,
    placeholder_found: bool = false,
    version_pragma_found: bool = false,
    unchecked_arithmetic: bool = false,
    in_loop_depth: usize = 0,
    current_contract_kind: ?AST.ContractKind = null,
    source_unit: ?*AST.Node = null,

    fn deinit(self: *SyntaxChecker) void {
        self.frames.deinit(self.tree.backing_allocator);
        self.* = undefined;
    }

    fn run(self: *SyntaxChecker, root: *AST.Node) CheckError!void {
        try self.frames.append(self.tree.backing_allocator, .{
            .node = root,
            .phase = .enter,
        });
        while (self.frames.pop()) |frame| switch (frame.phase) {
            .enter => try self.enter(frame.node),
            .leave => try self.leave(frame.node),
        };
    }

    fn enter(self: *SyntaxChecker, node: *AST.Node) CheckError!void {
        const traverse = try self.visit(node);
        try self.frames.append(self.tree.backing_allocator, .{
            .node = node,
            .phase = .leave,
        });
        if (!traverse) return;

        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.tree.backing_allocator);
        try ASTImplementation.appendChildren(self.tree.backing_allocator, &children, node);
        var index = children.items.len;
        while (index != 0) {
            index -= 1;
            try self.frames.append(self.tree.backing_allocator, .{
                .node = @constCast(children.items[index]),
                .phase = .enter,
            });
        }
    }

    fn leave(self: *SyntaxChecker, node: *AST.Node) CheckError!void {
        switch (node.payload) {
            .source_unit => try self.endSourceUnit(node),
            .modifier_definition => |modifier| try self.endModifier(node, modifier),
            .while_statement, .for_statement => {
                if (self.in_loop_depth == 0) return error.InvalidAst;
                self.in_loop_depth -= 1;
            },
            .block => |block| {
                if (block.unchecked) self.unchecked_arithmetic = false;
            },
            .contract_definition => self.current_contract_kind = null,
            else => {},
        }
    }

    fn visit(self: *SyntaxChecker, node: *AST.Node) CheckError!bool {
        if (node.experimentalSolidityOnly()) {
            const source = self.source_unit orelse return error.InvalidAst;
            if (!source.payload.source_unit.experimental_solidity) return error.InvalidAst;
        }

        return switch (node.payload) {
            .source_unit => self.visitSourceUnit(node),
            .pragma_directive => |pragma| self.visitPragma(node, pragma),
            .modifier_definition => self.visitModifier(),
            .if_statement => |statement| self.visitIf(statement),
            .while_statement => |statement| self.visitWhile(statement),
            .for_statement => |statement| self.visitFor(statement),
            .block => |block| self.visitBlock(node, block),
            .continue_statement => self.visitContinue(node),
            .break_statement => self.visitBreak(node),
            .throw_statement => self.visitThrow(node),
            .literal => |literal| self.visitLiteral(node, literal),
            .unary_operation => |operation| self.visitUnary(operation),
            .inline_assembly => self.visitInlineAssembly(node),
            .placeholder_statement => self.visitPlaceholder(node),
            .contract_definition => |contract| self.visitContract(node, contract),
            .using_for_directive => |using_for| self.visitUsingFor(node, using_for),
            .function_definition => |function| self.visitFunction(node, function),
            .function_type_name => |function_type| self.visitFunctionType(function_type),
            .struct_definition => |structure| self.visitStruct(node, structure),
            else => true,
        };
    }

    fn visitSourceUnit(self: *SyntaxChecker, node: *AST.Node) CheckError!bool {
        if (self.source_unit != null) return error.InvalidAst;
        self.version_pragma_found = false;
        self.source_unit = node;
        _ = try sourceUnitAnnotation(self.tree, node);
        return true;
    }

    fn endSourceUnit(self: *SyntaxChecker, node: *AST.Node) CheckError!void {
        if (self.source_unit != node) return error.InvalidAst;
        const annotation = try sourceUnitAnnotation(self.tree, node);
        if (!self.version_pragma_found) try self.reporter.warning(
            errorId(3420),
            .{ .source_name = node.location.source_name },
            "Source file does not specify required compiler version! Consider adding \"pragma solidity ^0.8.36;\"",
        );
        if (!annotation.use_abi_coder_v2.isSet())
            try annotation.use_abi_coder_v2.assign(true);
        self.source_unit = null;
    }

    fn visitPragma(
        self: *SyntaxChecker,
        node: *AST.Node,
        pragma: AST.PragmaDirective,
    ) CheckError!bool {
        if (pragma.tokens.len == 0 or pragma.tokens.len != pragma.literals.len)
            return error.InvalidAst;
        if (pragma.tokens[0] != .Identifier) {
            const message = try std.fmt.allocPrint(
                self.tree.backing_allocator,
                "Invalid pragma \"{s}\"",
                .{pragma.literals[0]},
            );
            defer self.tree.backing_allocator.free(message);
            try self.reporter.syntaxError(errorId(5226), node.location, message);
            return true;
        }
        const name = pragma.literals[0];
        if (std.mem.eql(u8, name, "experimental"))
            try self.checkExperimentalPragma(node, pragma.literals[1..])
        else if (std.mem.eql(u8, name, "abicoder"))
            try self.checkAbiCoderPragma(node, pragma.literals)
        else if (std.mem.eql(u8, name, "solidity"))
            self.version_pragma_found = true
        else {
            const message = try std.fmt.allocPrint(
                self.tree.backing_allocator,
                "Unknown pragma \"{s}\"",
                .{name},
            );
            defer self.tree.backing_allocator.free(message);
            try self.reporter.syntaxError(errorId(4936), node.location, message);
        }
        return true;
    }

    fn checkExperimentalPragma(
        self: *SyntaxChecker,
        node: *AST.Node,
        literals: []const []const u8,
    ) CheckError!void {
        if (literals.len == 0) return self.reporter.syntaxError(
            errorId(9679),
            node.location,
            "Experimental feature name is missing.",
        );
        if (literals.len > 1) return self.reporter.syntaxError(
            errorId(6022),
            node.location,
            "Stray arguments.",
        );
        const literal = literals[0];
        if (literal.len == 0) return self.reporter.syntaxError(
            errorId(3250),
            node.location,
            "Empty experimental feature name is invalid.",
        );
        const feature = Features.fromName(literal) orelse
            return self.reporter.syntaxError(
                errorId(8491),
                node.location,
                "Unsupported experimental feature name.",
            );
        const source = self.source_unit orelse return error.InvalidAst;
        const annotation = try sourceUnitAnnotation(self.tree, source);
        if (containsFeature(annotation.experimental_features.items, feature))
            return self.reporter.syntaxError(
                errorId(1231),
                node.location,
                "Duplicate experimental feature name.",
            );
        try annotation.experimental_features.append(self.tree.allocator(), feature);

        if (!Features.suppressesWarning(feature)) {
            if (!self.options.experimental) try self.reporter.syntaxError(
                errorId(2816),
                node.location,
                "Experimental pragmas can only be used if experimental mode is enabled. To enable experimental mode, use the --experimental flag.",
            ) else try self.reporter.warning(
                errorId(2264),
                node.location,
                "Experimental features are turned on. Do not use experimental features on live deployments.",
            );
        }

        if (feature == .ABIEncoderV2) {
            if (annotation.use_abi_coder_v2.isSet()) {
                if (!(try annotation.use_abi_coder_v2.get()).*)
                    try self.reporter.syntaxError(
                        errorId(8273),
                        node.location,
                        "ABI coder v1 has already been selected through \"pragma abicoder v1\".",
                    );
            } else try annotation.use_abi_coder_v2.assign(true);
        }
    }

    fn checkAbiCoderPragma(
        self: *SyntaxChecker,
        node: *AST.Node,
        literals: []const []const u8,
    ) CheckError!void {
        const valid = literals.len == 2 and
            (std.mem.eql(u8, literals[1], "v1") or std.mem.eql(u8, literals[1], "v2"));
        const source = self.source_unit orelse return error.InvalidAst;
        const annotation = try sourceUnitAnnotation(self.tree, source);
        if (!valid) {
            try self.reporter.syntaxError(
                errorId(2745),
                node.location,
                "Expected either \"pragma abicoder v1\" or \"pragma abicoder v2\".",
            );
        } else if (annotation.use_abi_coder_v2.isSet()) {
            try self.reporter.syntaxError(
                errorId(3845),
                node.location,
                "ABI coder has already been selected for this source unit.",
            );
        } else try annotation.use_abi_coder_v2.assign(std.mem.eql(u8, literals[1], "v2"));

        if (literals.len > 1 and std.mem.eql(u8, literals[1], "v1"))
            try self.reporter.warning(
                errorId(9511),
                node.location,
                "ABI coder v1 is deprecated and scheduled for removal. Use ABI coder v2 instead.",
            );
    }

    fn visitModifier(self: *SyntaxChecker) bool {
        self.placeholder_found = false;
        return true;
    }

    fn endModifier(
        self: *SyntaxChecker,
        node: *AST.Node,
        modifier: AST.ModifierDefinition,
    ) CheckError!void {
        if (modifier.implemented() and !self.placeholder_found)
            try self.reporter.syntaxError(
                errorId(2883),
                modifier.body.?.location,
                "Modifier body does not contain '_'.",
            );
        if (modifier.callable.marked_virtual)
            try self.reporter.warning(
                errorId(8429),
                node.location,
                "Virtual modifiers are deprecated and scheduled for removal.",
            );
        self.placeholder_found = false;
    }

    fn checkSingleStatementVariableDeclaration(
        self: *SyntaxChecker,
        statement: *const AST.Node,
    ) CheckError!void {
        if (statement.nodeKind() == .variable_declaration_statement)
            try self.reporter.syntaxError(
                errorId(9079),
                statement.location,
                "Variable declarations can only be used inside blocks.",
            );
    }

    fn visitIf(self: *SyntaxChecker, statement: AST.IfStatement) CheckError!bool {
        try self.checkSingleStatementVariableDeclaration(statement.true_body);
        if (statement.false_body) |body| try self.checkSingleStatementVariableDeclaration(body);
        return true;
    }

    fn visitWhile(self: *SyntaxChecker, statement: AST.WhileStatement) CheckError!bool {
        self.in_loop_depth += 1;
        try self.checkSingleStatementVariableDeclaration(statement.body);
        return true;
    }

    fn visitFor(self: *SyntaxChecker, statement: AST.ForStatement) CheckError!bool {
        self.in_loop_depth += 1;
        try self.checkSingleStatementVariableDeclaration(statement.body);
        return true;
    }

    fn visitBlock(
        self: *SyntaxChecker,
        node: *AST.Node,
        block: AST.Block,
    ) CheckError!bool {
        if (block.unchecked) {
            if (self.unchecked_arithmetic)
                try self.reporter.syntaxError(
                    errorId(1941),
                    node.location,
                    "\"unchecked\" blocks cannot be nested.",
                );
            self.unchecked_arithmetic = true;
        }
        return true;
    }

    fn visitContinue(self: *SyntaxChecker, node: *AST.Node) CheckError!bool {
        if (self.in_loop_depth == 0) try self.reporter.syntaxError(
            errorId(4123),
            node.location,
            "\"continue\" has to be in a \"for\" or \"while\" loop.",
        );
        return true;
    }

    fn visitBreak(self: *SyntaxChecker, node: *AST.Node) CheckError!bool {
        if (self.in_loop_depth == 0) try self.reporter.syntaxError(
            errorId(6102),
            node.location,
            "\"break\" has to be in a \"for\" or \"while\" loop.",
        );
        return true;
    }

    fn visitThrow(self: *SyntaxChecker, node: *AST.Node) CheckError!bool {
        try self.reporter.syntaxError(
            errorId(4538),
            node.location,
            "\"throw\" is deprecated in favour of \"revert()\", \"require()\" and \"assert()\".",
        );
        return true;
    }

    fn visitLiteral(
        self: *SyntaxChecker,
        node: *AST.Node,
        literal: AST.Literal,
    ) CheckError!bool {
        if (literal.token == .UnicodeStringLiteral) {
            var invalid_position: usize = undefined;
            if (!UTF8.validateUTF8(literal.value, &invalid_position)) {
                const message = try std.fmt.allocPrint(
                    self.tree.backing_allocator,
                    "Contains invalid UTF-8 sequence at position {d}.",
                    .{invalid_position},
                );
                defer self.tree.backing_allocator.free(message);
                try self.reporter.syntaxError(errorId(8452), node.location, message);
            }
        }
        if (literal.token != .Number) return true;
        if (literal.value.len == 0) return error.InvalidAst;
        if (literal.value[literal.value.len - 1] == '_') {
            try self.reporter.syntaxError(
                errorId(2090),
                node.location,
                "Invalid use of underscores in number literal. No trailing underscores allowed.",
            );
            return true;
        }
        if (std.mem.find(u8, literal.value, "__") != null) {
            try self.reporter.syntaxError(
                errorId(2990),
                node.location,
                "Invalid use of underscores in number literal. Only one consecutive underscore between digits is allowed.",
            );
            return true;
        }
        if (!ASTImplementation.literalIsHexNumber(literal)) {
            const checks = [_]struct { pattern: []const u8, id: u64, message: []const u8 }{
                .{ .pattern = "._", .id = 3891, .message = "Invalid use of underscores in number literal. No underscores in front of the fraction part allowed." },
                .{ .pattern = "_.", .id = 1023, .message = "Invalid use of underscores in number literal. No underscores in front of the fraction part allowed." },
                .{ .pattern = "_e", .id = 6415, .message = "Invalid use of underscores in number literal. No underscore at the end of the mantissa allowed." },
                .{ .pattern = "e_", .id = 6165, .message = "Invalid use of underscores in number literal. No underscore in front of exponent allowed." },
            };
            for (checks) |check|
                if (std.mem.find(u8, literal.value, check.pattern) != null)
                    try self.reporter.syntaxError(errorId(check.id), node.location, check.message);
        }
        return true;
    }

    fn visitUnary(_: *SyntaxChecker, operation: AST.UnaryOperation) CheckError!bool {
        if (operation.operator == .Add) return error.InvalidAst;
        return true;
    }

    fn visitInlineAssembly(self: *SyntaxChecker, node: *AST.Node) CheckError!bool {
        const annotation_value = try ASTAnnotations.ensure(self.tree, node);
        const annotation = switch (annotation_value.*) {
            .inline_assembly => |*value| value,
            else => return error.InvalidAst,
        };
        const assembly = node.payload.inline_assembly;
        if (assembly.flags) |flags| for (flags) |maybe_flag| {
            const flag = maybe_flag orelse continue;
            if (std.mem.eql(u8, flag, "memory-safe")) {
                if (annotation.marked_memory_safe)
                    try self.reporter.syntaxError(
                        errorId(7026),
                        node.location,
                        "Inline assembly marked memory-safe multiple times.",
                    );
                annotation.marked_memory_safe = true;
            } else {
                const message = try std.fmt.allocPrint(
                    self.tree.backing_allocator,
                    "Unknown inline assembly flag: \"{s}\"",
                    .{flag},
                );
                defer self.tree.backing_allocator.free(message);
                try self.reporter.warning(errorId(4430), node.location, message);
            }
        };
        if (!self.options.use_yul_optimizer) return false;
        const dialect = assembly.dialect orelse return error.InvalidAst;
        const operations = assembly.operations orelse return error.InvalidAst;
        const contains_msize = YulSemantics.MSizeFinder.containsMSize(
            dialect,
            operations.root(),
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.InvalidAst,
        };
        if (contains_msize) try self.reporter.syntaxError(
            errorId(6553),
            node.location,
            "The msize instruction cannot be used when the Yul optimizer is activated because it can change its semantics. Either disable the Yul optimizer or do not use the instruction.",
        );
        return false;
    }

    fn visitPlaceholder(self: *SyntaxChecker, node: *AST.Node) CheckError!bool {
        if (self.unchecked_arithmetic)
            try self.reporter.syntaxError(
                errorId(2573),
                node.location,
                "The placeholder statement \"_\" cannot be used inside an \"unchecked\" block.",
            );
        self.placeholder_found = true;
        return true;
    }

    fn visitContract(
        self: *SyntaxChecker,
        _: *AST.Node,
        contract: AST.ContractDefinition,
    ) CheckError!bool {
        if (self.current_contract_kind != null) return error.InvalidAst;
        self.current_contract_kind = contract.contract_kind;
        for (contract.sub_nodes) |child| {
            if (child.nodeKind() != .function_definition) continue;
            const function = child.payload.function_definition;
            if (std.mem.eql(
                u8,
                function.callable.declaration.name,
                contract.declaration.name,
            )) try self.reporter.syntaxError(
                errorId(5796),
                child.location,
                "Functions are not allowed to have the same name as the contract. If you intend this to be a constructor, use \"constructor(...) { ... }\" to define it.",
            );
        }
        return true;
    }

    fn visitUsingFor(
        self: *SyntaxChecker,
        node: *AST.Node,
        using_for: AST.UsingForDirective,
    ) CheckError!bool {
        if (!using_for.uses_braces and
            (using_for.functions_and_operators.len != 1 or
                using_for.functions_and_operators[0].operator != null))
            return error.InvalidAst;
        if (self.current_contract_kind == null and using_for.type_name == null)
            try self.reporter.syntaxError(
                errorId(8118),
                node.location,
                "The type has to be specified explicitly at file level (cannot use '*').",
            )
        else if (using_for.uses_braces and using_for.type_name == null)
            try self.reporter.syntaxError(
                errorId(3349),
                node.location,
                "The type has to be specified explicitly when attaching specific functions.",
            );
        if (using_for.global and using_for.type_name == null)
            try self.reporter.syntaxError(
                errorId(2854),
                node.location,
                "Can only globally attach functions to specific types.",
            );
        if (using_for.global and self.current_contract_kind != null)
            try self.reporter.syntaxError(
                errorId(3367),
                node.location,
                "\"global\" can only be used at file level.",
            );
        if (self.current_contract_kind == .Interface)
            try self.reporter.syntaxError(
                errorId(9088),
                node.location,
                "The \"using for\" directive is not allowed inside interfaces.",
            );
        return true;
    }

    fn visitFunction(
        self: *SyntaxChecker,
        node: *AST.Node,
        function: AST.FunctionDefinition,
    ) CheckError!bool {
        if (self.source_unit) |source|
            if (source.payload.source_unit.experimental_solidity) return true;

        const is_constructor = function.kind == .Constructor;
        if (!function.free and !is_constructor and
            function.callable.declaration.visibility == .Default)
        {
            const suggested = if (function.kind == .Fallback or
                function.kind == .Receive or
                self.current_contract_kind == .Interface)
                "external"
            else
                "public";
            const message = try std.fmt.allocPrint(
                self.tree.backing_allocator,
                "No visibility specified. Did you intend to add \"{s}\"?",
                .{suggested},
            );
            defer self.tree.backing_allocator.free(message);
            try self.reporter.syntaxError(errorId(4937), node.location, message);
        } else if (function.free) {
            if (function.callable.declaration.visibility != .Default)
                try self.reporter.syntaxError(
                    errorId(4126),
                    node.location,
                    "Free functions cannot have visibility.",
                );
            if (!function.implemented())
                try self.reporter.typeError(
                    errorId(4668),
                    node.location,
                    "Free functions must be implemented.",
                );
        }

        if (self.current_contract_kind == .Interface and function.modifiers.len != 0)
            try self.reporter.syntaxError(
                errorId(5842),
                node.location,
                "Functions in interfaces cannot have modifiers.",
            )
        else if (!function.implemented() and function.modifiers.len != 0)
            try self.reporter.syntaxError(
                errorId(2668),
                node.location,
                "Functions without implementation cannot have modifiers.",
            );
        return true;
    }

    fn visitFunctionType(
        self: *SyntaxChecker,
        function_type: AST.FunctionTypeName,
    ) CheckError!bool {
        for (function_type.parameter_types.payload.parameter_list.parameters) |declaration|
            if (declaration.declarationConst()) |data|
                if (data.name.len != 0) try self.reporter.warning(
                    errorId(6162),
                    declaration.location,
                    "Naming function type parameters is deprecated.",
                );
        for (function_type.return_types.payload.parameter_list.parameters) |declaration|
            if (declaration.declarationConst()) |data|
                if (data.name.len != 0) try self.reporter.syntaxError(
                    errorId(7304),
                    declaration.location,
                    "Return parameters in function types may not be named.",
                );
        return true;
    }

    fn visitStruct(
        self: *SyntaxChecker,
        node: *AST.Node,
        structure: AST.StructDefinition,
    ) CheckError!bool {
        if (structure.members.len == 0)
            try self.reporter.syntaxError(
                errorId(5306),
                node.location,
                "Defining empty structs is disallowed.",
            );
        return true;
    }
};

pub fn checkSyntax(
    tree: *AST.Tree,
    root: *AST.Node,
    reporter: *Diagnostics.ErrorReporter,
    options: Options,
) CheckError!bool {
    var checker: SyntaxChecker = .{
        .tree = tree,
        .reporter = reporter,
        .options = options,
    };
    defer checker.deinit();
    try checker.run(root);
    return !reporter.hasErrors();
}

fn sourceUnitAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.SourceUnitAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .source_unit => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn containsFeature(
    items: []const Features.ExperimentalFeature,
    feature: Features.ExperimentalFeature,
) bool {
    for (items) |item| if (item == feature) return true;
    return false;
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}

test "syntax checker emits ordinary control-flow and declaration diagnostics in order" {
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../parsing/parser.zig");

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { " ++
        "struct Empty {} " ++
        "modifier m() {} " ++
        "function C() {} " ++
        "function f() { break; continue; throw; } " ++
        "}";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "Syntax.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
    try std.testing.expect(!reporter.hasErrors());

    _ = try checkSyntax(&parsed.tree, parsed.tree.root.?, &reporter, .{});
    const diagnostics = reporter.diagnostics();
    const expected = [_]u64{ 5796, 5306, 2883, 4937, 4937, 6102, 4123, 4538, 3420 };
    try std.testing.expectEqual(expected.len, diagnostics.len);
    for (expected, diagnostics) |id, diagnostic|
        try std.testing.expectEqual(id, diagnostic.error_id.value);
}

test "syntax checker owns pragma state and inline-assembly safety flags" {
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../parsing/parser.zig");

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "pragma solidity ^0.8.36; pragma abicoder v1; pragma abicoder v2; " ++
        "contract C { function f() external { " ++
        "assembly (\"memory-safe\", \"memory-safe\", \"future\") {} " ++
        "} }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "Flags.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
    try std.testing.expect(!reporter.hasErrors());

    _ = try checkSyntax(&parsed.tree, parsed.tree.root.?, &reporter, .{});
    const diagnostics = reporter.diagnostics();
    const expected = [_]u64{ 9511, 3845, 7026, 4430 };
    try std.testing.expectEqual(expected.len, diagnostics.len);
    for (expected, diagnostics) |id, diagnostic|
        try std.testing.expectEqual(id, diagnostic.error_id.value);

    const root_annotation = try sourceUnitAnnotation(&parsed.tree, parsed.tree.root.?);
    try std.testing.expect(!(try root_annotation.use_abi_coder_v2.get()).*);
    const function = parsed.tree.root.?.payload.source_unit.nodes[3]
        .payload.contract_definition.sub_nodes[0].payload.function_definition;
    const inline_assembly = function.body.?.payload.block.statements[0];
    const inline_annotation = ASTAnnotations.annotation(inline_assembly).?.inline_assembly;
    try std.testing.expect(inline_annotation.marked_memory_safe);
}
