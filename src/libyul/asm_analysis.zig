// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Yul semantic analysis over scope-filled ASTs.
//!
//! Includes the generic dialect path and the EVM-version-specific instruction
//! validator used by `EVMDialect`.

const std = @import("std");
const AST = @import("ast.zig");
const AsmAnalysisInfo = @import("asm_analysis_info.zig").AsmAnalysisInfo;
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const ObjectModule = @import("object.zig");
const ScopeModule = @import("scope.zig");
const ScopeFiller = @import("scope_filler.zig").ScopeFiller;
const SideEffects = @import("side_effects.zig").SideEffects;
const StringUtils = @import("../libsolutil/string_utils.zig");
const Token = @import("../liblangutil/token.zig");
const Utilities = @import("utilities.zig");
const YulName = @import("yul_name.zig").YulName;
const EVMDialectModule = @import("backends/evm/evm_dialect.zig");

pub const IdentifierContext = enum {
    l_value,
    r_value,
    variable_declaration,
    non_external,
};

pub const Resolver = struct {
    context: ?*anyopaque = null,
    resolve: ?*const fn (?*anyopaque, *const AST.Identifier, IdentifierContext, bool) bool = null,

    fn call(
        self: Resolver,
        identifier: *const AST.Identifier,
        identifier_context: IdentifierContext,
        inside_function: bool,
    ) bool {
        const callback = self.resolve orelse return false;
        return callback(self.context, identifier, identifier_context, inside_function);
    }
};

pub const ObjectStructure = struct {
    object_name: []const u8 = "",
    object_paths: []const []const u8 = &.{},
    data_paths: []const []const u8 = &.{},

    pub fn contains(self: ObjectStructure, path: []const u8) bool {
        for (self.object_paths) |candidate| if (std.mem.eql(u8, candidate, path)) return true;
        for (self.data_paths) |candidate| if (std.mem.eql(u8, candidate, path)) return true;
        return false;
    }

    pub fn fromObjectStructure(structure: *const ObjectModule.Structure) ObjectStructure {
        return .{
            .object_name = structure.object_name,
            .object_paths = structure.object_paths.values.items,
            .data_paths = structure.data_paths.values.items,
        };
    }
};

pub const InstructionValidator = struct {
    context: ?*anyopaque = null,
    validate: ?*const fn (
        ?*anyopaque,
        []const u8,
        Diagnostics.SourceLocation,
        *Diagnostics.ErrorReporter,
    ) Diagnostics.ReportError!bool = null,

    fn call(
        self: InstructionValidator,
        name: []const u8,
        location: Diagnostics.SourceLocation,
        reporter: *Diagnostics.ErrorReporter,
    ) Diagnostics.ReportError!bool {
        const callback = self.validate orelse return false;
        return callback(self.context, name, location, reporter);
    }
};

pub fn instructionValidatorForEVMDialect(
    dialect: *const EVMDialectModule.EVMDialect,
) InstructionValidator {
    return .{
        .context = dialect.instructionValidatorContext(),
        .validate = EVMDialectModule.EVMDialect.validateInstructionCallback,
    };
}

pub const AnalyzeError = std.mem.Allocator.Error || error{
    FatalDiagnostic,
    InvalidAst,
    InvalidLiteral,
    InvalidNumberLiteral,
    InvalidYulStringHandle,
    UnexpectedBoolLiteral,
    UnknownBuiltin,
    MissingObjectCode,
    AnalysisFailed,
};

pub const AsmAnalyzer = struct {
    allocator: std.mem.Allocator,
    resolver: Resolver,
    info: *AsmAnalysisInfo,
    error_reporter: *Diagnostics.ErrorReporter,
    dialect: AST.Dialect,
    object_structure: ObjectStructure,
    instruction_validator: InstructionValidator,
    current_scope: ?*ScopeModule.Scope = null,
    active_variables: std.AutoHashMap(*const ScopeModule.Variable, void),
    current_for_loop: ?*const AST.ForLoop = null,
    side_effects: SideEffects = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        info: *AsmAnalysisInfo,
        error_reporter: *Diagnostics.ErrorReporter,
        dialect: AST.Dialect,
        resolver: Resolver,
        object_structure: ObjectStructure,
        instruction_validator: InstructionValidator,
    ) AsmAnalyzer {
        return .{
            .allocator = allocator,
            .resolver = resolver,
            .info = info,
            .error_reporter = error_reporter,
            .dialect = dialect,
            .object_structure = object_structure,
            .instruction_validator = instruction_validator,
            .active_variables = std.AutoHashMap(*const ScopeModule.Variable, void).init(allocator),
        };
    }

    pub fn deinit(self: *AsmAnalyzer) void {
        self.active_variables.deinit();
        self.* = undefined;
    }

    pub fn analyze(self: *AsmAnalyzer, block: *const AST.Block) AnalyzeError!bool {
        const watcher = self.error_reporter.errorWatcher();
        var filler = try ScopeFiller.init(self.info, self.error_reporter);
        const filled = filler.fill(block) catch |err| switch (err) {
            error.FatalDiagnostic => return watcher.ok(),
            else => return err,
        };
        if (!filled) return false;
        self.visitBlock(block) catch |err| switch (err) {
            error.FatalDiagnostic => return watcher.ok(),
            else => return err,
        };
        return watcher.ok();
    }

    pub fn sideEffects(self: *const AsmAnalyzer) SideEffects {
        return self.side_effects;
    }

    fn visitExpression(self: *AsmAnalyzer, expression: *const AST.Expression) AnalyzeError!usize {
        return switch (expression.*) {
            .literal => |*literal| self.visitLiteral(literal),
            .identifier => |*identifier| self.visitIdentifier(identifier),
            .function_call => |*call| self.visitFunctionCall(call),
        };
    }

    fn visitStatement(self: *AsmAnalyzer, statement: *const AST.Statement) AnalyzeError!void {
        switch (statement.*) {
            .expression_statement => |*node| try self.visitExpressionStatement(node),
            .assignment => |*node| try self.visitAssignment(node),
            .variable_declaration => |*node| try self.visitVariableDeclaration(node),
            .function_definition => |*node| try self.visitFunctionDefinition(node),
            .if_statement => |*node| try self.visitIf(node),
            .switch_statement => |*node| try self.visitSwitch(node),
            .for_loop => |*node| try self.visitForLoop(node),
            .block => |*node| try self.visitBlock(node),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitLiteral(self: *AsmAnalyzer, literal: *const AST.Literal) AnalyzeError!usize {
        var erroneous = false;
        const hint = literal.value.hint() catch null;
        if (literal.kind == .String and !literal.value.unlimited() and hint != null and hint.?.len > 32) {
            erroneous = true;
            try self.reportFormat(
                .TypeError,
                3069,
                nativeDebug(literal.debug_data),
                "String literal too long ({d} > 32)",
                .{hint.?.len},
            );
        } else if (literal.kind == .Number and hint != null and numberExceedsU256(hint.?)) {
            erroneous = true;
            try self.error_reporter.typeError(
                .{ .value = 6708 },
                nativeDebug(literal.debug_data),
                "Number literal too large (> 256 bits)",
            );
        }
        if (!erroneous and !Utilities.validLiteral(literal)) return error.InvalidLiteral;
        return 1;
    }

    fn visitIdentifier(self: *AsmAnalyzer, identifier: *const AST.Identifier) AnalyzeError!usize {
        const scope = self.current_scope orelse return error.InvalidAst;
        const watcher = self.error_reporter.errorWatcher();
        if (scope.lookup(identifier.name)) |resolved| {
            switch (resolved.*) {
                .variable => |*variable| {
                    if (!self.active_variables.contains(variable)) {
                        try self.reportFormat(
                            .DeclarationError,
                            4990,
                            nativeDebug(identifier.debug_data),
                            "Variable {s} used before it was declared.",
                            .{try identifier.name.str()},
                        );
                    }
                },
                .function => try self.reportFormat(
                    .TypeError,
                    6041,
                    nativeDebug(identifier.debug_data),
                    "Function {s} used without being called.",
                    .{try identifier.name.str()},
                ),
            }
            if (self.resolver.resolve != null) {
                _ = self.resolver.call(identifier, .non_external, scope.insideFunction());
            }
        } else {
            const found = self.resolver.resolve != null and
                self.resolver.call(identifier, .r_value, scope.insideFunction());
            if (!found and watcher.ok()) {
                try self.reportFormat(
                    .DeclarationError,
                    8198,
                    nativeDebug(identifier.debug_data),
                    "Identifier \"{s}\" not found.",
                    .{try identifier.name.str()},
                );
            }
        }
        return 1;
    }

    fn visitExpressionStatement(
        self: *AsmAnalyzer,
        statement: *const AST.ExpressionStatement,
    ) AnalyzeError!void {
        const watcher = self.error_reporter.errorWatcher();
        const num_returns = try self.visitExpression(&statement.expression);
        if (watcher.ok() and num_returns > 0) {
            try self.reportFormat(
                .TypeError,
                3083,
                nativeDebug(statement.debug_data),
                "Top-level expressions are not supposed to return values (this expression returns {d} value{s}). Use ``pop()`` or assign them.",
                .{ num_returns, if (num_returns == 1) "" else "s" },
            );
        }
    }

    fn visitAssignment(self: *AsmAnalyzer, assignment: *const AST.Assignment) AnalyzeError!void {
        const value = assignment.value orelse return error.InvalidAst;
        const num_variables = assignment.variable_names.items.len;
        if (num_variables == 0) return error.InvalidAst;
        var variables = std.AutoHashMap(YulName, void).init(self.allocator);
        defer variables.deinit();
        for (assignment.variable_names.items) |*variable| {
            const result = try variables.getOrPut(variable.name);
            if (result.found_existing) {
                try self.reportFormat(
                    .DeclarationError,
                    9005,
                    nativeDebug(assignment.debug_data),
                    "Variable {s} occurs multiple times on the left-hand side of the assignment.",
                    .{try variable.name.str()},
                );
            }
        }
        const num_values = try self.visitExpression(value);
        if (num_values != num_variables) {
            const names = try self.joinIdentifierNames(assignment.variable_names.items);
            defer self.allocator.free(names);
            try self.reportFormat(
                .DeclarationError,
                8678,
                nativeDebug(assignment.debug_data),
                "Variable count for assignment to \"{s}\" does not match number of values ({d} vs. {d})",
                .{ names, num_variables, num_values },
            );
        }
        for (assignment.variable_names.items) |*variable| try self.checkAssignment(variable);
    }

    fn visitVariableDeclaration(
        self: *AsmAnalyzer,
        declaration: *const AST.VariableDeclaration,
    ) AnalyzeError!void {
        const scope = self.current_scope orelse return error.InvalidAst;
        if (self.resolver.resolve != null) {
            for (declaration.variables.items) |*variable| {
                const identifier: AST.Identifier = .{
                    .debug_data = variable.debug_data,
                    .name = variable.name,
                };
                _ = self.resolver.call(&identifier, .variable_declaration, scope.insideFunction());
            }
        }
        for (declaration.variables.items) |*variable| {
            try self.expectValidIdentifier(variable.name, nativeDebug(variable.debug_data));
        }
        if (declaration.value) |value| {
            const num_values = try self.visitExpression(value);
            if (num_values != declaration.variables.items.len) {
                const names = try self.joinDeclarationNames(declaration.variables.items);
                defer self.allocator.free(names);
                try self.reportFormat(
                    .DeclarationError,
                    3812,
                    nativeDebug(declaration.debug_data),
                    "Variable count mismatch for declaration of \"{s}\": {d} variables and {d} values.",
                    .{ names, declaration.variables.items.len, num_values },
                );
            }
        }
        for (declaration.variables.items) |variable| {
            const resolved = scope.identifiers.getPtr(variable.name) orelse return error.InvalidAst;
            switch (resolved.*) {
                .variable => |*scope_variable| try self.active_variables.put(scope_variable, {}),
                .function => return error.InvalidAst,
            }
        }
    }

    fn visitFunctionDefinition(
        self: *AsmAnalyzer,
        definition: *const AST.FunctionDefinition,
    ) AnalyzeError!void {
        try self.expectValidIdentifier(definition.name, nativeDebug(definition.debug_data));
        const virtual_block = self.info.getVirtualBlock(definition) orelse return error.InvalidAst;
        const variable_scope = self.info.getScope(virtual_block) orelse return error.InvalidAst;
        for (definition.parameters.items) |variable| {
            try self.activateFunctionVariable(variable_scope, variable);
        }
        for (definition.return_variables.items) |variable| {
            try self.activateFunctionVariable(variable_scope, variable);
        }
        try self.visitBlock(&definition.body);
    }

    fn activateFunctionVariable(
        self: *AsmAnalyzer,
        variable_scope: *ScopeModule.Scope,
        variable: AST.NameWithDebugData,
    ) AnalyzeError!void {
        try self.expectValidIdentifier(variable.name, nativeDebug(variable.debug_data));
        const resolved = variable_scope.identifiers.getPtr(variable.name) orelse return error.InvalidAst;
        switch (resolved.*) {
            .variable => |*scope_variable| try self.active_variables.put(scope_variable, {}),
            .function => return error.InvalidAst,
        }
    }

    fn visitFunctionCall(self: *AsmAnalyzer, call: *const AST.FunctionCall) AnalyzeError!usize {
        const scope = self.current_scope orelse return error.InvalidAst;
        const watcher = self.error_reporter.errorWatcher();
        var num_parameters: ?usize = null;
        var num_returns: ?usize = null;
        var literal_arguments: ?[]const ?AST.LiteralKind = null;
        switch (call.function_name) {
            .builtin => |builtin_name| {
                const builtin = try self.dialect.builtin(builtin_name.handle);
                if (std.mem.eql(u8, builtin.name, "selfdestruct")) {
                    try self.error_reporter.warning(
                        .{ .value = 1699 },
                        nativeDebug(builtin_name.debug_data),
                        "\"selfdestruct\" has been deprecated. Note that, starting from the Cancun hard fork, the underlying opcode no longer deletes the code and data associated with an account and only transfers its Ether to the beneficiary, unless executed in the same transaction in which the contract was created (see EIP-6780). Any use in newly deployed contracts is strongly discouraged even if the new behavior is taken into account. Future changes to the EVM might further reduce the functionality of the opcode.",
                    );
                } else if (std.mem.eql(u8, builtin.name, "tstore") and
                    !self.error_reporter.hasError(.{ .value = 2394 }))
                {
                    try self.error_reporter.warning(
                        .{ .value = 2394 },
                        nativeDebug(builtin_name.debug_data),
                        "Transient storage as defined by EIP-1153 can break the composability of smart contracts: Since transient storage is cleared only at the end of the transaction and not at the end of the outermost call frame to the contract within a transaction, your contract may unintentionally misbehave when invoked multiple times in a complex transaction. To avoid this, be sure to clear all transient storage at the end of any call to your contract. The use of transient storage for reentrancy guards that are cleared at the end of the call is safe.",
                    );
                }
                num_parameters = builtin.num_parameters;
                num_returns = builtin.num_returns;
                if (builtin.literal_arguments.len != 0) literal_arguments = builtin.literal_arguments;
                _ = try self.instruction_validator.call(
                    builtin.name,
                    nativeFunctionName(&call.function_name),
                    self.error_reporter,
                );
                self.side_effects.combineAssign(builtin.side_effects);
            },
            .identifier => |*identifier| {
                if (scope.lookup(identifier.name)) |resolved| {
                    switch (resolved.*) {
                        .variable => try self.error_reporter.typeError(
                            .{ .value = 4202 },
                            nativeDebug(identifier.debug_data),
                            "Attempt to call variable instead of function.",
                        ),
                        .function => |function| {
                            num_parameters = function.num_arguments;
                            num_returns = function.num_returns;
                        },
                    }
                    if (self.resolver.resolve != null) {
                        _ = self.resolver.call(identifier, .non_external, scope.insideFunction());
                    }
                } else {
                    const function_name = try identifier.name.str();
                    if (!try self.instruction_validator.call(
                        function_name,
                        nativeDebug(identifier.debug_data),
                        self.error_reporter,
                    )) {
                        try self.reportFormat(
                            .DeclarationError,
                            4619,
                            nativeDebug(identifier.debug_data),
                            "Function \"{s}\" not found.",
                            .{function_name},
                        );
                    }
                }
            },
        }

        const function_name = try Utilities.resolveFunctionName(&call.function_name, self.dialect);
        if (num_parameters) |expected| {
            if (call.arguments.items.len != expected) {
                try self.reportFormat(
                    .TypeError,
                    7000,
                    nativeFunctionName(&call.function_name),
                    "Function \"{s}\" expects {d} arguments but got {d}.",
                    .{ function_name, expected, call.arguments.items.len },
                );
            }
        }

        var index = call.arguments.items.len;
        while (index != 0) {
            index -= 1;
            const argument = &call.arguments.items[index];
            const expected_literal = if (literal_arguments) |arguments|
                if (index < arguments.len) arguments[index] else null
            else
                null;
            if (expected_literal) |kind| {
                if (argument.* != .literal) {
                    try self.error_reporter.typeError(
                        .{ .value = 9114 },
                        nativeFunctionName(&call.function_name),
                        "Function expects direct literals as arguments.",
                    );
                } else if (argument.literal.kind != kind) {
                    try self.reportFormat(
                        .TypeError,
                        5859,
                        nativeExpression(argument),
                        "Function expects {s} literal.",
                        .{literalKindName(kind)},
                    );
                } else if (kind == .String) {
                    if (std.mem.eql(u8, function_name, "datasize") or
                        std.mem.eql(u8, function_name, "dataoffset"))
                    {
                        const value = try Utilities.formatLiteralAlloc(self.allocator, &argument.literal, true);
                        defer self.allocator.free(value);
                        if (!self.object_structure.contains(value)) {
                            try self.reportFormat(
                                .TypeError,
                                3517,
                                nativeExpression(argument),
                                "Unknown data object \"{s}\".",
                                .{value},
                            );
                        }
                    } else if (std.mem.startsWith(u8, function_name, "verbatim_")) {
                        const value = argument.literal.value.builtinStringLiteralValue() catch return error.InvalidAst;
                        if (value.len == 0) {
                            try self.error_reporter.typeError(
                                .{ .value = 1844 },
                                nativeExpression(argument),
                                "The \"verbatim_*\" builtins cannot be used with empty bytecode.",
                            );
                        }
                    }
                    if (!argument.literal.value.unlimited()) return error.InvalidAst;
                    continue;
                }
            }
            try self.expectExpression(argument);
        }
        if (watcher.ok()) {
            if (num_parameters == null or num_returns == null or
                num_parameters.? != call.arguments.items.len) return error.InvalidAst;
            return num_returns.?;
        }
        return num_returns orelse 0;
    }

    fn visitIf(self: *AsmAnalyzer, if_statement: *const AST.If) AnalyzeError!void {
        try self.expectExpression(if_statement.condition orelse return error.InvalidAst);
        try self.visitBlock(&if_statement.body);
    }

    fn visitSwitch(self: *AsmAnalyzer, switch_statement: *const AST.Switch) AnalyzeError!void {
        const expression = switch_statement.expression orelse return error.InvalidAst;
        if (switch_statement.cases.items.len == 1 and
            switch_statement.cases.items[0].value == null)
        {
            try self.error_reporter.warning(
                .{ .value = 9592 },
                nativeDebug(switch_statement.debug_data),
                "\"switch\" statement with only a default case.",
            );
        }
        try self.expectExpression(expression);
        var cases = std.AutoHashMap(u256, void).init(self.allocator);
        defer cases.deinit();
        for (switch_statement.cases.items) |*case_value| {
            if (case_value.value) |value| {
                const watcher = self.error_reporter.errorWatcher();
                _ = try self.visitLiteral(value);
                if (watcher.ok()) {
                    const numeric = value.value.value() catch return error.InvalidAst;
                    const result = try cases.getOrPut(numeric);
                    if (result.found_existing) {
                        const formatted = try Utilities.formatLiteralAlloc(self.allocator, value, true);
                        defer self.allocator.free(formatted);
                        try self.reportFormat(
                            .DeclarationError,
                            6792,
                            nativeDebug(case_value.debug_data),
                            "Duplicate case \"{s}\" defined.",
                            .{formatted},
                        );
                    }
                }
            }
            try self.visitBlock(&case_value.body);
        }
    }

    fn visitForLoop(self: *AsmAnalyzer, loop: *const AST.ForLoop) AnalyzeError!void {
        const condition = loop.condition orelse return error.InvalidAst;
        const outer_scope = self.current_scope;
        try self.visitBlock(&loop.pre);
        self.current_scope = self.info.getScope(&loop.pre) orelse return error.InvalidAst;
        defer self.current_scope = outer_scope;
        try self.expectExpression(condition);
        const outer_loop = self.current_for_loop;
        self.current_for_loop = loop;
        defer self.current_for_loop = outer_loop;
        try self.visitBlock(&loop.body);
        try self.visitBlock(&loop.post);
    }

    fn visitBlock(self: *AsmAnalyzer, block: *const AST.Block) AnalyzeError!void {
        const previous_scope = self.current_scope;
        self.current_scope = self.info.getScope(block) orelse return error.InvalidAst;
        defer self.current_scope = previous_scope;
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn expectExpression(self: *AsmAnalyzer, expression: *const AST.Expression) AnalyzeError!void {
        const num_values = try self.visitExpression(expression);
        if (num_values != 1) {
            try self.reportFormat(
                .TypeError,
                3950,
                nativeExpression(expression),
                "Expected expression to evaluate to one value, but got {d} values instead.",
                .{num_values},
            );
        }
    }

    fn checkAssignment(self: *AsmAnalyzer, variable: *const AST.Identifier) AnalyzeError!void {
        const scope = self.current_scope orelse return error.InvalidAst;
        const watcher = self.error_reporter.errorWatcher();
        var found = false;
        if (scope.lookup(variable.name)) |resolved| {
            if (self.resolver.resolve != null) {
                _ = self.resolver.call(variable, .non_external, scope.insideFunction());
            }
            switch (resolved.*) {
                .function => try self.error_reporter.typeError(
                    .{ .value = 2657 },
                    nativeDebug(variable.debug_data),
                    "Assignment requires variable.",
                ),
                .variable => |*scope_variable| {
                    if (!self.active_variables.contains(scope_variable)) {
                        try self.reportFormat(
                            .DeclarationError,
                            1133,
                            nativeDebug(variable.debug_data),
                            "Variable {s} used before it was declared.",
                            .{try variable.name.str()},
                        );
                    }
                },
            }
            found = true;
        } else if (self.resolver.resolve != null and
            self.resolver.call(variable, .l_value, scope.insideFunction()))
        {
            found = true;
        }
        if (!found and watcher.ok()) {
            try self.error_reporter.declarationError(
                .{ .value = 4634 },
                nativeDebug(variable.debug_data),
                "Variable not found or variable not lvalue.",
            );
        }
    }

    fn expectValidIdentifier(
        self: *AsmAnalyzer,
        identifier: YulName,
        location: Diagnostics.SourceLocation,
    ) AnalyzeError!void {
        const label = try identifier.str();
        if (std.mem.endsWith(u8, label, ".")) {
            try self.reportFormat(
                .SyntaxError,
                3384,
                location,
                "\"{s}\" is not a valid identifier (ends with a dot).",
                .{label},
            );
        }
        if (std.mem.find(u8, label, "..") != null) {
            try self.reportFormat(
                .SyntaxError,
                7771,
                location,
                "\"{s}\" is not a valid identifier (contains consecutive dots).",
                .{label},
            );
        }
        if (self.dialect.reservedIdentifier(label)) {
            try self.reportFormat(
                .DeclarationError,
                5017,
                location,
                "The identifier \"{s}\" is reserved and can not be used.",
                .{label},
            );
        }
        if (Token.isFutureYulKeyword(label) or Token.isFutureYulReservedIdentifier(label)) {
            try self.reportFormat(
                .Warning,
                5470,
                location,
                "\"{s}\" will be promoted to Yul {s} in the future and will not be allowed anymore as an identifier.",
                .{ label, if (Token.isFutureYulKeyword(label)) "keyword" else "reserved identifier" },
            );
        }
    }

    fn joinIdentifierNames(
        self: *AsmAnalyzer,
        identifiers: []const AST.Identifier,
    ) AnalyzeError![]u8 {
        const names = try self.allocator.alloc([]const u8, identifiers.len);
        defer self.allocator.free(names);
        for (identifiers, names) |identifier, *name| name.* = try identifier.name.str();
        return StringUtils.joinHumanReadableAlloc(self.allocator, names, ", ", "");
    }

    fn joinDeclarationNames(
        self: *AsmAnalyzer,
        identifiers: []const AST.NameWithDebugData,
    ) AnalyzeError![]u8 {
        const names = try self.allocator.alloc([]const u8, identifiers.len);
        defer self.allocator.free(names);
        for (identifiers, names) |identifier, *name| name.* = try identifier.name.str();
        return StringUtils.joinHumanReadableAlloc(self.allocator, names, ", ", "");
    }

    fn reportFormat(
        self: *AsmAnalyzer,
        error_type: Diagnostics.ErrorType,
        error_id: u64,
        location: Diagnostics.SourceLocation,
        comptime format: []const u8,
        arguments: anytype,
    ) AnalyzeError!void {
        const description = try std.fmt.allocPrint(self.allocator, format, arguments);
        defer self.allocator.free(description);
        try self.error_reporter.report(.{ .value = error_id }, error_type, location, description);
    }
};

/// Analyzes and retains scope information on a parsed object. The object owns
/// the resulting analysis state and replaces any previous analysis result.
pub fn analyzeObject(
    allocator: std.mem.Allocator,
    object: *ObjectModule.Object,
    error_reporter: *Diagnostics.ErrorReporter,
    resolver: Resolver,
    instruction_validator: InstructionValidator,
) AnalyzeError!bool {
    const code = object.code() orelse return error.MissingObjectCode;
    var structure = try object.summarizeStructure();
    defer structure.deinit();
    if (object.analysis_info) |*previous| previous.deinit();
    object.analysis_info = AsmAnalysisInfo.init(allocator);
    var analyzer = AsmAnalyzer.init(
        allocator,
        &object.analysis_info.?,
        error_reporter,
        code.dialect().*,
        resolver,
        ObjectStructure.fromObjectStructure(&structure),
        instruction_validator,
    );
    defer analyzer.deinit();
    return analyzer.analyze(code.root());
}

/// Typed-error counterpart of upstream's assert-correct helpers. Returned
/// scopes borrow nodes from `block`, so the AST must outlive the result.
pub fn analyzeStrictBlock(
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    block: *const AST.Block,
    structure: *const ObjectModule.Structure,
    instruction_validator: InstructionValidator,
) AnalyzeError!AsmAnalysisInfo {
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    errdefer info.deinit();
    var analyzer = AsmAnalyzer.init(
        allocator,
        &info,
        &reporter,
        dialect,
        .{},
        ObjectStructure.fromObjectStructure(structure),
        instruction_validator,
    );
    defer analyzer.deinit();
    if (!try analyzer.analyze(block)) return error.AnalysisFailed;
    return info;
}

pub fn analyzeStrictAst(
    allocator: std.mem.Allocator,
    ast: *const AST.AST,
    structure: *const ObjectModule.Structure,
    instruction_validator: InstructionValidator,
) AnalyzeError!AsmAnalysisInfo {
    return analyzeStrictBlock(
        allocator,
        ast.dialect().*,
        ast.root(),
        structure,
        instruction_validator,
    );
}

pub fn analyzeStrictObject(
    allocator: std.mem.Allocator,
    object: *const ObjectModule.Object,
    instruction_validator: InstructionValidator,
) AnalyzeError!AsmAnalysisInfo {
    const code = object.code() orelse return error.MissingObjectCode;
    var structure = try object.summarizeStructure();
    defer structure.deinit();
    return analyzeStrictAst(allocator, code, &structure, instruction_validator);
}

fn nativeDebug(debug_data: ?@import("../liblangutil/debug_data.zig").DebugData) Diagnostics.SourceLocation {
    return if (debug_data) |debug| debug.native_location else .{};
}

fn nativeExpression(expression: *const AST.Expression) Diagnostics.SourceLocation {
    return if (expression.debugData()) |debug| debug.native_location else .{};
}

fn nativeFunctionName(function_name: *const AST.FunctionName) Diagnostics.SourceLocation {
    return if (function_name.debugData()) |debug| debug.native_location else .{};
}

fn literalKindName(kind: AST.LiteralKind) []const u8 {
    return switch (kind) {
        .Number => "number",
        .Boolean => "boolean",
        .String => "string",
    };
}

fn numberExceedsU256(representation: []const u8) bool {
    if (std.mem.startsWith(u8, representation, "0x")) {
        const digits = std.mem.trimStart(u8, representation[2..], "0");
        return digits.len > 64;
    }
    const digits = std.mem.trimStart(u8, representation, "0");
    const maximum = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    return digits.len > maximum.len or
        (digits.len == maximum.len and std.mem.order(u8, digits, maximum) == .gt);
}

test "generic Yul analyzer accepts scoped functions and declarations" {
    const Parser = @import("asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a) -> r { r := a } let x := f(1) x := f(x) }",
        "analysis.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var info = AsmAnalysisInfo.init(allocator);
    defer info.deinit();
    var analyzer = AsmAnalyzer.init(allocator, &info, &reporter, .{}, .{}, .{}, .{});
    defer analyzer.deinit();
    try std.testing.expect(try analyzer.analyze(ast.root()));
    try std.testing.expectEqual(@as(usize, 0), reporter.diagnostics().len);
}
