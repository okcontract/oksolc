// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Flattens disambiguator suffixes independently in each function scope.

const std = @import("std");
const AST = @import("../ast.zig");
const NameCollector = @import("name_collector.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const OptimizerUtilities = @import("optimizer_utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const VarNameCleaner = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    names_to_keep: NameCollector.NameSet,
    used_names: NameCollector.NameSet,
    next_suffix: std.AutoHashMap(YulName, usize),
    translated_names: std.AutoHashMap(YulName, YulName),
    inside_function: bool = false,

    pub const name = "VarNameCleaner";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.scratchAllocator();
        var names_to_keep = try context.reserved_identifiers.clone(allocator);
        errdefer names_to_keep.deinit(allocator);
        for (ast.statements.items) |statement| switch (statement) {
            .function_definition => |function| _ = try names_to_keep.insert(allocator, function.name),
            else => {},
        };
        var used_names = try names_to_keep.clone(allocator);
        errdefer used_names.deinit(allocator);
        var cleaner: VarNameCleaner = .{
            .allocator = allocator,
            .dialect = context.dialect,
            .names_to_keep = names_to_keep,
            .used_names = used_names,
            .next_suffix = std.AutoHashMap(YulName, usize).init(allocator),
            .translated_names = std.AutoHashMap(YulName, YulName).init(allocator),
        };
        names_to_keep = .{};
        used_names = .{};
        defer cleaner.deinit();
        try cleaner.visitBlock(ast);
    }

    fn deinit(self: *VarNameCleaner) void {
        self.names_to_keep.deinit(self.allocator);
        self.used_names.deinit(self.allocator);
        self.next_suffix.deinit();
        self.translated_names.deinit();
        self.* = undefined;
    }

    fn visitBlock(self: *VarNameCleaner, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *VarNameCleaner, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| {
                for (value.variable_names.items) |*identifier| self.translateIdentifier(identifier);
                try self.visitExpression(value.value orelse return error.InvalidAst);
            },
            .variable_declaration => |*value| {
                try self.renameVariables(value.variables.items);
                if (value.value) |expression| try self.visitExpression(expression);
            },
            .function_definition => |*value| try self.visitFunction(value),
            .if_statement => |*value| {
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                try self.visitExpression(value.expression orelse return error.InvalidAst);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitFunction(self: *VarNameCleaner, function: *AST.FunctionDefinition) anyerror!void {
        if (self.inside_function) return error.NestedFunctionDefinition;
        self.inside_function = true;
        defer self.inside_function = false;

        const global_used_names = self.used_names;
        const global_translated_names = self.translated_names;
        const global_next_suffix = self.next_suffix;
        self.used_names = try self.names_to_keep.clone(self.allocator);
        self.translated_names = std.AutoHashMap(YulName, YulName).init(self.allocator);
        self.next_suffix = std.AutoHashMap(YulName, usize).init(self.allocator);
        defer {
            self.used_names.deinit(self.allocator);
            self.translated_names.deinit();
            self.next_suffix.deinit();
            self.used_names = global_used_names;
            self.translated_names = global_translated_names;
            self.next_suffix = global_next_suffix;
        }

        try self.renameVariables(function.parameters.items);
        try self.renameVariables(function.return_variables.items);
        try self.visitBlock(&function.body);
    }

    fn renameVariables(
        self: *VarNameCleaner,
        variables: []AST.NameWithDebugData,
    ) anyerror!void {
        for (variables) |*variable| {
            const old_name = variable.name;
            const new_name = try self.findCleanName(old_name);
            if (!new_name.eql(old_name)) {
                try self.translated_names.put(old_name, new_name);
                variable.name = new_name;
            }
            _ = try self.used_names.insert(self.allocator, variable.name);
        }
    }

    fn translateIdentifier(self: *const VarNameCleaner, identifier: *AST.Identifier) void {
        if (self.translated_names.get(identifier.name)) |translated| identifier.name = translated;
    }

    fn visitExpression(self: *VarNameCleaner, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .identifier => |*identifier| self.translateIdentifier(identifier),
            .literal => {},
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
        }
    }

    fn findCleanName(self: *VarNameCleaner, original: YulName) anyerror!YulName {
        const stripped = try stripSuffix(original);
        if (!try self.isUsedName(stripped)) return stripped;
        const entry = try self.next_suffix.getOrPut(stripped);
        if (!entry.found_existing or entry.value_ptr.* == 0) entry.value_ptr.* = 1;
        while (entry.value_ptr.* < std.math.maxInt(usize)) {
            const candidate_string = try std.fmt.allocPrint(
                self.allocator,
                "{s}_{d}",
                .{ try stripped.str(), entry.value_ptr.* },
            );
            defer self.allocator.free(candidate_string);
            const candidate = try YulName.init(candidate_string);
            entry.value_ptr.* += 1;
            if (!try self.isUsedName(candidate)) return candidate;
        }
        return error.NameSuffixExhausted;
    }

    fn isUsedName(self: *const VarNameCleaner, candidate: YulName) anyerror!bool {
        return OptimizerUtilities.isRestrictedIdentifier(self.dialect, try candidate.str()) or
            self.used_names.contains(candidate);
    }
};

fn stripSuffix(original: YulName) anyerror!YulName {
    const string = try original.str();
    var position = string.len;
    var matched = false;
    while (position != 0) {
        const group_end = position;
        while (position != 0 and std.ascii.isDigit(string[position - 1])) position -= 1;
        if (position == group_end) break;
        const digits_start = position;
        while (position != 0 and string[position - 1] == '_') position -= 1;
        if (position == digits_start) {
            position = group_end;
            break;
        }
        matched = true;
        if (position == 0 or !std.ascii.isDigit(string[position - 1])) break;
    }
    return if (matched) YulName.init(string[0..position]) else original;
}

test "variable name cleaner flattens suffixes per function scope" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a_1_2) -> r_9 { let x_1 := a_1_2 let x_2 := x_1 r_9 := x_2 } }",
        "var-name-cleaner.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(
        allocator,
        dialect.dialect(),
        ast.root(),
        &reserved,
    );
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = dialect.dialect(),
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    try VarNameCleaner.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "function f(a) -> r") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "let x_1 := x") != null);
}
