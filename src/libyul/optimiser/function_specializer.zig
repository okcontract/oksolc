// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Clones non-recursive functions with literal call arguments materialized in
//! their bodies, leaving only dynamic parameters at the call site.

const std = @import("std");
const AST = @import("../ast.zig");
const ASTCopierModule = @import("ast_copier.zig");
const CallGraphModule = @import("call_graph_generator.zig");
const NameCollector = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const YulName = @import("../yul_name.zig").YulName;

pub const LiteralArguments = struct {
    items: std.ArrayList(?AST.Expression) = .empty,

    fn deinit(self: *LiteralArguments, allocator: std.mem.Allocator, scratch_allocator: std.mem.Allocator) void {
        for (self.items.items) |*maybe_expression| if (maybe_expression.*) |*expression|
            expression.deinit(allocator);
        self.items.deinit(scratch_allocator);
        self.* = undefined;
    }
};

const Specialization = struct {
    new_name: YulName,
    arguments: LiteralArguments,

    fn deinit(self: *Specialization, allocator: std.mem.Allocator, scratch_allocator: std.mem.Allocator) void {
        self.arguments.deinit(allocator, scratch_allocator);
        self.* = undefined;
    }
};

const SpecializationList = std.ArrayList(Specialization);
const SpecializationMap = std.AutoHashMap(YulName, SpecializationList);

pub const FunctionSpecializer = struct {
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    recursive_functions: *const CallGraphModule.FunctionHandleSet,
    name_dispenser: *NameDispenser,
    old_to_new: SpecializationMap,

    pub const name = "FunctionSpecializer";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        const scratch_allocator = context.scratchAllocator();
        var graph = try CallGraphModule.CallGraphGenerator.callGraph(scratch_allocator, ast);
        defer graph.deinit();
        var recursive = try graph.recursiveFunctions();
        defer recursive.deinit(scratch_allocator);
        var specializer: FunctionSpecializer = .{
            .allocator = allocator,
            .scratch_allocator = scratch_allocator,
            .recursive_functions = &recursive,
            .name_dispenser = context.dispenser,
            .old_to_new = SpecializationMap.init(scratch_allocator),
        };
        defer specializer.deinit();
        try specializer.visitBlock(ast);
        try specializer.insertSpecializedFunctions(ast);
    }

    fn deinit(self: *FunctionSpecializer) void {
        var lists = self.old_to_new.valueIterator();
        while (lists.next()) |list| {
            for (list.items) |*specialization| specialization.deinit(self.allocator, self.scratch_allocator);
            list.deinit(self.scratch_allocator);
        }
        self.old_to_new.deinit();
        self.* = undefined;
    }

    fn visitBlock(self: *FunctionSpecializer, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *FunctionSpecializer, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| try self.visitExpression(value.value orelse return error.InvalidAst),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitBlock(&value.body),
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

    fn visitExpression(self: *FunctionSpecializer, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
                try self.visitFunctionCall(call);
            },
            .identifier, .literal => {},
        }
    }

    fn visitFunctionCall(self: *FunctionSpecializer, call: *AST.FunctionCall) anyerror!void {
        const identifier = switch (call.function_name) {
            .identifier => |*value| value,
            .builtin => return,
        };
        if (self.recursive_functions.contains(.{ .user = identifier.name })) return;

        const has_literal = for (call.arguments.items) |argument| {
            if (argument == .literal) break true;
        } else false;
        if (!has_literal) return;

        // Reserve every destination before transferring ownership. The argument
        // list borrows no call storage: literals move into this pass-local owner,
        // and the remaining arguments compact in their original allocation.
        var arguments: LiteralArguments = .{};
        errdefer arguments.deinit(self.allocator, self.scratch_allocator);
        try arguments.items.ensureTotalCapacityPrecise(self.scratch_allocator, call.arguments.items.len);
        const old_name = identifier.name;
        const entry = try self.old_to_new.getOrPut(old_name);
        if (!entry.found_existing) entry.value_ptr.* = .empty;
        try entry.value_ptr.ensureUnusedCapacity(self.scratch_allocator, 1);
        const new_name = try self.name_dispenser.newName(old_name);

        var kept: usize = 0;
        for (call.arguments.items) |argument| {
            if (argument == .literal) {
                arguments.items.appendAssumeCapacity(argument);
            } else {
                arguments.items.appendAssumeCapacity(null);
                call.arguments.items[kept] = argument;
                kept += 1;
            }
        }
        call.arguments.shrinkRetainingCapacity(kept);
        identifier.name = new_name;
        entry.value_ptr.appendAssumeCapacity(.{
            .new_name = new_name,
            .arguments = arguments,
        });
    }

    fn insertSpecializedFunctions(self: *FunctionSpecializer, ast: *AST.Block) anyerror!void {
        if (self.old_to_new.count() == 0) return;
        const old_len = ast.statements.items.len;
        var expanded_len = old_len;
        for (ast.statements.items) |statement| {
            if (statement == .function_definition) {
                if (self.old_to_new.get(statement.function_definition.name)) |specializations|
                    expanded_len = std.math.add(usize, expanded_len, specializations.items.len) catch return error.OutOfMemory;
            }
        }
        if (expanded_len == old_len) return;

        // Place original statements and empty specialization slots in their
        // final positions before copying any body. All slots are valid owners
        // when fallible copying starts, including after a partial failure.
        try ast.statements.ensureTotalCapacityPrecise(self.allocator, expanded_len);
        ast.statements.items.len = expanded_len;
        var source_index = old_len;
        var destination_index = expanded_len;
        while (source_index != 0) {
            source_index -= 1;
            const statement = ast.statements.items[source_index];
            ast.statements.items[source_index] = emptyStatement();
            destination_index -= 1;
            ast.statements.items[destination_index] = statement;
            if (statement == .function_definition) {
                if (self.old_to_new.get(statement.function_definition.name)) |specializations| {
                    const end = destination_index;
                    destination_index -= specializations.items.len;
                    @memset(ast.statements.items[destination_index..end], emptyStatement());
                }
            }
        }
        std.debug.assert(destination_index == 0);

        // Copies occupy slots before the current original, which this walk has
        // already passed. The root cannot grow while specialize borrows it.
        for (ast.statements.items, 0..) |*statement, index| {
            if (statement.* == .function_definition) {
                const function = &statement.function_definition;
                if (self.old_to_new.getPtr(function.name)) |specializations| {
                    for (specializations.items, 0..) |*specialization, offset| {
                        const destination = index - specializations.items.len + offset;
                        // A fallible union initializer can write into its result
                        // location before returning an error. Publish only a
                        // completed function so failure leaves the empty slot.
                        const specialized = try self.specialize(function, specialization);
                        ast.statements.items[destination] = .{ .function_definition = specialized };
                    }
                }
            }
        }
    }

    fn specialize(
        self: *FunctionSpecializer,
        function: *const AST.FunctionDefinition,
        specialization: *Specialization,
    ) anyerror!AST.FunctionDefinition {
        if (specialization.arguments.items.items.len != function.parameters.items.len)
            return error.InvalidSpecializationArity;

        var names = try NameCollector.NameCollector.initFunction(
            self.scratch_allocator,
            function,
            .only_variables,
        );
        defer names.deinit();
        var translations: std.ArrayList(ASTCopierModule.NameTranslation) = .empty;
        defer translations.deinit(self.scratch_allocator);
        try translations.ensureTotalCapacityPrecise(self.scratch_allocator, names.names().len());
        for (0..names.names().len()) |index| {
            const old_name = names.names().at(index);
            translations.appendAssumeCapacity(.{
                .from = old_name,
                .to = try self.name_dispenser.newName(old_name),
            });
        }
        var copier = ASTCopierModule.FunctionCopier.init(self.allocator, translations.items);
        copier.bind();
        var new_function = try copier.copier.translateFunctionDefinition(function);
        errdefer new_function.deinit(self.allocator);

        var literal_count: usize = 0;
        for (specialization.arguments.items.items) |argument|
            if (argument != null) {
                literal_count += 1;
            };

        // Grow the copied body once and place declarations directly into it.
        // Empty prefix slots are valid cleanup owners throughout construction.
        const body = &new_function.body.statements;
        const old_len = body.items.len;
        try body.ensureUnusedCapacity(self.allocator, literal_count);
        body.items.len += literal_count;
        std.mem.copyBackwards(AST.Statement, body.items[literal_count..], body.items[0..old_len]);
        @memset(body.items[0..literal_count], emptyStatement());

        var declaration_index: usize = 0;
        var kept: usize = 0;
        for (specialization.arguments.items.items, new_function.parameters.items) |*maybe_argument, parameter| {
            if (maybe_argument.*) |argument| {
                const declaration = &body.items[declaration_index];
                const value = try AST.createExpression(self.allocator, argument);
                declaration.* = .{ .variable_declaration = .{
                    .debug_data = function.debug_data,
                    .value = value,
                } };
                maybe_argument.* = null;
                try declaration.variable_declaration.variables.ensureTotalCapacityPrecise(self.allocator, 1);
                declaration.variable_declaration.variables.appendAssumeCapacity(parameter);
                declaration_index += 1;
            } else {
                new_function.parameters.items[kept] = parameter;
                kept += 1;
            }
        }
        new_function.parameters.shrinkRetainingCapacity(kept);
        new_function.name = specialization.new_name;

        specialization.arguments.items.deinit(self.scratch_allocator);
        specialization.arguments.items = .empty;
        return new_function;
    }
};

fn emptyStatement() AST.Statement {
    return .{ .block = .{} };
}

test "function specializer materializes literal parameters" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ function f(a, b) { pop(add(a, b)) } let x := 1 f(x, 5) }",
        "function-specializer.yul",
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
    try FunctionSpecializer.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "function f_1") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "f_1(x)") != null);
}

test "function specializer moves literals and preserves dynamic storage across allocation failures" {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ function f(a, b, c) { pop(add(a, add(b, c))) }
        \\  function recursive(r) { if r { recursive(sub(r, 1)) } }
        \\  let x := 7
        \\  f(0x01, add(x, 2), 0x03)
        \\  f(x, x, x)
        \\  f(4, 5, 6)
        \\  recursive(8)
        \\}
    , "specializer-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    const Check = struct {
        fn run(failing: std.mem.Allocator, input: *const AST.AST, separate_scratch: bool) !void {
            const Printer = @import("../asm_printer.zig").AsmPrinter;
            const Analysis = @import("../asm_analysis.zig");
            const Structure = @import("../object.zig").Structure;
            var copier = ASTCopierModule.ASTCopier.init(failing);
            var ast = try copier.translateBlock(input.root());
            defer ast.deinit(failing);
            var reserved: NameCollector.NameSet = .{};
            defer reserved.deinit(failing);
            var dispenser = try NameDispenser.initFromAst(failing, input.dialect().*, &ast, &reserved);
            defer dispenser.deinit();
            var scratch = std.heap.ArenaAllocator.init(failing);
            defer scratch.deinit();
            var context: OptimiserStepContext = .{
                .dialect = input.dialect().*,
                .dispenser = &dispenser,
                .reserved_identifiers = &reserved,
                .scratch_arena = if (separate_scratch) &scratch else null,
            };
            const first_call = &ast.statements.items[3].expression_statement.expression.function_call;
            const call_storage = first_call.arguments.items.ptr;
            const nested_storage = first_call.arguments.items[1].function_call.arguments.items.ptr;
            const first_spelling = first_call.arguments.items[0].literal.value.string_value.?.ptr;
            const last_spelling = first_call.arguments.items[2].literal.value.string_value.?.ptr;
            const dynamic_storage = ast.statements.items[4].expression_statement.expression.function_call.arguments.items.ptr;
            try FunctionSpecializer.run(&context, &ast);
            _ = scratch.reset(.free_all);
            // Two specialized functions precede the original function. Their
            // literal spelling buffers transfer unchanged, and call containers
            // and nested dynamic expressions keep their original allocation.
            try std.testing.expectEqual(@as(usize, 9), ast.statements.items.len);
            const specialized = &ast.statements.items[0].function_definition;
            try std.testing.expectEqual(@as(usize, 1), specialized.parameters.items.len);
            try std.testing.expectEqual(first_spelling, specialized.body.statements.items[0].variable_declaration.value.?.literal.value.string_value.?.ptr);
            try std.testing.expectEqual(last_spelling, specialized.body.statements.items[1].variable_declaration.value.?.literal.value.string_value.?.ptr);
            const moved_call = &ast.statements.items[5].expression_statement.expression.function_call;
            try std.testing.expectEqual(call_storage, moved_call.arguments.items.ptr);
            try std.testing.expectEqual(@as(usize, 1), moved_call.arguments.items.len);
            try std.testing.expectEqual(nested_storage, moved_call.arguments.items[0].function_call.arguments.items.ptr);
            try std.testing.expectEqual(dynamic_storage, ast.statements.items[6].expression_statement.expression.function_call.arguments.items.ptr);
            try std.testing.expectEqual(@as(usize, 0), ast.statements.items[7].expression_statement.expression.function_call.arguments.items.len);
            try std.testing.expectEqualStrings("recursive", try ast.statements.items[8].expression_statement.expression.function_call.function_name.identifier.name.str());
            var structure = try Structure.init(failing, "");
            defer structure.deinit();
            var analysis = try Analysis.analyzeStrictBlock(failing, input.dialect().*, &ast, &structure, .{});
            defer analysis.deinit();
            var printer = Printer.init(failing, input.dialect().*, &.{}, .{}, null);
            const rendered = try printer.renderBlock(&ast);
            defer failing.free(rendered);
            try std.testing.expect(std.mem.find(u8, rendered, "0x01") != null);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ &source, false });
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ &source, true });
}
