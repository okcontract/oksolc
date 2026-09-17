// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Statement-level function inlining with the upstream two-pass heuristic.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const ASTCopierModule = @import("ast_copier.zig");
const CallGraphModule = @import("call_graph_generator.zig");
const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
const FunctionCallFinder = @import("function_call_finder.zig");
const Metrics = @import("metrics.zig");
const NameCollector = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");
const SSAValueTracker = @import("ssa_value_tracker.zig").SSAValueTracker;
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

const FunctionMap = ordered.OrderedMap(YulName, *AST.FunctionDefinition, lessYulName);
const SizeMap = ordered.OrderedMap(YulName, usize, lessYulName);
const TranslationMap = ordered.OrderedMap(YulName, YulName, lessYulName);

const Pass = enum {
    inline_tiny,
    inline_rest,
};

pub const FullInliner = struct {
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    ast: *AST.Block,
    recursive_functions: CallGraphModule.FunctionHandleSet,
    name_dispenser: *NameDispenser,
    dialect: AST.Dialect,
    pass: Pass = .inline_tiny,
    functions: FunctionMap = .{},
    no_inline_functions: NameCollector.NameSet = .{},
    has_memory_guard: bool = false,
    single_use: NameCollector.NameSet = .{},
    constants: NameCollector.NameSet = .{},
    function_sizes: SizeMap = .{},

    pub const name = "FullInliner";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var inliner = try init(
            context.dispenser.allocator,
            context.scratchAllocator(),
            ast,
            context.dispenser,
            context.dialect,
        );
        defer inliner.deinit();
        try inliner.runPass(.inline_tiny);
        try inliner.runPass(.inline_rest);
    }

    fn init(
        allocator: std.mem.Allocator,
        scratch_allocator: std.mem.Allocator,
        ast: *AST.Block,
        dispenser: *NameDispenser,
        dialect: AST.Dialect,
    ) !FullInliner {
        var graph = try CallGraphModule.CallGraphGenerator.callGraph(scratch_allocator, ast);
        defer graph.deinit();
        var result: FullInliner = .{
            .allocator = allocator,
            .scratch_allocator = scratch_allocator,
            .ast = ast,
            .recursive_functions = try graph.recursiveFunctions(),
            .name_dispenser = dispenser,
            .dialect = dialect,
        };
        errdefer result.deinit();

        var tracker = SSAValueTracker.init(scratch_allocator);
        defer tracker.deinit();
        try tracker.run(ast);
        var values = tracker.values().iterator();
        while (values.next()) |entry| {
            if (entry.value_ptr.*.* == .literal) {
                _ = try result.constants.insert(scratch_allocator, entry.key_ptr.*);
            }
        }

        _ = try result.function_sizes.insert(
            scratch_allocator,
            .{},
            Metrics.CodeSize.codeSize(ast, .{}),
        );
        var references = try NameCollector.ReferencesCounter.countReferencesBlock(
            scratch_allocator,
            ast,
        );
        defer references.deinit(scratch_allocator);
        for (ast.statements.items) |*statement| {
            if (statement.* != .function_definition) continue;
            const function = &statement.function_definition;
            if (!(try result.functions.insert(scratch_allocator, function.name, function)))
                return error.InputNotDisambiguated;
            if (Semantics.LeaveFinder.containsLeave(function))
                _ = try result.no_inline_functions.insert(scratch_allocator, function.name);
            const reference_count = references.get(.{ .user = function.name });
            if (reference_count != null and reference_count.?.* == 1)
                _ = try result.single_use.insert(scratch_allocator, function.name);
            try result.updateCodeSize(function);
        }

        if (dialect.findBuiltin("memoryguard")) |handle| {
            var calls = try FunctionCallFinder.findFunctionCallsConst(
                scratch_allocator,
                ast,
                .{ .builtin = handle },
            );
            defer calls.deinit(scratch_allocator);
            result.has_memory_guard = calls.items.len != 0;
        }
        return result;
    }

    fn deinit(self: *FullInliner) void {
        self.recursive_functions.deinit(self.scratch_allocator);
        self.functions.deinit(self.scratch_allocator);
        self.no_inline_functions.deinit(self.scratch_allocator);
        self.single_use.deinit(self.scratch_allocator);
        self.constants.deinit(self.scratch_allocator);
        self.function_sizes.deinit(self.scratch_allocator);
        self.* = undefined;
    }

    fn runPass(self: *FullInliner, pass: Pass) !void {
        self.pass = pass;
        var depths = try self.callDepths();
        defer depths.deinit(self.scratch_allocator);
        var functions: std.ArrayList(*AST.FunctionDefinition) = .empty;
        defer functions.deinit(self.scratch_allocator);
        for (self.ast.statements.items) |*statement|
            if (statement.* == .function_definition)
                try functions.append(self.scratch_allocator, &statement.function_definition);
        std.sort.insertion(*AST.FunctionDefinition, functions.items, &depths, struct {
            fn lessThan(
                known_depths: *const NameCollector.ReferenceMap,
                left: *AST.FunctionDefinition,
                right: *AST.FunctionDefinition,
            ) bool {
                const left_depth = known_depths.get(.{ .user = left.name }) orelse
                    @panic("missing function depth");
                const right_depth = known_depths.get(.{ .user = right.name }) orelse
                    @panic("missing function depth");
                return left_depth.* < right_depth.*;
            }
        }.lessThan);
        for (functions.items) |function_definition| {
            try self.handleBlock(function_definition.name, &function_definition.body);
            try self.updateCodeSize(function_definition);
        }
        for (self.ast.statements.items) |*statement|
            if (statement.* == .block)
                try self.handleBlock(.{}, &statement.block);
    }

    fn callDepths(self: *FullInliner) !NameCollector.ReferenceMap {
        var graph = try CallGraphModule.CallGraphGenerator.callGraph(self.scratch_allocator, self.ast);
        defer graph.deinit();
        if (graph.function_calls.remove(.{ .user = .{} })) |entry_value| {
            var entry = entry_value;
            entry.value.deinit(self.scratch_allocator);
        }
        for (graph.function_calls.mutableItems()) |*entry| {
            var index: usize = 0;
            while (index < entry.value.items.len) {
                if (entry.value.items[index] == .builtin)
                    _ = entry.value.orderedRemove(index)
                else
                    index += 1;
            }
        }

        var depths: NameCollector.ReferenceMap = .{};
        errdefer depths.deinit(self.scratch_allocator);
        var current_depth: usize = 0;
        while (true) {
            var removed: std.ArrayList(AST.FunctionHandle) = .empty;
            defer removed.deinit(self.scratch_allocator);
            for (graph.function_calls.items()) |entry|
                if (entry.value.items.len == 0)
                    try removed.append(self.scratch_allocator, entry.key);
            for (removed.items) |handle| {
                _ = try depths.insert(self.scratch_allocator, handle, current_depth);
                if (graph.function_calls.remove(handle)) |entry_value| {
                    var entry = entry_value;
                    entry.value.deinit(self.scratch_allocator);
                }
            }
            for (graph.function_calls.mutableItems()) |*entry| {
                var index: usize = 0;
                while (index < entry.value.items.len) {
                    var erase = false;
                    for (removed.items) |handle|
                        if (FunctionCallFinder.functionHandlesEqual(entry.value.items[index], handle)) {
                            erase = true;
                            break;
                        };
                    if (erase)
                        _ = entry.value.orderedRemove(index)
                    else
                        index += 1;
                }
            }
            current_depth = std.math.add(usize, current_depth, 1) catch
                return error.CallDepthOverflow;
            if (removed.items.len == 0) break;
        }
        for (graph.function_calls.items()) |entry|
            _ = try depths.insert(self.scratch_allocator, entry.key, current_depth);
        return depths;
    }

    fn updateCodeSize(self: *FullInliner, function_definition: *const AST.FunctionDefinition) !void {
        _ = try self.function_sizes.fetchPut(
            self.scratch_allocator,
            function_definition.name,
            Metrics.CodeSize.codeSize(&function_definition.body, .{}),
        );
    }

    fn handleBlock(self: *FullInliner, current_function: YulName, block: *AST.Block) !void {
        var modifier: InlineModifier = .{
            .allocator = self.allocator,
            .scratch_allocator = self.scratch_allocator,
            .current_function = current_function,
            .driver = self,
        };
        try modifier.run(block);
    }

    fn lookupFunction(self: *const FullInliner, name_value: YulName) ?*AST.FunctionDefinition {
        const result = self.functions.get(name_value) orelse return null;
        return result.*;
    }

    fn recursive(self: *FullInliner, function_definition: *const AST.FunctionDefinition) !bool {
        var references = try NameCollector.ReferencesCounter.countReferencesFunction(
            self.scratch_allocator,
            function_definition,
        );
        defer references.deinit(self.scratch_allocator);
        const count = references.get(.{ .user = function_definition.name }) orelse return false;
        return count.* > 0;
    }

    fn shallInline(self: *FullInliner, call: *const AST.FunctionCall, call_site: YulName) !bool {
        const function_name = switch (call.function_name) {
            .builtin => return false,
            .identifier => |identifier| identifier.name,
        };
        if (function_name.eql(call_site)) return false;
        const called_function = self.lookupFunction(function_name) orelse return false;
        if (self.no_inline_functions.contains(function_name) or
            try self.recursive(called_function))
            return false;
        for (call.arguments.items) |argument|
            if (argument != .literal and argument != .identifier)
                return false;

        const size = (self.function_sizes.get(called_function.name) orelse
            return error.MissingFunctionSize).*;
        if (size <= 1) return true;
        if (self.pass == .inline_tiny) return false;

        var aggressive = if (EVMDialectModule.fromDialect(self.dialect)) |evm|
            evm.providesObjectAccess() and
                @intFromEnum(evm.evmVersion().version) >
                    @intFromEnum(@import("../../liblangutil/evm_version.zig").Version.Homestead)
        else
            false;
        if (!self.has_memory_guard or
            self.recursive_functions.contains(.{ .user = call_site }))
            aggressive = false;
        const call_site_size = (self.function_sizes.get(call_site) orelse
            return error.MissingCallSiteSize).*;
        if (!aggressive and call_site_size > 45) return false;
        if (self.single_use.contains(called_function.name)) return true;

        var constant_argument = false;
        for (call.arguments.items) |argument| switch (argument) {
            .literal => {
                constant_argument = true;
                break;
            },
            .identifier => |identifier| if (self.constants.contains(identifier.name)) {
                constant_argument = true;
                break;
            },
            .function_call => {},
        };
        return size < (if (aggressive) @as(usize, 8) else 6) or
            (constant_argument and size < (if (aggressive) @as(usize, 16) else 12));
    }

    fn tentativelyUpdateCodeSize(self: *FullInliner, function_name: YulName, call_site: YulName) !void {
        const call_size = self.function_sizes.get(function_name) orelse
            return error.MissingFunctionSize;
        const site_size = self.function_sizes.getPtr(call_site) orelse
            return error.MissingCallSiteSize;
        site_size.* = std.math.add(usize, site_size.*, call_size.*) catch
            return error.CodeSizeOverflow;
    }
};

pub const InlineModifier = struct {
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    current_function: YulName,
    driver: *FullInliner,

    pub fn run(self: *InlineModifier, block: *AST.Block) anyerror!void {
        var index: usize = 0;
        while (index < block.statements.items.len) {
            try self.visitChildren(&block.statements.items[index]);
            if (try self.tryInlineStatement(&block.statements.items[index])) |replacement_value| {
                var replacement = replacement_value;
                defer deinitStatements(self.allocator, &replacement);
                try block.statements.ensureUnusedCapacity(self.allocator, replacement.items.len);
                var removed = block.statements.orderedRemove(index);
                removed.deinit(self.allocator);
                block.statements.insertSliceAssumeCapacity(index, replacement.items);
                const inserted = replacement.items.len;
                replacement.clearRetainingCapacity();
                index += inserted;
            } else {
                index += 1;
            }
        }
    }

    fn visitChildren(self: *InlineModifier, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*function| try self.run(&function.body),
            .if_statement => |*if_statement| try self.run(&if_statement.body),
            .switch_statement => |*switch_statement| for (switch_statement.cases.items) |*case_value|
                try self.run(&case_value.body),
            .for_loop => |*loop| {
                try self.run(&loop.pre);
                try self.run(&loop.post);
                try self.run(&loop.body);
            },
            .block => |*nested| try self.run(nested),
            else => {},
        }
    }

    fn tryInlineStatement(
        self: *InlineModifier,
        statement: *const AST.Statement,
    ) anyerror!?std.ArrayList(AST.Statement) {
        const expression = switch (statement.*) {
            .expression_statement => |*value| &value.expression,
            .assignment => |*value| value.value orelse return null,
            .variable_declaration => |*value| value.value orelse return null,
            else => return null,
        };
        const call = switch (expression.*) {
            .function_call => |*value| value,
            else => return null,
        };
        if (!try self.driver.shallInline(call, self.current_function)) return null;
        const replacement = try self.performInline(statement, call);
        return replacement;
    }

    fn performInline(
        self: *InlineModifier,
        statement: *const AST.Statement,
        call: *const AST.FunctionCall,
    ) anyerror!std.ArrayList(AST.Statement) {
        const function_name = switch (call.function_name) {
            .identifier => |identifier| identifier.name,
            .builtin => return error.CannotInlineBuiltin,
        };
        const function = self.driver.lookupFunction(function_name) orelse
            return error.FunctionNotFound;
        if (function.parameters.items.len != call.arguments.items.len)
            return error.InvalidCallArity;
        const output_count = switch (statement.*) {
            .assignment => |value| value.variable_names.items.len,
            .variable_declaration => |value| value.variables.items.len,
            .expression_statement => 0,
            else => unreachable,
        };
        if (output_count != function.return_variables.items.len)
            return error.InvalidReturnArity;
        try self.driver.tentativelyUpdateCodeSize(function.name, self.current_function);

        var replacements: TranslationMap = .{};
        defer replacements.deinit(self.scratch_allocator);
        var result: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(self.allocator, &result);
        var copier = ASTCopierModule.ASTCopier.init(self.allocator);

        var parameter_index = function.parameters.items.len;
        while (parameter_index != 0) {
            parameter_index -= 1;
            var argument = try copier.translateExpression(&call.arguments.items[parameter_index]);
            errdefer argument.deinit(self.allocator);
            try self.newVariable(
                &result,
                &replacements,
                function.parameters.items[parameter_index],
                call.debug_data,
                argument,
            );
        }
        for (function.return_variables.items) |return_variable| {
            const zero = AST.Expression{
                .literal = try self.driver.dialect.zeroLiteral(self.allocator),
            };
            try self.newVariable(
                &result,
                &replacements,
                return_variable,
                call.debug_data,
                zero,
            );
        }

        var body_copier = BodyCopier.init(
            self.allocator,
            self.scratch_allocator,
            self.driver.name_dispenser,
            &replacements,
        );
        var body = try body_copier.translateBlock(&function.body);
        defer body.deinit(self.allocator);
        try result.ensureUnusedCapacity(self.allocator, body.statements.items.len);
        while (body.statements.items.len != 0)
            result.appendAssumeCapacity(body.statements.orderedRemove(0));

        switch (statement.*) {
            .assignment => |assignment| for (assignment.variable_names.items, 0..) |variable, index|
                try appendAssignment(
                    self.allocator,
                    &result,
                    assignment.debug_data,
                    variable,
                    replacements.get(function.return_variables.items[index].name).?.*,
                ),
            .variable_declaration => |declaration| for (declaration.variables.items, 0..) |variable, index|
                try appendDeclaration(
                    self.allocator,
                    &result,
                    declaration.debug_data,
                    variable,
                    .{ .identifier = .{
                        .debug_data = declaration.debug_data,
                        .name = replacements.get(function.return_variables.items[index].name).?.*,
                    } },
                ),
            .expression_statement => {},
            else => unreachable,
        }
        return result;
    }

    fn newVariable(
        self: *InlineModifier,
        output: *std.ArrayList(AST.Statement),
        replacements: *TranslationMap,
        existing: AST.NameWithDebugData,
        debug_data: ?@import("../../liblangutil/debug_data.zig").DebugData,
        value: AST.Expression,
    ) !void {
        const new_name = try self.driver.name_dispenser.newName(existing.name);
        if (!(try replacements.insert(self.scratch_allocator, existing.name, new_name)))
            return error.DuplicateInlineVariable;
        try appendDeclaration(
            self.allocator,
            output,
            debug_data,
            .{ .debug_data = debug_data, .name = new_name },
            value,
        );
    }
};

pub const BodyCopier = struct {
    allocator: std.mem.Allocator,
    map_allocator: std.mem.Allocator,
    dispenser: *NameDispenser,
    replacements: *TranslationMap,

    pub fn init(
        allocator: std.mem.Allocator,
        map_allocator: std.mem.Allocator,
        dispenser: *NameDispenser,
        replacements: *TranslationMap,
    ) BodyCopier {
        return .{
            .allocator = allocator,
            .map_allocator = map_allocator,
            .dispenser = dispenser,
            .replacements = replacements,
        };
    }

    pub fn translateBlock(self: *BodyCopier, block: *const AST.Block) !AST.Block {
        try self.collectLocalDeclarations(block);
        var copier = ASTCopierModule.ASTCopier.initWithHooks(
            self.allocator,
            self,
            .{ .translate_identifier = translateIdentifier },
        );
        return copier.translateBlock(block);
    }

    fn translateIdentifier(context: ?*anyopaque, name_value: YulName) anyerror!YulName {
        const self: *BodyCopier = @ptrCast(@alignCast(context.?));
        const replacement = self.replacements.get(name_value) orelse return name_value;
        return replacement.*;
    }

    fn collectLocalDeclarations(self: *BodyCopier, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| switch (statement.*) {
            .variable_declaration => |*declaration| for (declaration.variables.items) |variable| {
                const new_name = try self.dispenser.newName(variable.name);
                if (!(try self.replacements.insert(self.map_allocator, variable.name, new_name)))
                    return error.DuplicateInlineVariable;
            },
            .function_definition => return error.FunctionHoisterNotRun,
            .if_statement => |*if_statement| try self.collectLocalDeclarations(&if_statement.body),
            .switch_statement => |*switch_statement| for (switch_statement.cases.items) |*case_value|
                try self.collectLocalDeclarations(&case_value.body),
            .for_loop => |*loop| {
                try self.collectLocalDeclarations(&loop.pre);
                try self.collectLocalDeclarations(&loop.post);
                try self.collectLocalDeclarations(&loop.body);
            },
            .block => |*nested| try self.collectLocalDeclarations(nested),
            else => {},
        };
    }
};

fn appendDeclaration(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(AST.Statement),
    debug_data: ?@import("../../liblangutil/debug_data.zig").DebugData,
    variable: AST.NameWithDebugData,
    value: AST.Expression,
) !void {
    try output.ensureUnusedCapacity(allocator, 1);
    var declaration: AST.VariableDeclaration = .{ .debug_data = debug_data };
    errdefer declaration.deinit(allocator);
    try declaration.variables.append(allocator, variable);
    declaration.value = try AST.createExpression(allocator, value);
    output.appendAssumeCapacity(.{ .variable_declaration = declaration });
}

fn appendAssignment(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(AST.Statement),
    debug_data: ?@import("../../liblangutil/debug_data.zig").DebugData,
    variable: AST.Identifier,
    value_name: YulName,
) !void {
    try output.ensureUnusedCapacity(allocator, 1);
    var assignment: AST.Assignment = .{ .debug_data = debug_data };
    errdefer assignment.deinit(allocator);
    try assignment.variable_names.append(allocator, variable);
    assignment.value = try AST.createExpression(allocator, .{ .identifier = .{
        .debug_data = debug_data,
        .name = value_name,
    } });
    output.appendAssumeCapacity(.{ .assignment = assignment });
}

fn deinitStatements(
    allocator: std.mem.Allocator,
    statements: *std.ArrayList(AST.Statement),
) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(allocator);
}

test "inline declarations and assignments transfer ownership on allocation failure" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseInlineStatements, .{});
}

fn exerciseInlineStatements(allocator: std.mem.Allocator) !void {
    var output: std.ArrayList(AST.Statement) = .empty;
    defer {
        for (output.items) |*statement| statement.deinit(allocator);
        output.deinit(allocator);
    }
    {
        var value: AST.Expression = .{ .function_call = .{ .function_name = .{ .identifier = .{ .name = .{} } } } };
        errdefer value.deinit(allocator);
        try value.function_call.arguments.append(allocator, .{ .identifier = .{ .name = .{} } });
        try appendDeclaration(allocator, &output, null, .{ .name = .{} }, value);
    }
    try appendAssignment(allocator, &output, null, .{ .name = .{} }, .{});
    try std.testing.expectEqual(@as(usize, 2), output.items.len);
    try std.testing.expectEqual(@as(usize, 1), output.items[0].variable_declaration.value.?.function_call.arguments.items.len);
}

test "full inliner expands direct calls with fresh parameter and return variables" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMDialect = EVMDialectModule.EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ { let z := f(1, 2) pop(z) } function f(a, b) -> c { c := add(a, b) } }",
        "full-inliner.yul",
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
    try FullInliner.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "f(1, 2)") == null);
    try std.testing.expect(std.mem.find(u8, rendered, "add(") != null);
}
