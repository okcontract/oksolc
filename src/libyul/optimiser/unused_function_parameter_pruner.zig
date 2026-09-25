// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Splits functions so unused parameters and return variables can be removed.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const Common = @import("unused_functions_common.zig");
const NameCollectorModule = @import("name_collector.zig");
const NameDisplacerModule = @import("name_displacer.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const YulName = @import("../yul_name.zig").YulName;

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

const OwnedMasks = struct {
    parameters: std.ArrayList(bool) = .empty,
    returns: std.ArrayList(bool) = .empty,

    fn deinit(self: *OwnedMasks, allocator: std.mem.Allocator) void {
        self.parameters.deinit(allocator);
        self.returns.deinit(allocator);
        self.* = undefined;
    }

    fn borrowed(self: *const OwnedMasks) Common.UsageMasks {
        return .{ .parameters = self.parameters.items, .returns = self.returns.items };
    }
};

const UsageMap = ordered.OrderedMap(YulName, OwnedMasks, lessYulName);

pub const UnusedFunctionParameterPruner = struct {
    pub const name = "UnusedFunctionParameterPruner";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.scratchAllocator();
        var references = try NameCollectorModule.VariableReferencesCounter.countReferencesBlock(
            allocator,
            ast,
        );
        defer references.deinit(allocator);
        var usage: UsageMap = .{};
        defer {
            for (usage.mutableItems()) |*entry| entry.value.deinit(allocator);
            usage.deinit(allocator);
        }

        for (ast.statements.items) |*statement| {
            if (statement.* != .function_definition) continue;
            const function = &statement.function_definition;
            if (Common.tooSimpleToBePruned(function)) continue;
            var masks: OwnedMasks = .{};
            errdefer masks.deinit(allocator);
            var all_used = true;
            try masks.parameters.ensureTotalCapacity(allocator, function.parameters.items.len);
            for (function.parameters.items) |parameter| {
                const is_used = references.contains(parameter.name);
                masks.parameters.appendAssumeCapacity(is_used);
                all_used = all_used and is_used;
            }
            try masks.returns.ensureTotalCapacity(allocator, function.return_variables.items.len);
            for (function.return_variables.items) |return_variable| {
                const is_used = references.contains(return_variable.name);
                masks.returns.appendAssumeCapacity(is_used);
                all_used = all_used and is_used;
            }
            if (all_used) {
                masks.deinit(allocator);
                continue;
            }
            if (!(try usage.insert(allocator, function.name, masks)))
                return error.DuplicateFunctionName;
            masks = .{};
        }
        if (usage.isEmpty()) return;

        var names_to_free: NameCollectorModule.NameSet = .{};
        defer names_to_free.deinit(allocator);
        for (usage.items()) |entry| _ = try names_to_free.insert(allocator, entry.key);
        var displacer = try NameDisplacerModule.NameDisplacer.init(
            allocator,
            context.dispenser,
            &names_to_free,
        );
        defer displacer.deinit();
        try displacer.run(ast);

        const ast_allocator = context.dispenser.allocator;
        var output: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(ast_allocator, &output);
        try output.ensureTotalCapacity(ast_allocator, ast.statements.items.len + usage.len());
        for (ast.statements.items) |*statement| {
            if (statement.* == .function_definition and
                originalName(displacer.translations(), statement.function_definition.name) != null)
            {
                const linking_name = statement.function_definition.name;
                const original_name = originalName(displacer.translations(), linking_name).?;
                const masks = usage.get(original_name) orelse return error.MissingUsageMask;
                var linking = try Common.createLinkingFunction(
                    ast_allocator,
                    &statement.function_definition,
                    masks.borrowed(),
                    original_name,
                    linking_name,
                    context.dispenser,
                );
                errdefer linking.deinit(ast_allocator);
                statement.function_definition.name = original_name;
                try filterNames(&statement.function_definition.parameters, masks.parameters.items);
                try filterNames(
                    &statement.function_definition.return_variables,
                    masks.returns.items,
                );
                output.appendAssumeCapacity(statement.*);
                statement.* = .{ .block = .{} };
                output.appendAssumeCapacity(.{ .function_definition = linking });
                linking = .{};
            } else {
                output.appendAssumeCapacity(statement.*);
                statement.* = .{ .block = .{} };
            }
        }
        ast.statements.deinit(ast_allocator);
        ast.statements = output;
        output = .empty;
    }
};

fn originalName(
    translations: *const NameDisplacerModule.TranslationMap,
    translated: YulName,
) ?YulName {
    for (translations.items()) |entry| if (entry.value.eql(translated)) return entry.key;
    return null;
}

fn filterNames(names: *AST.NameWithDebugDataList, mask: []const bool) !void {
    if (names.items.len != mask.len) return error.InvalidUsageMask;
    var kept: usize = 0;
    for (names.items, mask) |entry, used| if (used) {
        names.items[kept] = entry;
        kept += 1;
    };
    names.items.len = kept;
}

fn deinitStatements(allocator: std.mem.Allocator, statements: *std.ArrayList(AST.Statement)) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(allocator);
}

test "unused parameter filtering compacts names in their existing buffer" {
    const allocator = std.testing.allocator;
    var names: AST.NameWithDebugDataList = .empty;
    defer names.deinit(allocator);
    for ([_][]const u8{ "first", "discarded", "last" }) |name|
        try names.append(allocator, .{ .name = try YulName.init(name) });
    const buffer = names.items.ptr;
    try std.testing.expectError(error.InvalidUsageMask, filterNames(&names, &.{true}));
    try std.testing.expectEqual(@as(usize, 3), names.items.len);
    try filterNames(&names, &.{ true, false, true });
    try std.testing.expectEqual(buffer, names.items.ptr);
    try std.testing.expectEqual(@as(usize, 2), names.items.len);
    try std.testing.expectEqualStrings("first", try names.items[0].name.str());
    try std.testing.expectEqualStrings("last", try names.items[1].name.str());
    try filterNames(&names, &.{ true, true });
    try std.testing.expectEqual(buffer, names.items.ptr);
    try filterNames(&names, &.{ false, false });
    try std.testing.expectEqual(@as(usize, 0), names.items.len);
    try std.testing.expectEqual(buffer, names.items.ptr);
}
