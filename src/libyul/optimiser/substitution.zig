// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deep-copy substitution of identifier expressions without recursive replacement.

const std = @import("std");
const AST = @import("../ast.zig");
const ASTCopierModule = @import("ast_copier.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const SubstitutionMap = std.AutoHashMap(YulName, *const AST.Expression);

pub const Substitution = struct {
    copier: ASTCopierModule.ASTCopier,
    substitutions: *const SubstitutionMap,

    pub fn init(allocator: std.mem.Allocator, substitutions: *const SubstitutionMap) Substitution {
        return .{
            .copier = ASTCopierModule.ASTCopier.initWithHooks(allocator, null, .{
                .translate_expression = translateExpressionHook,
            }),
            .substitutions = substitutions,
        };
    }

    pub fn translateExpression(self: *Substitution, expression: *const AST.Expression) anyerror!AST.Expression {
        self.bind();
        return self.copier.translateExpression(expression);
    }

    pub fn translateStatement(self: *Substitution, statement: *const AST.Statement) anyerror!AST.Statement {
        self.bind();
        return self.copier.translateStatement(statement);
    }

    pub fn translateBlock(self: *Substitution, block: *const AST.Block) anyerror!AST.Block {
        self.bind();
        return self.copier.translateBlock(block);
    }

    fn bind(self: *Substitution) void {
        self.copier.context = self;
    }

    fn translateExpressionHook(
        context: ?*anyopaque,
        copier: *ASTCopierModule.ASTCopier,
        expression: *const AST.Expression,
    ) anyerror!?AST.Expression {
        const self: *Substitution = @ptrCast(@alignCast(context.?));
        if (expression.* != .identifier) return null;
        const replacement = self.substitutions.get(expression.identifier.name) orelse return null;
        var plain_copier = ASTCopierModule.ASTCopier.init(copier.allocator);
        return try plain_copier.translateExpression(replacement);
    }
};

test "substitution copies replacements without recursively substituting them" {
    const allocator = std.testing.allocator;
    const x = try YulName.init("x");
    const y = try YulName.init("y");
    const original: AST.Expression = .{ .identifier = .{ .name = x } };
    const replacement_x: AST.Expression = .{ .identifier = .{ .name = y } };
    var replacement_y: AST.Expression = .{ .literal = .{
        .kind = .Number,
        .value = try AST.LiteralValue.initNumeric(allocator, 9, null),
    } };
    defer replacement_y.deinit(allocator);
    var substitutions = SubstitutionMap.init(allocator);
    defer substitutions.deinit();
    try substitutions.put(x, &replacement_x);
    try substitutions.put(y, &replacement_y);
    var substitution = Substitution.init(allocator, &substitutions);
    var translated = try substitution.translateExpression(&original);
    defer translated.deinit(allocator);
    try std.testing.expect(translated == .identifier);
    try std.testing.expect(translated.identifier.name.eql(y));
}
