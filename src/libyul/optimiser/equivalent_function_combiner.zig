// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Redirects calls to the first representative of each equivalent-function
//! class detected by `EquivalentFunctionDetector`.

const AST = @import("../ast.zig");
const Detector = @import("equivalent_function_detector.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const EquivalentFunctionCombiner = struct {
    duplicates: *const Detector.DuplicateMap,

    pub const name = "EquivalentFunctionCombiner";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        var duplicates = try Detector.EquivalentFunctionDetector.run(allocator, ast);
        defer duplicates.deinit();
        var combiner: EquivalentFunctionCombiner = .{ .duplicates = &duplicates };
        try combiner.visitBlock(ast);
    }

    fn visitExpression(
        self: *EquivalentFunctionCombiner,
        expression: *AST.Expression,
    ) anyerror!void {
        switch (expression.*) {
            .function_call => |*call| {
                switch (call.function_name) {
                    .identifier => |*identifier| {
                        if (self.duplicates.get(identifier.name)) |replacement|
                            identifier.name = replacement.name;
                    },
                    .builtin => {},
                }
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
            .literal, .identifier => {},
        }
    }

    fn visitBlock(self: *EquivalentFunctionCombiner, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(
        self: *EquivalentFunctionCombiner,
        statement: *AST.Statement,
    ) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| {
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression| try self.visitExpression(expression);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }
};
