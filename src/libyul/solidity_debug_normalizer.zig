// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Reproduce the debug annotation propagation of printing and reparsing Yul
//! with Solidity source mappings, without serializing the program. Native Yul
//! offsets are intentionally retained: this transform is for typed Solidity,
//! whose public source maps use origin locations, not generated text offsets.

const AST = @import("ast.zig");
const Object = @import("object.zig").Object;
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;

pub fn hasSourceMappings(object: *const Object) bool {
    const debug = object.debug_data orelse return false;
    const names = debug.source_names orelse return false;
    if (names.entries.items.len == 0) return false;
    for (object.sub_objects.items) |node| switch (node) {
        .object => |child| if (!hasSourceMappings(child)) return false,
        .data => {},
    };
    return true;
}

pub fn normalize(object: *Object, selection: DebugInfoSelection) void {
    var normalizer: Normalizer = .{ .selection = selection };
    normalizer.block(&object.code_value.?.root_block);
    for (object.sub_objects.items) |node| switch (node) {
        .object => |child| normalize(child, selection),
        .data => {},
    };
}

pub fn normalizeBlock(block: *AST.Block) void {
    var normalizer: Normalizer = .{};
    normalizer.block(block);
}

const Normalizer = struct {
    selection: DebugInfoSelection = .{ .location = true, .ast_id = true },
    printed_location: SourceLocation = .{},
    parsed_location: SourceLocation = .{},
    pending_location: ?SourceLocation = null,
    pending_ast_id: ?i64 = null,

    fn comment(self: *Normalizer, data: ?DebugData) void {
        const debug = data orelse return;
        if (self.selection.none()) return;
        const ast_id = if (self.selection.ast_id) debug.ast_id else null;
        const changed = !self.printed_location.eql(debug.origin_location);
        if (!changed and ast_id == null) return;
        // The scanner keeps the last adjacent documentation comment. An
        // ast-id-only comment can therefore replace a pending @src comment.
        self.pending_ast_id = ast_id;
        self.pending_location = if (changed) debug.origin_location else null;
        self.printed_location = debug.origin_location;
    }

    fn token(self: *Normalizer, old: ?DebugData) DebugData {
        if (self.pending_location) |location| self.parsed_location = location;
        const result: DebugData = .{
            .native_location = if (old) |data| data.native_location else .{},
            .origin_location = self.parsed_location,
            .ast_id = self.pending_ast_id,
        };
        self.pending_location = null;
        self.pending_ast_id = null;
        return result;
    }

    fn annotated(self: *Normalizer, data: *?DebugData) void {
        self.comment(data.*);
        data.* = self.token(data.*);
    }

    fn expression(self: *Normalizer, expr: *AST.Expression) void {
        switch (expr.*) {
            .identifier => |*value| self.annotated(&value.debug_data),
            .literal => |*value| self.annotated(&value.debug_data),
            .function_call => |*call| {
                self.comment(call.debug_data);
                switch (call.function_name) {
                    inline else => |*name| {
                        self.annotated(&name.debug_data);
                        const native = if (call.debug_data) |data| data.native_location else SourceLocation{};
                        call.debug_data = name.debug_data;
                        call.debug_data.?.native_location = native;
                    },
                }
                for (call.arguments.items) |*argument| self.expression(argument);
            },
        }
    }

    fn block(self: *Normalizer, value: *AST.Block) void {
        self.annotated(&value.debug_data);
        for (value.statements.items) |*stmt| self.statement(stmt);
    }

    fn names(self: *Normalizer, values: []AST.NameWithDebugData) void {
        for (values) |*value| self.annotated(&value.debug_data);
    }

    fn statement(self: *Normalizer, stmt: *AST.Statement) void {
        switch (stmt.*) {
            .block => |*value| self.block(value),
            .expression_statement => |*value| {
                self.comment(value.debug_data);
                self.expression(&value.expression);
                value.debug_data = value.expression.debugData().?.*;
            },
            .assignment => |*value| {
                self.comment(value.debug_data);
                for (value.variable_names.items) |*name| self.annotated(&name.debug_data);
                const native = if (value.debug_data) |data| data.native_location else SourceLocation{};
                value.debug_data = value.variable_names.items[0].debug_data;
                value.debug_data.?.native_location = native;
                self.expression(value.value.?);
            },
            .variable_declaration => |*value| {
                self.annotated(&value.debug_data);
                self.names(value.variables.items);
                if (value.value) |expr| self.expression(expr);
            },
            .function_definition => |*value| {
                self.annotated(&value.debug_data);
                self.names(value.parameters.items);
                self.names(value.return_variables.items);
                self.block(&value.body);
            },
            .if_statement => |*value| {
                self.annotated(&value.debug_data);
                self.expression(value.condition.?);
                self.block(&value.body);
            },
            .switch_statement => |*value| {
                self.annotated(&value.debug_data);
                self.expression(value.expression.?);
                for (value.cases.items) |*case| {
                    // AsmPrinter does not print the Case node's annotations.
                    case.debug_data = self.token(case.debug_data);
                    if (case.value) |literal| self.annotated(&literal.debug_data);
                    self.block(&case.body);
                }
            },
            .for_loop => |*value| {
                self.annotated(&value.debug_data);
                self.block(&value.pre);
                self.expression(value.condition.?);
                self.block(&value.post);
                self.block(&value.body);
            },
            inline .break_statement, .continue_statement, .leave_statement => |*value| self.annotated(&value.debug_data),
        }
    }
};
