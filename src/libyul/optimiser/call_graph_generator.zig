// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Disambiguated Yul call graph construction and recursion detection.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const Tarjan = @import("../../libsolutil/tarjan_scc.zig");
const NameCollectorModule = @import("name_collector.zig");
const YulName = @import("../yul_name.zig").YulName;

fn lessFunctionHandle(left: AST.FunctionHandle, right: AST.FunctionHandle) bool {
    const left_tag = @intFromEnum(left);
    const right_tag = @intFromEnum(right);
    if (left_tag != right_tag) return left_tag < right_tag;
    return switch (left) {
        .user => |name| name.lessThan(right.user),
        .builtin => |handle| handle.id < right.builtin.id,
    };
}

pub const FunctionCalls = ordered.OrderedMap(
    AST.FunctionHandle,
    std.ArrayList(AST.FunctionHandle),
    lessFunctionHandle,
);
pub const FunctionHandleSet = ordered.OrderedSet(AST.FunctionHandle, lessFunctionHandle);

pub const CallGraph = struct {
    allocator: std.mem.Allocator,
    function_calls: FunctionCalls = .{},
    functions_with_loops: NameCollectorModule.NameSet = .{},

    pub fn deinit(self: *CallGraph) void {
        for (self.function_calls.mutableItems()) |*entry| entry.value.deinit(self.allocator);
        self.function_calls.deinit(self.allocator);
        self.functions_with_loops.deinit(self.allocator);
        self.* = undefined;
    }

    /// The returned set is owned by the caller and uses this graph's allocator.
    pub fn recursiveFunctions(self: *const CallGraph) anyerror!FunctionHandleSet {
        var handles: std.ArrayList(AST.FunctionHandle) = .empty;
        defer handles.deinit(self.allocator);
        for (self.function_calls.items()) |entry| {
            try appendUniqueHandle(self.allocator, &handles, entry.key);
            for (entry.value.items) |callee| try appendUniqueHandle(self.allocator, &handles, callee);
        }

        const adjacency_lists = try self.allocator.alloc(std.ArrayList(usize), handles.items.len);
        defer self.allocator.free(adjacency_lists);
        for (adjacency_lists) |*list| list.* = .empty;
        defer for (adjacency_lists) |*list| list.deinit(self.allocator);
        for (self.function_calls.items()) |entry| {
            const caller = indexOfHandle(handles.items, entry.key) orelse return error.MissingCallGraphNode;
            for (entry.value.items) |callee| {
                const callee_index = indexOfHandle(handles.items, callee) orelse return error.MissingCallGraphNode;
                if (!containsIndex(adjacency_lists[caller].items, callee_index))
                    try adjacency_lists[caller].append(self.allocator, callee_index);
            }
            std.sort.heap(usize, adjacency_lists[caller].items, {}, std.sort.asc(usize));
        }
        const adjacency = try self.allocator.alloc([]const usize, adjacency_lists.len);
        defer self.allocator.free(adjacency);
        for (adjacency_lists, adjacency) |list, *slice| slice.* = list.items;
        var components = try Tarjan.computeStronglyConnectedComponents(usize, self.allocator, adjacency);
        defer components.deinit();

        var recursive: FunctionHandleSet = .{};
        errdefer recursive.deinit(self.allocator);
        for (components.items) |component| {
            if (component.len > 1) {
                for (component) |node| _ = try recursive.insert(self.allocator, handles.items[node]);
            } else if (component.len == 1 and
                containsIndex(adjacency_lists[component[0]].items, component[0]))
            {
                _ = try recursive.insert(self.allocator, handles.items[component[0]]);
            }
        }
        for (0..recursive.len()) |index| switch (recursive.at(index)) {
            .user => |name| if (name.empty()) return error.TopLevelCannotBeRecursive,
            .builtin => return error.BuiltinCannotBeRecursive,
        };
        return recursive;
    }
};

pub const CallGraphGenerator = struct {
    allocator: std.mem.Allocator,
    graph: CallGraph,
    current_function: YulName = .{},

    pub fn callGraph(allocator: std.mem.Allocator, ast: *const AST.Block) anyerror!CallGraph {
        var generator: CallGraphGenerator = .{
            .allocator = allocator,
            .graph = .{ .allocator = allocator },
        };
        errdefer generator.graph.deinit();
        _ = try generator.graph.function_calls.insert(
            allocator,
            .{ .user = .{} },
            .empty,
        );
        try generator.visitBlock(ast);
        return generator.graph;
    }

    fn visitBlock(self: *CallGraphGenerator, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *CallGraphGenerator, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| {
                const handle: AST.FunctionHandle = .{ .user = value.name };
                if (self.graph.function_calls.contains(handle)) return error.InputNotDisambiguated;
                _ = try self.graph.function_calls.insert(self.allocator, handle, .empty);
                const previous = self.current_function;
                self.current_function = value.name;
                try self.visitBlock(&value.body);
                self.current_function = previous;
            },
            .if_statement => |*value| {
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression| try self.visitExpression(expression);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                _ = try self.graph.functions_with_loops.insert(self.allocator, self.current_function);
                try self.visitBlock(&value.pre);
                if (value.condition) |condition| try self.visitExpression(condition);
                try self.visitBlock(&value.body);
                try self.visitBlock(&value.post);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *CallGraphGenerator, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .function_call => |*call| {
                const caller: AST.FunctionHandle = .{ .user = self.current_function };
                const calls = self.graph.function_calls.getPtr(caller) orelse return error.MissingCaller;
                const callee: AST.FunctionHandle = switch (call.function_name) {
                    .builtin => |builtin| .{ .builtin = builtin.handle },
                    .identifier => |identifier| .{ .user = identifier.name },
                };
                if (!containsHandle(calls.items, callee)) try calls.append(self.allocator, callee);
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
            .identifier, .literal => {},
        }
    }
};

fn appendUniqueHandle(
    allocator: std.mem.Allocator,
    handles: *std.ArrayList(AST.FunctionHandle),
    handle: AST.FunctionHandle,
) !void {
    if (!containsHandle(handles.items, handle)) try handles.append(allocator, handle);
}

fn indexOfHandle(handles: []const AST.FunctionHandle, needle: AST.FunctionHandle) ?usize {
    for (handles, 0..) |handle, index| if (std.meta.eql(handle, needle)) return index;
    return null;
}

fn containsHandle(handles: []const AST.FunctionHandle, needle: AST.FunctionHandle) bool {
    return indexOfHandle(handles, needle) != null;
}

fn containsIndex(indices: []const usize, needle: usize) bool {
    for (indices) |index| if (index == needle) return true;
    return false;
}

test "call graph identifies mutual and direct recursion" {
    const allocator = std.testing.allocator;
    const f = try YulName.init("f");
    const g = try YulName.init("g");
    var graph: CallGraph = .{ .allocator = allocator };
    defer graph.deinit();
    var f_calls: std.ArrayList(AST.FunctionHandle) = .empty;
    try f_calls.append(allocator, .{ .user = g });
    _ = try graph.function_calls.insert(allocator, .{ .user = f }, f_calls);
    var g_calls: std.ArrayList(AST.FunctionHandle) = .empty;
    try g_calls.append(allocator, .{ .user = f });
    _ = try graph.function_calls.insert(allocator, .{ .user = g }, g_calls);
    var recursive = try graph.recursiveFunctions();
    defer recursive.deinit(allocator);
    try std.testing.expect(recursive.contains(.{ .user = f }));
    try std.testing.expect(recursive.contains(.{ .user = g }));
}
