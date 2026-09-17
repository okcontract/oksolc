// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared control-flow engine for dead assignments and dead EVM stores.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimizerUtilities = @import("optimizer_utilities.zig");

pub const UnusedStoreEliminatorKey = enum {
    Memory,
    Storage,
};

pub fn UnusedStoreBase(comptime Key: type) type {
    return struct {
        const Self = @This();

        pub const StatementSet = OptimizerUtilities.StatementSet;
        pub const ActiveStores = std.AutoHashMap(Key, StatementSet);

        pub const Hooks = struct {
            context: ?*anyopaque = null,
            identifier: ?*const fn (?*anyopaque, *Self, *const AST.Identifier) anyerror!void = null,
            assignment: ?*const fn (?*anyopaque, *Self, *const AST.Assignment) anyerror!bool = null,
            function_call: ?*const fn (?*anyopaque, *Self, *const AST.FunctionCall) anyerror!void = null,
            enter_function: ?*const fn (?*anyopaque, *Self, *const AST.FunctionDefinition) anyerror!void = null,
            finalize_function: ?*const fn (?*anyopaque, *Self, *const AST.FunctionDefinition) anyerror!void = null,
            leave_function: ?*const fn (?*anyopaque, *Self, *const AST.FunctionDefinition) anyerror!void = null,
            leave_statement: ?*const fn (?*anyopaque, *Self, *const AST.Leave) anyerror!void = null,
            after_block: ?*const fn (?*anyopaque, *Self, *const AST.Block) anyerror!void = null,
            after_statement: ?*const fn (?*anyopaque, *Self, *const AST.Statement) anyerror!void = null,
            shortcut_nested_loop: ?*const fn (?*anyopaque, *Self, *const ActiveStores) anyerror!void = null,
        };

        const ForLoopInfo = struct {
            pending_break_statements: std.ArrayList(ActiveStores) = .empty,
            pending_continue_statements: std.ArrayList(ActiveStores) = .empty,

            fn deinit(self: *ForLoopInfo, allocator: std.mem.Allocator) void {
                for (self.pending_break_statements.items) |*stores| deinitActiveStores(stores);
                self.pending_break_statements.deinit(allocator);
                for (self.pending_continue_statements.items) |*stores| deinitActiveStores(stores);
                self.pending_continue_statements.deinit(allocator);
                self.* = undefined;
            }
        };

        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        hooks: Hooks = .{},
        all_stores: StatementSet,
        used_stores: StatementSet,
        stores_to_remove: std.ArrayList(*const AST.Statement) = .empty,
        active_stores: ActiveStores,
        for_loop_info: ForLoopInfo = .{},
        for_loop_nesting_depth: usize = 0,

        pub fn init(allocator: std.mem.Allocator, dialect: AST.Dialect) Self {
            return .{
                .allocator = allocator,
                .dialect = dialect,
                .all_stores = StatementSet.init(allocator),
                .used_stores = StatementSet.init(allocator),
                .active_stores = ActiveStores.init(allocator),
            };
        }

        pub fn deinit(self: *Self) void {
            self.all_stores.deinit();
            self.used_stores.deinit();
            self.stores_to_remove.deinit(self.allocator);
            deinitActiveStores(&self.active_stores);
            self.for_loop_info.deinit(self.allocator);
            self.* = undefined;
        }

        pub fn run(self: *Self, block: *const AST.Block) anyerror!void {
            try self.visitBlock(block);
        }

        pub fn addCurrentUnusedStoresToRemoval(self: *Self) !void {
            var iterator = self.all_stores.keyIterator();
            while (iterator.next()) |statement|
                if (!self.used_stores.contains(statement.*))
                    try self.stores_to_remove.append(self.allocator, statement.*);
        }

        pub fn removalSet(self: *const Self) !StatementSet {
            var result = StatementSet.init(self.allocator);
            errdefer result.deinit();
            for (self.stores_to_remove.items) |statement| try result.put(statement, {});
            return result;
        }

        pub fn activeSet(self: *Self, key: Key) !*StatementSet {
            const entry = try self.active_stores.getOrPut(key);
            if (!entry.found_existing) entry.value_ptr.* = StatementSet.init(self.allocator);
            return entry.value_ptr;
        }

        pub fn clearActiveKey(self: *Self, key: Key) !void {
            (try self.activeSet(key)).clearRetainingCapacity();
        }

        pub fn replaceActiveWithStatement(
            self: *Self,
            key: Key,
            statement: *const AST.Statement,
        ) !void {
            const set = try self.activeSet(key);
            set.clearRetainingCapacity();
            try set.put(statement, {});
        }

        pub fn markKeyUsed(self: *Self, key: Key) !void {
            const removed = self.active_stores.fetchRemove(key) orelse return;
            var stores = removed.value;
            defer stores.deinit();
            var iterator = stores.keyIterator();
            while (iterator.next()) |statement| try self.used_stores.put(statement.*, {});
        }

        pub fn clearAllActive(self: *Self) void {
            deinitActiveStores(&self.active_stores);
            self.active_stores = ActiveStores.init(self.allocator);
        }

        pub fn visitExpression(self: *Self, expression: *const AST.Expression) anyerror!void {
            switch (expression.*) {
                .literal => {},
                .identifier => |*identifier| if (self.hooks.identifier) |hook|
                    try hook(self.hooks.context, self, identifier),
                .function_call => |*call| {
                    var index = call.arguments.items.len;
                    while (index != 0) {
                        index -= 1;
                        try self.visitExpression(&call.arguments.items[index]);
                    }
                    if (self.hooks.function_call) |hook|
                        try hook(self.hooks.context, self, call);
                },
            }
        }

        fn visitStatement(self: *Self, statement: *const AST.Statement) anyerror!void {
            switch (statement.*) {
                .expression_statement => |*value| try self.visitExpression(&value.expression),
                .assignment => |*value| {
                    const handled = if (self.hooks.assignment) |hook|
                        try hook(self.hooks.context, self, value)
                    else
                        false;
                    if (!handled) {
                        for (value.variable_names.items) |*name|
                            if (self.hooks.identifier) |hook|
                                try hook(self.hooks.context, self, name);
                        try self.visitExpression(value.value orelse return error.InvalidAst);
                    }
                },
                .variable_declaration => |*value| if (value.value) |expression|
                    try self.visitExpression(expression),
                .function_definition => |*value| try self.visitFunctionDefinition(value),
                .if_statement => |*value| try self.visitIf(value),
                .switch_statement => |*value| try self.visitSwitch(value),
                .for_loop => |*value| try self.visitForLoop(value),
                .break_statement => try self.visitBreak(),
                .continue_statement => try self.visitContinue(),
                .leave_statement => |*value| if (self.hooks.leave_statement) |hook|
                    try hook(self.hooks.context, self, value),
                .block => |*value| try self.visitBlock(value),
            }
            if (self.hooks.after_statement) |hook|
                try hook(self.hooks.context, self, statement);
        }

        fn visitBlock(self: *Self, block: *const AST.Block) anyerror!void {
            for (block.statements.items) |*statement| try self.visitStatement(statement);
            if (self.hooks.after_block) |hook| try hook(self.hooks.context, self, block);
        }

        fn visitIf(self: *Self, if_statement: *const AST.If) anyerror!void {
            try self.visitExpression(if_statement.condition orelse return error.InvalidAst);
            var skip_branch = try cloneActiveStores(self.allocator, &self.active_stores);
            errdefer deinitActiveStores(&skip_branch);
            try self.visitBlock(&if_statement.body);
            try merge(&self.active_stores, &skip_branch);
        }

        fn visitSwitch(self: *Self, switch_statement: *const AST.Switch) anyerror!void {
            try self.visitExpression(switch_statement.expression orelse return error.InvalidAst);
            var pre_state = try cloneActiveStores(self.allocator, &self.active_stores);
            defer deinitActiveStores(&pre_state);
            var branches: std.ArrayList(ActiveStores) = .empty;
            defer {
                for (branches.items) |*stores| deinitActiveStores(stores);
                branches.deinit(self.allocator);
            }
            var has_default = false;
            for (switch_statement.cases.items) |*case_value| {
                if (case_value.value == null) has_default = true;
                try self.visitBlock(&case_value.body);
                try branches.append(self.allocator, self.active_stores);
                self.active_stores = try cloneActiveStores(self.allocator, &pre_state);
            }
            if (has_default) {
                deinitActiveStores(&self.active_stores);
                self.active_stores = branches.pop().?;
            }
            for (branches.items) |*branch| try merge(&self.active_stores, branch);
            branches.clearRetainingCapacity();
        }

        fn visitFunctionDefinition(
            self: *Self,
            function: *const AST.FunctionDefinition,
        ) anyerror!void {
            const saved_all_stores = self.all_stores;
            const saved_used_stores = self.used_stores;
            const saved_active_stores = self.active_stores;
            const saved_for_loop_info = self.for_loop_info;
            const saved_nesting_depth = self.for_loop_nesting_depth;

            self.all_stores = StatementSet.init(self.allocator);
            self.used_stores = StatementSet.init(self.allocator);
            self.active_stores = ActiveStores.init(self.allocator);
            self.for_loop_info = .{};
            self.for_loop_nesting_depth = 0;
            defer {
                self.all_stores.deinit();
                self.used_stores.deinit();
                deinitActiveStores(&self.active_stores);
                self.for_loop_info.deinit(self.allocator);
                self.all_stores = saved_all_stores;
                self.used_stores = saved_used_stores;
                self.active_stores = saved_active_stores;
                self.for_loop_info = saved_for_loop_info;
                self.for_loop_nesting_depth = saved_nesting_depth;
            }

            if (self.hooks.enter_function) |hook|
                try hook(self.hooks.context, self, function);
            try self.visitBlock(&function.body);
            if (self.hooks.finalize_function) |hook|
                try hook(self.hooks.context, self, function);
            try self.addCurrentUnusedStoresToRemoval();
            if (self.hooks.leave_function) |hook|
                try hook(self.hooks.context, self, function);
        }

        fn visitForLoop(self: *Self, loop: *const AST.ForLoop) anyerror!void {
            if (loop.pre.statements.items.len != 0) return error.NonEmptyForLoopPre;

            const saved_loop_info = self.for_loop_info;
            self.for_loop_info = .{};
            self.for_loop_nesting_depth += 1;
            defer {
                self.for_loop_info.deinit(self.allocator);
                self.for_loop_info = saved_loop_info;
                self.for_loop_nesting_depth -= 1;
            }

            try self.visitExpression(loop.condition orelse return error.InvalidAst);
            var zero_runs = try cloneActiveStores(self.allocator, &self.active_stores);
            errdefer deinitActiveStores(&zero_runs);

            try self.visitBlock(&loop.body);
            try mergeList(&self.active_stores, &self.for_loop_info.pending_continue_statements);
            try self.visitBlock(&loop.post);
            try self.visitExpression(loop.condition orelse return error.InvalidAst);

            if (self.for_loop_nesting_depth < 6) {
                var one_run = try cloneActiveStores(self.allocator, &self.active_stores);
                errdefer deinitActiveStores(&one_run);
                try self.visitBlock(&loop.body);
                try mergeList(&self.active_stores, &self.for_loop_info.pending_continue_statements);
                try self.visitBlock(&loop.post);
                try self.visitExpression(loop.condition orelse return error.InvalidAst);
                try merge(&self.active_stores, &one_run);
            } else if (self.hooks.shortcut_nested_loop) |hook| {
                try hook(self.hooks.context, self, &zero_runs);
            }

            try merge(&self.active_stores, &zero_runs);
            try mergeList(&self.active_stores, &self.for_loop_info.pending_break_statements);
        }

        fn visitBreak(self: *Self) !void {
            try self.for_loop_info.pending_break_statements.append(
                self.allocator,
                self.active_stores,
            );
            self.active_stores = ActiveStores.init(self.allocator);
        }

        fn visitContinue(self: *Self) !void {
            try self.for_loop_info.pending_continue_statements.append(
                self.allocator,
                self.active_stores,
            );
            self.active_stores = ActiveStores.init(self.allocator);
        }

        fn cloneActiveStores(
            allocator: std.mem.Allocator,
            source: *const ActiveStores,
        ) !ActiveStores {
            var result = ActiveStores.init(allocator); // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
            errdefer deinitActiveStores(&result);
            var iterator = source.iterator();
            while (iterator.next()) |entry| {
                var set = StatementSet.init(allocator);
                errdefer set.deinit();
                var stores = entry.value_ptr.keyIterator();
                while (stores.next()) |statement| try set.put(statement.*, {});
                try result.put(entry.key_ptr.*, set);
            }
            return result;
        }

        fn deinitActiveStores(stores: *ActiveStores) void {
            var iterator = stores.valueIterator();
            while (iterator.next()) |set| set.deinit();
            stores.deinit();
        }

        fn merge(target: *ActiveStores, source: *ActiveStores) !void {
            defer {
                source.deinit();
                source.* = undefined;
            }
            var iterator = source.iterator();
            while (iterator.next()) |entry| {
                const target_entry = try target.getOrPut(entry.key_ptr.*);
                if (!target_entry.found_existing)
                    target_entry.value_ptr.* = StatementSet.init(target.allocator);
                var stores = entry.value_ptr.keyIterator();
                while (stores.next()) |statement| try target_entry.value_ptr.put(statement.*, {});
                entry.value_ptr.deinit();
                entry.value_ptr.* = undefined;
            }
        }

        fn mergeList(target: *ActiveStores, sources: *std.ArrayList(ActiveStores)) !void {
            for (sources.items) |*source| try merge(target, source);
            sources.clearRetainingCapacity();
        }
    };
}
