// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Definite-assignment and unreachable-code analysis translated from
//! `ControlFlowAnalyzer.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const TypeBehavior = @import("../ast/types.zig");
const Types = @import("../ast/types.zig");
const Graph = @import("control_flow_graph.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;

pub const AnalyzeError = std.mem.Allocator.Error ||
    Diagnostics.ReportError || error{InvalidAst};

const DeclarationSet = std.AutoHashMap(*const AST.Node, void);
const OccurrenceSet = std.AutoHashMap(*const Graph.VariableOccurrence, void);
const NodeSet = std.AutoHashMap(*const Graph.CFGNode, void);

const NodeInfo = struct {
    unassigned_at_entry: DeclarationSet,
    unassigned_at_exit: DeclarationSet,
    uninitialized_accesses: OccurrenceSet,

    fn init(allocator: std.mem.Allocator) NodeInfo {
        return .{
            .unassigned_at_entry = DeclarationSet.init(allocator),
            .unassigned_at_exit = DeclarationSet.init(allocator),
            .uninitialized_accesses = OccurrenceSet.init(allocator),
        };
    }

    fn deinit(self: *NodeInfo) void {
        self.uninitialized_accesses.deinit();
        self.unassigned_at_exit.deinit();
        self.unassigned_at_entry.deinit();
        self.* = undefined;
    }
};

pub const ControlFlowAnalyzer = struct {
    allocator: std.mem.Allocator,
    cfg: *const Graph.CFG,
    reporter: *Diagnostics.ErrorReporter,
    unreachable_warned: std.ArrayList(SourceLocation) = .empty,
    return_variables_warned: std.AutoHashMap(*const AST.Node, void),

    pub fn init(
        allocator: std.mem.Allocator,
        cfg: *const Graph.CFG,
        reporter: *Diagnostics.ErrorReporter,
    ) ControlFlowAnalyzer {
        return .{
            .allocator = allocator,
            .cfg = cfg,
            .reporter = reporter,
            .return_variables_warned = std.AutoHashMap(*const AST.Node, void).init(allocator),
        };
    }

    pub fn deinit(self: *ControlFlowAnalyzer) void {
        self.return_variables_warned.deinit();
        self.unreachable_warned.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn run(self: *ControlFlowAnalyzer) AnalyzeError!bool {
        const watcher = self.reporter.errorWatcher();
        var ordered: std.ArrayList(*const Graph.FlowEntry) = .empty;
        defer ordered.deinit(self.allocator);
        for (self.cfg.function_flows.items) |*entry|
            try ordered.append(self.allocator, entry);
        std.mem.sort(*const Graph.FlowEntry, ordered.items, {}, flowEntryLessThan);
        for (ordered.items) |entry|
            try self.analyze(entry.key, &entry.flow);
        return watcher.ok();
    }

    fn analyze(
        self: *ControlFlowAnalyzer,
        key: Graph.FunctionContractTuple,
        flow: *const Graph.FunctionFlow,
    ) AnalyzeError!void {
        if (key.function.nodeKind() != .function_definition or
            !key.function.payload.function_definition.implemented()) return;
        const declaring_scope = ASTImplementation.scope(key.function);
        const most_derived_name: ?[]const u8 = if (key.contract != null and
            key.contract != declaring_scope)
            key.contract.?.payload.contract_definition.declaration.name
        else
            null;
        const body = key.function.payload.function_definition.body.?;
        const empty_body = body.nodeKind() == .block and
            body.payload.block.statements.len == 0;
        try self.checkUninitializedAccess(
            flow.entry,
            flow.exit,
            empty_body,
            most_derived_name,
        );
        try self.checkUnreachable(
            flow.entry,
            flow.exit,
            flow.revert,
            flow.transaction_return,
        );
    }

    fn checkUninitializedAccess(
        self: *ControlFlowAnalyzer,
        entry: *const Graph.CFGNode,
        exit: *const Graph.CFGNode,
        empty_body: bool,
        contract_name: ?[]const u8,
    ) AnalyzeError!void {
        var infos = std.AutoHashMap(*const Graph.CFGNode, NodeInfo).init(self.allocator);
        defer {
            var iterator = infos.valueIterator();
            while (iterator.next()) |info| info.deinit();
            infos.deinit();
        }
        var queue: std.ArrayList(*const Graph.CFGNode) = .empty;
        defer queue.deinit(self.allocator);
        try queue.append(self.allocator, entry);
        var queue_index: usize = 0;
        while (queue_index < queue.items.len) : (queue_index += 1) {
            const node = queue.items[queue_index];
            const info_result = try infos.getOrPut(node);
            if (!info_result.found_existing) info_result.value_ptr.* = NodeInfo.init(self.allocator);
            const info = info_result.value_ptr;
            var unassigned = DeclarationSet.init(self.allocator);
            defer unassigned.deinit();
            _ = try unionDeclarations(&unassigned, &info.unassigned_at_entry);
            for (node.variable_occurrences.items) |*occurrence| switch (occurrence.kind) {
                .Assignment => _ = unassigned.remove(occurrence.declaration),
                .InlineAssembly, .Access, .Return => {
                    if (unassigned.contains(occurrence.declaration))
                        try info.uninitialized_accesses.put(occurrence, {});
                },
                .Declaration => try unassigned.put(occurrence.declaration, {}),
            };
            _ = try unionDeclarations(&info.unassigned_at_exit, &unassigned);

            for (node.exits.items) |next| {
                const next_result = try infos.getOrPut(next);
                if (!next_result.found_existing) next_result.value_ptr.* = NodeInfo.init(self.allocator);
                var changed = !next_result.found_existing;

                // `getOrPut()` may grow `infos`, invalidating `info_result.value_ptr`.
                // Reacquire both entries before borrowing their nested maps.
                const current_info = infos.getPtr(node) orelse return error.InvalidAst;
                const next_info = infos.getPtr(next) orelse return error.InvalidAst;
                changed = (try unionDeclarations(
                    &next_info.unassigned_at_entry,
                    &current_info.unassigned_at_exit,
                )) or changed;
                changed = (try unionOccurrences(
                    &next_info.uninitialized_accesses,
                    &current_info.uninitialized_accesses,
                )) or changed;
                if (changed) try queue.append(self.allocator, next);
            }
        }

        const exit_info = infos.getPtr(exit) orelse return;
        var ordered: std.ArrayList(*const Graph.VariableOccurrence) = .empty;
        defer ordered.deinit(self.allocator);
        var occurrence_iterator = exit_info.uninitialized_accesses.keyIterator();
        while (occurrence_iterator.next()) |occurrence|
            try ordered.append(self.allocator, occurrence.*);
        std.mem.sort(
            *const Graph.VariableOccurrence,
            ordered.items,
            {},
            occurrenceLessThan,
        );
        for (ordered.items) |occurrence|
            try self.reportUninitialized(occurrence, empty_body, contract_name);
    }

    fn reportUninitialized(
        self: *ControlFlowAnalyzer,
        occurrence: *const Graph.VariableOccurrence,
        empty_body: bool,
        contract_name: ?[]const u8,
    ) AnalyzeError!void {
        const variable = occurrence.declaration;
        const type_ref = try variableType(variable);
        const storage = TypeBehavior.dataStoredIn(type_ref, .Storage);
        const calldata = TypeBehavior.dataStoredIn(type_ref, .CallData);
        if (storage or calldata) {
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.allocator);
            if (occurrence.occurrence != null)
                try secondary.append(
                    self.allocator,
                    "The variable was declared here.",
                    variable.location,
                );
            const message = try std.fmt.allocPrint(
                self.allocator,
                "This variable is of {s} pointer type and can be {s} without prior assignment, which would lead to undefined behaviour.",
                .{
                    if (storage) "storage" else "calldata",
                    if (occurrence.kind == .Return) "returned" else "accessed",
                },
            );
            defer self.allocator.free(message);
            try self.reporter.reportWithSecondary(
                errorId(3464),
                .TypeError,
                occurrence.occurrence orelse variable.location,
                &secondary,
                message,
            );
            return;
        }
        const declaration = variable.payload.variable_declaration.declaration;
        if (empty_body or declaration.name.len != 0) return;
        const inserted = try self.return_variables_warned.getOrPut(variable);
        if (inserted.found_existing) return;
        const message = if (contract_name) |name|
            try std.fmt.allocPrint(
                self.allocator,
                "Unnamed return variable can remain unassigned when the function is called when \"{s}\" is the most derived contract. Add an explicit return with value to all non-reverting code paths or name the variable.",
                .{name},
            )
        else
            try self.allocator.dupe(
                u8,
                "Unnamed return variable can remain unassigned. Add an explicit return with value to all non-reverting code paths or name the variable.",
            );
        defer self.allocator.free(message);
        try self.reporter.warning(errorId(6321), variable.location, message);
    }

    fn checkUnreachable(
        self: *ControlFlowAnalyzer,
        entry: *const Graph.CFGNode,
        exit: *const Graph.CFGNode,
        revert: *const Graph.CFGNode,
        transaction_return: *const Graph.CFGNode,
    ) AnalyzeError!void {
        var reachable = NodeSet.init(self.allocator);
        defer reachable.deinit();
        try walkForward(self.allocator, entry, &reachable);

        var reverse_seen = NodeSet.init(self.allocator);
        defer reverse_seen.deinit();
        var queue: std.ArrayList(*const Graph.CFGNode) = .empty;
        defer queue.deinit(self.allocator);
        try queue.appendSlice(self.allocator, &.{ exit, revert, transaction_return });
        var unreachable_locations: std.ArrayList(SourceLocation) = .empty;
        defer unreachable_locations.deinit(self.allocator);
        var index: usize = 0;
        while (index < queue.items.len) : (index += 1) {
            const node = queue.items[index];
            const inserted = try reverse_seen.getOrPut(node);
            if (inserted.found_existing) continue;
            if (!reachable.contains(node) and node.location.isValid() and
                !containsLocation(unreachable_locations.items, node.location))
                try unreachable_locations.append(self.allocator, node.location);
            for (node.entries.items) |previous|
                try queue.append(self.allocator, previous);
        }
        std.mem.sort(SourceLocation, unreachable_locations.items, {}, locationLessThan);
        var location_index: usize = 0;
        while (location_index < unreachable_locations.items.len) {
            var location = unreachable_locations.items[location_index];
            location_index += 1;
            while (location_index < unreachable_locations.items.len and
                location.equalSources(unreachable_locations.items[location_index]) and
                unreachable_locations.items[location_index].start <= location.end)
            {
                location.end = @max(location.end, unreachable_locations.items[location_index].end);
                location_index += 1;
            }
            if (containsLocation(self.unreachable_warned.items, location)) continue;
            try self.unreachable_warned.append(self.allocator, location);
            try self.reporter.warning(errorId(5740), location, "Unreachable code.");
        }
    }
};

fn unionDeclarations(target: *DeclarationSet, source: *const DeclarationSet) !bool {
    const before = target.count();
    var iterator = source.keyIterator();
    while (iterator.next()) |key| try target.put(key.*, {});
    return target.count() != before;
}

fn unionOccurrences(target: *OccurrenceSet, source: *const OccurrenceSet) !bool {
    const before = target.count();
    var iterator = source.keyIterator();
    while (iterator.next()) |key| try target.put(key.*, {});
    return target.count() != before;
}

fn occurrenceLessThan(
    _: void,
    lhs: *const Graph.VariableOccurrence,
    rhs: *const Graph.VariableOccurrence,
) bool {
    return Graph.VariableOccurrence.lessThan({}, lhs.*, rhs.*);
}

fn flowEntryLessThan(
    _: void,
    lhs: *const Graph.FlowEntry,
    rhs: *const Graph.FlowEntry,
) bool {
    const lhs_contract_id = if (lhs.key.contract) |contract|
        ASTAnnotations.compatibilityId(contract)
    else
        -1;
    const rhs_contract_id = if (rhs.key.contract) |contract|
        ASTAnnotations.compatibilityId(contract)
    else
        -1;
    if (lhs_contract_id != rhs_contract_id) return lhs_contract_id < rhs_contract_id;
    return ASTAnnotations.compatibilityId(lhs.key.function) <
        ASTAnnotations.compatibilityId(rhs.key.function);
}

fn walkForward(
    allocator: std.mem.Allocator,
    entry: *const Graph.CFGNode,
    visited: *NodeSet,
) !void {
    var queue: std.ArrayList(*const Graph.CFGNode) = .empty;
    defer queue.deinit(allocator);
    try queue.append(allocator, entry);
    var index: usize = 0;
    while (index < queue.items.len) : (index += 1) {
        const node = queue.items[index];
        const inserted = try visited.getOrPut(node);
        if (inserted.found_existing) continue;
        for (node.exits.items) |next| try queue.append(allocator, next);
    }
}

fn variableType(variable: *const AST.Node) AnalyzeError!*const Types.Type {
    if (variable.nodeKind() != .variable_declaration) return error.InvalidAst;
    const annotation = ASTAnnotations.annotationConst(variable) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .variable_declaration => |value| value.type_ref orelse error.InvalidAst,
        else => error.InvalidAst,
    };
}

fn containsLocation(locations: []const SourceLocation, needle: SourceLocation) bool {
    for (locations) |location| if (location.eql(needle)) return true;
    return false;
}

fn locationLessThan(_: void, lhs: SourceLocation, rhs: SourceLocation) bool {
    return lhs.lessThan(rhs);
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
