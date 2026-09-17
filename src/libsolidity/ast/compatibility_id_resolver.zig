// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Revision-scoped compatibility IDs for syntax and reserved semantic nodes.

const AST = @import("ast.zig");
const CompatibilityIds = @import("../../incremental/compatibility_ids.zig");

pub const CompatibilityIdResolver = struct {
    projection: ?*const CompatibilityIds.CompatibilityIdProjection,

    pub fn init(
        projection: *const CompatibilityIds.CompatibilityIdProjection,
    ) CompatibilityIdResolver {
        return .{ .projection = projection };
    }

    /// Explicit adapter for focused tests and callers that construct detached
    /// AST nodes. Production compilation always supplies a revision projection.
    pub fn legacyNodeIds() CompatibilityIdResolver {
        return .{ .projection = null };
    }

    /// Returns null only when a non-builtin node is not part of this revision.
    pub fn id(self: CompatibilityIdResolver, node: *const AST.Node) ?i64 {
        // Global-context declarations are semantic builtins with reserved
        // negative compatibility IDs, not source-local syntax nodes.
        if (node.nodeKind() == .magic_variable_declaration) return node.id;
        const projection = self.projection orelse return node.id;
        return projection.id(node.node_ref);
    }
};
