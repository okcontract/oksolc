// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Stable domain identities used by incremental compiler state.

const std = @import("std");
const KeyHasher = @import("key_hasher.zig").KeyHasher;
const H256 = @import("key_hasher.zig").H256;

pub const SourceId = enum(u32) {
    _,

    pub fn init(raw_index: u32) SourceId {
        return @enumFromInt(raw_index);
    }

    pub fn index(self: SourceId) u32 {
        return @intFromEnum(self);
    }
};

pub const ContractId = enum(u32) {
    _,

    pub fn init(raw_index: u32) ContractId {
        return @enumFromInt(raw_index);
    }

    pub fn index(self: ContractId) u32 {
        return @intFromEnum(self);
    }
};

/// Dense zero-based identity within one immutable source tree. A local node
/// ID is meaningful only together with its stable logical `SourceId`.
pub const LocalNodeId = enum(u32) {
    _,

    pub fn init(raw_index: u32) LocalNodeId {
        return @enumFromInt(raw_index);
    }

    pub fn index(self: LocalNodeId) u32 {
        return @intFromEnum(self);
    }
};

/// Stable source-local syntax identity, separate from
/// the compilation-wide AST ID exposed by Standard JSON output.
pub const NodeRef = struct {
    source: SourceId,
    local_node: LocalNodeId,

    pub fn eql(left: NodeRef, right: NodeRef) bool {
        return left.source == right.source and left.local_node == right.local_node;
    }

    pub fn lessThan(_: void, left: NodeRef, right: NodeRef) bool {
        if (left.source != right.source)
            return left.source.index() < right.source.index();
        return left.local_node.index() < right.local_node.index();
    }
};

fn DigestKey(comptime key_domain: []const u8) type {
    return struct {
        const Self = @This();

        digest: H256,

        pub fn fromDigest(value: H256) Self {
            return .{ .digest = value };
        }

        pub fn fromBytes(value: [H256.size]u8) Self {
            return fromDigest(H256.fromArray(value));
        }

        pub fn bytes(self: *const Self) []const u8 {
            return self.digest.bytes();
        }

        pub fn eql(self: *const Self, other: *const Self) bool {
            return self.digest.eql(&other.digest);
        }

        pub fn lessThan(self: *const Self, other: *const Self) bool {
            return self.digest.lessThan(&other.digest);
        }

        pub const domain = key_domain;
    };
}

/// Stable cross-process identity of a canonical logical source name. Source
/// content is excluded so the identity survives body edits.
pub const SourceKey = struct {
    const Storage = DigestKey("source");
    const schema_version: u32 = 1;

    storage: Storage,

    pub fn init(canonical_name: []const u8) SourceKey {
        var hasher = KeyHasher.init("solidity.source", schema_version);
        hasher.addBytes(1, canonical_name);
        return fromDigest(hasher.finish());
    }

    pub fn fromDigest(value: H256) SourceKey {
        return .{ .storage = Storage.fromDigest(value) };
    }

    pub fn fromBytes(value: [H256.size]u8) SourceKey {
        return fromDigest(H256.fromArray(value));
    }

    pub fn digest(self: *const SourceKey) H256 {
        return self.storage.digest;
    }

    pub fn bytes(self: *const SourceKey) []const u8 {
        return self.storage.bytes();
    }

    pub fn eql(self: *const SourceKey, other: *const SourceKey) bool {
        return self.storage.eql(&other.storage);
    }

    pub fn lessThan(self: *const SourceKey, other: *const SourceKey) bool {
        return self.storage.lessThan(&other.storage);
    }
};

/// Stable cross-process identity of a contract declaration. The source key
/// represents the logical source name, not a particular source revision.
pub const ContractKey = struct {
    const Storage = DigestKey("contract");
    const schema_version: u32 = 1;

    storage: Storage,

    pub fn init(source: SourceKey, contract_name: []const u8) ContractKey {
        var hasher = KeyHasher.init("solidity.contract", schema_version);
        const source_digest = source.digest();
        hasher.addDigest(1, &source_digest);
        hasher.addBytes(2, contract_name);
        return fromDigest(hasher.finish());
    }

    pub fn fromDigest(value: H256) ContractKey {
        return .{ .storage = Storage.fromDigest(value) };
    }

    pub fn fromBytes(value: [H256.size]u8) ContractKey {
        return fromDigest(H256.fromArray(value));
    }

    pub fn digest(self: *const ContractKey) H256 {
        return self.storage.digest;
    }

    pub fn bytes(self: *const ContractKey) []const u8 {
        return self.storage.bytes();
    }

    pub fn eql(self: *const ContractKey, other: *const ContractKey) bool {
        return self.storage.eql(&other.storage);
    }

    pub fn lessThan(self: *const ContractKey, other: *const ContractKey) bool {
        return self.storage.lessThan(&other.storage);
    }
};

test "dense IDs and node references remain distinct domain types" {
    const source = SourceId.init(7);
    const contract = ContractId.init(7);
    try std.testing.expectEqual(@as(u32, 7), source.index());
    try std.testing.expectEqual(@as(u32, 7), contract.index());

    const local = LocalNodeId.init(1);
    const first: NodeRef = .{ .source = source, .local_node = local };
    const second: NodeRef = .{ .source = SourceId.init(8), .local_node = local };
    try std.testing.expect(!first.eql(second));
    try std.testing.expect(NodeRef.lessThan({}, first, second));
}

test "source and contract keys are stable logical identities" {
    const source = SourceKey.init("contracts/A.sol");
    const same_source = SourceKey.init("contracts/A.sol");
    const renamed_source = SourceKey.init("contracts/B.sol");
    try std.testing.expect(source.eql(&same_source));
    try std.testing.expect(!source.eql(&renamed_source));

    const contract = ContractKey.init(source, "A");
    const same_contract = ContractKey.init(same_source, "A");
    const renamed_contract = ContractKey.init(source, "B");
    try std.testing.expect(contract.eql(&same_contract));
    try std.testing.expect(!contract.eql(&renamed_contract));

    var encoded: [H256.size]u8 = undefined;
    @memcpy(&encoded, contract.bytes());
    const restored = ContractKey.fromBytes(encoded);
    try std.testing.expect(contract.eql(&restored));
}
