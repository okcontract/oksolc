// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural hashes for alpha-equivalent Yul blocks and disambiguated
//! expressions.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const Utilities = @import("../utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const fnv_prime: u64 = 1_099_511_628_211;
pub const fnv_empty_hash: u64 = 14_695_981_039_346_656_037;

pub const HasherBase = struct {
    hash: u64 = fnv_empty_hash,

    fn hash8(self: *HasherBase, value: u8) void {
        self.hash *%= fnv_prime;
        self.hash ^= value;
    }

    fn hash16(self: *HasherBase, value: u16) void {
        self.hash8(@truncate(value));
        self.hash8(@truncate(value >> 8));
    }

    fn hash32(self: *HasherBase, value: u32) void {
        self.hash16(@truncate(value));
        self.hash16(@truncate(value >> 16));
    }

    fn hash64(self: *HasherBase, value: u64) void {
        self.hash32(@truncate(value));
        self.hash32(@truncate(value >> 32));
    }
};

pub const ASTHasherBase = struct {
    hasher: HasherBase = .{},

    fn hashLiteral(self: *ASTHasherBase, literal: *const AST.Literal) anyerror!void {
        self.hasher.hash64(literalTagHash("Literal"));
        if (!literal.value.unlimited())
            self.hasher.hash64(hashU256(try literal.value.value()))
        else
            self.hasher.hash64(cityHash64(try literal.value.builtinStringLiteralValue()));
        self.hasher.hash8(@intFromBool(literal.value.unlimited()));
    }

    fn hashFunctionCall(self: *ASTHasherBase, call: *const AST.FunctionCall) void {
        self.hasher.hash64(literalTagHash("FunctionCall"));
        switch (call.function_name) {
            .builtin => |builtin| {
                self.hasher.hash64(literalTagHash("Builtin"));
                self.hasher.hash64(builtin.handle.id);
            },
            .identifier => |identifier| {
                self.hasher.hash64(literalTagHash("UserDefined"));
                self.hasher.hash64(identifier.name.hashValue());
            },
        }
    }
};

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

const VariableReference = struct {
    id: usize,
    is_external: bool,
};

const VariableReferenceMap = ordered.OrderedMap(
    YulName,
    VariableReference,
    lessYulName,
);

pub const BlockHashMap = std.AutoHashMap(*const AST.Block, u64);

pub const BlockHasher = struct {
    allocator: std.mem.Allocator,
    base: ASTHasherBase = .{},
    block_hashes: *BlockHashMap,
    variable_references: VariableReferenceMap = .{},
    external_references: std.ArrayList(YulName) = .empty,
    external_identifier_count: usize = 0,
    internal_identifier_count: usize = 0,

    pub fn run(allocator: std.mem.Allocator, block: *const AST.Block) anyerror!BlockHashMap {
        var result = BlockHashMap.init(allocator);
        errdefer result.deinit();
        var hasher: BlockHasher = .{ .allocator = allocator, .block_hashes = &result };
        defer hasher.deinit();
        try hasher.visitBlock(block);
        return result;
    }

    fn deinit(self: *BlockHasher) void {
        self.variable_references.deinit(self.allocator);
        self.external_references.deinit(self.allocator);
        self.* = undefined;
    }

    fn visitExpression(self: *BlockHasher, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .literal => |*literal| try self.base.hashLiteral(literal),
            .identifier => |*identifier| try self.visitIdentifier(identifier),
            .function_call => |*call| {
                self.base.hashFunctionCall(call);
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
        }
    }

    fn visitIdentifier(self: *BlockHasher, identifier: *const AST.Identifier) anyerror!void {
        self.base.hasher.hash64(literalTagHash("Identifier"));
        const reference = self.variable_references.get(identifier.name) orelse blk: {
            const value: VariableReference = .{
                .id = self.external_identifier_count,
                .is_external = true,
            };
            self.external_identifier_count += 1;
            _ = try self.variable_references.insert(self.allocator, identifier.name, value);
            try self.external_references.append(self.allocator, identifier.name);
            break :blk self.variable_references.get(identifier.name).?;
        };
        if (reference.is_external)
            self.base.hasher.hash64(literalTagHash("external"))
        else
            self.base.hasher.hash64(literalTagHash("internal"));
        self.base.hasher.hash64(reference.id);
    }

    fn visitStatement(self: *BlockHasher, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| {
                self.base.hasher.hash64(literalTagHash("ExpressionStatement"));
                try self.visitExpression(&value.expression);
            },
            .assignment => |*value| {
                self.base.hasher.hash64(literalTagHash("Assignment"));
                self.base.hasher.hash64(value.variable_names.items.len);
                for (value.variable_names.items) |*identifier| try self.visitIdentifier(identifier);
                try self.visitExpression(value.value orelse return error.InvalidAst);
            },
            .variable_declaration => |*value| {
                self.base.hasher.hash64(literalTagHash("VariableDeclaration"));
                self.base.hasher.hash64(value.variables.items.len);
                for (value.variables.items) |variable| {
                    if (self.variable_references.contains(variable.name))
                        return error.SourceNotDisambiguated;
                    _ = try self.variable_references.insert(self.allocator, variable.name, .{
                        .id = self.internal_identifier_count,
                        .is_external = false,
                    });
                    self.internal_identifier_count += 1;
                }
                if (value.value) |expression| try self.visitExpression(expression);
            },
            .if_statement => |*value| {
                self.base.hasher.hash64(literalTagHash("If"));
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                self.base.hasher.hash64(literalTagHash("Switch"));
                self.base.hasher.hash64(value.cases.items.len);
                var cases: std.ArrayList(*const AST.Case) = .empty;
                defer cases.deinit(self.allocator);
                for (value.cases.items) |*case_value| try cases.append(self.allocator, case_value);
                std.sort.heap(*const AST.Case, cases.items, {}, caseLessThan);
                try self.visitExpression(value.expression orelse return error.InvalidAst);
                for (cases.items) |case_value| {
                    if (case_value.value) |literal| try self.base.hashLiteral(literal);
                    try self.visitBlock(&case_value.body);
                }
            },
            .function_definition => |*value| {
                self.base.hasher.hash64(literalTagHash("FunctionDefinition"));
                try self.visitBlock(&value.body);
            },
            .for_loop => |*value| {
                if (value.pre.statements.items.len != 0) return error.ForLoopInitRewriterNotRun;
                self.base.hasher.hash64(literalTagHash("ForLoop"));
                try self.visitBlock(&value.pre);
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
                try self.visitBlock(&value.post);
            },
            .break_statement => self.base.hasher.hash64(literalTagHash("Break")),
            .continue_statement => self.base.hasher.hash64(literalTagHash("Continue")),
            .leave_statement => self.base.hasher.hash64(literalTagHash("Leave")),
            .block => |*value| try self.visitBlock(value),
        }
    }

    fn visitBlock(self: *BlockHasher, block: *const AST.Block) anyerror!void {
        self.base.hasher.hash64(literalTagHash("Block"));
        self.base.hasher.hash64(block.statements.items.len);
        if (block.statements.items.len == 0) return;

        var sub_hasher: BlockHasher = .{
            .allocator = self.allocator,
            .block_hashes = self.block_hashes,
        };
        defer sub_hasher.deinit();
        for (block.statements.items) |*statement| try sub_hasher.visitStatement(statement);
        try self.block_hashes.put(block, sub_hasher.base.hasher.hash);

        self.base.hasher.hash64(sub_hasher.base.hasher.hash);
        self.base.hasher.hash64(sub_hasher.external_references.items.len);
        for (sub_hasher.external_references.items) |external_reference|
            try self.visitIdentifier(&.{ .name = external_reference });
    }
};

pub const ExpressionHasher = struct {
    base: ASTHasherBase = .{},

    pub fn run(expression: *const AST.Expression) anyerror!u64 {
        var hasher: ExpressionHasher = .{};
        try hasher.visitExpression(expression);
        return hasher.base.hasher.hash;
    }

    fn visitExpression(self: *ExpressionHasher, expression: *const AST.Expression) anyerror!void {
        switch (expression.*) {
            .literal => |*literal| try self.base.hashLiteral(literal),
            .identifier => |identifier| {
                self.base.hasher.hash64(literalTagHash("Identifier"));
                self.base.hasher.hash64(identifier.name.hashValue());
            },
            .function_call => |*call| {
                self.base.hashFunctionCall(call);
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
        }
    }
};

/// A composable structural fingerprint for post-order expression walkers.
/// Unlike `ExpressionHasher`, a parent consumes the already-computed
/// fingerprints of its direct children and therefore never re-walks them.
/// Hash collisions remain guarded by syntactic equality at CSE lookup sites.
pub const ExpressionFingerprint = struct {
    base: ASTHasherBase = .{},

    pub fn initFunctionCall(call: *const AST.FunctionCall) ExpressionFingerprint {
        var result: ExpressionFingerprint = .{};
        result.base.hashFunctionCall(call);
        result.base.hasher.hash64(call.arguments.items.len);
        return result;
    }

    pub fn addChild(self: *ExpressionFingerprint, fingerprint: u64) void {
        self.base.hasher.hash64(fingerprint);
    }

    pub fn finish(self: *const ExpressionFingerprint) u64 {
        return self.base.hasher.hash;
    }

    pub fn literal(value: *const AST.Literal) anyerror!u64 {
        var result: ExpressionFingerprint = .{};
        try result.base.hashLiteral(value);
        return result.finish();
    }

    pub fn identifier(value: *const AST.Identifier) u64 {
        var result: ExpressionFingerprint = .{};
        result.base.hasher.hash64(literalTagHash("Identifier"));
        result.base.hasher.hash64(value.name.hashValue());
        return result.finish();
    }

    pub fn run(expression: *const AST.Expression) anyerror!u64 {
        return switch (expression.*) {
            .literal => |*value| literal(value),
            .identifier => |*value| identifier(value),
            .function_call => |*call| blk: {
                var result = initFunctionCall(call);
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    result.addChild(try run(&call.arguments.items[index]));
                }
                break :blk result.finish();
            },
        };
    }
};

pub const ExpressionHash = struct {
    pub fn hash(expression: *const AST.Expression) anyerror!u64 {
        return ExpressionHasher.run(expression);
    }
};

fn caseLessThan(_: void, left: *const AST.Case, right: *const AST.Case) bool {
    return Utilities.switchCaseLessThan(left, right);
}

fn literalTagHash(comptime literal: []const u8) u64 {
    var result: u64 = fnv_empty_hash;
    var index: usize = literal.len + 1;
    while (index != 0) {
        index -= 1;
        const byte: u8 = if (index == literal.len) 0 else literal[index];
        result = (@as(u64, byte) *% fnv_prime) ^ result;
    }
    return result;
}

fn hashCombine(seed: u64, value: u64) u64 {
    return seed ^ (value +% 0x9e3779b9 +% (seed << 6) +% (seed >> 2));
}

fn hashU256(value: u256) u64 {
    var limb_count: usize = 1;
    var remaining = value >> 64;
    while (remaining != 0) : (remaining >>= 64) limb_count += 1;
    var result: u64 = 0;
    for (0..limb_count) |index|
        result = hashCombine(result, @truncate(value >> @intCast(index * 64)));
    return hashCombine(result, 0);
}

const city_k0: u64 = 0xc3a5c85c97cb3127;
const city_k1: u64 = 0xb492b66fbe98f273;
const city_k2: u64 = 0x9ae16a3b2f90404f;
const city_k3: u64 = 0xc949d7c7509e6557;

fn loadU32(bytes: []const u8, offset: usize) u32 {
    return std.mem.readInt(u32, bytes[offset..][0..4], .little);
}

fn loadU64(bytes: []const u8, offset: usize) u64 {
    return std.mem.readInt(u64, bytes[offset..][0..8], .little);
}

fn rotate(value: u64, shift: u6) u64 {
    return std.math.rotr(u64, value, shift);
}

fn shiftMix(value: u64) u64 {
    return value ^ (value >> 47);
}

fn hashLen16(u: u64, v: u64) u64 {
    const multiplier: u64 = 0x9ddfea08eb382d69;
    var a = (u ^ v) *% multiplier;
    a ^= a >> 47;
    var b = (v ^ a) *% multiplier;
    b ^= b >> 47;
    b *%= multiplier;
    return b;
}

const WeakHash = struct {
    first: u64,
    second: u64,
};

fn weakHashLen32WithSeedsWords(
    w: u64,
    x: u64,
    y: u64,
    z: u64,
    initial_a: u64,
    initial_b: u64,
) WeakHash {
    var a = initial_a +% w;
    var b = rotate(initial_b +% a +% z, 21);
    const c = a;
    a +%= x;
    a +%= y;
    b +%= rotate(a, 44);
    return .{ .first = a +% z, .second = b +% c };
}

fn weakHashLen32WithSeeds(
    bytes: []const u8,
    offset: usize,
    a: u64,
    b: u64,
) WeakHash {
    return weakHashLen32WithSeedsWords(
        loadU64(bytes, offset),
        loadU64(bytes, offset + 8),
        loadU64(bytes, offset + 16),
        loadU64(bytes, offset + 24),
        a,
        b,
    );
}

fn hashLen33To64(bytes: []const u8) u64 {
    const length: u64 = bytes.len;
    var z = loadU64(bytes, 24);
    var a = loadU64(bytes, 0) +% ((length +% loadU64(bytes, bytes.len - 16)) *% city_k0);
    var b = rotate(a +% z, 52);
    var c = rotate(a, 37);
    a +%= loadU64(bytes, 8);
    c +%= rotate(a, 7);
    a +%= loadU64(bytes, 16);
    const vf = a +% z;
    const vs = b +% rotate(a, 31) +% c;
    a = loadU64(bytes, 16) +% loadU64(bytes, bytes.len - 32);
    z +%= loadU64(bytes, bytes.len - 8);
    b = rotate(a +% z, 52);
    c = rotate(a, 37);
    a +%= loadU64(bytes, bytes.len - 24);
    c +%= rotate(a, 7);
    a +%= loadU64(bytes, bytes.len - 16);
    const wf = a +% z;
    const ws = b +% rotate(a, 31) +% c;
    const r = shiftMix(((vf +% ws) *% city_k2) +% ((wf +% vs) *% city_k0));
    return shiftMix((r *% city_k0) +% vs) *% city_k2;
}

fn cityHash64(bytes: []const u8) u64 {
    const length: u64 = bytes.len;
    if (bytes.len <= 16) {
        if (bytes.len > 8) {
            const a = loadU64(bytes, 0);
            const b = loadU64(bytes, bytes.len - 8);
            return hashLen16(a, rotate(b +% length, @intCast(bytes.len))) ^ b;
        }
        if (bytes.len >= 4) {
            const a: u32 = loadU32(bytes, 0);
            const b: u64 = loadU32(bytes, bytes.len - 4);
            // Solidity's supported libc++ ABI is version 1, which preserves
            // the historical 32-bit overflow in this CityHash expression.
            return hashLen16(length +% @as(u64, a << 3), b);
        }
        if (bytes.len > 0) {
            const a: u32 = bytes[0];
            const b: u32 = bytes[bytes.len >> 1];
            const c: u32 = bytes[bytes.len - 1];
            const y = a + (b << 8);
            const z: u32 = @intCast(length +% (@as(u64, c) << 2));
            return shiftMix(@as(u64, y) *% city_k2 ^ @as(u64, z) *% city_k3) *% city_k2;
        }
        return city_k2;
    }
    if (bytes.len <= 32) {
        const a = loadU64(bytes, 0) *% city_k1;
        const b = loadU64(bytes, 8);
        const c = loadU64(bytes, bytes.len - 8) *% city_k2;
        const d = loadU64(bytes, bytes.len - 16) *% city_k0;
        return hashLen16(
            rotate(a -% b, 43) +% rotate(c, 30) +% d,
            a +% rotate(b ^ city_k3, 20) -% c +% length,
        );
    }
    if (bytes.len <= 64) return hashLen33To64(bytes);

    var x = loadU64(bytes, bytes.len - 40);
    var y = loadU64(bytes, bytes.len - 16) +% loadU64(bytes, bytes.len - 56);
    var z = hashLen16(
        loadU64(bytes, bytes.len - 48) +% length,
        loadU64(bytes, bytes.len - 24),
    );
    var v = weakHashLen32WithSeeds(bytes, bytes.len - 64, length, z);
    var w = weakHashLen32WithSeeds(bytes, bytes.len - 32, y +% city_k1, x);
    x = (x *% city_k1) +% loadU64(bytes, 0);

    var offset: usize = 0;
    var remaining = (bytes.len - 1) & ~@as(usize, 63);
    while (true) {
        x = rotate(
            x +% y +% v.first +% loadU64(bytes, offset + 8),
            37,
        ) *% city_k1;
        y = rotate(
            y +% v.second +% loadU64(bytes, offset + 48),
            42,
        ) *% city_k1;
        x ^= w.second;
        y +%= v.first +% loadU64(bytes, offset + 40);
        z = rotate(z +% w.first, 33) *% city_k1;
        v = weakHashLen32WithSeeds(
            bytes,
            offset,
            v.second *% city_k1,
            x +% w.first,
        );
        w = weakHashLen32WithSeeds(
            bytes,
            offset + 32,
            z +% w.second,
            y +% loadU64(bytes, offset + 16),
        );
        const old_z = z;
        z = x;
        x = old_z;
        offset += 64;
        remaining -= 64;
        if (remaining == 0) break;
    }
    return hashLen16(
        hashLen16(v.first, w.first) +% (shiftMix(y) *% city_k1) +% z,
        hashLen16(v.second, w.second) +% x,
    );
}

test "expression hashes distinguish names and block hashes ignore local spelling" {
    const allocator = std.testing.allocator;
    const x = try YulName.init("hash_x");
    const y = try YulName.init("hash_y");
    const left: AST.Expression = .{ .identifier = .{ .name = x } };
    const right: AST.Expression = .{ .identifier = .{ .name = y } };
    try std.testing.expect((try ExpressionHasher.run(&left)) != (try ExpressionHasher.run(&right)));
    try std.testing.expect((try ExpressionFingerprint.run(&left)) !=
        (try ExpressionFingerprint.run(&right)));

    var first: AST.Block = .{};
    defer first.deinit(allocator);
    var first_decl: AST.VariableDeclaration = .{};
    try first_decl.variables.append(allocator, .{ .name = x });
    try first.statements.append(allocator, .{ .variable_declaration = first_decl });
    var second: AST.Block = .{};
    defer second.deinit(allocator);
    var second_decl: AST.VariableDeclaration = .{};
    try second_decl.variables.append(allocator, .{ .name = y });
    try second.statements.append(allocator, .{ .variable_declaration = second_decl });
    var first_hashes = try BlockHasher.run(allocator, &first);
    defer first_hashes.deinit();
    var second_hashes = try BlockHasher.run(allocator, &second);
    defer second_hashes.deinit();
    try std.testing.expectEqual(first_hashes.get(&first).?, second_hashes.get(&second).?);
}

const implementation = @This();

pub const fnvEmptyHash = implementation.fnv_empty_hash;

pub const fnvPrime = implementation.fnv_prime;
