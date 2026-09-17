// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");
const Address = @import("address.zig");
const Keccak = @import("../libsolutil/keccak256.zig");

// Independently calculated with cast 1.7.1-Homebrew, commit
// 4072e48705af9d93e3c0f6e29e93b5e9a40caed8. Every request supplies its nonce
// or salt/initcode explicitly; reference generation does not query a chain.
test "CREATE matches reference addresses at every nonce encoding boundary" {
    const Case = struct { creator: u160, nonce: u64, expected: u160 };
    const cases = [_]Case{
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x0, .expected = 0xbd770416a3345f91e4b34576cb804a576fa48eb1 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x1, .expected = 0x5a443704dd4b594b382c22a083e2bd3090a6fef3 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x2, .expected = 0x47e9fbef8c83a1714f1951f142132e6e90f5fa5d },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x7e, .expected = 0xec176e41e1d0d2c68ae175133e2db6ecd37b31ec },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x7f, .expected = 0x5a1bfc20f2037f3e54d367a70957a5327130cea5 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x80, .expected = 0xc1784bd8a0ffebd60d0bc7099dcd811b57f30bc4 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x81, .expected = 0x2823552581b0be905c3d9ba0eb7902a92ccfcf6b },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xff, .expected = 0x2e021f429ff10bfc9373f73720a14bee2cfd5fdd },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x100, .expected = 0x1183a5a83c1fa113618603abc4509077ec672699 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x101, .expected = 0x38a94106bef07ee9de282cb431f3be8783bb1dec },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xffff, .expected = 0xae80be2f887b0efb148934160afd38459969571a },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x10000, .expected = 0x3c61d75af3a48777914e865f50a38540a11c41c0 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x10001, .expected = 0xdf07d6ad1a67d0fb014429ba87e3033ad8485cea },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xffffff, .expected = 0xbbaeb4cb1f1468d2820259d137e7f2a80c751f33 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x1000000, .expected = 0xb5987b13b2788f3bd5703fd8873557ccada84bb8 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x1000001, .expected = 0x2b92fa8bb4e73dd1d459b793f13d96f6e8361f1b },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xffffffff, .expected = 0x83317d2df02af8fe91040765f49719e8115c0f04 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x100000000, .expected = 0x736fd6c74b4cf6cc32253372850bd559067ac5f7 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x100000001, .expected = 0x6f7372534025d713924e62cbaeeb61413f35ea51 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xffffffffff, .expected = 0xb07df933f16bfa5a78a4e62826e18cc8acefddb5 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x10000000000, .expected = 0xcc8d3e72cf698064b521d663088943001a02316f },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x10000000001, .expected = 0x9879a37c1f6b206f82d5e4e63f6555ba3f9a8fa8 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xffffffffffff, .expected = 0x154238be5817b2576267644878b50d61f4d240d5 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x1000000000000, .expected = 0x0ea0057ebcbf62c4021299d808472714b6a0f340 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x1000000000001, .expected = 0xe7b894aa63ea62008818c482fc1c3b6b47a02957 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xffffffffffffff, .expected = 0x06ef26aa0739f263e6026ec283df7ee579dd05f6 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x100000000000000, .expected = 0xe72a12bd4ead3c02e618af2cc3379bcddbb56177 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x100000000000001, .expected = 0xd364aa5f26b0616c91fe8f44b77c26047d48befe },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0x123456789abcdef, .expected = 0xbbec53ee74dac93348a610bc652ed766319d6f88 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xfffffffffffffffe, .expected = 0x9e62200d49f674521a8da24ebe4d69e597ce84b6 },
        .{ .creator = 0x0000000000000000000000000000000000000000, .nonce = 0xffffffffffffffff, .expected = 0x1262d73ea59d3a661bf8751d16cf1a5377149e75 },
        .{ .creator = 0xffffffffffffffffffffffffffffffffffffffff, .nonce = 0x0, .expected = 0xb318d82866cd9f7d7a55dbbf0a80f787b72bf97c },
        .{ .creator = 0xffffffffffffffffffffffffffffffffffffffff, .nonce = 0x1, .expected = 0xa34794dff7e5d2b06f5b98f3b27aae9b919f3469 },
        .{ .creator = 0xffffffffffffffffffffffffffffffffffffffff, .nonce = 0x80, .expected = 0x58007b400428a2ce8343b2d5b69ca4d609bb14f2 },
        .{ .creator = 0xffffffffffffffffffffffffffffffffffffffff, .nonce = 0xffffffffffffffff, .expected = 0x529974ed318bc56f864d2dace65768219b3e7259 },
        .{ .creator = 0xb20a608c624ca5003905aa834de7156c68b2e1d0, .nonce = 0x0, .expected = 0x00000000219ab540356cbb839cbe05303d7705fa },
        .{ .creator = 0xb20a608c624ca5003905aa834de7156c68b2e1d0, .nonce = 0x1, .expected = 0xe33c6e89e69d085897f98e92b06ebd541d1daa99 },
        .{ .creator = 0xb20a608c624ca5003905aa834de7156c68b2e1d0, .nonce = 0x80, .expected = 0x40ef63d70dd790be41533fc53a85d043a5abe6f5 },
        .{ .creator = 0xb20a608c624ca5003905aa834de7156c68b2e1d0, .nonce = 0xffffffffffffffff, .expected = 0x9e628174dd6482b6ae1506d170c1e691cd285a95 },
        .{ .creator = 0x1804c8ab1f12e6bbf3894d4083f33e07309d1f38, .nonce = 0x0, .expected = 0x5b73c5498c1e3b4dba84de0f1833c4a029d90519 },
        .{ .creator = 0x1804c8ab1f12e6bbf3894d4083f33e07309d1f38, .nonce = 0x1, .expected = 0x7fa9385be102ac3eac297483dd6233d62b3e1496 },
        .{ .creator = 0x1804c8ab1f12e6bbf3894d4083f33e07309d1f38, .nonce = 0x80, .expected = 0x1470a0d52c89da1875038ad7e96e2e1675a6d243 },
        .{ .creator = 0x1804c8ab1f12e6bbf3894d4083f33e07309d1f38, .nonce = 0xffffffffffffffff, .expected = 0x8983f961505bbf8a3c341c4b130c238b0be9d943 },
    };
    for (cases) |case| try std.testing.expectEqual(case.expected, Address.create(case.creator, case.nonce));
}

const Create2Case = struct { creator: u160, salt: u256, init_code: []const u8, expected: u160 };

fn expectCreate2(cases: []const Create2Case) !void {
    for (cases) |case| try std.testing.expectEqual(
        case.expected,
        Address.create2(case.creator, case.salt, Keccak.keccak256(case.init_code)),
    );
}

// All seven published examples, also cross-checked against the cast pin above.
// https://eips.ethereum.org/EIPS/eip-1014#examples
test "CREATE2 matches all EIP-1014 examples" {
    try expectCreate2(&.{
        .{ .creator = 0x0, .salt = 0x0, .init_code = "\x00", .expected = 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38 },
        .{ .creator = 0xdeadbeef00000000000000000000000000000000, .salt = 0x0, .init_code = "\x00", .expected = 0xb928f69bb1d91cd65274e3c79d8986362984fda3 },
        .{ .creator = 0xdeadbeef00000000000000000000000000000000, .salt = 0xfeed000000000000000000000000000000000000, .init_code = "\x00", .expected = 0xd04116cdd17bebe565eb2422f2497e06cc1c9833 },
        .{ .creator = 0x0, .salt = 0x0, .init_code = "\xde\xad\xbe\xef", .expected = 0x70f2b2914a2a4b783faefb75f459a580616fcb5e },
        .{ .creator = 0xdeadbeef, .salt = 0xcafebabe, .init_code = "\xde\xad\xbe\xef", .expected = 0x60f3f640a8508fc6a86d45df051962668e1e8ac7 },
        .{ .creator = 0xdeadbeef, .salt = 0xcafebabe, .init_code = "\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef\xde\xad\xbe\xef", .expected = 0x1d8bfdc5d46dc4f61d6b6115972536ebe6a8854c },
        .{ .creator = 0x0, .salt = 0x0, .init_code = "", .expected = 0xe33c0c7f7df4809055c3eba6c09cfe4baf1bd9e0 },
    });
}

test "CREATE2 preserves full salt and address widths and constructor input hashes" {
    try expectCreate2(&.{
        .{ .creator = 0xffffffffffffffffffffffffffffffffffffffff, .salt = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, .init_code = "\x00", .expected = 0xaed1470f2992c0bcedd0b9898e12ee3df61437f8 },
        .{ .creator = 0x1, .salt = 0x8000000000000000000000000000000000000000000000000000000000000000, .init_code = "\x00", .expected = 0xac483ee0a21a6bb4c3e175c097c64815991e7df3 },
        .{ .creator = 0x1, .salt = 0x1, .init_code = "\x00", .expected = 0x67af9469677968ffb8be1b7912173c746da9f5df },
        .{ .creator = 0x1, .salt = 0x1, .init_code = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01", .expected = 0xc15314a812dc90d153b70960a25dcef419dcdbad },
        .{ .creator = 0x1, .salt = 0x1, .init_code = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02", .expected = 0x6e1530db6fdbcc9fdba6d1225cae3f4c7bd418f9 },
    });
}
