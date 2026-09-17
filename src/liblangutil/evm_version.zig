// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! EVM revision ordering and opcode feature gates.

const std = @import("std");

pub const Version = enum(c_int) {
    Homestead,
    TangerineWhistle,
    SpuriousDragon,
    Byzantium,
    Constantinople,
    Petersburg,
    Istanbul,
    Berlin,
    London,
    Paris,
    Shanghai,
    Cancun,
    Prague,
    Osaka,
    Amsterdam,
    Future,
};

pub const current_version = Version.Osaka;

pub const EVMVersion = struct {
    version: Version = current_version,

    pub fn current() EVMVersion {
        return .{};
    }

    pub fn init(version: Version) EVMVersion {
        return .{ .version = version };
    }

    pub fn allVersions() [16]EVMVersion {
        var result: [16]EVMVersion = undefined;
        inline for (std.meta.fields(Version)[0..16], 0..) |field, index| {
            result[index] = .{ .version = @enumFromInt(field.value) };
        }
        return result;
    }

    pub fn fromString(input: []const u8) ?EVMVersion {
        for (allVersions()) |version| if (std.mem.eql(u8, input, version.name())) return version;
        return null;
    }

    pub fn name(self: EVMVersion) []const u8 {
        return switch (self.version) {
            .Homestead => "homestead",
            .TangerineWhistle => "tangerineWhistle",
            .SpuriousDragon => "spuriousDragon",
            .Byzantium => "byzantium",
            .Constantinople => "constantinople",
            .Petersburg => "petersburg",
            .Istanbul => "istanbul",
            .Berlin => "berlin",
            .London => "london",
            .Paris => "paris",
            .Shanghai => "shanghai",
            .Cancun => "cancun",
            .Prague => "prague",
            .Osaka => "osaka",
            .Amsterdam => "amsterdam",
            .Future => "@future",
        };
    }

    pub fn isExperimental(self: EVMVersion) bool {
        return self.after(.{ .version = current_version });
    }

    pub fn eql(self: EVMVersion, other: EVMVersion) bool {
        return self.version == other.version;
    }

    pub fn before(self: EVMVersion, other: EVMVersion) bool {
        return @intFromEnum(self.version) < @intFromEnum(other.version);
    }

    pub fn atLeast(self: EVMVersion, version: Version) bool {
        return @intFromEnum(self.version) >= @intFromEnum(version);
    }

    pub fn after(self: EVMVersion, other: EVMVersion) bool {
        return @intFromEnum(self.version) > @intFromEnum(other.version);
    }

    pub fn supportsReturndata(self: EVMVersion) bool {
        return self.atLeast(.Byzantium);
    }
    pub fn hasStaticCall(self: EVMVersion) bool {
        return self.atLeast(.Byzantium);
    }
    pub fn hasBitwiseShifting(self: EVMVersion) bool {
        return self.atLeast(.Constantinople);
    }
    pub fn hasCLZ(self: EVMVersion) bool {
        return self.atLeast(.Osaka);
    }
    pub fn hasCreate2(self: EVMVersion) bool {
        return self.atLeast(.Constantinople);
    }
    pub fn hasExtCodeHash(self: EVMVersion) bool {
        return self.atLeast(.Constantinople);
    }
    pub fn hasChainID(self: EVMVersion) bool {
        return self.atLeast(.Istanbul);
    }
    pub fn hasSelfBalance(self: EVMVersion) bool {
        return self.atLeast(.Istanbul);
    }
    pub fn hasBaseFee(self: EVMVersion) bool {
        return self.atLeast(.London);
    }
    pub fn hasBlobBaseFee(self: EVMVersion) bool {
        return self.atLeast(.Cancun);
    }
    pub fn hasPrevRandao(self: EVMVersion) bool {
        return self.atLeast(.Paris);
    }
    pub fn hasPush0(self: EVMVersion) bool {
        return self.atLeast(.Shanghai);
    }
    pub fn hasBlobHash(self: EVMVersion) bool {
        return self.atLeast(.Cancun);
    }
    pub fn hasMcopy(self: EVMVersion) bool {
        return self.atLeast(.Cancun);
    }
    pub fn supportsTransientStorage(self: EVMVersion) bool {
        return self.atLeast(.Cancun);
    }
    pub fn reachableStackDepth(_: EVMVersion) usize {
        return 16;
    }
    pub fn canOverchargeGasForCall(self: EVMVersion) bool {
        return self.atLeast(.TangerineWhistle);
    }

    /// Accepts the byte representation of `evmasm::Instruction`, avoiding a
    /// dependency cycle until the instruction module is translated.
    pub fn hasOpcode(self: EVMVersion, opcode: u8) bool {
        return switch (opcode) {
            0x3d, 0x3e => self.supportsReturndata(),
            0xfa => self.hasStaticCall(),
            0x1b, 0x1c, 0x1d => self.hasBitwiseShifting(),
            0x1e => self.hasCLZ(),
            0xf5 => self.hasCreate2(),
            0x3f => self.hasExtCodeHash(),
            0x46 => self.hasChainID(),
            0x47 => self.hasSelfBalance(),
            0x48 => self.hasBaseFee(),
            0x49 => self.hasBlobHash(),
            0x4a => self.hasBlobBaseFee(),
            0x5e => self.hasMcopy(),
            0x5c, 0x5d => self.supportsTransientStorage(),
            else => true,
        };
    }
};

test "EVM revisions retain ordering, names, and opcode gates" {
    const constantinople = EVMVersion.init(.Constantinople);
    try std.testing.expect(constantinople.hasOpcode(0x1b));
    try std.testing.expect(!EVMVersion.init(.Byzantium).hasOpcode(0x1b));
    try std.testing.expect(EVMVersion.current().eql(EVMVersion.init(.Osaka)));
    try std.testing.expect(EVMVersion.init(.Amsterdam).isExperimental());
    try std.testing.expectEqualStrings("tangerineWhistle", EVMVersion.init(.TangerineWhistle).name());
}
