// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const W = @import("std").hash.Wyhash;

// Capture the unchanged standard-library bodies through their public entries.
// These wrappers supply no model implementation or successful-execution premise.
export fn initialize(result: *W, seed: u64) void {
    result.* = W.init(seed);
}

export fn update(self: *W, bytes: [*]const u8, length: usize) void {
    self.update(bytes[0..length]);
}

export fn finish(self: *W) u64 {
    return self.final();
}
