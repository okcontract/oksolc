// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const Classes = @import("src/libevmasm/expression_classes.zig").ExpressionClasses;
const Map = @FieldType(Classes, "expressions");
const Key = @FieldType(Map.KV, "key");
const Context = @typeInfo(@TypeOf(Map.getOrPutContext)).@"fn".param_types[3].?;

// Keep the actual production hash body and its native initialization/call order.
// This entry supplies neither a replacement hash nor callback contracts.
export fn hash(key: *const Key) u64 {
    return (Context{}).hash(key.*);
}
