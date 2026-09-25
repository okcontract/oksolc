// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Keep construction tests reachable before every lowering producer is migrated.
test "Yul AST construction test inventory" {
    _ = @import("libyul/ast_builder.zig");
    _ = @import("libyul/ast_encoding.zig");
    _ = @import("libyul/asm_stream.zig");
    _ = @import("libyul/generated_code.zig");
    _ = @import("libyul/generated_object.zig");
    _ = @import("libsolidity/codegen/multi_use_yul_function_collector.zig");
    _ = @import("libsolidity/codegen/yul_util_functions.zig");
    _ = @import("libsolidity/codegen/abi_functions.zig");
    _ = @import("libsolidity/codegen/ir/ir_generator_for_statements.zig");
    _ = @import("libsolidity/codegen/ir/irl_value.zig");
    _ = @import("libyul/ast_template.zig");
    _ = @import("libyul/ast_template/syntax.zig");
}
