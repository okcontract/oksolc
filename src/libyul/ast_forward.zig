// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Forward-declaration surface maps directly to Zig's declaration-order-independent AST types.

const AST = @import("ast.zig");

pub const YulString = @import("yul_string.zig").YulString;
pub const YulName = @import("yul_name.zig").YulName;
pub const LiteralKind = AST.LiteralKind;
pub const LiteralValue = AST.LiteralValue;
pub const Literal = AST.Literal;
pub const Identifier = AST.Identifier;
pub const Assignment = AST.Assignment;
pub const VariableDeclaration = AST.VariableDeclaration;
pub const FunctionDefinition = AST.FunctionDefinition;
pub const FunctionCall = AST.FunctionCall;
pub const If = AST.If;
pub const Switch = AST.Switch;
pub const Case = AST.Case;
pub const ForLoop = AST.ForLoop;
pub const Break = AST.Break;
pub const Continue = AST.Continue;
pub const Leave = AST.Leave;
pub const ExpressionStatement = AST.ExpressionStatement;
pub const Block = AST.Block;
pub const BuiltinName = AST.BuiltinName;
pub const BuiltinHandle = @import("builtins.zig").BuiltinHandle;
pub const Expression = AST.Expression;
pub const FunctionName = AST.FunctionName;
pub const FunctionHandle = AST.FunctionHandle;
pub const Statement = AST.Statement;
pub const NameWithDebugData = AST.NameWithDebugData;
