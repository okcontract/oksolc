/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Builder

namespace Compiler.Algebraic
open Contract.Yul

-- Generated from the actual Zig apply body by lean/extract_compiler.py.
-- Source SHA-256: d2c488ec16a8dcd03b89c992a1f4e0a21c998184a84d94aef65d0cd0781ee3fa
def zigApply {m : Type → Type} [Monad m] {Debug : Type}
    (replacement : Replacement) (classes : Builder m Debug)
    (left right : NodeId) (debug_data : Debug) : m NodeId :=
  (match replacement with | .left => (pure left) | .right => (pure right) | .zero => (classes.makeConstant 0 debug_data) | .one => (classes.makeConstant 1 debug_data) | .max => (classes.makeConstant (BitVec.allOnes 256) debug_data) | .not_right => (classes.makeOperation .NOT [right] debug_data) | .neg_left => ((classes.makeConstant 0 debug_data) >>= fun extracted_0 => (if (replacement == .neg_left) then (classes.makeOperation .SUB [extracted_0, left] debug_data) else (classes.makeOperation .SUB [extracted_0, right] debug_data))) | .neg_right => ((classes.makeConstant 0 debug_data) >>= fun extracted_0 => (if (replacement == .neg_left) then (classes.makeOperation .SUB [extracted_0, left] debug_data) else (classes.makeOperation .SUB [extracted_0, right] debug_data))) | .iszero_left => (if (replacement == .iszero_left) then (classes.makeOperation .ISZERO [left] debug_data) else (classes.makeOperation .ISZERO [right] debug_data)) | .iszero_right => (if (replacement == .iszero_left) then (classes.makeOperation .ISZERO [left] debug_data) else (classes.makeOperation .ISZERO [right] debug_data)) | .bool_left => (if (replacement == .bool_left) then ((classes.makeOperation .ISZERO [left] debug_data) >>= fun extracted_1 => (classes.makeOperation .ISZERO [extracted_1] debug_data)) else ((classes.makeOperation .ISZERO [right] debug_data) >>= fun extracted_2 => (classes.makeOperation .ISZERO [extracted_2] debug_data))) | .bool_right => (if (replacement == .bool_left) then ((classes.makeOperation .ISZERO [left] debug_data) >>= fun extracted_1 => (classes.makeOperation .ISZERO [extracted_1] debug_data)) else ((classes.makeOperation .ISZERO [right] debug_data) >>= fun extracted_2 => (classes.makeOperation .ISZERO [extracted_2] debug_data))))

end Compiler.Algebraic
