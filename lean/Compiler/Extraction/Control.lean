/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Algebraic.Model

namespace Compiler.Algebraic

/-- Ordered finite iteration with function-level early return. Compile-time
unrolling has the same observation for this pure, terminating Zig subset. -/
def firstReturn (items : List α) (body : α → Option β) (next : Option β) : Option β :=
  match items with
  | [] => next
  | item :: rest =>
    match body item with
    | some result => some result
    | none => firstReturn rest body next

end Compiler.Algebraic
