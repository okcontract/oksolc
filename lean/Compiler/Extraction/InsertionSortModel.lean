/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.Builder
import Init.Data.List.Nat.Perm

/-! Value-level interpretation of the insertion sort used by normalization.
Indexed exchange represents std.mem.swap on distinct valid elements; native
byte storage and borrow refinement are separate obligations. The generated
control retains incomplete and invalid-index outcomes and their prefix state. -/
namespace Compiler.Extraction.InsertionSort
open Compiler.Algebraic

inductive Fault where
  | bounds | incomplete | indexWidth
  deriving DecidableEq, Repr

inductive Result where
  | ok (items : List NodeId)
  | fault (reason : Fault) (items : List NodeId)
  deriving DecidableEq, Repr

/-- Shared source control is independent of its storage interpretation. Reads
are pure; exchanges retain their exact state on either success or failure. -/
structure Operations (σ ε : Type) where
  read : σ → Nat → Except ε NodeId
  exchange : σ → Nat → Nat → Except ε Unit × σ
  exhausted : ε

def Result.fromOutcome : Except Fault Unit × List NodeId → Result
  | (.ok (), after) => .ok after
  | (.error reason, after) => .fault reason after

def listOperations : Operations (List NodeId) Fault where
  read items index := match items[index]? with
    | none => .error .bounds
    | some value => .ok value
  exchange items left right := match items[left]?, items[right]? with
    | some current, some previous => (.ok (), (items.set left previous).set right current)
    | _, _ => (.error .bounds, items)
  exhausted := .incomplete

end Compiler.Extraction.InsertionSort
