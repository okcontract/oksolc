/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerScopeControl
import Compiler.Extraction.Recursive

namespace Compiler.Extraction.ScopedRecursive
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested

/-- Uses the actual dispatcher and extracted constructor request encoding.
Each recursive call opens and closes its own scope; the private allocation
cursor and graph effects flow back into its caller. -/
def callbacks (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat) (find : Recursive.Find) : Primitives :=
  { p with simplify := fun key before =>
    Dispatch.simplify (reads before) (Recursive.constructors find) usizeBits key.instruction key.arguments () before }

def step (r : Scoped.Resources) (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat)
    (find : Recursive.Find) : Recursive.Find := Scoped.find r (callbacks p reads usizeBits find)

def unfold (r : Scoped.Resources) (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat) : Nat → Recursive.Find
  | 0 => fun _ => Interner.fail .unsupported
  | depth + 1 => step r p reads usizeBits (unfold r p reads usizeBits depth)

def detailed (r : Scoped.Resources) (p : Primitives) (reads : Heap → Reads) (usizeBits depth : Nat)
    (request : Request) (before : Heap) : Except Error NodeId × Scoped.Session :=
  match depth with
  | 0 => (.error .unsupported, ⟨{}, before⟩)
  | depth + 1 => Scoped.findDetailed r (callbacks p reads usizeBits (unfold r p reads usizeBits depth)) request before

theorem detailed_projection (r : Scoped.Resources) (p : Primitives) (reads : Heap → Reads)
    (usizeBits depth : Nat) (request : Request) (before : Heap) :
    unfold r p reads usizeBits depth request before =
      let (result, after) := detailed r p reads usizeBits depth request before
      (result, after.heap) := by cases depth <;> rfl

/-- All finite depths, arities, opcodes and callback outcomes. This is a local
ownership theorem; it does not replace semantic-preservation or native
completed-execution refinement for the expanded interpreter. -/
theorem all_scopes_closed (r : Scoped.Resources) (p : Primitives) (reads : Heap → Reads)
    (usizeBits depth : Nat) (request : Request) (before : Heap) :
    Scoped.Closed (detailed r p reads usizeBits depth request before).2.scope := by
  cases depth with
  | zero => rfl
  | succ depth => exact Scoped.find_closed r _ request before

end Compiler.Extraction.ScopedRecursive
