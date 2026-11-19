/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Interner

namespace Compiler.Extraction.Interner.Fixtures
open Compiler.Algebraic Compiler.Extraction.Cache

def empty : Heap := ⟨fun id => if id == 0 then some 10 else none, fun _ => none, none, 0⟩
def cached : Heap := { empty with table := fun _ => some 3 }
def request : Request := ⟨⟨1, some 1, 0⟩, [0, 0], 0⟩
def key : Key := ⟨1, 1, 0, [0, 0], 0⟩
def grown (heap : Heap) : Heap := { heap with read := fun id => if id == 0 then heap.read id else some 42 }

/-- Deliberately observable callback behavior, for source-mutation and error-order
controls. These fixtures are traces, not assumptions used by the soundness proof. -/
def primitives : Primitives where
  atCapacity := fun _ => false
  normalize := fun request => Local.fromExcept (.ok request.arguments)
  deterministic := fun _ => .ok true
  takeOwned := fun _ => Local.fromExcept (.ok ())
  simplify := fun _ heap => (.ok (some 7), grown heap)
  insert := fun _ _ => pure 9
  publish := publish true

end Compiler.Extraction.Interner.Fixtures
