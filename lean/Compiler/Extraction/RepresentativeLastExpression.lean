/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayAppend

namespace Compiler.Extraction.RepresentativeArray.Last
open Compiler.ZigAir.Memory

/-- Read the reached native length before subtracting one. Empty rollback is
an invalid caller state, not saturating Nat subtraction or a successful no-op.
The shared append selector resolves the complete row in the same live backing. -/
def select (state : State) (header : Address) : Except Fault Address := do
  let value ← readItems state header
  let .slice _ _ length := value | .error .malformed
  if length = 0 then .error .sourceBounds else Append.selectNewElement state header length

theorem read_rejected (state : State) (header : Address) (fault : Fault)
    (rejected : readItems state header = .error fault) : select state header = .error fault := by
  simp only [select, rejected, bind, Except.bind]

theorem empty (state : State) (header data : Address) (type : Ty)
    (loaded : readItems state header = .ok (.slice type data 0)) :
    select state header = .error .sourceBounds := by
  simp only [select, loaded, bind, Except.bind, ↓reduceIte]

theorem from_array (state : State) (header : Address) (lifetime capacity index : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ (index + 1))) :
    select state header = .ok ⟨lifetime, index * 32⟩ := by
  have selected := Append.selectNewElement_from_array state header lifetime capacity index cell
    initial found typed writable inside loaded
  simpa only [select, loaded, bind, Except.bind, Nat.add_one_ne_zero, ↓reduceIte, Append.nextLength] using selected

end Compiler.Extraction.RepresentativeArray.Last
