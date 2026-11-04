/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Interner
import Compiler.Extraction.NestedProofs

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Nested

/-- Value and structure are kept together; equal word values alone do not
identify a representative's kind, opcode, argument slice or observation epoch. -/
def observedHeap (cells : List Storage.Cell) (table : Table) : Heap :=
  ⟨Storage.readValue cells, table, some cells, 0⟩

/-- Existing value-only clients retain exactly their earlier cache invariant. -/
theorem abstract_invariant_iff (meaning : Meaning) (read : Read) (table : Table) :
    Invariant meaning ⟨read, table, none, 0⟩ ↔ Valid meaning read table :=
  ⟨fun valid => valid.cache, fun cache => ⟨cache, trivial⟩⟩

theorem observed_invariant (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cache : Valid meaning (Storage.readValue cells) table) (coherent : Storage.Coherent meaning cells) :
    Invariant meaning (observedHeap cells table) := ⟨cache, rfl, coherent⟩

theorem invariant_observations (meaning : Meaning) (heap : Heap) (valid : Invariant meaning heap)
    (cells : List Storage.Cell) (present : heap.representatives = some cells) :
    heap.read = Storage.readValue cells ∧ Storage.Coherent meaning cells := by
  simpa only [Represented, present] using valid.representation

/-- Concrete reads use the source-bound storage accessors. Requesting such a
read on a value-only heap is an explicit model safety fault, never a normal miss.
The old abstract interface can still supply its own separately justified oracle. -/
def representativeReads (heap : Heap) : Reads :=
  match heap.representatives with
  | some cells => storageReads cells
  | none => { constant := fun _ => .error .safetyFault, operation := fun _ _ => .error .safetyFault }

theorem representative_reads_sound (meaning : Meaning) (heap : Heap) (valid : Invariant meaning heap) :
    Sound meaning heap.read (representativeReads heap) := by
  cases present : heap.representatives with
  | none =>
    constructor
    · intro id value found; simp [representativeReads, present] at found
    · intro id opcode slice found; simp [representativeReads, present] at found
    · intro left right a b equal lhs rhs
      simp only [sameExpression, representativeReads, present, beq_iff_eq] at equal
      subst right
      exact Option.some.inj (lhs.symm.trans rhs)
  | some cells =>
    obtain ⟨read, coherent⟩ := invariant_observations meaning heap valid cells present
    simpa only [representativeReads, present, read] using storage_reads_sound meaning cells coherent

theorem publication_preserves_observations (succeeds : Bool) (key : Key) (id : NodeId) (heap : Heap) :
    (publish succeeds key id heap).2.representatives = heap.representatives := by cases succeeds <;> rfl

end Compiler.Extraction.Interner
