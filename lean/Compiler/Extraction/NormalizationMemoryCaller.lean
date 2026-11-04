/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryFrame
import Compiler.Extraction.InsertionSortNormalization

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

/-- Under the native stack contract, the actual array allocation derives scratch
permissions, private registry identity and separation required by normalization.
Empty input needs no readable or distinct native sentinel. -/
theorem caller_array_buffer (extent : Nat) (before : Session σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (source : View) (values : List NodeId)
    (valid : Valid before) (represented : Represents before.memory source values)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory (.array extent word) = .ok (pointer, memory)) :
    let selected : Session σ := { before with memory := memory }
    let buffer : View := ⟨before.memory.nextId, 0, extent⟩
    Valid selected ∧ Represents memory source values ∧
      (∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer selected) ∧
      (∀ id cell, before.memory.heap.lookup id = some cell → memory.heap.lookup id = some cell) := by
  have frame : ∀ id, id ≠ before.memory.nextId → memory.heap.lookup id = before.memory.heap.lookup id := by
    obtain ⟨_, base, _, _, rfl⟩ := Compiler.ZigAir.Memory.allocate_shape before.memory (.array extent word) pointer memory allocated
    intro id apart
    simp [Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm apart]
  have keep : ∀ id cell, before.memory.heap.lookup id = some cell → memory.heap.lookup id = some cell := by
    intro id cell found
    have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell valid.memory found).1
    exact (frame id (by omega)).trans found
  have related : Related before.heap memory := by
    intro allocator id items nonempty stored
    obtain ⟨⟨cell, found, typed, writable, stack⟩, contents⟩ := valid.related allocator id items nonempty stored
    have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell valid.memory found).1
    exact ⟨⟨cell, keep id cell found, typed, writable, stack⟩, represented_frame _ items contents (frame id (by omega))⟩
  refine ⟨⟨Compiler.ZigAir.Memory.allocate_preserves_valid before.memory _ pointer memory allocated, related, ?_⟩, ?_, ?_, keep⟩
  · intro id block stored
    obtain ⟨cell, found, _persistent⟩ := valid.injected id block stored
    exact ⟨cell, keep id cell found, _persistent⟩
  · by_cases empty : values = []
    · subst values
      exact ⟨represented.1, fun _ impossible => False.elim (by simp at impossible)⟩
    · have older := Compiler.ZigAir.Memory.WordAllocation.source_older before.memory source values valid.memory represented empty
      exact represented_frame source values represented (frame source.allocation (by omega))
  · intro _ _ large _
    have nonempty : values ≠ [] := by intro empty; rw [empty] at represented; have length := represented.1; simp at length; omega
    have older := Compiler.ZigAir.Memory.WordAllocation.source_older before.memory source values valid.memory represented nonempty
    exact ⟨writable_fresh before.memory memory extent pointer allocated, valid.injected.fresh valid.memory, by dsimp only; omega⟩

/-- The production find/forceEqual callers declare a fresh `[2]Id` scratch
buffer. Retain their public contract as this specialization of array framing. -/
theorem caller_buffer (before : Session σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (source : View) (values : List NodeId)
    (valid : Valid before) (represented : Represents before.memory source values)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory (.array 2 word) = .ok (pointer, memory)) :
    let selected : Session σ := { before with memory := memory }
    let buffer : View := ⟨before.memory.nextId, 0, 2⟩
    Valid selected ∧ Represents memory source values ∧
      (∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer selected) ∧
      (∀ id cell, before.memory.heap.lookup id = some cell → memory.heap.lookup id = some cell) :=
  caller_array_buffer 2 before memory pointer source values valid represented allocated

/-- The contents computed by memory execution refine the existing source-bound
value projection, using the same decoded item commutativity decision. -/
theorem normalized_projection (item : Item) (commutative : Bool) (source : View) (values : List NodeId)
    (length : values.length = source.length) (decoded : Interner.Scoped.commutative item = .ok commutative) :
    normalizeCode.run sortIds item values = some (normalized commutative source values) := by
  unfold Interner.Scoped.commutative at decoded
  by_cases guard : normalizeCode.guard.run item = true
  · rw [if_pos guard] at decoded
    cases instruction : item.instruction with
    | none => simp [instruction] at decoded
    | some opcode =>
      simp only [instruction, Except.ok.injEq] at decoded
      subst commutative
      by_cases enough : 2 ≤ values.length <;>
        simp [NormalizeCode.run, guard, instruction, normalized, ← length,
          show normalizeCode.threshold = 2 from rfl, show normalizationOwnershipCode.threshold = 2 from rfl,
          enough, show (values.length < 2) = (¬2 ≤ values.length) from propext (by omega)]
  · rw [if_neg guard] at decoded
    cases decoded
    simp [NormalizeCode.run, guard, normalized]

theorem transferred_word (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before after : Session σ) (slice : ArgumentSlice)
    (item : Item) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (represented : Represents before.memory source values)
    (decoded : Interner.Scoped.commutative item = .ok commutative)
    (post : Post external budget allocator commutative source buffer values exit before (.ok (.transferred slice)) after) :
    item.eval (Folding.wordMeaning other) read slice.items sequence =
      item.eval (Folding.wordMeaning other) read values sequence := by
  have contents := post.verified.2.2.2.1
  rw [contents]
  exact InsertionSort.normalize_word other item values _ read sequence
    (normalized_projection item commutative source values represented.1 decoded)

/-- Production-operation composition from the caller's actual fresh stack
buffer through normalization, transfer and cleanup. Scratch safety is derived;
successful transfer also preserves the item's word meaning. Native stack
allocation success is an explicit resource contract, not a normalization
correctness premise. All old caller storage is framed on ordinary outcomes. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (commutative : Bool) (source : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before after : Session σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value) (result : Except Failure Outcome)
    (item : Item) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before) (represented : Represents before.memory source values)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative item = .ok commutative) (admitted : Admitted external)
    (executed : run normalizationOwnershipCode external budget allocator commutative source ⟨before.memory.nextId, 0, 2⟩ values exit
      { before with memory := memory } = (result, after)) :
    Post external budget allocator commutative source ⟨before.memory.nextId, 0, 2⟩ values exit
      { before with memory := memory } result after ∧
    (result = .error (.preparation .incomplete) ∨ result = .error (.preparation (.memory .outOfMemory)) ∨
      ((∀ id cell, before.memory.heap.lookup id = some cell → after.memory.heap.lookup id = some cell) ∧
       (∀ id block, before.heap id = some block → after.heap id = some block))) ∧
    (∀ slice, result = .ok (.transferred slice) →
      item.eval (Folding.wordMeaning other) read slice.items sequence = item.eval (Folding.wordMeaning other) read values sequence) := by
  obtain ⟨selectedValid, preserved, scratch, callerFrame⟩ := caller_buffer before memory pointer source values valid represented allocated
  obtain ⟨post, framed⟩ := run_verified external budget allocator commutative source ⟨before.memory.nextId, 0, 2⟩ values exit
    { before with memory := memory } after result selectedValid preserved (scratch commutative) admitted executed
  refine ⟨post, ?_, ?_⟩
  · rcases framed with incomplete | exhausted | frame
    · exact Or.inl incomplete
    · exact Or.inr (Or.inl exhausted)
    · refine Or.inr (Or.inr ⟨?_, frame.registry⟩)
      intro id cell found
      have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell valid.memory found).1
      exact frame.memory id cell (callerFrame id cell found) (by dsimp only; omega)
  · intro slice transferred
    rw [transferred] at post
    exact transferred_word external budget allocator commutative source _ values exit _ after slice item other read sequence preserved decoded post

end Compiler.Extraction.Memory.Arguments.Normalization
