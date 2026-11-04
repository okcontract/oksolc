/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryAllocation
import Compiler.Extraction.ArgumentMemoryPreparation
import Compiler.ZigAir.MemoryWordAllocationProofs

namespace Compiler.Extraction.Memory.Arguments.Allocation
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray
open Compiler.ZigAir.Memory

theorem extend_owned (state : Compiler.ZigAir.Memory.State) (length base : Nat) :
    Owned (WordAllocation.extend state length base) state.nextId length :=
  ⟨WordAllocation.cell length base, by simp [WordAllocation.extend_lookup], rfl, rfl, rfl⟩

theorem extend_others (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator base : Nat)
    (items : List NodeId) (valid : state.valid = true) (related : Related heap state) :
    Related (write (write heap state.nextId (some ⟨allocator, .arguments items⟩)) state.nextId none)
      (WordAllocation.extend state items.length base) := by
  intro owner id values nonempty stored
  by_cases selected : id = state.nextId
  · simp [write, selected] at stored
  · have old : heap id = some ⟨owner, .arguments values⟩ := by simpa [write, selected] using stored
    obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ := related owner id values nonempty old
    refine ⟨⟨cell, ?_, typed, writable, stack⟩, WordAllocation.source_preserved state items.length base _ values valid represented⟩
    simp only [WordAllocation.extend_lookup, if_neg (Ne.symm selected), found]

theorem reserve_empty (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (request : WordAllocation.Allocator σ) (effects : σ) :
    reserve heap state allocator [] request effects = ((.ok (some ⟨state.nextId, []⟩), heap, state), effects) := rfl

/-- Registration never hides a reached typed state, including a rejected
registry response after external allocation. -/
theorem reserve_reached (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (items : List NodeId) (request : WordAllocation.Allocator σ) (effects : σ) :
    (reserve heap state allocator items request effects).1.2.2 =
      (WordAllocation.reserve state items.length request effects).1.2 ∧
    (reserve heap state allocator items request effects).2 =
      (WordAllocation.reserve state items.length request effects).2 := by
  unfold reserve
  cases WordAllocation.reserve state items.length request effects with
  | mk outcome reached =>
    rcases outcome with ⟨result, after⟩
    cases result with
    | error fault => exact ⟨rfl, rfl⟩
    | ok selected =>
      cases selected with
      | none => exact ⟨rfl, rfl⟩
      | some target =>
        dsimp only
        split
        · exact ⟨rfl, rfl⟩
        · cases Memory.allocate heap allocator target.allocation (.arguments items) true <;> exact ⟨rfl, rfl⟩

theorem reserve_preserves_valid (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (items : List NodeId) (request : WordAllocation.Allocator σ) (effects : σ) (valid : state.valid = true) :
    (reserve heap state allocator items request effects).1.2.2.valid = true := by
  rw [(reserve_reached heap state allocator items request effects).1]
  exact WordAllocation.reserve_preserves_valid state items.length request effects valid

theorem reserve_failed (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ)
    (valid : state.valid = true) (nonempty : items ≠ []) (source : View) (represented : Represents state source items)
    (response : request (items.length * 4) effects = (none, reached)) :
    reserve heap state allocator items request effects = ((.ok none, heap, state), reached) := by
  unfold reserve
  rw [WordAllocation.reserve_failed state items.length request effects reached valid (by simpa using nonempty)
    (WordAllocation.source_bytes_bound state source items represented) response]

theorem reserve_admitted (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator base : Nat)
    (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ)
    (valid : state.valid = true) (nonempty : items ≠ []) (source : View) (represented : Represents state source items)
    (fresh : heap state.nextId = none) (response : request (items.length * 4) effects = (some base, reached))
    (fits : WordAllocation.Fits state items.length base) :
    reserve heap state allocator items request effects =
      ((.ok (some ⟨state.nextId, items⟩), write heap state.nextId (some ⟨allocator, .arguments items⟩),
        WordAllocation.extend state items.length base), reached) := by
  unfold reserve
  rw [WordAllocation.reserve_admitted state items.length base request effects reached valid (by simpa using nonempty)
    (WordAllocation.source_bytes_bound state source items represented) response fits]
  simp [List.isEmpty_eq_false_iff.mpr nonempty, Memory.allocate, fresh]

/-- Invert every observed nonempty success, including the exact reached
private state. No correspondence for item/representative registry blocks is
assumed: collision checks still apply to them. -/
theorem reserve_success (heap registered : Heap) (state after : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ) (destination : ArgumentSlice)
    (nonempty : items ≠ [])
    (done : reserve heap state allocator items request effects = ((.ok (some destination), registered, after), reached)) :
    ∃ base, destination = ⟨state.nextId, items⟩ ∧ after = WordAllocation.extend state items.length base ∧
      registered = write heap state.nextId (some ⟨allocator, .arguments items⟩) ∧
      heap state.nextId = none ∧ request (items.length * 4) effects = (some base, reached) ∧ after.valid = true := by
  unfold reserve at done
  cases reserved : WordAllocation.reserve state items.length request effects with
  | mk outcome advanced =>
    rcases outcome with ⟨result, memory⟩
    simp only [reserved] at done
    cases result with
    | error fault => simp at done
    | ok target =>
      cases target with
      | none => simp at done
      | some target =>
        simp only [List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, ↓reduceIte] at done
        cases allocated : Memory.allocate heap allocator target.allocation (.arguments items) true with
        | error fault => simp [allocated] at done
        | ok logical =>
          simp only [allocated] at done
          cases done
          obtain ⟨base, targetEq, rfl, response, valid⟩ := WordAllocation.reserve_nonempty_success state _ items.length request
            effects _ target (by simpa using nonempty) reserved
          subst target
          unfold Memory.allocate at allocated
          cases found : heap state.nextId with
          | none =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, found, Except.ok.injEq] at allocated
            subst registered
            exact ⟨base, rfl, rfl, rfl, rfl, response, valid⟩
          | some old => simp [found] at allocated

/-- Successful allocation discharges every destination obligation of the
existing captured copy/sort proof. The readonly source need not be registered
or writable. Persistent allocation's provisional payload is masked throughout
private initialization. This does not prove the native allocator contract. -/
theorem copied_refines (heap registered : Heap) (state allocated : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ) (destination : ArgumentSlice) (source : View)
    (valid : state.valid = true) (related : Related heap state) (represented : Represents state source items)
    (nonempty : items ≠ [])
    (done : reserve heap state allocator items request effects = ((.ok (some destination), registered, allocated), reached)) :
    ∃ result after values projected, Captured.Settles (fun budget => Copied.run budget allocated source (view destination)) (result, after) ∧
      Updated registered projected destination.address values ∧ Related projected after ∧
      after.valid = true ∧ values.Perm items ∧ Represents after source items ∧ HeapFrame (view destination) allocated after ∧
      SliceValid allocator projected ⟨destination.address, values⟩ ∧
      ((result = .ok () ∧ values = sortIds items) ∨ result = .error (.memory .outOfMemory)) := by
  obtain ⟨base, rfl, rfl, rfl, _, _, allocatedValid⟩ :=
    reserve_success heap registered state allocated allocator items request effects reached destination nonempty done
  have older := WordAllocation.source_older state source items valid represented nonempty
  exact Arguments.copied_refines _ _ allocator source ⟨state.nextId, items⟩ items allocatedValid
    (extend_owned state items.length base) (write_same _ _ _) (extend_others heap state allocator base items valid related)
    (WordAllocation.source_preserved state items.length base source items valid represented) represented.1.symm
    (by simp [Compiler.ZigAir.Memory.WordCopy.disjoint, view, show source.allocation ≠ state.nextId by omega])

end Compiler.Extraction.Memory.Arguments.Allocation
