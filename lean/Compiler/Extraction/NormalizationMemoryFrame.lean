/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemorySettles

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

structure InitialFrame (before : Session σ) (buffer : View) (handle : Handle) (after : Session σ) : Prop where
  memory : ∀ id cell, before.memory.heap.lookup id = some cell → id ≠ buffer.allocation → after.memory.heap.lookup id = some cell
  registry : ∀ id block, before.heap id = some block → after.heap id = some block
  freshOwned : ∀ slice, handle.owned = some slice → before.memory.heap.lookup slice.address = none

theorem reserve_shape (external : External σ) (allocator : Nat) (values : List NodeId) (before after : Session σ)
    (slice : ArgumentSlice) (reserved : reserve external allocator values before = (.ok slice, after)) :
    Allocation.reserve before.heap before.memory allocator values (external.allocate .temporary before) before.effects =
      ((.ok (some slice), after.heap, after.memory), after.effects) := by
  unfold reserve at reserved
  cases actual : Allocation.reserve before.heap before.memory allocator values (external.allocate .temporary before) before.effects with
  | mk outcome effects =>
    rcases outcome with ⟨result, heap, memory⟩
    rw [actual] at reserved
    cases result with
    | error fault => simp at reserved
    | ok selected =>
      cases selected with
      | none => simp at reserved
      | some destination =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at reserved
        rcases reserved with ⟨rfl, rfl⟩
        rfl

theorem prepare_footprint (budget allocator bufferLength : Nat) (source target : View) (values : List NodeId)
    (allocated : Bool) (before after : Session σ) (handle : Handle)
    (selected : Destination allocator source target values allocated before)
    (ownership : normalizationOwnershipCode.ownTemporary.test source.length bufferLength = allocated)
    (prepared : prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before = (.ok handle, after)) :
    HeapFrame target before.memory after.memory ∧
      (∀ id, id ≠ target.allocation → after.heap id = before.heap id) ∧
      (∀ slice, handle.owned = some slice → allocated = true ∧ slice.address = target.allocation) := by
  unfold prepare at prepared
  cases copied : Copied.run budget before.memory source target with
  | mk result memory =>
    rw [copied] at prepared
    cases result with
    | error fault => simp at prepared
    | ok returned =>
      cases returned
      rcases Copied.run_result budget before.memory memory source target values (.ok ()) selected.valid selected.writable
          selected.represented selected.lengths selected.disjoint copied with impossible | ⟨_, _, _, _, frame, _⟩
      · contradiction
      · rw [ownership] at prepared
        cases allocated <;> simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at prepared
        · rcases prepared with ⟨rfl, rfl⟩
          refine ⟨frame, fun _ _ => rfl, ?_⟩
          intro slice impossible; cases impossible
        · rcases prepared with ⟨rfl, rfl⟩
          refine ⟨frame, fun id apart => write_other _ _ _ _ apart, ?_⟩
          intro slice same; cases same; exact ⟨rfl, rfl⟩

theorem prepare_initial_frame (budget allocator bufferLength : Nat) (source target buffer : View) (values : List NodeId)
    (allocated : Bool) (initial before after : Session σ) (handle : Handle)
    (selected : Destination allocator source target values allocated before)
    (ownership : normalizationOwnershipCode.ownTemporary.test source.length bufferLength = allocated)
    (oldMemory : ∀ id cell, initial.memory.heap.lookup id = some cell → id ≠ buffer.allocation →
      id ≠ target.allocation ∧ before.memory.heap.lookup id = some cell)
    (oldHeap : ∀ id block, initial.heap id = some block → id ≠ target.allocation ∧ before.heap id = some block)
    (fresh : allocated = true → initial.memory.heap.lookup target.allocation = none)
    (prepared : prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before = (.ok handle, after)) :
    InitialFrame initial buffer handle after := by
  obtain ⟨memory, registry, owned⟩ := prepare_footprint budget allocator bufferLength source target values allocated before after handle
    selected ownership prepared
  refine ⟨?_, ?_, ?_⟩
  · intro id cell found apart
    have old := oldMemory id cell found apart
    exact (memory.allocations id old.1).trans old.2
  · intro id block stored
    have old := oldHeap id block stored
    exact (registry id old.1).trans old.2
  · intro slice own
    have selectedOwned := owned slice own
    rw [selectedOwned.2]
    exact fresh selectedOwned.1

theorem init_frame (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before after : Session σ) (handle : Handle) (valid : Valid before)
    (represented : Represents before.memory source values)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before)
    (admitted : Admitted external)
    (initialized : init normalizationOwnershipCode external budget allocator commutative source buffer values before = (.ok handle, after)) :
    InitialFrame before buffer handle after := by
  cases needed : !commutative || decide (source.length < normalizationOwnershipCode.threshold) with
  | true =>
    simp only [init, needed, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at initialized
    rcases initialized with ⟨rfl, rfl⟩
    refine ⟨fun _ _ found _ => found, fun _ _ stored => stored, ?_⟩
    intro slice impossible; cases impossible
  | false =>
    have conditions : commutative = true ∧ 2 ≤ source.length := by
      simpa [normalizationOwnershipCode, Bool.or_eq_false_iff, Bool.not_eq_false', Nat.not_lt] using needed
    by_cases fits : source.length ≤ buffer.length
    · have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = true := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      simp only [init, needed, Bool.false_eq_true, ↓reduceIte, choice] at initialized
      have privateBuffer := scratch conditions.1 conditions.2 fits
      apply prepare_initial_frame budget allocator buffer.length source (bufferPrefix buffer source.length) buffer values false before before after handle
        (scratch_destination allocator source buffer values before valid represented privateBuffer fits)
        (by simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, Nat.not_lt.mpr fits])
        (fun _ _ found apart => ⟨apart, found⟩) _ (by intro impossible; cases impossible) initialized
      intro id block stored
      refine ⟨?_, stored⟩
      intro same
      change id = buffer.allocation at same
      subst id
      rw [privateBuffer.unregistered] at stored
      contradiction
    · have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = false := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      have nonempty : values ≠ [] := by intro empty; rw [empty] at represented; have length := represented.1; simp at length; omega
      obtain ⟨reserved, allocated, reservedRun, selected⟩ := reserve_refines external allocator source values before valid represented nonempty admitted
      simp only [init, needed, Bool.false_eq_true, ↓reduceIte, choice, reservedRun] at initialized
      cases reserved with
      | error fault => simp at initialized
      | ok slice =>
        have raw := reserve_shape external allocator values before allocated slice reservedRun
        obtain ⟨base, sliceEq, memoryEq, heapEq, _, _, _⟩ := Allocation.reserve_success _ _ _ _ allocator values
          (external.allocate .temporary before) _ _ slice nonempty raw
        apply prepare_initial_frame budget allocator buffer.length source (view slice) buffer values true before allocated after handle selected
          (by simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, show buffer.length < source.length by omega]) _ _ _ initialized
        · intro id cell found _
          have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell valid.memory found).1
          have apart : id ≠ before.memory.nextId := by omega
          refine ⟨by simpa [sliceEq, view] using apart, ?_⟩
          simpa [memoryEq, Compiler.ZigAir.Memory.WordAllocation.extend_lookup, Ne.symm apart] using found
        · intro id block stored
          obtain ⟨cell, found, _persistent⟩ := valid.injected id block stored
          have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell valid.memory found).1
          have apart : id ≠ before.memory.nextId := by omega
          exact ⟨by simpa [sliceEq, view] using apart, by simpa [heapEq, write, apart] using stored⟩
        · intro _
          simpa [sliceEq, view] using Compiler.ZigAir.Memory.WordAllocation.next_id_fresh before.memory valid.memory

structure Frame (before : Session σ) (buffer : View) (after : Session σ) : Prop where
  memory : ∀ id cell, before.memory.heap.lookup id = some cell → id ≠ buffer.allocation → after.memory.heap.lookup id = some cell
  registry : ∀ id block, before.heap id = some block → after.heap id = some block

theorem closed_frame (external : External σ) (allocator : Nat) (source buffer : View) (values : List NodeId)
    (exit : NormalizationOwnership.Exit) (handle : Handle) (before prepared after : Session σ) (result : Except Failure Outcome)
    (valid : Valid before) (ready : Ready allocator source values handle prepared)
    (initial : InitialFrame before buffer handle prepared)
    (closed : Closed external allocator source values exit handle prepared result after) : Frame before buffer after := by
  refine ⟨?_, ?_⟩
  · intro id cell found apart
    exact (closed.frame id cell (initial.memory id cell found apart) (by
      intro owned own same
      have absent := initial.freshOwned owned own
      rw [← same, found] at absent
      contradiction)).1
  · intro id block stored
    have registered := initial.registry id block stored
    obtain ⟨cell, found, _persistent⟩ := ready.valid.injected id block registered
    have kept := closed.frame id cell found (by
      intro owned own same
      obtain ⟨old, present, _persistent⟩ := valid.injected id block stored
      have absent := initial.freshOwned owned own
      rw [← same, present] at absent
      contradiction)
    exact kept.2.trans registered

/-- Complete scoped preservation plus the explicit frame for all original
storage outside the caller's scratch allocation and every original registry
entry. Semantic preparation faults are retained as rejected observations. -/
theorem run_verified (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before after : Session σ) (result : Except Failure Outcome)
    (valid : Valid before) (represented : Represents before.memory source values)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before)
    (admitted : Admitted external)
    (executed : run normalizationOwnershipCode external budget allocator commutative source buffer values exit before = (result, after)) :
    Post external budget allocator commutative source buffer values exit before result after ∧
      (result = .error (.preparation .incomplete) ∨ result = .error (.preparation (.memory .outOfMemory)) ∨ Frame before buffer after) := by
  have post := run_result external budget allocator commutative source buffer values exit before after result valid represented scratch admitted executed
  refine ⟨post, ?_⟩
  rcases post.lifecycle with ⟨fault, _, rfl, initPost⟩ | ⟨handle, prepared, initialized, ready, _, _, closed⟩
  · cases fault with
    | allocation | release => contradiction
    | outOfMemory =>
      exact Or.inr (Or.inr ⟨fun id cell found _ => by simpa only [initPost.2.1] using found,
        fun id _ stored => by simpa only [initPost.1] using stored⟩)
    | preparation reason =>
      rcases initPost.1 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (closed_frame external allocator source buffer values exit handle before prepared after result valid ready
      (init_frame external budget allocator commutative source buffer values before prepared handle valid represented scratch admitted initialized) closed))

end Compiler.Extraction.Memory.Arguments.Normalization
