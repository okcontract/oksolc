/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryContracts

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

/-- Preconditions for the destination selected by the actual initializer.
Only the allocated branch needs an owned extent and provisional registration;
scratch remains unregistered caller storage. The next theorem discharges the
contents and ready-handle postcondition using actual captured preparation. -/
structure Destination (allocator : Nat) (source target : View) (values : List NodeId)
    (allocated : Bool) (before : Session σ) : Prop where
  valid : before.memory.valid = true
  injected : Injected before.heap before.memory
  represented : Represents before.memory source values
  writable : Writable before.memory target
  lengths : source.length = target.length
  disjoint : Compiler.ZigAir.Memory.WordCopy.disjoint source target = true
  storage : if allocated then
    target.first = 0 ∧ before.heap target.allocation = some ⟨allocator, .arguments values⟩ ∧
      Owned before.memory target.allocation values.length ∧ Related (write before.heap target.allocation none) before.memory ∧
      source.allocation ≠ target.allocation
    else Related before.heap before.memory ∧ before.heap target.allocation = none

theorem prepare_ready (budget allocator bufferLength : Nat) (source target : View) (values : List NodeId)
    (allocated : Bool) (before after : Session σ) (handle : Handle)
    (selected : Destination allocator source target values allocated before)
    (ownership : normalizationOwnershipCode.ownTemporary.test source.length bufferLength = allocated)
    (prepared : prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before = (.ok handle, after)) :
    Ready allocator source values handle after ∧ handle.values = sortIds values := by
  unfold prepare at prepared
  cases copied : Copied.run budget before.memory source target with
  | mk result memory =>
    rw [copied] at prepared
    cases result with
    | error fault => simp at prepared
    | ok returned =>
      cases returned
      rcases Copied.run_result budget before.memory memory source target values (.ok ()) selected.valid selected.writable
          selected.represented selected.lengths selected.disjoint copied with impossible | ⟨items, connected, _, preserved, frame, effect⟩
      · contradiction
      · rcases effect with ⟨_, sorted⟩ | impossible
        · subst items
          have shape := (Copied.run_storage budget before.memory source target selected.valid).2
          rw [copied] at shape
          have injected := selected.injected.retained shape
          have represented := connected.values
          rw [ownership] at prepared
          cases allocated with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at prepared
            rcases prepared with ⟨rfl, rfl⟩
            have storage := selected.storage
            refine ⟨⟨⟨connected.valid, related_frame _ _ _ target storage.1 storage.2 frame, injected⟩,
              represented, preserved, ?_, ?_⟩, rfl⟩
            · intro slice impossible; cases impossible
            · intro _ slice impossible; cases impossible
          | true =>
            simp only [↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at prepared
            rcases prepared with ⟨rfl, rfl⟩
            rcases selected.storage with ⟨first, stored, owned, others, apart⟩
            have retained := copied_owned budget before.memory source target target.allocation values.length selected.valid owned
            rw [copied] at retained
            have sortedOwned : Owned memory target.allocation (sortIds values).length := by
              simpa only [(sortIds_perm values).length_eq] using retained
            have sameView : view ⟨target.allocation, sortIds values⟩ = target := by
              cases target
              simp only [view, View.mk.injEq, true_and]
              exact ⟨first.symm, represented.1⟩
            refine ⟨⟨⟨connected.valid, related_publish _ _ _ allocator target (sortIds values) others frame sortedOwned first represented,
              injected.published target.allocation allocator values (sortIds values) stored⟩,
              represented, preserved, ?_, ?_⟩, rfl⟩
            · intro slice same
              cases same
              exact ⟨rfl, sameView, Or.inr (write_same _ _ _)⟩
            · intro _ slice same
              cases same
              exact apart
        · contradiction

/-- No descriptor or memory-contract fault can masquerade as ordinary OOM in
preparation. Under the selected-buffer premises, rejection is exactly finite
observation exhaustion or the captured stack-memory resource fault. -/
theorem prepare_failure (budget allocator bufferLength : Nat) (source target : View) (values : List NodeId)
    (allocated : Bool) (before after : Session σ) (fault : Failure)
    (selected : Destination allocator source target values allocated before)
    (prepared : prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before = (.error fault, after)) :
    (fault = .preparation .incomplete ∨ fault = .preparation (.memory .outOfMemory)) ∧
      after.memory.valid = true ∧ Injected after.heap after.memory ∧ after.effects = before.effects := by
  unfold prepare at prepared
  cases copied : Copied.run budget before.memory source target with
  | mk result memory =>
    rw [copied] at prepared
    cases result with
    | ok returned => cases returned; simp at prepared
    | error reason =>
      simp only [Except.error.injEq, Prod.mk.injEq] at prepared
      rcases prepared with ⟨rfl, rfl⟩
      have retained := Copied.run_storage budget before.memory source target selected.valid
      rw [copied] at retained
      refine ⟨?_, retained.1, selected.injected.retained retained.2, rfl⟩
      rcases Copied.run_result budget before.memory memory source target values (.error reason) selected.valid selected.writable
          selected.represented selected.lengths selected.disjoint copied with incomplete | ⟨_, _, _, _, _, effect⟩
      · cases incomplete; exact Or.inl rfl
      · rcases effect with ⟨impossible, _⟩ | exhausted
        · contradiction
        · cases exhausted; exact Or.inr rfl

/-- Caller scratch is borrowed, writable, private to the lookup and disjoint
from its input. The contract is required only on the selected scratch path. -/
structure Scratch (source buffer : View) (before : Session σ) : Prop where
  writable : Writable before.memory buffer
  unregistered : before.heap buffer.allocation = none
  separate : source.allocation ≠ buffer.allocation

theorem scratch_destination (allocator : Nat) (source buffer : View) (values : List NodeId) (before : Session σ)
    (valid : Valid before) (represented : Represents before.memory source values)
    (scratch : Scratch source buffer before) (fits : source.length ≤ buffer.length) :
    Destination allocator source (bufferPrefix buffer source.length) values false before := by
  refine ⟨valid.memory, valid.injected, represented, ?_, rfl, ?_, valid.related, scratch.unregistered⟩
  · obtain ⟨extent, cell, found, typed, writable, bound⟩ := scratch.writable
    exact ⟨extent, cell, found, typed, writable, by dsimp only [bufferPrefix]; omega⟩
  · simp [Compiler.ZigAir.Memory.WordCopy.disjoint, bufferPrefix, scratch.separate]

theorem allocated_destination (allocator : Nat) (source : View) (values : List NodeId) (before : Session σ)
    (valid : Valid before) (represented : Represents before.memory source values) (nonempty : values ≠ [])
    (request : Compiler.ZigAir.Memory.WordAllocation.Allocator σ) (slice : ArgumentSlice)
    (heap : Memory.Heap) (memory : Compiler.ZigAir.Memory.State) (effects : σ)
    (reserved : Allocation.reserve before.heap before.memory allocator values request before.effects = ((.ok (some slice), heap, memory), effects)) :
    Destination allocator source (view slice) values true (⟨heap, memory, effects⟩ : Session σ) := by
  obtain ⟨base, rfl, rfl, rfl, _, _, afterValid⟩ := Allocation.reserve_success _ _ _ _ allocator values request _ _ slice nonempty reserved
  have older := Compiler.ZigAir.Memory.WordAllocation.source_older before.memory source values valid.memory represented nonempty
  refine ⟨afterValid, valid.injected.extended allocator base values,
    Compiler.ZigAir.Memory.WordAllocation.source_preserved before.memory values.length base source values valid.memory represented,
    owned_writable _ _ _ (Allocation.extend_owned before.memory values.length base), represented.1.symm, ?_,
    rfl, write_same _ _ _, Allocation.extend_owned before.memory values.length base,
    Allocation.extend_others before.heap before.memory allocator base values valid.memory valid.related, ?_⟩
  · simp [Compiler.ZigAir.Memory.WordCopy.disjoint, view, show source.allocation ≠ before.memory.nextId by omega]
  · change source.allocation ≠ before.memory.nextId; omega

theorem reserve_refines (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (before : Session σ) (valid : Valid before) (represented : Represents before.memory source values)
    (nonempty : values ≠ []) (admitted : Admitted external) :
    ∃ result after, reserve external allocator values before = (result, after) ∧
      match result with
      | .ok slice => Destination allocator source (view slice) values true after
      | .error .outOfMemory => after.heap = before.heap ∧ after.memory = before.memory ∧ Valid after
      | .error _ => False := by
  cases response : external.allocate .temporary before (values.length * 4) before.effects with
  | mk selected effects =>
    cases selected with
    | none =>
      have failed := Allocation.reserve_failed before.heap before.memory allocator values (external.allocate .temporary before)
        before.effects effects valid.memory nonempty source represented response
      exact ⟨.error .outOfMemory, ⟨before.heap, before.memory, effects⟩,
        by simp only [reserve, failed], rfl, rfl, ⟨valid.memory, valid.related, valid.injected⟩⟩
    | some base =>
      have reserved := Allocation.reserve_admitted before.heap before.memory allocator base values (external.allocate .temporary before)
        before.effects effects valid.memory nonempty source represented (valid.injected.fresh valid.memory) response
        (admitted .temporary before values base effects valid.memory nonempty response)
      refine ⟨.ok ⟨before.memory.nextId, values⟩, _, ?_, allocated_destination allocator source values before valid represented nonempty
        (external.allocate .temporary before) _ _ _ effects reserved⟩
      simp only [reserve, reserved]

def normalized (commutative : Bool) (source : View) (values : List NodeId) : List NodeId :=
  if !commutative || decide (source.length < normalizationOwnershipCode.threshold) then values else sortIds values

def InitPost (allocator : Nat) (commutative : Bool) (source : View) (values : List NodeId)
    (before : Session σ) (result : Except Failure Handle) (after : Session σ) : Prop :=
  match result with
  | .ok handle => Ready allocator source values handle after ∧ handle.values = normalized commutative source values
  | .error .outOfMemory => after.heap = before.heap ∧ after.memory = before.memory ∧ Valid after
  | .error (.preparation reason) => (reason = .incomplete ∨ reason = .memory .outOfMemory) ∧
      after.memory.valid = true ∧ Injected after.heap after.memory
  | .error _ => False

theorem prepare_classified (budget allocator bufferLength : Nat) (commutative : Bool) (source target : View)
    (values : List NodeId) (allocated : Bool) (before initial : Session σ)
    (selected : Destination allocator source target values allocated before)
    (ownership : normalizationOwnershipCode.ownTemporary.test source.length bufferLength = allocated)
    (needed : (!commutative || decide (source.length < normalizationOwnershipCode.threshold)) = false) :
    ∃ result after, prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before = (result, after) ∧
      InitPost allocator commutative source values initial result after := by
  cases executed : prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before with
  | mk result after =>
    refine ⟨result, after, rfl, ?_⟩
    cases result with
    | ok handle =>
      obtain ⟨ready, sorted⟩ := prepare_ready budget allocator bufferLength source target values allocated before after handle selected ownership executed
      exact ⟨ready, by simpa only [normalized, needed, Bool.false_eq_true, ↓reduceIte] using sorted⟩
    | error fault =>
      obtain ⟨failure, valid, injected, _⟩ := prepare_failure budget allocator bufferLength source target values allocated before after fault selected executed
      rcases failure with rfl | rfl
      · exact ⟨Or.inl rfl, valid, injected⟩
      · exact ⟨Or.inr rfl, valid, injected⟩

/-- Complete initializer classification. The result and all buffer obligations
are derived from the source-bound selection, checked allocation and captured
preparation; no successful-normalization premise is supplied by the caller. -/
theorem init_refines (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session σ) (valid : Valid before) (represented : Represents before.memory source values)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before)
    (admitted : Admitted external) :
    ∃ result after, init normalizationOwnershipCode external budget allocator commutative source buffer values before = (result, after) ∧
      InitPost allocator commutative source values before result after := by
  cases needed : !commutative || decide (source.length < normalizationOwnershipCode.threshold) with
  | true =>
    refine ⟨.ok ⟨source, values, none⟩, before, ?_, ⟨⟨valid, represented, represented, ?_, ?_⟩, ?_⟩⟩
    · simp only [init, needed, ↓reduceIte]
    · intro slice impossible; cases impossible
    · intro _ slice impossible; cases impossible
    · simp only [normalized, needed, ↓reduceIte]
  | false =>
    have conditions : commutative = true ∧ 2 ≤ source.length := by
      simpa [normalizationOwnershipCode, Bool.or_eq_false_iff, Bool.not_eq_false', Nat.not_lt] using needed
    by_cases fits : source.length ≤ buffer.length
    · obtain ⟨result, after, prepared, post⟩ := prepare_classified budget allocator buffer.length commutative source
        (bufferPrefix buffer source.length) values false before before
        (scratch_destination allocator source buffer values before valid represented (scratch conditions.1 conditions.2 fits) fits)
        (by simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, Nat.not_lt.mpr fits]) needed
      refine ⟨result, after, ?_, post⟩
      have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = true := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      simpa only [init, needed, Bool.false_eq_true, ↓reduceIte, choice] using prepared
    · have large : buffer.length < source.length := by omega
      have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = false := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      have nonempty : values ≠ [] := by intro empty; rw [empty] at represented; have length := represented.1; simp at length; omega
      obtain ⟨reserved, allocated, reservedRun, selected⟩ := reserve_refines external allocator source values before valid represented nonempty admitted
      cases reserved with
      | error fault =>
        cases fault with
        | allocation | preparation | release => contradiction
        | outOfMemory =>
          refine ⟨.error .outOfMemory, allocated, ?_, selected⟩
          simp only [init, needed, Bool.false_eq_true, ↓reduceIte, choice, reservedRun]
      | ok slice =>
        obtain ⟨result, after, prepared, post⟩ := prepare_classified budget allocator buffer.length commutative source
          (view slice) values true allocated before selected
          (by simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, large]) needed
        refine ⟨result, after, ?_, post⟩
        simpa only [init, needed, Bool.false_eq_true, ↓reduceIte, choice, reservedRun] using prepared

end Compiler.Extraction.Memory.Arguments.Normalization
