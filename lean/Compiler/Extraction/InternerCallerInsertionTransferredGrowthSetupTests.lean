/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowingChainTests
import Compiler.Extraction.InternerCallerInsertionTransferredGrowth

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredGrowthTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- After five published rows, the next continuation selects nondeterministic
insertion. It reuses the same normalization, caller handoff and native executor. -/
def object (empty : Bool) := startId empty 4 + (if empty then 1 else 2)
def copied (empty : Bool) : AssemblyClone.NativeFields.ItemValue :=
  { input with verbatim := some ⟨2, 3, ⟨object empty + 1, [8, 9], 0⟩⟩ }
def made (safety empty : Bool) := AssemblyItem.Creation.create (observe ops.create) 7 input.item (taken safety empty 4).2.world.memory
def cloned (safety empty : Bool) := AssemblyClone.Physical.run (observe ops.copy) 7 input (made safety empty).2
def ready (safety empty : Bool) :=
  (AssemblyClone.NativeFields.install (copied empty) (object empty) (cloned safety empty).2).toOption.getD (cloned safety empty).2
def row (safety empty : Bool) : Storage.Cell :=
  ⟨(copied empty).item, value safety empty 4, object empty, values empty, (key empty).sequence, (normalized safety empty 4).address⟩
def grownLifetime (empty : Bool) := if empty then 27 else 38
def outcome (safety empty : Bool) := invokeWith ops safety empty (before safety empty 4) allocate false
def world (safety empty : Bool) := (outcome safety empty).2.world
def executed (safety empty : Bool) := execution ops allocate safety 7 6 (parent empty) source Insertion.Tests.model
  input (key empty) (normalized safety empty 4) false (cells safety empty 4) (taken safety empty 4).2.world (some growth)
def reached (safety empty : Bool) :=
  (insertWith ops safety empty (normalized safety empty 4) allocate false (taken safety empty 4).2.world).2

theorem preparation_results (safety empty : Bool) :
    (made safety empty).1 = .ok (object empty) ∧ (cloned safety empty).1 = .ok (copied empty) := by
  cases safety <;> cases empty <;> constructor <;> insertion_kernel_rfl

theorem prepared_geometry (safety empty : Bool) :
    ((cloned safety empty).2.memory.nextId, decide ((ready safety empty).memory.nextAddress ≤ 8192)) =
      (grownLifetime empty, true) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem ready_contract (safety empty : Bool) : Valid (ready safety empty) ∧
    (ready safety empty).memory.nextAddress = (cloned safety empty).2.memory.nextAddress := by
  have entry := (initialized_prefix safety empty 4 (by decide)).caller_input (by decide)
  have observed := preparation_results safety empty
  obtain ⟨installed, _, _, established, assigned, _⟩ := entry.prepare_transferred ops allocate safety 7 6 (object empty)
    (parent empty) source (request empty) (values empty) input (copied empty) (key empty) (normalized safety empty 4)
    (lookup empty) (before safety empty 4) (taken safety empty 4).2 (cells safety empty 4) (value safety empty 4)
    (fun _ _ => (taken safety empty 4).2.world.graph) (made safety empty).2 (cloned safety empty).2
    (Prod.ext observed.1 rfl) (Prod.ext observed.2 rfl)
  have same : ready safety empty = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
  rw [same]
  exact ⟨established.valid, established.written.nextAddress⟩

theorem backing_fits (safety empty : Bool) : Compiler.ZigAir.Memory.RegionAllocation.Fits (ready safety empty).memory ⟨416, 8⟩ 8192 := by
  have valid := (ready_contract safety empty).1.memory
  have bound := (Prod.mk.inj (prepared_geometry safety empty)).2
  simp only [decide_eq_true_eq] at bound
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  simp only [Compiler.ZigAir.Memory.State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
  have checked := valid.1.2 entry present
  simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact Or.inr (by omega)

theorem completed (safety empty : Bool) (after : Frame Nat)
    (ran : executed safety empty = ((.ok (some .success), transferredOwnership), after))
    (candidate : cell input (key empty) (normalized safety empty 4) (value safety empty 4) transferredOwnership after = row safety empty) :
    outcome safety empty = (.ok 5,
      ⟨reached safety empty, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    (reached safety empty).memory = memory after ∧
    (reached safety empty).graph.representatives = some (cells safety empty 4 ++ [row safety empty]) ∧
    (reached safety empty).graph.table = (before safety empty 4).graph.table := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have rows : (taken safety empty 4).2.world.graph.representatives.getD [] = cells safety empty 4 := by
    rw [entry.origin.graph]; rfl
  have selected : selectedGrowth (cells safety empty 4) = some growth := by simp only [selectedGrowth, prior.count, ↓reduceIte]
  have inserted : insertWith ops safety empty (normalized safety empty 4) allocate false (taken safety empty 4).2.world =
      (.ok 5, reached safety empty) := by
    apply Prod.ext
    · simp only [insertWith, rows, selected]
      change (match (executed safety empty).1.1 with
        | .error _ => (Except.error (OwnedCall.Fault.language .safetyFault) : Except OwnedCall.Fault NodeId)
        | .ok result => (Interner.insertionOutcome (cells safety empty 4) result).mapError OwnedCall.Fault.language) = _
      rw [ran]
      simp only [Interner.insertionOutcome, Except.mapError, Storage.idFor, prior.count]
      rfl
    · rfl
  have finished := entry.handoff_insert ops.arguments (fun slice => insertWith ops safety empty slice allocate false)
  simp only [inserted, ordinary, ↓reduceIte, (prefix_results safety empty 4 (by decide)).2.2.2] at finished
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold outcome invokeWith
    rw [(prefix_results safety empty 4 (by decide)).1]
    have initialized : prepared safety empty 4 = (.ok (values empty), (prepared safety empty 4).2) :=
      Prod.ext (prefix_results safety empty 4 (by decide)).2.1 rfl
    have transferred : taken safety empty 4 = (.ok (), (taken safety empty 4).2) :=
      Prod.ext (prefix_results safety empty 4 (by decide)).2.2.1 rfl
    unfold prepared at initialized
    unfold taken at transferred
    simp only [Caller.invoke, Effect.bind]
    change finish (Publication.external ops.arguments) 7 _ _ = _
    rw [initialized]
    change finish (Publication.external ops.arguments) 7
      (Effect.bind (take (Publication.external ops.arguments) 7)
        (fun _ => (do handoff; graph (fun slice => insertWith ops safety empty slice allocate false) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty 4).2).1
      (Effect.bind (take (Publication.external ops.arguments) 7)
        (fun _ => (do handoff; graph (fun slice => insertWith ops safety empty slice allocate false) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty 4).2).2 = _
    simp only [Effect.bind]
    rw [transferred]
    exact finished
  · unfold reached insertWith
    simp only [rows, selected]
    change memory (executed safety empty).2 = _
    rw [ran]
  · unfold reached insertWith
    simp only [rows, selected]
    change (Insertion.projected _ _ _ (cell _ _ _ _ (executed safety empty).1.2 (executed safety empty).2)
      (executed safety empty).1.2 (executed safety empty).2).graph.representatives = _
    rw [ran]
    change some (cells safety empty 4 ++ [cell input (key empty) (normalized safety empty 4) (value safety empty 4) transferredOwnership after]) = _
    rw [candidate]
  · unfold reached insertWith
    simp only [rows, selected]
    change (Insertion.projected _ _ _ (cell _ _ _ _ (executed safety empty).1.2 (executed safety empty).2)
      (executed safety empty).1.2 (executed safety empty).2).graph.table = _
    rw [ran]
    change (taken safety empty 4).2.world.graph.table = _
    rw [entry.origin.graph]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredGrowthTests
