/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionCapacity
import Compiler.Extraction.InternerInsertionNativeBody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The proved frame of every original native allocation preserves any prior
borrowed word view, including offsets and empty views. No final representation
or final Good premise is needed. -/
theorem CallerPreparationFailure.borrow {allocator : Nat} {normalized : ArgumentSlice}
    {before : World (Publication.Effects σ)} {history : Session (Publication.Effects σ)} {after : Frame σ}
    (post : CallerPreparationFailure allocator normalized before history after)
    (source : View) (values : List NodeId) (good : Good source values before) :
    Good source values (⟨before.graph, memory after⟩ : World (Publication.Effects σ)) := by
  refine ⟨post.valid, ?_⟩
  by_cases empty : values = []
  · exact ⟨good.2.1, fun _ inside => False.elim (by simp [empty] at inside)⟩
  · have inside : 0 < values.length := List.length_pos_iff.mpr empty
    have read := good.2.2 0 inside
    cases accessed : Compiler.ZigAir.Memory.access before.memory.memory (source.address 0) ⟨4, 4⟩ false with
    | error fault =>
      simp [Compiler.ZigAir.Memory.load, View.pointer, word, Compiler.ZigAir.Memory.Ty.layout,
        accessed, bind, Except.bind] at read
    | ok cell =>
      have found := (Compiler.ZigAir.Memory.access_success_region before.memory.memory _ _ false cell accessed).1
      exact represented_frame source values good.2 ((post.native _ _ found).trans found.symm)

/-- The concrete insertion suffix of the source caller: handoff, native insert,
then the existing ordinary-outcome defers. It does not select find's cache or
recursive branches, or invent a caller prefix. -/
def finishInsertion (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (deterministic : Bool)
    (taken : OwnedCall.State (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ) := none) :=
  let ran := (do handoff; graph (fun slice => insert ops allocate runtimeSafety allocator container source itemSource meaning
    input key slice deterministic growth) : Action (Publication.Effects σ) NodeId) taken
  finish (Publication.external ops.arguments) allocator ran.1 ran.2

section Caller
variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
  (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
  (meaning : Meaning) (request : Interner.Request) (values : List NodeId)
  (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
  (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
  (deterministic : Bool) (cells : List Storage.Cell) (growth : Option (Growth.Registered.Callbacks σ))

theorem CallerInput.finish_native
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup) :
    finishInsertion ops allocate runtimeSafety allocator container source itemSource meaning input key deterministic taken growth =
      (let (result, reached) := insert ops allocate runtimeSafety allocator container source itemSource meaning
         input key normalized deterministic growth taken.world
       if ordinary result then (result, ⟨reached, ⟨none, some normalized, true⟩⟩)
       else (result, ⟨reached, ⟨some lookup, some normalized, true⟩⟩)) := by
  simpa only [finishInsertion, entry.origin.scope] using entry.handoff_insert ops.arguments
    (fun slice => insert ops allocate runtimeSafety allocator container source itemSource meaning input key slice deterministic growth)

/-- Capacity cleanup and caller completion share the same native execution.
The reached graph is derived from the source ownership flags and initial graph
correspondence. Detached outer cleanup consumes no second normalized owner and
preserves all reached effects. No final graph, caller result or memory frame is
assumed. Transport through recursive children remains a separate obligation. -/
theorem CallerInput.capacity_completed
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (backing : Compiler.ZigAir.Memory.Address)
    (owner : before.memory.memory.heap.lookup container = some ownerCell)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells) (valid : Interner.Invariant meaning before.graph)
    (saturated : 2 ^ 32 - 1 ≤ cells.length) :
    ∃ after,
      body ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells taken.world growth =
        (.error (.language .capacity), ⟨before.graph, memory after⟩) ∧
      finishInsertion ops allocate runtimeSafety allocator container source itemSource meaning input key deterministic taken growth =
        (.error (.language .capacity), ⟨⟨before.graph, memory after⟩, ⟨none, some normalized, true⟩⟩) ∧
      CallerPreparationFailure allocator normalized before taken.world.memory after ∧
      (memory after).effects = (if normalized.items.isEmpty then taken.world.memory.effects
        else (Publication.external ops.arguments).free normalized taken.world.memory) ∧
      (∀ borrowed ids, Good borrowed ids before → Good borrowed ids (⟨before.graph, memory after⟩ : World (Publication.Effects σ))) := by
  obtain ⟨after, checked, _, post, effects⟩ := entry.capacity_failure ops allocate runtimeSafety allocator container source itemSource meaning
    request values input key normalized lookup before taken deterministic cells growth ownerCell backing owner header saturated
  have reachedRows : taken.world.graph.representatives = some cells := by rw [entry.origin.graph]; exact rows
  have reads : before.graph.read = Storage.readValue cells := by
    have represented := valid.representation
    simp only [Interner.Represented, rows] at represented
    exact represented.1
  have projected := body_unpublished ops allocate runtimeSafety allocator container source itemSource meaning input key normalized
    deterministic taken.world cells growth reachedRows (by rw [entry.origin.graph]; exact reads)
    (some .capacityFailure) (Storage.Release.normalized.run Storage.normalizedOwnership) after rfl rfl checked
  have ran : body ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells taken.world growth =
      (.error (.language .capacity), ⟨before.graph, memory after⟩) := by
    simpa only [Interner.insertionOutcome, Except.mapError, entry.origin.graph] using projected
  have finished := entry.finish_native ops allocate runtimeSafety allocator container source itemSource meaning request values input key normalized lookup
    before taken deterministic growth
  simp only [insert, reachedRows, ran, ordinary, OwnedCall.Fault.recoverable, ↓reduceIte] at finished
  exact ⟨after, ran, finished, post, effects, post.borrow⟩

/-- A count-binding rejection retains the actual normalized owner and detached
lookup after handoff. The caller does not translate it to OOM or invent unwind. -/
theorem CallerInput.rejected_completed
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (rows : before.graph.representatives = some cells) (fault : CountFault)
    (rejected : checkedCount taken.world.memory.memory container cells = .error fault) :
    finishInsertion ops allocate runtimeSafety allocator container source itemSource meaning input key deterministic taken growth =
      (.error (.language .safetyFault), ⟨taken.world, ⟨some lookup, some normalized, true⟩⟩) := by
  have ran := body_rejected ops allocate runtimeSafety allocator container source itemSource meaning input key normalized
    deterministic cells taken.world growth fault rejected
  have reachedRows : taken.world.graph.representatives = some cells := by rw [entry.origin.graph]; exact rows
  have finished := entry.finish_native ops allocate runtimeSafety allocator container source itemSource meaning request values input key normalized lookup
    before taken deterministic growth
  simpa only [insert, reachedRows, ran, ordinary, OwnedCall.Fault.recoverable, Bool.false_eq_true, ↓reduceIte] using finished

end Caller
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
