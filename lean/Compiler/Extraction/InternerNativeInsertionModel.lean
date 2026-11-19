/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeCapacityFailure
import Compiler.Extraction.InternerNativePreparationFailure
import Compiler.Extraction.InternerInsertionPreparationPolicy
import Compiler.Extraction.InternerInsertionNativePolicy
import Compiler.Extraction.InternerNativePublishedCompletion
import Compiler.Extraction.InternerNativeBackingFailure
import Compiler.Extraction.InternerNativePublicationRollback

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Reduce the general step's insertion obligation to executions with room
that pass the three duplicated-preparation failure sites. Capacity and actual
preparation OOM use the shared native completion and existing logical insertion
adapter. Actual successful first/spare publication and nonempty relocation derive their native
graph frames from reached custody and source observations; the enclosing parent
law stays explicit. First and nonempty no-remap backing OOM share the existing
private-cleanup frame law and derive their native frames from allocator refusal.
First, spare and no-remap relocated publication refusal share one completion
that derives the restored native graph; its enclosing-parent law is explicit. Other later
paths retain the native-frame obligation. Actual callback policy
derives result/graph matching with local policy/preparation-candidate bindings.
No candidate correspondence is needed on the eliminated failure paths. -/
theorem insertion_model (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (lookup : Handle) (detached : lookup.owned = none) (admitted : Admitted ops.arguments)
    (aligned : key.arguments = normalized.items)
    (candidate : Interner.Heap → Storage.Cell) (succeeds : Interner.Heap → Storage.Allocation → Bool)
    (logical : ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      Interner.Represented meaning world.graph)
    (policy : ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      Insertion.Native.PreparationPolicy ops allocator native normalized world.memory (succeeds world.graph))
    (parentFrame : ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      ∀ after, Valid after → Insertion.Native.PrivateFrame normalized world.memory after → parent { world with memory := after })
    (laterPolicy : ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops allocator native normalized world.memory →
      succeeds world.graph = Insertion.Native.observedPolicy ops allocate safety allocator owner source address meaning native key normalized
        true (world.graph.representatives.getD []) world growth)
    (laterCandidate : ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops allocator native normalized world.memory →
      let ran := Insertion.Native.execution ops allocate safety allocator owner source address meaning native key normalized
        true (world.graph.representatives.getD []) world growth
      ran.1.1 = .ok (some .success) →
        Insertion.Native.observedCandidate ops allocate safety allocator owner source address meaning native key normalized
          true (world.graph.representatives.getD []) world growth = candidate world.graph)
    (publishedParent : ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops allocator native normalized world.memory →
      Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key normalized growth world →
      parent (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world).2)
    (rollbackParent : ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops allocator native normalized world.memory →
      Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key normalized growth world →
      parent (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world).2)
    (remaining : ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops allocator native normalized world.memory →
      ¬ Insertion.Native.BackingAllocationOOM ops allocate allocator owner native normalized growth world →
      ¬ Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key normalized growth world →
      ¬ Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key normalized growth world →
      let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
      ordinary actual.1 = true → GraphFrame safety allocator owner rows parent actual.2) :
    ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
        source address meaning native key slice true growth) : Action (Publication.Effects σ) NodeId)
        ⟨world, ⟨some lookup, some normalized, false⟩⟩
      let model := Interner.observedInsert (candidate world.graph) key true (succeeds world.graph) world.graph
      Returns (GraphFrame safety allocator owner rows parent)
        (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2)
        (model.1.mapError Fault.language) model.2 := by
  classical
  intro world frame
  obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
  have represented := logical world frame
  have reads : world.graph.read = Storage.readValue (rows ++ added) := by
    simp only [Interner.Represented, facts.projected] at represented
    exact represented.1
  by_cases room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1
  · by_cases failed : Insertion.Native.PreparationOOM ops allocator native normalized world.memory
    · have model := (policy world frame).model_oom failed (candidate world.graph) key world.graph (rows ++ added)
        facts.projected reads (by simpa only [facts.projected, Option.getD_some] using room)
      simpa only [model, Except.mapError] using
        (frame.preparation_oom ops allocate growth meaning key lookup detached (logical world frame)
          room admitted failed (parentFrame world frame)).1
    · have matched := Insertion.Native.insert_model ops allocate safety allocator owner source address meaning native key normalized
        true (rows ++ added) world growth (candidate world.graph) (succeeds world.graph) data
        (readHeader_items _ _ _ _ facts.header) facts.projected
        (by simpa only [facts.projected, Option.getD_some] using laterPolicy world frame room failed)
        (by simpa only [facts.projected, Option.getD_some] using laterCandidate world frame room failed)
      have finished := finish_handoff (Publication.external ops.arguments) allocator lookup normalized world
        (fun slice => Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice true growth) detached
      change Returns (GraphFrame safety allocator owner rows parent) _ _ _
      simp only [bind, Effect.bind, handoff, graph] at finished ⊢
      rw [finished]
      unfold Returns
      split
      · rename_i ordinaryResult
        intro _
        have preserved : GraphFrame safety allocator owner rows parent
            (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world).2 := by
          by_cases backing : Insertion.Native.BackingAllocationOOM ops allocate allocator owner native normalized growth world
          · exact (frame.backing_oom ops allocate growth meaning key
              (by simpa only [facts.projected, Option.getD_some] using reads) room admitted backing (parentFrame world frame)).2.1
          · by_cases success : Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key normalized growth world
            · exact ⟨(frame.published ops allocate growth meaning key admitted aligned room success).2,
                publishedParent world frame room failed success⟩
            · by_cases refused : Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key normalized growth world
              · exact ⟨(frame.publication_rollback ops allocate growth meaning key
                    (by simpa only [facts.projected, Option.getD_some] using reads) admitted aligned room refused).2.1,
                  rollbackParent world frame room failed refused⟩
              · exact remaining world frame room failed backing success refused ordinaryResult
        exact ⟨⟨rfl, Or.inl rfl⟩, preserved, matched ordinaryResult⟩
      · rename_i rejected
        intro impossible
        exact False.elim (rejected impossible)
  · have saturated := Nat.le_of_not_gt room
    have model := Interner.observed_insert_capacity (candidate world.graph) key true (succeeds world.graph)
      world.graph (rows ++ added) facts.projected reads
      (by simpa only [facts.projected, Option.getD_some] using saturated)
    simpa only [model, Except.mapError] using
      (frame.capacity_failure ops allocate growth meaning key true lookup detached (logical world frame)
        saturated (parentFrame world frame)).1

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
