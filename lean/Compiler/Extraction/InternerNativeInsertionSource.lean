/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingInsertionCoverage

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Source validity needs only its own native allocation to survive. Empty
sentinels impose no allocation restriction. -/
theorem Good.source_frame {source : View} {values : List NodeId} {before after : World σ}
    (good : Good source values before) (valid : Valid after.memory)
    (kept : source.length ≠ 0 → ∀ cell, before.memory.memory.heap.lookup source.allocation = some cell →
      after.memory.memory.heap.lookup source.allocation = some cell) : Good source values after := by
  refine ⟨valid, ?_⟩
  by_cases empty : values = []
  · exact ⟨good.2.1, by intro index inside; simp [empty] at inside⟩
  · have nonempty : source.length ≠ 0 := by
      have size := good.2.1
      exact fun zero => empty (List.eq_nil_of_length_eq_zero (by omega))
    obtain ⟨cell, found⟩ := good.backed nonempty
    exact represented_frame source values good.2 ((kept nonempty cell found).trans found.symm)

namespace ConstructorItem.NativeRecursion

section
variable {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}

/-- Capacity and allocation failures reuse the existing native private-frame
proofs; source preservation is independent of the graph's logical read function. -/
theorem CallFrame.unpublished_source
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (outcome : Option Storage.Outcome) (closed : Storage.State) (after : Insertion.Native.Frame σ)
    (executed : Insertion.Native.execution ops allocate safety allocator owner source address meaning native key normalized
      deterministic (world.graph.representatives.getD []) world growth = ((.ok outcome, closed), after))
    (unappended : closed.appended = false) (unpublished : closed.published = false)
    (valid : Valid (Insertion.memory after))
    (retained : Insertion.Native.PrivateFrame normalized world.memory (Insertion.memory after)) :
    Good source values (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized
      deterministic growth world).2 := by
  obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
  simp only [facts.projected, Option.getD_some] at executed
  rw [Insertion.Native.insert_unpublished_projected ops allocate safety allocator owner source address meaning native key normalized
    deterministic world (rows ++ added) growth data (readHeader_items _ _ _ _ facts.header) facts.projected
    outcome closed after unappended unpublished executed]
  apply frame.1.2.1.source_frame valid
  intro nonempty cell found
  have valuesNonempty : values ≠ [] := by
    intro empty
    exact nonempty (by simpa only [empty, List.length_nil] using frame.1.2.1.2.1.symm)
  exact (retained.allocations _ cell found (fun _ => frame.1.2.2.2 valuesNonempty)).1

/-- Every admitted ordinary insertion outcome retains the caller's source.
The exhaustive source coverage and existing publication, rollback, transfer and
allocation proofs supply the result; no final graph or cleanup contract is assumed. -/
theorem CallFrame.insertion_source
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) :
    ordinary (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized
      deterministic growth world).1 = true →
    Good source values (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized
      deterministic growth world).2 := by
  intro completed
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1.1
  have nonemptyValues : source.length ≠ 0 → values ≠ [] := by
    intro nonempty empty
    exact nonempty (by simpa only [empty, List.length_nil] using frame.1.2.1.2.1.symm)
  by_cases room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1
  · have covered := Insertion.Native.insert_insertion_coverage ops allocate safety deterministic allocator owner source address native key
      normalized (rows ++ added) meaning growth world data capacity facts custody.live frame.2.1 domain (fun _ => admitted)
      (by simpa only [facts.projected, Option.getD_some] using room) completed
    rcases covered with preparation | backing | ⟨selected, published | refused⟩ | ⟨selected, transferred⟩
    · obtain ⟨after, closed, executed, unappended, unpublished, valid, _, retained⟩ :=
        Insertion.Native.preparation_oom_execution_at ops allocate growth safety allocator owner source address meaning native key normalized
          deterministic (world.graph.representatives.getD []) world facts.valid custody.live frame.2.1 admitted room preparation
      exact frame.unpublished_source ops allocate growth meaning key deterministic (some .allocationFailure) closed after
        executed unappended unpublished valid retained
    · obtain ⟨after, executed, valid, retained, _⟩ := frame.backing_oom_execution_at ops allocate deterministic growth meaning key room admitted backing
      exact frame.unpublished_source ops allocate growth meaning key deterministic (some .allocationFailure)
        (Insertion.Native.appendFailureState deterministic) after executed
        (by cases deterministic <;> rfl) (by cases deterministic <;> rfl) valid retained
    · subst deterministic
      obtain ⟨_, _, _, _, _, beforeFacts, post⟩ := frame.published_frame ops allocate growth meaning key admitted aligned room published
      obtain ⟨_, _, afterFacts⟩ := post.native
      have apart := frame.arraySource.storage beforeFacts
      exact frame.1.2.1.source_frame afterFacts.valid (fun nonempty cell found =>
        post.memory _ cell found (apart nonempty).1 (apart nonempty).2
          (fun old stored length => privateSource key old stored length nonempty))
    · subst deterministic
      obtain ⟨_, _, _, _, beforeFacts, post⟩ := frame.publication_rollback_frame ops allocate growth meaning key admitted aligned room refused
      obtain ⟨_, _, afterFacts⟩ := post.native
      have apart := frame.arraySource.storage beforeFacts
      exact frame.1.2.1.source_frame afterFacts.valid (fun nonempty cell found =>
        (post.retained _ cell found (apart nonempty).1 (apart nonempty).2
          (fun _ => frame.1.2.2.2 (nonemptyValues nonempty))).1)
    · subst deterministic
      obtain ⟨_, _, _, _, _, beforeFacts, post⟩ := frame.transferred ops allocate growth meaning key room transferred
      obtain ⟨_, _, afterFacts⟩ := post.native
      have apart := frame.arraySource.storage beforeFacts
      exact frame.1.2.1.source_frame afterFacts.valid (fun nonempty cell found =>
        post.memory _ cell found (apart nonempty).1 (apart nonempty).2)
  · obtain ⟨released, freed, valid, post, _⟩ := free_valid (Publication.external ops.arguments) allocator normalized
      world.memory facts.valid custody.live
    have executed := Insertion.Native.capacity_execution ops allocate safety allocator owner source address meaning native key normalized
      deterministic (world.graph.representatives.getD []) world growth released (by omega) freed
    exact frame.unpublished_source ops allocate growth meaning key deterministic (some .capacityFailure)
      (Storage.Release.normalized.run Storage.normalizedOwnership) _ executed rfl rfl valid
      (Insertion.Native.free_private_frame _ _ _ _ _ freed post)

end
end ConstructorItem.NativeRecursion
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
