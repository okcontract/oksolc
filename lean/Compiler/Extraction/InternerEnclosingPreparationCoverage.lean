/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingRollbackFrames
import Compiler.Extraction.InternerInsertionPreparationCoverage

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The shared reducer now supplies the actual successful preparation prefix
to its remaining append/publication duty. Existing failure, transfer, publication
and rollback proofs are retained. Native rejection stays explicit and cannot be
turned into a preparation success or an ordinary cleanup claim. -/
theorem Enclosing.insertion_prepared {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    {rows : List Storage.Cell} {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    (frame : CallFrame safety allocator owner rows source request.arguments owned address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = owned.items)
    (remaining : (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      (¬ Insertion.Native.PreparationOOMAt ops allocator native owned deterministic world.memory) →
      (¬ Insertion.Native.BackingAllocationOOMAt ops allocate allocator owner native owned deterministic growth world) →
      (deterministic = true → ¬ Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key owned growth world) →
      (deterministic = true → ¬ Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key owned growth world) →
      (deterministic = false → ¬ Insertion.Native.TransferredObservation ops allocate allocator owner native growth world) →
      Insertion.Native.PreparationSuccessAt ops allocator native owned deterministic world.memory →
      let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
        source address meaning native key slice deterministic growth) : Action (Publication.Effects σ) NodeId)
        ⟨world, ⟨some lookup, some owned, false⟩⟩
      FramePost (GraphFrame safety allocator owner rows parent)
        (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2)) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice deterministic growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some owned, false⟩⟩
    FramePost (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2) := by
  refine stack.insertion_rollback_derived initial origin frame ops allocate growth meaning key deterministic admitted aligned ?_
  intro room preparation backing publication refused transferred
  dsimp only
  intro completed
  have finished := finish_handoff (Publication.external ops.arguments) allocator lookup owned world
    (fun slice => Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice deterministic growth)
    origin.detached
  have result := congrArg Prod.fst finished
  simp only [apply_ite, ite_self] at result
  have ordinaryInsert : ordinary (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key owned
      deterministic growth world).1 = true := by
    simpa only [bind, Effect.bind, handoff, graph] using
      (congrArg ordinary result).symm.trans completed
  obtain ⟨added, data, capacity, facts, _⟩ := frame.1.1
  have covered := Insertion.Native.insert_preparation_coverage ops allocate safety allocator owner source address native key owned
    (rows ++ added) growth meaning deterministic world data facts.projected (readHeader_items _ _ _ _ facts.header)
    (by simpa only [facts.projected, Option.getD_some] using room) ordinaryInsert
  rcases covered with failed | prepared
  · exact (preparation failed).elim
  · exact remaining room preparation backing publication refused transferred prepared completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
