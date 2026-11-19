/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingPreparationCoverage
import Compiler.Extraction.InternerInsertionOutcomeCoverage

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Exhaust source insertion outcomes and consume the existing case proofs.
No remaining insertion-frame or successful allocation premise is required.
The admitted item tag comes from the constructor producer; ordinary completion
and the existing enclosing cleanup laws retain their original scope. -/
theorem Enclosing.insertion_covered {safety : Bool} {allocator owner : Nat}
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
    (domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice deterministic growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some owned, false⟩⟩
    FramePost (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2) := by
  refine stack.insertion_prepared initial origin frame ops allocate growth meaning key deterministic admitted aligned ?_
  intro room preparation backing publication refused transferred _
  dsimp only
  intro completed
  have finished := finish_handoff (Publication.external ops.arguments) allocator lookup owned world
    (fun slice => Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice deterministic growth)
    origin.detached
  have result := congrArg Prod.fst finished
  simp only [apply_ite, ite_self] at result
  have ordinaryInsert : ordinary (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key owned
      deterministic growth world).1 = true := by
    simpa only [bind, Effect.bind, handoff, graph] using (congrArg ordinary result).symm.trans completed
  obtain ⟨added, data, capacity, facts, _⟩ := frame.1.1
  have covered := Insertion.Native.insert_insertion_coverage ops allocate safety deterministic allocator owner source address native key owned
    (rows ++ added) meaning growth world data capacity facts frame.1.2.2.1 frame.2.1 domain (fun _ => admitted)
    (by simpa only [facts.projected, Option.getD_some] using room) ordinaryInsert
  rcases covered with failed | failed | ⟨selected, published | rejected⟩ | ⟨selected, accepted⟩
  · exact (preparation failed).elim
  · exact (backing failed).elim
  · exact (publication selected published).elim
  · exact (refused selected rejected).elim
  · exact (transferred selected accepted).elim

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
