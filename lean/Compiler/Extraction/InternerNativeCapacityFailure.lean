/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeInsertionFailure
import Compiler.Extraction.InternerInsertionCapacity

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Capacity is checked against the actual reached rows, including additions
made by recursive children. Both determinism settings consume the normalized
owner and close detached lookup through the same completion as preparation OOM.
Only the enclosing parent's private-cleanup frame law is supplied. -/
theorem CallFrame.capacity_failure {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (deterministic : Bool) (lookup : Handle) (detached : lookup.owned = none)
    (logical : Interner.Represented meaning world.graph)
    (saturated : 2 ^ 32 - 1 ≤ (world.graph.representatives.getD []).length)
    (parentFrame : ∀ after, Valid after → Insertion.Native.PrivateFrame normalized world.memory after →
      parent { world with memory := after }) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice deterministic growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2
    Returns (GraphFrame safety allocator owner rows parent) actual (.error (.language .capacity)) world.graph ∧
      Consumed normalized actual.2.world.memory := by
  obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
  obtain ⟨released, freed, valid, post, _⟩ := free_valid (Publication.external ops.arguments) allocator normalized
    world.memory facts.valid frame.1.2.2.1
  have executed := Insertion.Native.capacity_execution ops allocate safety allocator owner source address meaning native key normalized
    deterministic (world.graph.representatives.getD []) world growth released saturated freed
  exact frame.insertion_unpublished ops allocate growth meaning key deterministic lookup detached logical
    (some .capacityFailure) (Storage.Release.normalized.run Storage.normalizedOwnership) _ executed rfl rfl
    valid (released_consumed post) (Insertion.Native.free_private_frame _ _ _ _ _ freed post)
    (.error (.language .capacity)) rfl rfl parentFrame

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
