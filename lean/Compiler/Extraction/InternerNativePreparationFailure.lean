/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeInsertionFailure
import Compiler.Extraction.InternerInsertionPreparationOutcome

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The actual duplicate/create/clone failure consumes the reached normalized
owner, retains native graph correspondence and closes the caller's detached
lookup after handoff. Every cleanup prefix uses the same source projection and
private-owner frame. Only the enclosing parent's local frame law is supplied;
no final native graph, caller result or normalization origin is a premise.
Logical allocation-outcome coupling and other insertion exits remain separate. -/
theorem CallFrame.preparation_oom {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (lookup : Handle) (detached : lookup.owned = none)
    (logical : Interner.Represented meaning world.graph)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (admitted : Admitted ops.arguments)
    (failed : Insertion.Native.PreparationOOM ops allocator native normalized world.memory)
    (parentFrame : ∀ after, Valid after → Insertion.Native.PrivateFrame normalized world.memory after →
      parent { world with memory := after }) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice true growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2
    Returns (GraphFrame safety allocator owner rows parent) actual (.error (.language .outOfMemory)) world.graph ∧
      Consumed normalized actual.2.world.memory := by
  obtain ⟨added, data, capacity, facts, custody, _⟩ := frame.1.1
  have roomRows : (rows ++ added).length < 2 ^ 32 - 1 := by simpa only [facts.projected, Option.getD_some] using room
  obtain ⟨after, closed, executed, unappended, unpublished, valid, consumed, retained⟩ :=
    Insertion.Native.preparation_oom_execution ops allocate growth safety allocator owner source address meaning native key normalized
      (rows ++ added) world facts.valid frame.1.2.2.1 frame.2.1 admitted roomRows failed
  exact frame.insertion_unpublished ops allocate growth meaning key true lookup detached logical
    (some .allocationFailure) closed after (by simpa only [facts.projected, Option.getD_some] using executed)
    unappended unpublished valid consumed retained
    (.error (.language .outOfMemory)) rfl rfl parentFrame

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
