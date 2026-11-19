/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerRecursionEffects
import Compiler.Extraction.InternerTerminalProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Compiler.ZigAir.Memory.WordArray

/-- Force uses publication alone. This is equality of the complete body on
every input and outcome, before applying any preservation or cleanup theorem. -/
theorem forceBody_publish_congr (external : External σ) (budget allocator : Nat)
    (left right : Primitives σ) (queries : Queries) (source buffer : View)
    (id : NodeId) (item : Item) (values : List NodeId) (publish : left.publish = right.publish) :
    forceBody external budget allocator left queries source buffer id item values =
      forceBody external budget allocator right queries source buffer id item values := by
  cases left
  cases right
  cases publish
  rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive

attribute [local irreducible] NativeRecursion.unfold Caller.forceBody

/-- The exact native force caller consumes existing publication, normalization
and deferred cleanup proofs. No constructor model, child preservation, graph
callback contract or successful publication is supplied. Force still requires
the requested equality; it does not prove it by inserting a new representative. -/
theorem production_force_verified (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (env : AddressMask.Environment) (other : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (debug : AssemblyItem.Fields.Values) (depth : Nat)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (item : Item) (values : List NodeId) (id : NodeId) (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value) (expected : Word)
    (good : Good source values before)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted ops.arguments)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read values 0 = some expected)
    (equal : before.graph.read id = some expected) :
    let nativeBase := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth
    let nativeChildren := NativeRecursion.unfold nativeBase owner usizeBits depth
    let actual := (context nativeBase owner usizeBits nativeChildren debug).primitives source address native
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
    Semantic.Verified nativeBase.external base.allocator source values (Dispatch.wordDispatchMeaning env other)
      (Caller.forceBody nativeBase.external base.budget base.allocator actual base.queries source buffer id item values)
      input (fun _ _ => True) := by
  intro nativeBase nativeChildren actual buffer input
  let meaning := Dispatch.wordDispatchMeaning env other
  let checked := Insertion.graphCallbacks ops base.allocator source meaning (fun _ _ => native) actual
  have graphs := Insertion.graph_contracts ops base.allocator source values meaning (fun _ _ => native) actual admitted
  have contracts := Terminal.contracts base.allocator source values checked meaning graphs.1 graphs.2
  have publication : (Terminal.withoutSimplifier checked).publish = actual.publish :=
    (context_publishes ops allocate safety owner meaning base growth owner usizeBits nativeChildren debug source address native).symm
  have same := Caller.forceBody_publish_congr (Publication.external ops.arguments) base.budget base.allocator
    (Terminal.withoutSimplifier checked) actual base.queries source buffer id item values publication
  obtain ⟨validMemory, represented, scratch, _⟩ := caller_buffer before.memory memory pointer source values good.1 good.2 allocated
  have verified := Semantic.force_verified (Publication.external ops.arguments) base.budget base.allocator
    (Terminal.withoutSimplifier checked) base.queries source buffer id item values input
    (Dispatch.wordBaseMeaning env other) expected ⟨validMemory, represented⟩ scratch
    (Publication.external_admitted ops.arguments admitted) contracts.1 contracts.2.toGraphContracts valid evaluated equal
  rw [same] at verified
  exact verified

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
