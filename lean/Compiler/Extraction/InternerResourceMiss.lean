/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeResourceDispatch
import Compiler.Extraction.InternerMissReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ))

/-- The same native guard and reached row prefix consume resource-conditional
child contracts. An inactive guard needs no child law; an ordinary error keeps
the reached frame and exact result just as a successful dispatcher does. -/
theorem selected_resource_preserved (history : World (Publication.Effects σ) → List ε) (stream : List ε)
    (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : World (Publication.Effects σ) → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : (deterministic && (request.item.kind == 1)) = true → ∀ rows,
      (Resource.projection history stream (cursorGraph cursor) (fun world => predicate world ∧
        InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt
          (Nested.storageReads rows) debug children model) :
    let action := selected (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic
    let decision := action before
    let logical := if deterministic && request.item.kind == 1 then
      (dispatchModel seed model usizeBits debug).simplify key (cursorGraph cursor before)
      else (.ok none, cursorGraph cursor before)
    Resource.Admitted history stream action before → ordinary decision.1 = true →
      (predicate decision.2 ∧ InputFrame safety base.allocator owner originalRows source values slice decision.2) ∧
      decision.1 = logical.1.mapError Fault.language ∧ cursorGraph cursor decision.2 = logical.2 := by
  dsimp only [selected]
  split
  · rename_i selected
    obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1
    intro admitted completed
    have included : history ((MissStream.selected
        (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
        request key slice deterministic) before).2 <+: stream := admitted
    simp only [MissStream.selected, selected, ↓reduceIte] at included
    have preserved := dispatcher_resource_projected history stream (cursorGraph cursor) safety owner usizeBits
      (callerContext ops allocate safety owner meaning base growth) children model debug source values address input key slice
      (originalRows ++ added) before data capacity facts aligned
      (fun world => predicate world ∧ InputFrame safety base.allocator owner (originalRows ++ added) source values slice world)
      ⟨initial, InputFrame.initial facts frame.2 custody privateSource⟩ (fun _ held => held.2)
      (coupled selected (originalRows ++ added)) included completed
    obtain ⟨later, backing, bound, reached, retained, privateReached⟩ := preserved.1.2.1
    refine ⟨⟨preserved.1.1, ⟨?_, preserved.1.2.2⟩⟩, ?_⟩
    · exact ⟨added ++ later, backing, bound, by simpa only [List.append_assoc] using reached,
        by simpa only [List.append_assoc] using retained, privateReached⟩
    · simpa only [dispatchModel, cursorGraph, Interner.representativeReads, facts.projected] using preserved.2
  · exact fun _ _ => ⟨⟨initial, frame⟩, rfl, rfl⟩

/-- Resource-conditional children now feed the complete scoped miss. The same
reached-frame suffix proof derives insertion, publication and ordinary failure
cleanup; the original replay theorem retains exact result, scope and close.
The final dispatcher cursor is still an explicit boundary at this layer. -/
theorem scoped_from_resources (history : World (Publication.Effects σ) → List ε) (stream : List ε)
    (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : World (Publication.Effects σ) → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : (deterministic && (request.item.kind == 1)) = true → ∀ rows,
      (Resource.projection history stream (cursorGraph cursor) (fun world => predicate world ∧
        InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt
          (Nested.storageReads rows) debug children model)
    (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let action := selected (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic
    Resource.Admitted history stream action before →
      Completion ops allocate safety owner meaning base growth usizeBits children debug source address input
        request key slice deterministic before handle lookup values leading trailing mismatch ∧
      (ordinary (action before).1 = true → cursor (action before).2 = leading.length →
        Projected ops allocate safety owner meaning base growth usizeBits children debug source address input
          request key slice deterministic before handle lookup cursor model seed leading trailing mismatch) := by
  intro action admitted
  have preserved := selected_resource_preserved ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before history stream cursor model seed predicate values originalRows initial frame aligned coupled admitted
  have complete := from_frame ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before values originalRows aligned (fun completed => (preserved completed).1.2)
    handle lookup leading trailing mismatch detached unowned caller
  refine ⟨complete, fun completed boundary => ?_⟩
  dsimp only [action] at boundary
  have checked := preserved completed
  apply projected ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before handle lookup cursor model seed values leading trailing mismatch complete checked.2.1
  simpa only [cursorGraph, boundary] using checked.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
