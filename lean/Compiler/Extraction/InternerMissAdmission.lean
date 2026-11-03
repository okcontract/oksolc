/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerMissInvocation
import Compiler.Extraction.InternerNativeScopedDispatch

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

/-- The actual guard either retains the initial frame or invokes the existing
native dispatcher preservation theorem. Proper children preserve the current
snapshot; append witnesses compose with the caller's original row prefix.
The cursor is an observation parameter, not yet a complete event-stream binding. -/
theorem selected_preserved (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : World (Publication.Effects σ) → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : (deterministic && (request.item.kind == 1)) = true →
      ∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt (Nested.storageReads rows) debug children model) :
    let p := physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input
    let decision := selected p request key slice deterministic before
    let logical := if deterministic && request.item.kind == 1 then
      (dispatchModel seed model usizeBits debug).simplify key (cursorGraph cursor before)
      else (.ok none, cursorGraph cursor before)
    ordinary decision.1 = true →
      (predicate decision.2 ∧ InputFrame safety base.allocator owner originalRows source values slice decision.2) ∧
      decision.1 = logical.1.mapError Fault.language ∧ cursorGraph cursor decision.2 = logical.2 := by
  dsimp only [selected]
  split
  · rename_i selected
    obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1
    intro completed
    have preserved := simplify_at cursor safety owner
      (callerContext ops allocate safety owner meaning base growth) usizeBits children model seed debug source values address input
      key slice (originalRows ++ added) before predicate initial facts aligned frame.2 custody privateSource
      (coupled selected (originalRows ++ added)) completed
    obtain ⟨later, backing, bound, reached, retained, privateReached⟩ := preserved.1.2.1
    refine ⟨⟨preserved.1.1, ⟨?_, preserved.1.2.2⟩⟩, preserved.2⟩
    exact ⟨added ++ later, backing, bound, by simpa only [List.append_assoc] using reached,
      by simpa only [List.append_assoc] using retained, privateReached⟩
  · exact fun _ => ⟨⟨initial, frame⟩, rfl, rfl⟩

/-- One reached frame supplies all three local suffix inputs. Header and rows
refer to the reached owner, and publication admission uses reached key owners;
neither the original backing nor an unchanged key table is assumed. -/
theorem tail_inputs {safety : Bool} {allocator owner : Nat} {originalRows : List Storage.Cell}
    {source : View} {values : List NodeId} {slice : ArgumentSlice} {key : Key}
    {world : World (Publication.Effects σ)}
    (frame : InputFrame safety allocator owner originalRows source values slice world)
    (aligned : key.arguments = slice.items) :
    Held allocator source values slice world ∧ Publication.Input allocator source key slice world ∧
      ∃ (cells : List Storage.Cell) (backing : Compiler.ZigAir.Memory.Address),
        readItems world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType backing cells.length) ∧
        world.graph.representatives = some cells := by
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1
  exact ⟨frame.2, custody.publication source key aligned privateSource facts.live,
    originalRows ++ added, data, readHeader_items _ _ _ _ facts.header, facts.projected⟩

/-- The complete selected suffix, including actual deferred cleanup, retains
the existing branch-specific guarantees. Selection is the actual source guard
and native dispatcher result, not an independent logical branch premise. -/
def Completion (handle : Handle) (lookup : NormalizationOwnership.State) (values : List NodeId)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (mismatch : Insertion.Native.Fault) : Prop :=
  let p := physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input
  match (selected p request key slice deterministic before).1 with
  | .ok none => ∃ cells, (selected p request key slice deterministic before).2.graph.representatives = some cells ∧
      Inserted ops allocate safety owner meaning base growth owner usizeBits children debug source address input
      request key slice deterministic before handle lookup leading trailing cells mismatch
  | .ok (some id) => Published ops allocate safety owner meaning base growth owner usizeBits children debug source address input
      request key slice deterministic before handle lookup values id leading trailing
  | .error fault => Failed (Publication.external ops.arguments) base.allocator p request key slice deterministic before
      handle lookup source values fault leading trailing

/-- The actual selected frame supplies insertion, publication and failure
cleanup. This common suffix proof is independent of the relation used to prove
the dispatcher: ordinary failures still retain the reached ownership frame. -/
theorem from_frame (values : List NodeId) (originalRows : List Storage.Cell)
    (aligned : key.arguments = slice.items)
    (preserved :
      let decision := selected (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
        request key slice deterministic before
      ordinary decision.1 = true → InputFrame safety base.allocator owner originalRows source values slice decision.2)
    (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    Completion ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup values leading trailing mismatch := by
  dsimp only [Completion]
  split
  · rename_i chosen
    have ready := tail_inputs (preserved (by simp only [chosen, ordinary])) aligned
    obtain ⟨cells, backing, header, rows⟩ := ready.2.2
    exact ⟨cells, rows, inserted ops allocate safety owner meaning base growth owner usizeBits children debug source address input
      request key slice deterministic before handle lookup leading trailing cells backing mismatch chosen header rows detached unowned caller⟩
  · rename_i id chosen
    have ready := tail_inputs (preserved (by simp only [chosen, ordinary])) aligned
    exact published ops allocate safety owner meaning base growth owner usizeBits children debug source address input
      request key slice deterministic before handle lookup values id leading trailing chosen ready.1 ready.2.1 detached unowned caller
  · rename_i fault chosen
    apply failed (Publication.external ops.arguments) base.allocator _ request key slice deterministic before handle lookup source values
      fault leading trailing chosen ?_ detached unowned caller
    intro completed
    exact (preserved (by simpa only [chosen, ordinary] using completed)).2


/-- A proper-child induction hypothesis and the caller's initial valid frame
derive the selected insertion, publication or error suffix. No reached header,
row projection, publication admission or cleanup ownership premise remains.
Dispatcher events and the leading stream boundary still need composition. -/
theorem from_children (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : World (Publication.Effects σ) → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : (deterministic && (request.item.kind == 1)) = true →
      ∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    Completion ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup values leading trailing mismatch := by
  have preserved := selected_preserved ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before cursor model seed predicate values originalRows initial frame aligned coupled
  exact from_frame ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before values originalRows aligned (fun completed => (preserved completed).1.2)
    handle lookup leading trailing mismatch detached unowned caller

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
