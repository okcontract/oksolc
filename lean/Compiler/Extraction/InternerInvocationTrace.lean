/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceScope
import Compiler.Extraction.StorageExecutionTrace

namespace Compiler.Extraction.Interner.InvocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache

/-- One ordered protocol stream. These are callback events, not physical host
calls. Further invocation operations require their own explicit bindings. -/
inductive Event (ν ι : Type) where
  | normalization (event : NormalizationOwnership.Trace.Event ν)
  | insertion (event : Storage.Trace.Event ι)
  /-- One admitted publication's actual probe decision. Old-key retirement is
  internal to that callback and is accounted for by its native memory proof. -/
  | publicationProbe (key : Key) (accepted : Bool)
  /-- Allocation cursors at an actual native constructor entry. This is proof
  instrumentation, not an allocation decision or a returned-value assertion. -/
  | nativeEntry (nextId nextAddress : Nat)
  /-- Allocation cursors at the reached insertion call, after any recursive
  children. This observes native inputs, never a returned cell or graph. -/
  | nativeInsertion (nextId nextAddress : Nat)

/-- Keep every cursor position when selecting a protocol. Foreign slots are
explicit rejections, never fabricated allocation outcomes or skipped events. -/
def normalization : Event ν ι → NormalizationOwnership.Trace.Event ν
  | .normalization event => event
  | .insertion _ => .foreign
  | .publicationProbe _ _ => .foreign
  | .nativeEntry _ _ => .foreign
  | .nativeInsertion _ _ => .foreign

def insertion : Event ν ι → Storage.Trace.Event ι
  | .normalization _ => .foreign
  | .insertion event => event
  | .publicationProbe _ _ => .foreign
  | .nativeEntry _ _ => .foreign
  | .nativeInsertion _ _ => .foreign

def normalizations (events : List (Event ν ι)) := events.map normalization
def insertions (events : List (Event ν ι)) := events.map insertion

@[simp] theorem normalizations_length (events : List (Event ν ι)) :
    (normalizations events).length = events.length := List.length_map _

@[simp] theorem insertions_length (events : List (Event ν ι)) :
    (insertions events).length = events.length := List.length_map _

@[simp] theorem normalizations_append (left right : List (Event ν ι)) :
    normalizations (left ++ right) = normalizations left ++ normalizations right := List.map_append

@[simp] theorem insertions_append (left right : List (Event ν ι)) :
    insertions (left ++ right) = insertions left ++ insertions right := List.map_append

@[simp] theorem normalizations_embed (events : List (NormalizationOwnership.Trace.Event ν)) :
    normalizations (events.map (Event.normalization (ι := ι))) = events := by
  simp [normalizations, normalization, List.map_map, Function.comp_def]

@[simp] theorem insertions_embed (events : List (Storage.Trace.Event ι)) :
    insertions (events.map (Event.insertion (ν := ν))) = events := by
  simp [insertions, insertion, List.map_map, Function.comp_def]

def resources (events : List (Event ν ι)) (mismatch : ν) : Scoped.Resources :=
  NormalizationOwnership.Trace.Scope.resources (normalizations events) mismatch

def operations (events : List (Event ν ι)) (mismatch : ι) : Storage.Operations Nat ι :=
  Storage.Trace.replay (insertions events) mismatch

/-- Publication consumes only the next matching probe slot. Neither a foreign
event nor a different key can be reinterpreted as allocation refusal. -/
def publish (events : List (Event ν ι)) (key : Key) (id : NodeId) : Interner.Action Unit := fun before =>
  let rejected := (.error .safetyFault, { before with allocationCursor := events.length + 1 })
  match events[before.allocationCursor]? with
  | some (.publicationProbe queried accepted) =>
    if queried = key then
      let (result, after) := Interner.publish accepted key id before
      (result, { after with allocationCursor := before.allocationCursor + 1 })
    else rejected
  | _ => rejected

theorem publish_slot (leading trailing : List (Event ν ι)) (key : Key) (id : NodeId) (accepted : Bool) (before : Heap) :
    publish (leading ++ [.publicationProbe key accepted] ++ trailing) key id
      { before with allocationCursor := leading.length } =
      (let called := Interner.publish accepted key id before
       (called.1, { called.2 with allocationCursor := leading.length + 1 })) := by
  cases accepted <;> simp [publish, Interner.publish]

end Compiler.Extraction.Interner.InvocationTrace
