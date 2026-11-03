/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionPrimitiveValidity
import Compiler.Extraction.InternerPublicationProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open AssemblyClone (Value)

/-- Existing allocation/copy/release contracts and observed container outcomes.
Append/probe still require native container refinement; putting them in this
interface does not add a trusted host assumption or verify a native container. -/
structure Operations (σ : Type) where
  arguments : External σ
  create : AssemblyItem.Creation.Allocate σ
  copy : AssemblyClone.Physical.Allocate σ
  bytes : AssemblyItemDeinit.Release σ
  objects : AssemblyItem.Release σ
  append : Nat → Session σ → Bool × σ
  probe : OwnedKeys.Physical.Probe σ

/-- Only allocator-private state is returned by external observations. The
existing physical key table remains owned by the publication interpreter. -/
def observe (action : α → Session σ → β × σ) (argument : α) (before : Session (Publication.Effects σ)) :
    β × Publication.Effects σ :=
  let (result, effects) := action argument (Publication.forget before)
  (result, ⟨before.effects.keys, effects⟩)

def release (action : α → Session σ → σ) (argument : α) (before : Session (Publication.Effects σ)) : Publication.Effects σ :=
  ⟨before.effects.keys, action argument (Publication.forget before)⟩

/-- Locals of one insertion, separate from the caller's lookup handle. Both
registries are those already used by normalization, creation and clone. -/
structure State (Metadata σ : Type) where
  item : AssemblyItem.Creation.Insertion.State Metadata (Publication.Effects σ)
  duplicate : Option ArgumentSlice := none

def memory (state : State Metadata σ) : Session (Publication.Effects σ) := state.item.clone.execution.memory
def withMemory (state : State Metadata σ) (next : Session (Publication.Effects σ)) : State Metadata σ :=
  { state with item := { state.item with clone := { state.item.clone with execution := { state.item.clone.execution with memory := next } } } }

inductive Rejection where
  | creation (fault : AssemblyItem.Creation.Insertion.Fault)
  | arguments (fault : Failure)
  | publication (fault : OwnedCall.Fault)
  | missingArguments | missingValue | incomingOwnership
  deriving DecidableEq, Repr

def arguments (normalized : ArgumentSlice) (owner : Storage.State) (before : State Metadata σ) : Option ArgumentSlice :=
  if owner.aliasesNormalized then some normalized else before.duplicate

/-- Check the exact incoming argument descriptor before its duplicate. This is
an admission check in the model, not an added native compiler branch. -/
def ownsArguments (allocator : Nat) (slice : ArgumentSlice) (heap : Memory.Heap) : Bool :=
  if slice.items.isEmpty then true else match heap slice.address with
  | some ⟨owner, .arguments values⟩ => decide (owner = allocator ∧ values = slice.items)
  | _ => false

def itemOperations (ops : Operations σ) (allocator : Nat) (input : Value Metadata) (normalized : ArgumentSlice)
    (owner : Storage.State) (before : State Metadata σ) :=
  AssemblyItem.Creation.Insertion.operations (observe ops.create) (observe ops.copy) (release ops.bytes) (release ops.objects)
    (Publication.external ops.arguments) allocator input
    (fun _ _ => (arguments normalized owner before).getD ⟨0, []⟩)
    { attempt := fun _ _ state => (.error .missingObject, state)
      release := fun _ _ state => (.error .missingObject, state) }

def callbacks (ops : Operations σ) (allocator count : Nat) (source : View) (input : Value Metadata)
    (key : Key) (normalized : ArgumentSlice) (graph : Storage.State → State Metadata σ → Interner.Heap) :
    Storage.Operations (State Metadata σ) Rejection where
  attempt site owner before := match site with
    | .arguments =>
      if !ownsArguments allocator normalized (memory before).heap then (.error .incomingOwnership, before) else
      let handle : Handle := ⟨Arguments.view normalized, normalized.items, none⟩
      let (result, after) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator handle (memory before)
      let reached := withMemory before after
      match result with
      | .ok (slice, _) => (.ok true, { reached with duplicate := some slice })
      | .error .outOfMemory => (.ok false, reached)
      | .error fault => (.error (.arguments fault), reached)
    | .item | .clone =>
      let (result, after) := (itemOperations ops allocator input normalized owner before).attempt site owner before.item
      (result.mapError Rejection.creation, { before with item := after })
    | .append =>
      if before.item.object.isNone || before.item.clone.value.isNone || (arguments normalized owner before).isNone then
        (.error .missingValue, before)
      else
        let (result, effects) := observe ops.append count (memory before)
        (.ok result, withMemory before { memory before with effects })
    | .publish =>
      let (result, after) := Publication.publish ops.probe ops.arguments allocator source key normalized (BitVec.ofNat 32 count)
        ⟨graph owner before, memory before⟩
      let reached := withMemory before after.memory
      match result with
      | .ok () => (.ok true, reached)
      | .error (.language .outOfMemory) => (.ok false, reached)
      | .error fault => (.error (.publication fault), reached)
  release action owner before := match action with
    | .normalized =>
      let (result, after) := free (Publication.external ops.arguments) allocator normalized (memory before)
      (result.mapError Rejection.arguments, withMemory before after)
    | .arguments => match arguments normalized owner before with
      | none => (.error .missingArguments, before)
      | some slice =>
        let (result, after) := free (Publication.external ops.arguments) allocator slice (memory before)
        (result.mapError Rejection.arguments, withMemory before after)
    | .allocation | .value =>
      let (result, after) := (itemOperations ops allocator input normalized owner before).release action owner before.item
      (result.mapError Rejection.creation, { before with item := after })
    | .lastValue => match arguments normalized owner before with
      | none => (.error .missingArguments, before)
      | some _ =>
        let (result, after) := (itemOperations ops allocator input normalized owner before).release action owner before.item
        (result.mapError Rejection.creation, { before with item := after })
    | .pop => (.ok (), before)

/-- The word value is the existing ghost denotation, not a native computation.
The item and allocation descriptors come from the actual reached local values.
An absent local is never admitted as a successful inserted representative. -/
def cell (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (value : Word)
    (owner : Storage.State) (state : State Metadata σ) : Storage.Cell :=
  { item := (state.item.clone.value.getD input).item
    itemAddress := state.item.object.getD 0
    arguments := ((arguments normalized owner state).getD normalized).items
    argumentsAddress := ((arguments normalized owner state).getD normalized).address
    sequence := key.sequence
    otherValue := value }

def execution (ops : Operations σ) (allocator : Nat) (source : View) (meaning : Meaning) (input : Value Metadata)
    (key : Key) (normalized : ArgumentSlice) (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ)) :=
  let value := (key.eval meaning before.graph.read).getD 0
  let projection := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  Storage.insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
    (callbacks ops allocator cells.length source input key normalized projection) {}
    ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
