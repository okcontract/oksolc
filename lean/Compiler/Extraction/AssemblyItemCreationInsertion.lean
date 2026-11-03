/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemCreation
import Compiler.Extraction.AssemblyCloneInsertion

namespace Compiler.Extraction.AssemblyItem.Creation.Insertion
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization
open AssemblyClone (Value)

/-- `object` is the production owned_item local, in the existing session's
lifetime namespace. The clone local and both heaps are reused unchanged. -/
structure State (Metadata σ : Type) where
  clone : AssemblyClone.Physical.Insertion.State Metadata σ
  object : Option Nat := none

inductive Fault where
  | creation (reason : Creation.Fault)
  | insertion (reason : AssemblyClone.Physical.Insertion.Fault)
  | missingObject | alreadyCreated
  deriving DecidableEq, Repr

/-- The existing clone/value/lastValue callbacks own their semantic logic.
Other operations are unavailable here and are dispatched by operations below. -/
def cloneOperations (copy : AssemblyClone.Physical.Allocate σ) (bytes : AssemblyItemDeinit.Release σ)
    (objects : AssemblyItem.Release σ) (external : External σ) (allocator object : Nat) (input : Value Metadata)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ArgumentSlice) :=
  AssemblyClone.Physical.Insertion.operations copy bytes objects external allocator input
    (fun ownership state => ⟨object, arguments ownership state⟩)
    { attempt := fun _ _ state => (.error .missingValue, state)
      release := fun _ _ state => (.error .missingValue, state) }

def operations (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (input : Value Metadata)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ArgumentSlice)
    (rest : Storage.Operations (State Metadata σ) Fault) : Storage.Operations (State Metadata σ) Fault where
  attempt site ownership before := match site with
    | .item => if before.object.isSome then (.error .alreadyCreated, before) else
      let (result, memory) := create allocate allocator input.item before.clone.execution.memory
      let reached := { before with clone := { before.clone with execution := { before.clone.execution with memory } } }
      match result with
      | .ok object => (.ok true, { reached with object := some object })
      | .error .outOfMemory => (.ok false, reached)
      | .error fault => (.error (.creation fault), reached)
    | .clone => match before.object with
      | none => (.error .missingObject, before)
      | some object =>
        let (result, after) := (cloneOperations copy bytes objects external allocator object input arguments).attempt site ownership before.clone
        (result.mapError Fault.insertion, { before with clone := after })
    | _ => rest.attempt site ownership before
  release action ownership before := match action with
    | .allocation => match before.object with
      | none => (.error .missingObject, before)
      | some object =>
        let (result, memory) := destroy objects allocator object before.clone.execution.memory
        (result.mapError (fun reason => Fault.insertion (.destroy (.item (.inr reason)))),
          { clone := { before.clone with execution := { before.clone.execution with memory } }
            object := if result.isOk then none else before.object })
    | .value | .lastValue => match before.object with
      | none => (.error .missingObject, before)
      | some object =>
        let (result, after) := (cloneOperations copy bytes objects external allocator object input arguments).release action ownership before.clone
        (result.mapError Fault.insertion,
          { clone := after, object := if after.execution.invalidated then none else before.object })
    | _ => rest.release action ownership before

theorem create_callback (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator object : Nat) (input : Value Metadata)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ArgumentSlice)
    (rest : Storage.Operations (State Metadata σ) Fault) (ownership : Storage.State) (before : State Metadata σ)
    (allocated : Session σ) (absent : before.object = none) (initial : Valid before.clone.execution.memory)
    (created : create allocate allocator input.item before.clone.execution.memory = (.ok object, allocated)) :
    (operations allocate copy bytes objects external allocator input arguments rest).attempt .item ownership before =
      (.ok true, { clone := { before.clone with execution := { before.clone.execution with memory := allocated } }, object := some object }) ∧
    Created allocator object before.clone.execution.memory allocated := by
  exact ⟨by simp [operations, absent, created], create_verified allocate allocator object input.item _ allocated initial created⟩

/-- Creation establishes the object ownership consumed by clone and complete
rollback. There is no already-owned-object or owned-cloned-payload premise.
Successful observations are checked under the host contracts; native field
assignment and container refinement remain outside this composed statement. -/
theorem create_clone_rollback (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator object : Nat) (input copied : Value Metadata) (arguments : ArgumentSlice)
    (rest : Storage.Operations (State Metadata σ) Fault) (ownership : Storage.State)
    (before allocated middle : Session σ) (initial : Valid before) (live : SliceValid allocator before.heap arguments)
    (created : create allocate allocator input.item before = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run copy allocator input allocated = (.ok copied, middle)) :
    let callbacks := operations allocate copy bytes objects external allocator input (fun _ _ => arguments) rest
    let start : State Metadata σ := ⟨⟨⟨before, false⟩, none⟩, none⟩
    let made : State Metadata σ := ⟨⟨⟨allocated, false⟩, none⟩, some object⟩
    let filled : State Metadata σ := ⟨⟨⟨middle, false⟩, some copied⟩, some object⟩
    callbacks.attempt .item ownership start = (.ok true, made) ∧
    callbacks.attempt .clone ownership made = (.ok true, filled) ∧
    AssemblyClone.Physical.Cloned allocator input copied allocated middle ∧
    ∃ after, callbacks.release .lastValue ownership filled = (.ok (), after) ∧
      after.object = none ∧ after.clone.value = none ∧
      ExpressionDeinit.Lifetime.Post (AssemblyClone.Physical.payload copied) ⟨object, arguments⟩ middle after.clone.execution := by
  dsimp only
  have allocatedPost := create_verified allocate allocator object input.item before allocated initial created
  have copiedPost := AssemblyClone.Physical.run_valid copy allocator input copied allocated middle allocatedPost.valid cloned
  have argumentsLive := allocatedPost.arguments allocator object before allocated initial arguments live
  obtain ⟨after, cleaned, cleared, post⟩ := AssemblyClone.Physical.Insertion.last_value_callback copy bytes objects external allocator
    input copied (fun _ _ => ⟨object, arguments⟩)
    { attempt := fun _ _ state => (.error .missingValue, state)
      release := fun _ _ state => (.error .missingValue, state) }
    ownership ⟨⟨middle, false⟩, some copied⟩ rfl rfl copiedPost.valid
    (copiedPost.item allocatedPost.valid object allocatedPost.owned)
    (copiedPost.arguments allocatedPost.valid arguments argumentsLive) copiedPost.owned
  refine ⟨by simp [operations, created], ?_, copiedPost, ⟨after, none⟩, ?_, rfl, cleared, post⟩
  · simp [operations, cloneOperations, AssemblyClone.Physical.Insertion.operations, cloned, Except.mapError]
  · simpa only [operations, cloneOperations, Except.mapError, post.invalidated, ↓reduceIte] using congrArg
      (fun result => (result.1.mapError Fault.insertion,
        ({ clone := result.2, object := if result.2.execution.invalidated then none else some object } : State Metadata σ))) cleaned

/-- On ordinary clone OOM, the successfully created allocation remains owned
and can be destroyed by the actual errdefer callback at the reached effects. -/
theorem clone_oom_release (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator object : Nat) (input : Value Metadata)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ArgumentSlice)
    (rest : Storage.Operations (State Metadata σ) Fault) (ownership : Storage.State)
    (before allocated reached : Session σ) (initial : Valid before)
    (created : create allocate allocator input.item before = (.ok object, allocated))
    (failed : AssemblyClone.Physical.run copy allocator input allocated = (.error .outOfMemory, reached)) :
    ∃ after, (operations allocate copy bytes objects external allocator input arguments rest).release .allocation ownership
      ⟨⟨⟨reached, false⟩, none⟩, some object⟩ = (.ok (), after) ∧ after.object = none ∧
      Released object reached after.clone.execution.memory ∧ after.clone.execution.memory.effects = objects object reached := by
  have post := create_verified allocate allocator object input.item before allocated initial created
  obtain ⟨heap, memory⟩ := AssemblyClone.Physical.run_oom copy allocator input allocated reached failed
  have valid : Valid reached := ⟨by simpa only [memory] using post.valid.memory,
    by simpa only [heap, memory] using post.valid.related,
    by simpa only [heap, memory] using post.valid.injected⟩
  have owned : Owned allocator object reached := by simpa only [Owned, heap, memory] using post.owned
  obtain ⟨after, released, cleared, effects⟩ := destroy_verified objects allocator object reached valid owned
  exact ⟨⟨⟨⟨after, false⟩, none⟩, none⟩, by simp [operations, released, Except.mapError, Except.isOk, Except.toBool], rfl, cleared, effects⟩

end Compiler.Extraction.AssemblyItem.Creation.Insertion
