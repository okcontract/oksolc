/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneFields
import Compiler.Extraction.AssemblyItemCreationInsertion

namespace Compiler.Extraction.AssemblyItem.Creation.NativeFields
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization
open AssemblyClone.NativeFields (ItemValue Represents Installed)

abbrev State (σ : Type) := Insertion.State Fields.Values σ

inductive Fault where
  | base (reason : Insertion.Fault)
  | source (reason : AssemblyClone.NativeFields.SourceFault)
  | assignment (reason : Compiler.ZigAir.Memory.Fault)
  deriving DecidableEq, Repr

def installResult (result : Except Compiler.ZigAir.Memory.Fault (Session σ)) (reached : State σ) :
    Except Fault Bool × State σ := match result with
  | .error reason => (.error (.assignment reason), reached)
  | .ok memory => (.ok true, { reached with clone := { reached.clone with execution := { reached.clone.execution with memory } } })

/-- Complete the successful clone callback using its returned local and the
same reached session. Ordinary OOM and semantic faults retain their reached
state. A failed model admission is never turned into ordinary OOM or cleanup. -/
def finish (object : Nat) (result : Except Insertion.Fault Bool) (reached : State σ) :
    Except Fault Bool × State σ := match result with
  | .error reason => (.error (.base reason), reached)
  | .ok false => (.ok false, reached)
  | .ok true => match reached.clone.value with
    | none => (.error (.base (.insertion .missingValue)), reached)
    | some copied => installResult (AssemblyClone.NativeFields.install copied object reached.clone.execution.memory) reached

theorem finish_assigned (object : Nat) (reached : State σ) (copied : ItemValue) (after : Session σ)
    (present : reached.clone.value = some copied)
    (assigned : AssemblyClone.NativeFields.install copied object reached.clone.execution.memory = .ok after) :
    finish object (.ok true) reached =
      (.ok true, { reached with clone := { reached.clone with execution := { reached.clone.execution with memory := after } } }) := by
  simp only [finish, present]
  exact (congrArg (fun result => installResult result reached) assigned).trans (by simp only [installResult, present])

theorem finish_failed (object : Nat) (reached : State σ) (copied : ItemValue) (reason : Compiler.ZigAir.Memory.Fault)
    (present : reached.clone.value = some copied)
    (rejected : AssemblyClone.NativeFields.install copied object reached.clone.execution.memory = .error reason) :
    finish object (.ok true) reached = (.error (.assignment reason), reached) := by
  simp only [finish, present]
  exact congrArg (fun result => installResult result reached) rejected

/-- Reuse creation, clone, insertion and destructor callbacks. Only the missing
`owned_item.* = try item.clone(...)` handoff is added. Initial native source
admission reads every member; byte reads keep the clone's allocation order. -/
def operations (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (source : Compiler.ZigAir.Memory.Address) (input : ItemValue)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Fields.Values σ → ArgumentSlice)
    (rest : Storage.Operations (State σ) Insertion.Fault) : Storage.Operations (State σ) Fault :=
  let base := Insertion.operations allocate copy bytes objects external allocator input arguments rest
  { attempt := fun site ownership before =>
      match site, before.object with
      | .clone, some object =>
        match AssemblyClone.NativeFields.checkSource before.clone.execution.memory.memory source input with
        | .error reason => (.error (.source reason), before)
        | .ok () =>
          let (result, reached) := base.attempt site ownership before
          finish object result reached
      | _, _ =>
        let (result, after) := base.attempt site ownership before
        (result.mapError Fault.base, after)
    release := fun action ownership before =>
      let (result, after) := base.release action ownership before
      (result.mapError Fault.base, after) }

theorem clone_callback_installed (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator object : Nat) (source : Compiler.ZigAir.Memory.Address) (input copied : ItemValue)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Fields.Values σ → ArgumentSlice)
    (rest : Storage.Operations (State σ) Insertion.Fault) (ownership : Storage.State) (before : State σ)
    (middle : Session σ) (present : before.object = some object) (initial : Valid before.clone.execution.memory)
    (represented : Represents before.clone.execution.memory.memory source input)
    (owned : Owned allocator object before.clone.execution.memory)
    (cloned : AssemblyClone.Physical.run copy allocator input before.clone.execution.memory = (.ok copied, middle)) :
    ∃ after, (operations allocate copy bytes objects external allocator source input arguments rest).attempt .clone ownership before =
      (.ok true, { clone := { execution := { before.clone.execution with memory := after }, value := some copied }, object := some object }) ∧
      Installed allocator object copied middle after ∧
      AssemblyClone.NativeFields.install copied object middle = .ok after := by
  obtain ⟨after, assigned, installed⟩ := AssemblyClone.NativeFields.clone_install copy allocator object source
    input copied before.clone.execution.memory middle initial represented owned cloned
  refine ⟨after, ?_, installed, assigned⟩
  have checked := (AssemblyClone.NativeFields.checkSource_iff _ _ _).mpr represented
  let reached : State σ := ⟨⟨{ before.clone.execution with memory := middle }, some copied⟩, before.object⟩
  have finished := finish_assigned object reached copied after rfl assigned
  simp only [operations, present, checked, Insertion.operations, Insertion.cloneOperations,
    AssemblyClone.Physical.Insertion.operations, cloned, Except.mapError]
  generalize @finish σ = finishCallback at finished ⊢
  simpa only [reached, present] using finished

theorem clone_callback (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator object : Nat) (source : Compiler.ZigAir.Memory.Address) (input copied : ItemValue)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Fields.Values σ → ArgumentSlice)
    (rest : Storage.Operations (State σ) Insertion.Fault) (ownership : Storage.State) (before : State σ)
    (middle : Session σ) (present : before.object = some object) (initial : Valid before.clone.execution.memory)
    (represented : Represents before.clone.execution.memory.memory source input)
    (owned : Owned allocator object before.clone.execution.memory)
    (cloned : AssemblyClone.Physical.run copy allocator input before.clone.execution.memory = (.ok copied, middle)) :
    ∃ after, (operations allocate copy bytes objects external allocator source input arguments rest).attempt .clone ownership before =
      (.ok true, { clone := { execution := { before.clone.execution with memory := after }, value := some copied }, object := some object }) ∧
      Installed allocator object copied middle after := by
  obtain ⟨after, called, installed, _⟩ := clone_callback_installed allocate copy bytes objects external allocator object source
    input copied arguments rest ownership before middle present initial represented owned cloned
  exact ⟨after, called, installed⟩

theorem clone_oom (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator object : Nat) (source : Compiler.ZigAir.Memory.Address) (input : ItemValue)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Fields.Values σ → ArgumentSlice)
    (rest : Storage.Operations (State σ) Insertion.Fault) (ownership : Storage.State) (before : State σ)
    (reached : Session σ) (present : before.object = some object)
    (represented : Represents before.clone.execution.memory.memory source input)
    (failed : AssemblyClone.Physical.run copy allocator input before.clone.execution.memory = (.error .outOfMemory, reached)) :
    (operations allocate copy bytes objects external allocator source input arguments rest).attempt .clone ownership before =
      (.ok false, { before with clone := { before.clone with execution := { before.clone.execution with memory := reached } } }) := by
  have checked := (AssemblyClone.NativeFields.checkSource_iff _ _ _).mpr represented
  simp only [operations, present, checked, Insertion.operations, Insertion.cloneOperations,
    AssemblyClone.Physical.Insertion.operations, failed, Except.mapError, finish]

theorem represented_after_create (before after : Session σ) (allocator object : Nat)
    (source : Compiler.ZigAir.Memory.Address) (input : ItemValue) (initial : Valid before)
    (represented : Represents before.memory source input) (created : Created allocator object before after) :
    Represents after.memory source input := by
  obtain ⟨cell, found⟩ := represented.live
  have older := (Compiler.ZigAir.Memory.valid_lookup before.memory source.allocation cell initial.memory found).1
  exact represented.frame (created.frame source.allocation (by rw [created.fresh]; omega)).2

/-- Creation supplies item ownership, initial native reads supply all field
values, and actual clone execution supplies payload ownership. Complete field
assignment precedes the existing last-value cleanup in the same execution. -/
theorem create_clone_rollback (allocate : Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator object : Nat) (source : Compiler.ZigAir.Memory.Address) (input copied : ItemValue) (arguments : ArgumentSlice)
    (rest : Storage.Operations (State σ) Insertion.Fault) (ownership : Storage.State)
    (before allocated middle : Session σ) (initial : Valid before) (live : SliceValid allocator before.heap arguments)
    (represented : Represents before.memory source input)
    (created : create allocate allocator input.item before = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run copy allocator input allocated = (.ok copied, middle)) :
    let callbacks := operations allocate copy bytes objects external allocator source input (fun _ _ => arguments) rest
    let start : State σ := ⟨⟨⟨before, false⟩, none⟩, none⟩
    let made : State σ := ⟨⟨⟨allocated, false⟩, none⟩, some object⟩
    callbacks.attempt .item ownership start = (.ok true, made) ∧
    ∃ installed,
      callbacks.attempt .clone ownership made =
        (.ok true, ⟨⟨⟨installed, false⟩, some copied⟩, some object⟩) ∧
      Installed allocator object copied middle installed ∧
      ∃ after, callbacks.release .lastValue ownership ⟨⟨⟨installed, false⟩, some copied⟩, some object⟩ = (.ok (), after) ∧
        after.object = none ∧ after.clone.value = none ∧
        ExpressionDeinit.Lifetime.Post (AssemblyClone.Physical.payload copied) ⟨object, arguments⟩ installed after.clone.execution := by
  dsimp only
  have allocatedPost := create_verified allocate allocator object input.item before allocated initial created
  have copiedPost := AssemblyClone.Physical.run_valid copy allocator input copied allocated middle allocatedPost.valid cloned
  have argumentsLive := copiedPost.arguments allocatedPost.valid arguments
    (allocatedPost.arguments allocator object before allocated initial arguments live)
  obtain ⟨installed, assigned, installedPost⟩ := clone_callback allocate copy bytes objects external allocator object source input copied
    (fun _ _ => arguments) rest ownership ⟨⟨⟨allocated, false⟩, none⟩, some object⟩ middle rfl allocatedPost.valid
    (represented_after_create before allocated allocator object source input initial represented allocatedPost) allocatedPost.owned cloned
  have finalArguments : SliceValid allocator installed.heap arguments := by
    rw [installedPost.heap]; exact argumentsLive
  obtain ⟨after, cleaned, cleared, post⟩ := AssemblyClone.Physical.Insertion.last_value_callback copy bytes objects external allocator
    input copied (fun _ _ => ⟨object, arguments⟩)
    { attempt := fun _ _ state => (.error .missingValue, state)
      release := fun _ _ state => (.error .missingValue, state) }
    ownership ⟨⟨installed, false⟩, some copied⟩ rfl rfl installedPost.valid installedPost.owned finalArguments installedPost.payload
  refine ⟨by simp [operations, Insertion.operations, created, Except.mapError], installed, assigned, installedPost,
    ⟨after, none⟩, ?_, rfl, cleared, post⟩
  simpa only [operations, Insertion.operations, Insertion.cloneOperations, Except.mapError, post.invalidated, ↓reduceIte] using congrArg
    (fun result => ((result.1.mapError Insertion.Fault.insertion).mapError Fault.base,
      ({ clone := result.2, object := if result.2.execution.invalidated then none else some object } : State σ))) cleaned

end Compiler.Extraction.AssemblyItem.Creation.NativeFields
