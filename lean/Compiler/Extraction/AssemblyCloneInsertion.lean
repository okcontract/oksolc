/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyClonePhysical

namespace Compiler.Extraction.AssemblyClone.Physical.Insertion
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The returned clone value is a local of the insertion execution, not another
heap. Native assignment/field projection and container storage remain obligations. -/
structure State (Metadata σ : Type) where
  execution : ExpressionDeinit.State σ
  value : Option (Value Metadata) := none

inductive Fault where
  | clone (reason : Physical.Fault)
  | value (reason : AssemblyItemDeinit.Fault)
  | destroy (reason : ExpressionDeinit.Fault ExpressionDeinit.Lifetime.ItemFault)
  | missingValue
  deriving DecidableEq, Repr

def operations (request : Allocate σ) (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ)
    (external : External σ) (allocator : Nat) (input : Value Metadata)
    (target : Storage.State → State Metadata σ → ExpressionDeinit.Descriptor)
    (rest : Storage.Operations (State Metadata σ) Fault) : Storage.Operations (State Metadata σ) Fault where
  attempt site ownership before := match site with
    | .clone =>
      let (result, memory) := run request allocator input before.execution.memory
      let reached := { before with execution := { before.execution with memory } }
      match result with
      | .ok copied => (.ok true, { reached with value := some copied })
      | .error .outOfMemory => (.ok false, reached)
      | .error fault => (.error (.clone fault), reached)
    | _ => rest.attempt site ownership before
  release action ownership before := match action with
    | .value => if before.execution.invalidated then (.error (.destroy .invalidDescriptor), before) else match before.value with
      | none => (.error .missingValue, before)
      | some copied =>
        let (result, after) := AssemblyItemDeinit.run bytes allocator (payload copied) before.execution.memory
        let reached : State Metadata σ := {
          execution := { before.execution with memory := after.memory }
          value := if after.invalidated then none else before.value }
        (result.mapError Fault.value, reached)
    | .lastValue => if before.execution.invalidated then (.error (.destroy .invalidDescriptor), before) else match before.value with
      | none => (.error .missingValue, before)
      | some copied =>
        let (result, after) := ExpressionDeinit.Lifetime.run bytes objects external allocator
          (fun _ => payload copied) (target ownership before) before.execution.memory
        (result.mapError Fault.destroy, { execution := after, value := if after.invalidated then none else before.value })
    | _ => rest.release action ownership before

theorem clone_callback (request : Allocate σ) (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ)
    (external : External σ) (allocator : Nat) (input copied : Value Metadata)
    (target : Storage.State → State Metadata σ → ExpressionDeinit.Descriptor)
    (rest : Storage.Operations (State Metadata σ) Fault) (ownership : Storage.State) (before : State Metadata σ)
    (middle : Session σ) (valid : Valid before.execution.memory)
    (cloned : run request allocator input before.execution.memory = (.ok copied, middle)) :
    (operations request bytes objects external allocator input target rest).attempt .clone ownership before =
      (.ok true, { execution := { before.execution with memory := middle }, value := some copied }) ∧
    Cloned allocator input copied before.execution.memory middle := by
  exact ⟨by simp [operations, cloned], run_valid request allocator input copied before.execution.memory middle valid cloned⟩

theorem last_value_callback (request : Allocate σ) (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ)
    (external : External σ) (allocator : Nat) (input copied : Value Metadata)
    (target : Storage.State → State Metadata σ → ExpressionDeinit.Descriptor)
    (rest : Storage.Operations (State Metadata σ) Fault) (ownership : Storage.State) (before : State Metadata σ)
    (present : before.value = some copied) (ready : before.execution.invalidated = false) (initial : Valid before.execution.memory)
    (object : AssemblyItem.Owned allocator (target ownership before).item before.execution.memory)
    (arguments : SliceValid allocator before.execution.memory.heap (target ownership before).arguments)
    (owned : ∀ slice, payload copied = some slice → AssemblyItemDeinit.Owned allocator slice before.execution.memory) :
    ∃ after, (operations request bytes objects external allocator input target rest).release .lastValue ownership before =
      (.ok (), after) ∧ after.value = none ∧
      ExpressionDeinit.Lifetime.Post (payload copied) (target ownership before) before.execution.memory after.execution := by
  obtain ⟨after, destroyed, post⟩ := ExpressionDeinit.Lifetime.run_verified bytes objects external allocator
    (fun _ => payload copied) (target ownership before) before.execution.memory initial object arguments owned
  refine ⟨⟨after, none⟩, ?_, rfl, post⟩
  simp [operations, present, ready, destroyed, Except.mapError, post.invalidated]

end Compiler.Extraction.AssemblyClone.Physical.Insertion
