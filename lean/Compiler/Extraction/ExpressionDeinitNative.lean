/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitFields
import Compiler.Extraction.ExpressionInvalidation
import Compiler.Extraction.AssemblyItemDeinitNative

namespace Compiler.Extraction.ExpressionDeinit.Native
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory (Address)

inductive Fault where
  | fields (reason : Fields.Fault)
  | item (reason : AssemblyItemDeinit.Native.Fault)
  | allocation (reason : Memory.Arguments.ReleaseFault)
  | arguments (reason : Failure)
  | invalidation (reason : Compiler.ZigAir.Memory.Fault)
  | invalidDescriptor
  deriving DecidableEq, Repr

/-- Read each field at the source stage which consumes it. In particular the
item pointer is read again before destroy, and arguments are read only after
item destruction. Later rejection retains every earlier free and private effect.
The item destructor's own invalidation marker never invalidates this row. -/
def step (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (descriptor : Address) (stage : Stage) (before : State σ) : Except Fault Unit × State σ :=
  if before.invalidated then (.error .invalidDescriptor, before) else
  match stage with
  | .itemValue =>
    match Fields.item before.memory.memory descriptor with
    | .error reason => (.error (.fields reason), before)
    | .ok object =>
      let (result, reached) := AssemblyItemDeinit.Native.run bytes allocator object before.memory
      (result.mapError Fault.item, { before with memory := reached.memory })
  | .itemAllocation =>
    match Fields.item before.memory.memory descriptor with
    | .error reason => (.error (.fields reason), before)
    | .ok object =>
      if object.offset ≠ 0 then (.error (.allocation (.ownership .bounds)), before) else
      let (result, reached) := AssemblyItem.destroy objects allocator object.allocation before.memory
      (result.mapError Fault.allocation, { before with memory := reached })
  | .arguments =>
    match Fields.arguments before.memory descriptor with
    | .error reason => (.error (.fields reason), before)
    | .ok slice =>
      let (result, reached) := free external allocator slice before.memory
      (result.mapError Fault.arguments, { before with memory := reached })
  | .invalidate =>
    match Expression.invalidate before.memory.memory descriptor with
    | .error reason => (.error (.invalidation reason), before)
    | .ok memory => (.ok (), ⟨{ before.memory with memory }, true⟩)

def run (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (descriptor : Address) (before : Session σ) : Except Fault Unit × State σ :=
  executeStages (step bytes objects external allocator descriptor) expressionDeinitCode ⟨before, false⟩

theorem item_stage (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (descriptor object : Address) (before : Session σ)
    (read : Fields.item before.memory descriptor = .ok object) :
    step bytes objects external allocator descriptor .itemValue ⟨before, false⟩ =
      let (result, reached) := AssemblyItemDeinit.Native.run bytes allocator object before
      (result.mapError Fault.item, ⟨reached.memory, false⟩) := by
  simp only [step, Bool.false_eq_true, ↓reduceIte, read]

theorem allocation_stage (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator object : Nat) (descriptor : Address) (before : Session σ)
    (read : Fields.item before.memory descriptor = .ok ⟨object, 0⟩) :
    step bytes objects external allocator descriptor .itemAllocation ⟨before, false⟩ =
      let (result, reached) := AssemblyItem.destroy objects allocator object before
      (result.mapError Fault.allocation, ⟨reached, false⟩) := by
  simp only [step, Bool.false_eq_true, ↓reduceIte, read, ne_self_iff_false]

theorem allocation_interior (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (descriptor object : Address) (before : Session σ)
    (read : Fields.item before.memory descriptor = .ok object) (interior : object.offset ≠ 0) :
    step bytes objects external allocator descriptor .itemAllocation ⟨before, false⟩ =
      (.error (.allocation (.ownership .bounds)), ⟨before, false⟩) := by
  simp only [step, Bool.false_eq_true, ↓reduceIte, read]
  exact if_pos interior

theorem arguments_stage (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (descriptor : Address) (slice : Storage.ArgumentSlice) (before : Session σ)
    (read : Fields.arguments before descriptor = .ok slice) :
    step bytes objects external allocator descriptor .arguments ⟨before, false⟩ =
      let (result, reached) := free external allocator slice before
      (result.mapError Fault.arguments, ⟨reached, false⟩) := by
  simp only [step, Bool.false_eq_true, ↓reduceIte, read]

theorem invalidation_stage (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (descriptor : Address) (before : Session σ) :
    step bytes objects external allocator descriptor .invalidate ⟨before, false⟩ =
      match Expression.invalidate before.memory descriptor with
      | .error reason => (.error (.invalidation reason), ⟨before, false⟩)
      | .ok memory => (.ok (), ⟨{ before with memory }, true⟩) := rfl

end Compiler.Extraction.ExpressionDeinit.Native
