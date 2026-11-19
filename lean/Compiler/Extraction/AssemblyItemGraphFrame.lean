/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemQuery
import Compiler.Extraction.RepresentativeAppendFrame
import Compiler.Extraction.RepresentativeRegisteredPublication

namespace Compiler.Extraction.AssemblyItem.Query
open Compiler.ZigAir.Memory Compiler.Algebraic
open RepresentativeArray

theorem no_descriptor (offset : Nat) : acceptsView viewType offset Expression.allocationType = false := by
  have location (offset : Nat) : Ty.project (fun type => decide (type = Expression.allocationType)) sourceLocationType offset = none := by
    simp [sourceLocationType, sourceNameType, Expression.allocationType, Field.type]
  have debug (offset : Nat) : Ty.project (fun type => decide (type = Expression.allocationType)) debugDataType offset = none := by
    simp only [debugDataType, Ty.project, Field.projectFields, Field.project, location]
    simp [Expression.allocationType]
  simp only [acceptsView, viewType, Ty.project, Field.projectFields, Field.project, Field.type, debug]
  simp [Expression.allocationType, verbatimOptionalType]

/-- Actual pointer/capacity publication preserves the complete item allocation
on success and on either rejected store. Owner separation follows its type. -/
theorem publication_frame (runtimeSafety : Bool) (owner : Nat) (ownerCell : Allocation)
    (data : Address) (capacity : Nat) (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ)
    (logical : Storage.Cell) (cell : Allocation)
    (valid : Compiler.Extraction.Memory.Arguments.Normalization.Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (found : before.memory.heap.lookup logical.itemAddress = some cell) (typed : cell.type = viewType)
    (item : Operation.Item before.memory logical) :
    let after := (Publication.Registered.run (Owner.headerAddress ⟨owner, 0⟩) data capacity before).2
    after.memory.heap.lookup logical.itemAddress = some cell ∧ Operation.Item after.memory logical := by
  have separate := before.memory.heap.lookup_ne_of_type_ne logical.itemAddress owner cell ownerCell found ownerFound
    (by simp [typed, ownerTyped, viewType, Owner.viewType])
  have same := (Publication.Registered.storage runtimeSafety owner ownerCell data capacity before valid ownerFound ownerTyped).2.2.2.2.2.2
    logical.itemAddress separate
  exact ⟨same.trans found, frame before.memory _ logical same item⟩

/-- Every reached owner append preserves the complete item and query reads.
This includes OOM, unsupported growth and partial descriptor assignment. -/
theorem append_frame (runtimeSafety : Bool) (state : State) (owner : Nat) (ownerCell : Allocation)
    (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (logical : Storage.Cell) (cell : Allocation)
    (initial : state.valid = true) (ownerFound : state.heap.lookup owner = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (found : state.heap.lookup logical.itemAddress = some cell) (typed : cell.type = viewType)
    (item : Operation.Item state logical) :
    let after := (Append.Execution.ownerRun runtimeSafety state ⟨owner, 0⟩ itemAddress argumentsAddress argumentsLength id sequence allocate effects).1.2
    after.heap.lookup logical.itemAddress = some cell ∧ Operation.Item after logical := by
  have separate := state.heap.lookup_ne_of_type_ne logical.itemAddress owner cell ownerCell found ownerFound
    (by simp [typed, ownerTyped, viewType, Owner.viewType])
  have selected := Owner.root_header_pointer runtimeSafety state owner ownerCell true initial ownerFound ownerTyped
  simp only [Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected]
  have retained := Append.Execution.run_allocation_frame state (Owner.headerAddress ⟨owner, 0⟩)
    itemAddress argumentsAddress argumentsLength id sequence allocate effects logical.itemAddress cell initial found
    (fun offset => typed.symm ▸ no_descriptor offset) separate
  exact ⟨retained, frame state _ logical (retained.trans found.symm) item⟩

end Compiler.Extraction.AssemblyItem.Query
