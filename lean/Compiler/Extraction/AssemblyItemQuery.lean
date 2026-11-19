/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemAssignment
import Compiler.Extraction.RepresentativeOperationProofs

namespace Compiler.Extraction.AssemblyItem.Query
open Compiler.ZigAir.Memory Compiler.Algebraic
open Fields

/-- Connect complete typed member readback to the actual query reader. A typed
i32 is not native enum admission; the captured kind domain remains explicit. -/
theorem of_members (state : State) (logical : Storage.Cell) (cell : Allocation)
    (valid : state.valid = true) (found : state.heap.lookup logical.itemAddress = some cell)
    (typed : cell.type = viewType) (domain : (logical.item.kind.toNat : Int) ∈ itemTagValues)
    (kindRead : member state ⟨logical.itemAddress, 0⟩ .kind = .ok (.scalar (.int true 32 logical.item.kind.toNat)))
    (instructionRead : member state ⟨logical.itemAddress, 0⟩ .instruction = .ok (OptionalScalar.byteValue logical.item.instruction)) :
    RepresentativeArray.Operation.Item state logical := by
  rw [member, readTyped_from_root state logical.itemAddress _ cell _ valid found typed] at kindRead instructionRead
  have nativeKind : read state ⟨logical.itemAddress, 0⟩ item_typeOffset =
      .ok (.scalar (.int true 32 logical.item.kind.toNat)) := by
    rw [read_from_root state logical.itemAddress item_typeOffset cell _ valid found typed
      (show fieldType viewType item_typeOffset = some (.scalar (.int true 32)) by decide)]
    exact kindRead
  have nativeInstruction : read state ⟨logical.itemAddress, 0⟩ instruction_valueOffset =
      .ok (OptionalScalar.byteValue logical.item.instruction) := by
    rw [read_from_root state logical.itemAddress instruction_valueOffset cell _ valid found typed instruction_field_checked]
    exact instructionRead
  constructor
  · rw [kind, tag_of_read state ⟨logical.itemAddress, 0⟩ item_typeOffset itemTagValues _ nativeKind, if_pos domain]
  · intro _
    rw [Fields.instruction, Fields.optional, OptionalField.offset, nativeInstruction]
    exact OptionalScalar.bytePayload_value logical.item.instruction

/-- Preserve conditional reads, including rejection and absent instruction,
from the exact owning allocation. No final successful read is assumed. -/
theorem frame (before after : State) (logical : Storage.Cell)
    (same : after.heap.lookup logical.itemAddress = before.heap.lookup logical.itemAddress)
    (represented : RepresentativeArray.Operation.Item before logical) :
    RepresentativeArray.Operation.Item after logical := by
  simpa only [RepresentativeArray.Operation.Item, kind, tag, Fields.instruction, Fields.optional,
    read_frame before after ⟨logical.itemAddress, 0⟩ _ same] using represented

end Compiler.Extraction.AssemblyItem.Query
