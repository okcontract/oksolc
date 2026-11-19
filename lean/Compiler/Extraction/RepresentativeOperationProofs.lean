/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOperation
import Compiler.Extraction.RepresentativeDescriptorRelation
import Compiler.Extraction.StorageOperations

namespace Compiler.Extraction.RepresentativeArray.Operation
open Compiler.ZigAir.Memory Compiler.Algebraic

def returned (slice : Storage.ArgumentSlice) : Value := borrowed ⟨slice.address, 0⟩ slice.items.length

/-- Initial pointee correspondence for just the fields this query reads. A
non-Operation does not need an initialized instruction. Establishing this
relation from native item initialization and preserving it remains separate. -/
def Item (state : State) (cell : Storage.Cell) : Prop :=
  AssemblyItem.Fields.kind state ⟨cell.itemAddress, 0⟩ = .ok cell.item.kind.toNat ∧
  (cell.item.kind = 1#32 → AssemblyItem.Fields.instruction state ⟨cell.itemAddress, 0⟩ = .ok cell.item.instruction)

theorem kind_one_iff (kind : BitVec 32) : (kind.toNat : Int) = 1 ↔ kind = 1#32 := by
  constructor
  · intro equal
    apply BitVec.eq_of_toNat_eq
    change kind.toNat = 1
    omega
  · rintro rfl; rfl

/-- Complete descriptor correspondence supplies both field reads, while the
initial item relation supplies the conditional pointee reads. The resulting
descriptor keeps the original allocation and length, with const permission. -/
theorem read_row (state : State) (lifetime index : Nat) (cell : Storage.Cell) (opcode : BitVec 8)
    (row : DescriptorRelation.Row state lifetime index cell) (item : Item state cell) :
    read state ⟨lifetime, index * 32⟩ opcode =
      .ok ((Storage.operationResult cell opcode).map (Option.map returned)) := by
  have fields := Expression.readFields_parts state false ⟨lifetime, index * 32⟩ _ _ _ _ row
  have args := arguments_from_field state ⟨lifetime, index * 32⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length fields.2.1
  simp only [read, fields.1, bind, Except.bind, ne_self_iff_false, ↓reduceIte, item.1,
    Storage.operationProgram]
  by_cases kind : cell.item.kind = 1#32
  · have native := (kind_one_iff cell.item.kind).mpr kind
    have instruction := item.2 kind
    rw [native]
    cases optional : cell.item.instruction with
    | none => simp [instruction, optional, Storage.operationResult, kind, pure, Except.pure, Except.map]
    | some actual =>
      by_cases equal : actual = opcode <;>
        simp [instruction, optional, Storage.operationResult, kind, equal, args,
          pure, Except.pure, Except.map, returned, Storage.Cell.argumentSlice]
  · have native : (cell.item.kind.toNat : Int) ≠ 1 := fun equal => kind ((kind_one_iff cell.item.kind).mp equal)
    simp [native, Storage.operationResult, kind, pure, Except.pure, Except.map]

/-- Exact all-ID query correspondence in one initial memory. No successful
query, final observation or argument-content read is a premise. This consumes
initial descriptor/item relations, not an assumed native graph invariant. -/
theorem query (state : State) (header : Address) (lifetime capacity : Nat) (backing : Allocation)
    (cells : List Storage.Cell) (id : NodeId) (opcode : BitVec 8) (valid : state.valid = true)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (found : state.heap.lookup lifetime = some backing) (typed : backing.type = .array capacity Expression.allocationType)
    (writable : backing.writable = true) (extent : cells.length ≤ capacity)
    (represented : DescriptorRelation.Prefix state lifetime cells) (items : ∀ cell ∈ cells, Item state cell) :
    run state header id opcode = .ok ((Storage.operationProgram.run cells id opcode).map (Option.map returned)) := by
  rw [Storage.operation_correct]
  by_cases inside : id.toNat < cells.length
  · have selected := representative_from_array state header lifetime capacity cells.length backing id valid loaded found typed writable extent inside
    have row := represented id.toNat cells[id.toNat] (List.getElem?_eq_getElem inside)
    have fields := read_row state lifetime id.toNat cells[id.toNat] opcode row (items _ (List.getElem_mem inside))
    simp only [run, selected, bind, Except.bind, ne_self_iff_false, ↓reduceIte, fields, List.getElem?_eq_getElem inside]
  · rw [invalid_id state header ⟨lifetime, 0⟩ cells.length id opcode loaded (by omega), List.getElem?_eq_none (by omega)]
    rfl

end Compiler.Extraction.RepresentativeArray.Operation
