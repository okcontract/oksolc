/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOperationProofs

namespace Compiler.Extraction.RepresentativeArray.Constant
open Compiler.ZigAir.Memory Compiler.Algebraic

/-- Only Push queries read this scalar member. The relation names the actual
item allocation and field, rather than a successful constant-query result. -/
def Data (state : State) (cell : Storage.Cell) : Prop :=
  cell.item.kind = 2#32 →
    AssemblyItem.Fields.readTyped state ⟨cell.itemAddress, 0⟩ AssemblyItem.data_valueOffset
      (.scalar (.int false 256)) = .ok (.scalar (.int false 256 cell.item.data.toNat))

theorem Data.nonpush (state : State) (cell : Storage.Cell) (kind : cell.item.kind ≠ 2#32) : Data state cell :=
  fun push => False.elim (kind push)

theorem Data.frame (represented : Data before cell)
    (same : after.heap.lookup cell.itemAddress = before.heap.lookup cell.itemAddress) : Data after cell := by
  intro push
  exact (AssemblyItem.Fields.readTyped_frame before after ⟨cell.itemAddress, 0⟩ _ _ same).trans (represented push)

/-- The admitted knownConstant body borrows the item's data field; it does not
read data or operands on a non-Push row. Field selection shares the existing
record-view and field-pointer operations used by every native item access. -/
def read (state : State) (descriptor : Address) : Except Fault (Option Value) := do
  let .pointer type item ← Expression.readField state false descriptor Expression.itemOffset
    | .error .malformed
  if type ≠ Expression.itemType then .error .malformed else do
  let kind ← AssemblyItem.Fields.kind state item
  if kind ≠ 2 then return none else do
  let root ← recordView state AssemblyItem.viewType (.pointer (.pointer false false AssemblyItem.allocationType) item)
  return some (← fieldPointer state root AssemblyItem.data_valueOffset)

def pointer (state : State) (header : Address) (id : NodeId) :
    Except Fault (Except Storage.ReadError (Option Value)) := do
  let selected ← representative state header id
  match selected with
  | .error .invalidId => return .ok none
  | .error fault => return .error fault
  | .ok (.pointer type descriptor) =>
    if type ≠ .pointer false false Expression.allocationType then .error .malformed
    else return .ok (← read state descriptor)
  | .ok _ => .error .malformed

/-- knownConstantValue dereferences only a successful borrowed pointer. Native
memory faults remain rejected observations, distinct from an absent constant. -/
def value (state : State) (header : Address) (id : NodeId) :
    Except Fault (Except Storage.ReadError (Option Contract.Yul.Word)) := do
  let result ← pointer state header id
  match result with
  | .error fault => return .error fault
  | .ok none => return .ok none
  | .ok (some address) =>
    let .scalar (.int false 256 word) ← load state address | .error .malformed
    return .ok (some (BitVec.ofInt 256 word))

theorem read_nonpush (state : State) (descriptor item : Address) (kind : Int)
    (selected : Expression.readField state false descriptor Expression.itemOffset = .ok (.pointer Expression.itemType item))
    (tag : AssemblyItem.Fields.kind state item = .ok kind) (notPush : kind ≠ 2) :
    read state descriptor = .ok none := by
  simp only [read, selected, bind, Except.bind, ne_self_iff_false, ↓reduceIte, tag, pure, Except.pure]
  exact if_pos notPush

theorem value_of_miss (state : State) (header : Address) (id : NodeId)
    (missed : pointer state header id = .ok (.ok none)) :
    value state header id = .ok (.ok none) := by
  simp only [value, missed, bind, Except.bind, pure, Except.pure]

/-- A Push query borrows and then loads the actual u256 member of the selected
item. The data premise is the native field relation established by construction,
not an assumed result of knownConstantValue. -/
theorem push (state : State) (header : Address) (lifetime capacity : Nat) (backing : Allocation)
    (cells : List Storage.Cell) (id : NodeId) (valid : state.valid = true)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (found : state.heap.lookup lifetime = some backing) (typed : backing.type = .array capacity Expression.allocationType)
    (writable : backing.writable = true) (extent : cells.length ≤ capacity)
    (represented : DescriptorRelation.Prefix state lifetime cells) (inside : id.toNat < cells.length)
    (native : Allocation) (itemFound : state.heap.lookup cells[id.toNat].itemAddress = some native)
    (itemTyped : native.type = AssemblyItem.viewType)
    (tag : AssemblyItem.Fields.kind state ⟨cells[id.toNat].itemAddress, 0⟩ = .ok 2)
    (data : AssemblyItem.Fields.readTyped state ⟨cells[id.toNat].itemAddress, 0⟩ AssemblyItem.data_valueOffset
      (.scalar (.int false 256)) = .ok (.scalar (.int false 256 cells[id.toNat].item.data.toNat))) :
    pointer state header id = .ok (.ok (some (.pointer (.pointer false false (.scalar (.int false 256)))
      ⟨cells[id.toNat].itemAddress, AssemblyItem.data_valueOffset⟩))) ∧
    value state header id = .ok (.ok (some cells[id.toNat].item.data)) := by
  have selected := representative_from_array state header lifetime capacity cells.length backing id valid loaded found typed writable extent inside
  have row := represented id.toNat cells[id.toNat] (List.getElem?_eq_getElem inside)
  have fields := Expression.readFields_parts state false ⟨lifetime, id.toNat * 32⟩ _ _ _ _ row
  have viewed := AssemblyItem.Fields.root_view state cells[id.toNat].itemAddress native false valid itemFound itemTyped
  have member := AssemblyItem.Fields.root_field state cells[id.toNat].itemAddress AssemblyItem.data_valueOffset native
    (.scalar (.int false 256)) false valid itemFound itemTyped AssemblyItem.Fields.scalar_fields_checked.2.2.1
  have borrowed : pointer state header id = .ok (.ok (some (.pointer (.pointer false false (.scalar (.int false 256)))
      ⟨cells[id.toNat].itemAddress, AssemblyItem.data_valueOffset⟩))) := by
    simp only [pointer, selected, read, fields.1, tag, viewed, member, bind, Except.bind,
      ne_self_iff_false, ↓reduceIte, pure, Except.pure]
  refine ⟨borrowed, ?_⟩
  have word := data
  rw [AssemblyItem.Fields.readTyped_from_root _ _ _ _ _ valid itemFound itemTyped] at word
  simp only [value, borrowed, bind, Except.bind, word, pure, Except.pure]
  simp

theorem invalid_id (state : State) (header data : Address) (length : Nat) (id : NodeId)
    (loaded : readItems state header = .ok (.slice itemsType data length)) (outside : length ≤ id.toNat) :
    pointer state header id = .ok (.ok none) := by
  simp only [pointer, invalid_from_loaded_header state header data length id loaded outside, bind, Except.bind, pure, Except.pure]

/-- The native representative lookup and item-kind load derive a miss without
any premise about the result of the constant query or its data payload. -/
theorem nonpush (state : State) (header : Address) (lifetime capacity : Nat) (backing : Allocation)
    (cells : List Storage.Cell) (id : NodeId) (valid : state.valid = true)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (found : state.heap.lookup lifetime = some backing) (typed : backing.type = .array capacity Expression.allocationType)
    (writable : backing.writable = true) (extent : cells.length ≤ capacity)
    (represented : DescriptorRelation.Prefix state lifetime cells) (inside : id.toNat < cells.length)
    (item : Operation.Item state cells[id.toNat]) (notPush : (cells[id.toNat].item.kind.toNat : Int) ≠ 2) :
    pointer state header id = .ok (.ok none) ∧ value state header id = .ok (.ok none) := by
  have selected := representative_from_array state header lifetime capacity cells.length backing id valid loaded found typed writable extent inside
  have row := represented id.toNat cells[id.toNat] (List.getElem?_eq_getElem inside)
  have fields := Expression.readFields_parts state false ⟨lifetime, id.toNat * 32⟩ _ _ _ _ row
  have absent := read_nonpush state ⟨lifetime, id.toNat * 32⟩ ⟨cells[id.toNat].itemAddress, 0⟩ _ fields.1 item.1 notPush
  have missed : pointer state header id = .ok (.ok none) := by
    simp only [pointer, selected, bind, Except.bind, ne_self_iff_false, ↓reduceIte, absent, pure, Except.pure]
  exact ⟨missed, value_of_miss state header id missed⟩

end Compiler.Extraction.RepresentativeArray.Constant
