/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLaneRefinement

namespace Compiler.ZigAir.WyhashUpdateAir.Round
open Memory AggregateAir Compiler.Extraction

/-- Every hasher-buffer byte is a declared byte leaf in the native object. -/
theorem buffer_locate : ∀ i : Fin 48,
    ScalarBytes.locate objectType (56 + i.val) = some (56 + i.val, false, 8) := by
  decide +kernel

/-- Reads of the self-buffer follow from the same sparse cells used by the
update invariant, even after preceding lanes have changed their state words. -/
theorem buffer_reads {state : State} {id : Nat} (frame : CellFrame state id)
    (cells : Cells) (typed : frame.cell.type = objectType) (bytes : Nat → BitVec 8)
    (represented : ByteSlice.Represents cells (WyhashBuffer.buffer 0 48) bytes) :
    ByteRange.Reads (frame.install cells) ⟨id, 56⟩ 48 bytes := by
  intro i inside
  have layout := WyhashInit.object_frame_layout frame typed
  have accessed := frame.field_read_access cells (56 + i) ⟨1, 1⟩ (by decide)
    (by rw [layout]; dsimp; omega) (Nat.mod_one _) (Nat.mod_one _)
  have geometry := WyhashBuffer.buffer_geometry 0 48 (by decide) i inside
  change leafType objectType (56 + i) = some (.scalar (.int false 8)) ∧
    acceptsView objectType (56 + i) (.scalar (.int false 8)) = true at geometry
  have found : cells.lookup (56 + i) = some (ByteSlice.value (bytes i)) := represented i inside
  have valueType : (ByteSlice.value (bytes i)).hasType (.scalar (.int false 8)) = true :=
    ByteSlice.value_typed (bytes i)
  have cellRead : cells.read objectType (56 + i) ByteSlice.byte = .ok (ByteSlice.value (bytes i)) := by
    simp only [Cells.read, Cells.readLeaf, ByteSlice.byte, geometry.1, geometry.2,
      found, valueType, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_self_iff_false]
  have loaded := frame.load_eq cells (56 + i) ByteSlice.byte ⟨1, 1⟩ rfl (by decide)
    (by rw [layout]; dsimp; omega) (Nat.mod_one _) (Nat.mod_one _)
  rw [typed, cellRead] at loaded
  have readonly : Memory.load (frame.install cells)
      (.pointer (.pointer false false ByteSlice.byte) ⟨id, 56 + i⟩) =
      .ok (ByteSlice.value (bytes i)) := by simpa only [Memory.load] using loaded
  simp only [ByteSlice.byte] at readonly
  simp only [ScalarBytes.readAt, accessed, typed, buffer_locate ⟨i, inside⟩,
    readonly, bind, Except.bind, ByteSlice.value, Nat.sub_self, Nat.pow_zero, Nat.div_one,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- External data remains in a different allocation. A fill round instead uses
the actual native self-buffer; its byte reads are derived from representation. -/
def InputAdmitted (state : State) (id : Nat) (input : WyhashUpdate.Input)
    (offset : Nat) (address : Address) (bytes : Nat → BitVec 8) : Prop :=
  match input with
  | .external _ _ => address.allocation ≠ id ∧
      ByteRange.Reads state address 48 (fun i => bytes (offset + i))
  | .buffer => address = ⟨id, 56⟩

theorem InputAdmitted.reads {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (input : WyhashUpdate.Input) (offset : Nat) (address : Address) (bytes : Nat → BitVec 8)
    (admitted : InputAdmitted state id input offset address bytes)
    (represented : ByteSlice.Represents (input.cells frame.cell.cells) input.view bytes)
    (inside : offset + 48 ≤ input.view.length) :
    ByteRange.Reads state address 48 (fun i => bytes (offset + i)) := by
  cases input with
  | external source view => exact admitted.2
  | buffer =>
    have zero : offset = 0 := by change offset + 48 ≤ 48 at inside; omega
    subst offset
    change address = ⟨id, 56⟩ at admitted
    subst address
    simpa only [Nat.zero_add, frame.install_current valid] using buffer_reads frame frame.cell.cells typed bytes represented

theorem represented_frame (input : WyhashUpdate.Input) (before after : Cells)
    (bytes : Nat → BitVec 8) (represented : ByteSlice.Represents (input.cells before) input.view bytes)
    (retained : ∀ query, query < 16 ∨ 40 ≤ query → after.lookup query = before.lookup query) :
    ByteSlice.Represents (input.cells after) input.view bytes := by
  cases input with
  | external source view => exact represented
  | buffer =>
    intro i inside
    change after.lookup (56 + i) = _
    rw [retained _ (Or.inr (by omega))]
    exact represented i inside

theorem InputAdmitted.install {state : State} {id : Nat} (frame : CellFrame state id)
    (cells : Cells) (input : WyhashUpdate.Input) (offset : Nat) (address : Address) (bytes : Nat → BitVec 8)
    (admitted : InputAdmitted state id input offset address bytes) :
    InputAdmitted (frame.install cells) id input offset address bytes := by
  cases input with
  | external source view => exact ⟨admitted.1, admitted.2.install frame cells address 48 _ admitted.1⟩
  | buffer => exact admitted

theorem InputAdmitted.extend {before after : State} {id : Nat} (stack : StackFrame before after)
    (input : WyhashUpdate.Input) (offset : Nat) (address : Address) (bytes : Nat → BitVec 8)
    (admitted : InputAdmitted before id input offset address bytes) :
    InputAdmitted after id input offset address bytes := by
  cases input with
  | external source view => exact ⟨admitted.1, admitted.2.extend stack address 48 _⟩
  | buffer => exact admitted

end Compiler.ZigAir.WyhashUpdateAir.Round
