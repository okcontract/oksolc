/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryEffects

namespace Compiler.ZigAir.Memory

theorem Value.usize_value (value : Value) (typed : value.hasType usize = true) :
    ∃ number, value = .scalar (.int false 64 number) := by
  cases value with
  | scalar value =>
    cases value with
    | unit | bool => simp [Value.hasType, Value.type, Scalar.Value.type, usize] at typed
    | int signed width number =>
      simp only [Value.hasType, Value.type, Scalar.Value.type, usize, Bool.and_eq_true,
        decide_eq_true_eq, Ty.scalar.injEq, Scalar.Ty.int.injEq] at typed
      obtain ⟨rfl, rfl⟩ := typed.1
      exact ⟨number, rfl⟩
  | optionalScalar child payload | optionalObject child _ payload => simp [Value.hasType, Value.type, usize] at typed
  | pointer type address =>
    simp only [Value.hasType, Value.type, usize, Bool.and_eq_true, decide_eq_true_eq] at typed
    obtain ⟨rfl, valid⟩ := typed
    simp [Value.valid] at valid
  | slice type address length =>
    simp only [Value.hasType, Value.type, usize, Bool.and_eq_true, decide_eq_true_eq] at typed
    obtain ⟨rfl, valid⟩ := typed
    simp [Value.valid] at valid

/-- A successful sparse read checks every stored leaf, including the unsigned
length of a reconstructed slice. No initial heap-validity premise is required. -/
theorem Cells.read_hasType (cells : Cells) (owner : Ty) (offset : Nat) (wanted : Ty) (value : Value)
    (loaded : cells.read owner offset wanted = .ok value) : value.hasType wanted = true := by
  unfold Cells.read at loaded
  split at loaded
  · contradiction
  · cases wanted with
    | array | record | aggregate => contradiction
    | scalar type => exact cells.readLeaf_hasType owner offset (.scalar type) value loaded
    | optionalScalar child => exact cells.readLeaf_hasType owner offset (.optionalScalar child) value loaded
    | optionalObject child layout => exact cells.readLeaf_hasType owner offset (.optionalObject child layout) value loaded
    | pointer writable many child => exact cells.readLeaf_hasType owner offset (.pointer writable many child) value loaded
    | slice writable child =>
      cases pointerRead : cells.readLeaf owner offset (.pointer writable true child) with
      | error fault => simp only [pointerRead, bind, Except.bind] at loaded; cases loaded
      | ok pointer =>
        simp only [pointerRead, bind, Except.bind] at loaded
        cases pointer with
        | scalar | optionalScalar | optionalObject | slice => cases loaded
        | pointer type address =>
          cases lengthRead : cells.readLeaf owner (offset + 8) usize with
          | error fault => simp only [lengthRead] at loaded; cases loaded
          | ok length =>
            obtain ⟨number, rfl⟩ := Value.usize_value length
              (cells.readLeaf_hasType owner (offset + 8) usize length lengthRead)
            have checked := cells.readLeaf_hasType owner (offset + 8) usize (.scalar (.int false 64 number)) lengthRead
            simp only [lengthRead] at loaded
            have same := Except.ok.inj loaded
            subst value
            simp only [Value.hasType, Value.type, Value.valid, decide_true, Bool.true_and, decide_eq_true_eq]
            simp only [Value.hasType, Value.type, Scalar.Value.type, usize, decide_true, Bool.true_and,
              Value.valid, Scalar.Value.valid, Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper,
              decide_eq_true_eq] at checked
            dsimp [addressLimit]
            omega

theorem load_hasType (state : State) (writable many : Bool) (child : Ty) (address : Address) (value : Value)
    (loaded : load state (.pointer (.pointer writable many child) address) = .ok value) :
    value.hasType child = true := by
  cases shaped : child.layout with
  | none => simp [load, shaped] at loaded
  | some layout =>
    cases accessed : access state address layout false with
    | error fault => simp [load, shaped, accessed, bind, Except.bind] at loaded
    | ok cell =>
      apply cell.cells.read_hasType cell.type address.offset child value
      simpa only [load, shaped, accessed, bind, Except.bind, readCell] using loaded

/-- A checked slice read exposes the exact typed pointer and unsigned length
leaves. Both partial-field update laws use this same reconstruction boundary. -/
theorem Cells.read_slice_parts (cells : Cells) (owner : Ty) (offset : Nat) (writable : Bool) (child : Ty)
    (address : Address) (length : Nat)
    (loaded : cells.read owner offset (.slice writable child) = .ok (.slice (.slice writable child) address length)) :
    acceptsView owner offset (.slice writable child) = true ∧
      cells.readLeaf owner offset (.pointer writable true child) = .ok (.pointer (.pointer writable true child) address) ∧
      cells.readLeaf owner (offset + 8) usize = .ok (.scalar (.int false 64 length)) := by
  by_cases view : acceptsView owner offset (.slice writable child) = true
  · simp only [Cells.read, view, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at loaded
    cases pointerRead : cells.readLeaf owner offset (.pointer writable true child) with
    | error fault => simp only [pointerRead, bind, Except.bind] at loaded; cases loaded
    | ok pointer =>
      simp only [pointerRead, bind, Except.bind] at loaded
      cases pointer with
      | scalar | optionalScalar | optionalObject | slice => cases loaded
      | pointer type data =>
        have pointerTyped := cells.readLeaf_hasType owner offset (.pointer writable true child) (.pointer type data) pointerRead
        simp only [Value.hasType, Value.type, Bool.and_eq_true, decide_eq_true_eq] at pointerTyped
        obtain ⟨rfl, _⟩ := pointerTyped
        cases lengthRead : cells.readLeaf owner (offset + 8) usize with
        | error fault => simp only [lengthRead] at loaded; cases loaded
        | ok value =>
          obtain ⟨number, rfl⟩ := Value.usize_value value (cells.readLeaf_hasType owner (offset + 8) usize value lengthRead)
          have checked := cells.readLeaf_hasType owner (offset + 8) usize (.scalar (.int false 64 number)) lengthRead
          simp only [lengthRead] at loaded
          have same := Value.slice.inj (Except.ok.inj loaded)
          simp only [Value.hasType, Value.type, Scalar.Value.type, usize, decide_true, Bool.true_and,
            Value.valid, Scalar.Value.valid, Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper,
            decide_eq_true_eq] at checked
          have numberEq : number = (length : Int) := by omega
          exact ⟨view, by simp only [same.2.1], by simp only [numberEq]⟩
  · have rejected := Bool.eq_false_iff.mpr view
    simp only [Cells.read, rejected, Bool.not_false, ↓reduceIte] at loaded
    cases loaded

theorem Cells.read_slice_of_parts (cells : Cells) (owner : Ty) (offset : Nat) (writable : Bool) (child : Ty)
    (address : Address) (length : Nat) (view : acceptsView owner offset (.slice writable child) = true)
    (pointerRead : cells.readLeaf owner offset (.pointer writable true child) = .ok (.pointer (.pointer writable true child) address))
    (lengthRead : cells.readLeaf owner (offset + 8) usize = .ok (.scalar (.int false 64 length))) :
    cells.read owner offset (.slice writable child) = .ok (.slice (.slice writable child) address length) := by
  simp only [Cells.read, view, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pointerRead, lengthRead, bind, Except.bind,
    Int.toNat_natCast]

end Compiler.ZigAir.Memory
