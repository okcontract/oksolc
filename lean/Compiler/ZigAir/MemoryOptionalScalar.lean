/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryReadTyping

namespace Compiler.ZigAir.Memory.OptionalScalar

/-- One typed optional integer. Width does not imply an admitted memory layout;
only the captured children in `Ty.leafLayout` can be allocated or accessed. No
discriminator/payload byte view is exposed. -/
def unsigned (bits : Nat) : Ty := .optionalScalar (.int false bits)

def unsignedValue (bits : Nat) (payload : Option (BitVec bits)) : Value :=
  .optionalScalar (.int false bits) (payload.map fun value => .int false bits value.toNat)

theorem unsignedValue_type (bits : Nat) (payload : Option (BitVec bits)) :
    (unsignedValue bits payload).type = unsigned bits := rfl

theorem unsignedValue_valid (bits : Nat) (payload : Option (BitVec bits)) :
    (unsignedValue bits payload).valid = true := by
  cases payload with
  | none => rfl
  | some value =>
    have bound := value.isLt
    simp only [unsignedValue, Option.map_some, Value.valid, Scalar.Value.type, decide_true, Bool.true_and,
      Scalar.Value.valid, Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper, decide_eq_true_eq]
    change 0 ≤ (value.toNat : Int) ∧ (value.toNat : Int) < ((2 ^ bits : Nat) : Int)
    constructor <;> omega

theorem unsignedValue_typed (bits : Nat) (payload : Option (BitVec bits)) :
    (unsignedValue bits payload).hasType (unsigned bits) = true := by
  simp only [Value.hasType, unsignedValue_type, decide_true, Bool.true_and, unsignedValue_valid]

/-- Decode only a valid typed optional. Null remains a value; the caller owns
any source unwrap and its safety precondition. Malformed payloads never wrap. -/
def unsignedPayload (bits : Nat) (value : Value) : Except Fault (Option (BitVec bits)) :=
  if !value.hasType (unsigned bits) then .error .malformed else
  match value with
  | .optionalScalar _ none => .ok none
  | .optionalScalar _ (some (.int _ _ value)) => .ok (some (BitVec.ofInt bits value))
  | _ => .error .malformed

theorem unsignedPayload_value (bits : Nat) (payload : Option (BitVec bits)) :
    unsignedPayload bits (unsignedValue bits payload) = .ok payload := by
  simp only [unsignedPayload, unsignedValue_typed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases payload <;> simp [unsignedValue]

/-- Actual checked stores establish exact optional readback, including None.
The existing alias law supplies lifetime/type checking and readonly access. -/
theorem unsigned_read_after_store (state after : State) (address : Address) (bits : Nat) (payload : Option (BitVec bits))
    (stored : store state (.pointer (.pointer true false (unsigned bits)) address) (unsignedValue bits payload) = .ok after) :
    (do let value ← load after (.pointer (.pointer false false (unsigned bits)) address); unsignedPayload bits value) =
      .ok payload := by
  rw [load_alias_after_store state true false (unsigned bits) address (unsignedValue bits payload) after false false stored]
  exact unsignedPayload_value bits payload

-- Preserve the instruction reader's interface; all widths share one checked decoder.
def byte : Ty := unsigned 8
def byteValue := unsignedValue 8
def bytePayload := unsignedPayload 8
theorem layout_captured : byte.layout = some ⟨2, 1⟩ := rfl
theorem usize_layout_captured : (unsigned 64).layout = some ⟨16, 8⟩ := rfl
theorem word_layout_captured : (unsigned 256).layout = some ⟨48, 16⟩ := rfl
theorem byteValue_type (payload : Option (BitVec 8)) : (byteValue payload).type = byte := unsignedValue_type 8 payload
theorem byteValue_valid (payload : Option (BitVec 8)) : (byteValue payload).valid = true := unsignedValue_valid 8 payload
theorem byteValue_typed (payload : Option (BitVec 8)) : (byteValue payload).hasType byte = true := unsignedValue_typed 8 payload
theorem bytePayload_value (payload : Option (BitVec 8)) : bytePayload (byteValue payload) = .ok payload := unsignedPayload_value 8 payload
theorem read_after_store (state after : State) (address : Address) (payload : Option (BitVec 8))
    (stored : store state (.pointer (.pointer true false byte) address) (byteValue payload) = .ok after) :
    (do let value ← load after (.pointer (.pointer false false byte) address); bytePayload value) = .ok payload :=
  unsigned_read_after_store state after address 8 payload stored

end Compiler.ZigAir.Memory.OptionalScalar
