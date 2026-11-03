/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryOptionalScalar
import Compiler.ZigAir.MemorySlots
import Compiler.ZigAir.MemoryRelease

namespace Compiler.ZigAir.Memory.OptionalScalar.Tests

def cell : Allocation := ⟨16, byte, [], true, false⟩
def before : State := ⟨[(0, cell), (1, ⟨20, .scalar (.int false 32), [(0, .scalar (.int false 32 7))], true, false⟩)], 2, 24⟩
def pointer : Value := .pointer (.pointer true false byte) ⟨0, 0⟩
def readonly : Value := .pointer (.pointer false false byte) ⟨0, 0⟩
def saved (payload : Option (BitVec 8)) := (store before pointer (byteValue payload)).toOption.getD before
def get (state : State) : Except Fault (Option (BitVec 8)) := do
  let value ← load state readonly
  bytePayload value

theorem before_valid : before.valid = true := by decide

theorem write_result (payload : Option (BitVec 8)) : store before pointer (byteValue payload) = .ok (saved payload) := by
  obtain ⟨after, stored⟩ := root_store_total before 0 cell (byteValue payload) ⟨2, 1⟩ before_valid rfl
    (byteValue_type payload).symm rfl (byteValue_valid payload) rfl (by decide)
  have executed : store before pointer (byteValue payload) = .ok after := stored
  simp only [saved, executed, Except.toOption, Option.getD]

theorem saved_valid (payload : Option (BitVec 8)) : (saved payload).valid = true :=
  store_preserves_valid before pointer (byteValue payload) (saved payload) before_valid (write_result payload)

theorem saved_payload (payload : Option (BitVec 8)) : get (saved payload) = .ok payload :=
  read_after_store before (saved payload) ⟨0, 0⟩ payload (write_result payload)

theorem missing_is_uninitialized : get before = .error .uninitialized := by rfl'
theorem null_is_initialized : get (saved none) = .ok none := saved_payload none
theorem zero_is_present : get (saved (some 0)) = .ok (some 0) := saved_payload (some 0)
theorem largest_is_present : get (saved (some 255)) = .ok (some 255) := saved_payload (some 255)

def erasedPayload := (store (saved (some 255)) pointer (byteValue none)).toOption.getD before

theorem overwrite_clears_payload : get erasedPayload = .ok none ∧
    (erasedPayload.heap.lookup 0).map (fun cell => cell.cells.length) = some 1 := ⟨by rfl', by rfl'⟩
theorem independent_word : load (saved (some 0)) (.pointer (.pointer false false (.scalar (.int false 32))) ⟨1, 0⟩) =
    .ok (.scalar (.int false 32 7)) := by rfl'
theorem readonly_rejects : store (saved none) readonly (byteValue (some 1)) = .error .readOnly := by rfl'

theorem wrong_payload_type : store before pointer (.optionalScalar (.int false 8) (some (.int true 8 1))) =
    .error .malformed := by rfl'
theorem wrong_payload_range : store before pointer (.optionalScalar (.int false 8) (some (.int false 8 256))) =
    .error .malformed ∧ store before pointer (.optionalScalar (.int false 8) (some (.int false 8 (-1)))) =
    .error .malformed := ⟨by rfl', by rfl'⟩
theorem wrong_optional_type : store before pointer (.optionalScalar (.int true 8) none) = .error .malformed := by rfl'
theorem malformed_payload_never_wraps : bytePayload (.optionalScalar (.int false 8) (some (.int false 8 256))) =
    .error .malformed ∧ bytePayload (.optionalScalar (.int false 8) (some (.int false 8 (-1)))) =
    .error .malformed := ⟨by rfl', by rfl'⟩

theorem no_payload_field : fieldType byte 0 = none ∧ fieldType byte 1 = none := ⟨rfl, rfl⟩
theorem scalar_punning_rejects : load (saved (some 0)) (.pointer (.pointer false false (.scalar (.int false 8))) ⟨0, 0⟩) =
    .error .unsupported ∧ store before (.pointer (.pointer true false (.scalar (.int false 8))) ⟨0, 0⟩)
    (.scalar (.int false 8 1)) = .error .unsupported := ⟨by rfl', by rfl'⟩
theorem interior_rejects : load (saved none) (.pointer (.pointer false false byte) ⟨0, 1⟩) = .error .memoryValidity := by rfl'
theorem unsupported_optional_layouts : (Ty.optionalScalar (.int false 16)).layout = none ∧
    (Ty.optionalScalar .bool).layout = none ∧ allocate before (.optionalScalar (.int false 16)) = .error .unsupported :=
  ⟨rfl, rfl, by rfl'⟩
theorem dead_alias_rejects : get (erase (saved (some 1)) 0) = .error .unallocated := by rfl'

def array : State := ⟨[(0, ⟨16, .array 2 byte, [], true, false⟩)], 1, 20⟩
def arraySlice : Value := .slice (.slice true byte) ⟨0, 0⟩ 2
theorem array_stride_and_bound : sliceElementPointer array arraySlice 1 = .ok (.pointer (.pointer true false byte) ⟨0, 2⟩) ∧
    sliceElementPointer array arraySlice 2 = .error .sourceBounds := ⟨by rfl', by rfl'⟩

namespace Wide

def cell (bits : Nat) : Allocation := ⟨32, unsigned bits, [], true, false⟩
def before (bits : Nat) : State := ⟨[(0, cell bits)], 1, 80⟩
def pointer (bits : Nat) (writable : Bool := true) : Value := .pointer (.pointer writable false (unsigned bits)) ⟨0, 0⟩
def saved (bits : Nat) (payload : Option (BitVec bits)) :=
  (store (before bits) (pointer bits) (unsignedValue bits payload)).toOption.getD (before bits)
def get (bits : Nat) (state : State) : Except Fault (Option (BitVec bits)) := do
  let value ← load state (pointer bits false)
  unsignedPayload bits value

theorem write_result (bits : Nat) (admitted : bits = 64 ∨ bits = 256) (payload : Option (BitVec bits)) :
    store (before bits) (pointer bits) (unsignedValue bits payload) = .ok (saved bits payload) := by
  have valid : (before bits).valid = true := by rcases admitted with rfl | rfl <;> decide
  have shaped : (unsigned bits).layout = some (if bits = 64 then ⟨16, 8⟩ else ⟨48, 16⟩) := by
    rcases admitted with rfl | rfl <;> rfl
  obtain ⟨after, stored⟩ := root_store_total (before bits) 0 (cell bits) (unsignedValue bits payload) _ valid rfl
    (unsignedValue_type bits payload).symm rfl (unsignedValue_valid bits payload) shaped
    (by rcases admitted with rfl | rfl <;> decide)
  have executed : store (before bits) (pointer bits) (unsignedValue bits payload) = .ok after := stored
  simp only [saved, executed, Except.toOption, Option.getD]

theorem every_payload (bits : Nat) (admitted : bits = 64 ∨ bits = 256) (payload : Option (BitVec bits)) :
    (saved bits payload).valid = true ∧ get bits (saved bits payload) = .ok payload :=
  ⟨store_preserves_valid (before bits) (pointer bits) (unsignedValue bits payload) (saved bits payload)
    (by rcases admitted with rfl | rfl <;> decide) (write_result bits admitted payload),
   unsigned_read_after_store (before bits) (saved bits payload) ⟨0, 0⟩ bits payload (write_result bits admitted payload)⟩

theorem missing_is_uninitialized : get 64 (before 64) = .error .uninitialized ∧
    get 256 (before 256) = .error .uninitialized := ⟨by rfl', by rfl'⟩
theorem null_and_zero_differ : get 64 (saved 64 none) = .ok none ∧ get 64 (saved 64 (some 0)) = .ok (some 0) ∧
    get 256 (saved 256 none) = .ok none ∧ get 256 (saved 256 (some 0)) = .ok (some 0) :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem maximum_values : get 64 (saved 64 (some (2^64 - 1))) = .ok (some (2^64 - 1)) ∧
    get 256 (saved 256 (some (2^256 - 1))) = .ok (some (2^256 - 1)) :=
  ⟨(every_payload 64 (Or.inl rfl) _).2, (every_payload 256 (Or.inr rfl) _).2⟩

def cleared (bits : Nat) := (store (saved bits (some (-1))) (pointer bits) (unsignedValue bits none)).toOption.getD (before bits)
theorem clear_payload : get 64 (cleared 64) = .ok none ∧ get 256 (cleared 256) = .ok none ∧
    ((cleared 64).heap.lookup 0).map (fun c => c.cells.length) = some 1 ∧
    ((cleared 256).heap.lookup 0).map (fun c => c.cells.length) = some 1 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem invalid_values :
    unsignedPayload 64 (.optionalScalar (.int false 64) (some (.int false 64 (2^64)))) = .error .malformed ∧
    unsignedPayload 256 (.optionalScalar (.int false 256) (some (.int false 256 (-1)))) = .error .malformed ∧
    store (before 256) (pointer 256) (.optionalScalar (.int false 256) (some (.int false 256 (2^256)))) = .error .malformed ∧
    store (before 64) (pointer 64) (.optionalScalar (.int false 64) (some (.int false 64 (-1)))) = .error .malformed :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem wrong_children : unsignedPayload 64 (unsignedValue 256 (some 1)) = .error .malformed ∧
    unsignedPayload 256 (unsignedValue 64 none) = .error .malformed ∧
    unsignedPayload 64 (.optionalScalar (.int false 64) (some (.int true 64 1))) = .error .malformed :=
  ⟨by rfl', by rfl', by rfl'⟩
theorem no_payload_projection : fieldType (unsigned 64) 0 = none ∧ fieldType (unsigned 256) 32 = none ∧
    load (saved 256 (some 0)) (.pointer (.pointer false false (.scalar (.int false 256))) ⟨0, 0⟩) = .error .unsupported :=
  ⟨rfl, rfl, by rfl'⟩
theorem readonly_and_dead : store (before 64) (pointer 64 false) (unsignedValue 64 none) = .error .readOnly ∧
    get 256 (erase (saved 256 none) 0) = .error .unallocated := ⟨by rfl', by rfl'⟩
theorem unsupported_widths : (unsigned 32).layout = none ∧ (unsigned 128).layout = none ∧
    allocate (before 64) (unsigned 128) = .error .unsupported := ⟨rfl, rfl, by rfl'⟩

def array (bits : Nat) : State := ⟨[(0, ⟨32, .array 2 (unsigned bits), [], true, false⟩)], 1, 128⟩
def slice (bits : Nat) : Value := .slice (.slice true (unsigned bits)) ⟨0, 0⟩ 2
theorem array_stride_and_bounds :
    sliceElementPointer (array 64) (slice 64) 1 = .ok (.pointer (.pointer true false (unsigned 64)) ⟨0, 16⟩) ∧
    sliceElementPointer (array 256) (slice 256) 1 = .ok (.pointer (.pointer true false (unsigned 256)) ⟨0, 48⟩) ∧
    sliceElementPointer (array 256) (slice 256) 2 = .error .sourceBounds := ⟨by rfl', by rfl', by rfl'⟩

end Wide

namespace Signed

def type : Ty := .optionalScalar (.int true 64)
theorem captured_layout_and_stride : type.layout = some ⟨16, 8⟩ ∧
    (Ty.array 2 type).layout = some ⟨32, 8⟩ := ⟨rfl, rfl⟩
theorem unsupported_widths : (Ty.optionalScalar (.int true 32)).layout = none ∧
    (Ty.optionalScalar (.int true 256)).layout = none := ⟨rfl, rfl⟩
theorem signed_is_not_unsigned : unsignedPayload 64 (.optionalScalar (.int true 64) none) = .error .malformed ∧
    unsignedPayload 64 (.optionalScalar (.int true 64) (some (.int true 64 (-1)))) = .error .malformed := ⟨by rfl', by rfl'⟩

end Signed

end Compiler.ZigAir.Memory.OptionalScalar.Tests
