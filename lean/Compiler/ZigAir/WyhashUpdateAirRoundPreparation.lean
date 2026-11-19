/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRoundExecution

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction Control.Machine

theorem size_add_constant (state : State) (a b reg : Nat) (args : List Register) (env : Env)
    (bound : a + b < addressLimit) (found : env reg = some (size a)) :
    (AggregateAir.Prim.memory (.scalar (.arithmetic .add .unchecked (.local reg)
      (.constant (.int false 64 b))))).eval args env state = (.ok (size (a + b)), state) := by
  apply eval_scalar
  have validB := Scalar.unsigned_nat_valid b 64 (by omega : b < addressLimit)
  have constant : (Scalar.Ref.constant (.int false 64 b)).eval (MemoryAir.scalarEnv (values env)) =
      .ok (.int false 64 b) := by simp only [Scalar.Ref.eval, validB, ↓reduceIte]
  rw [scalar_arithmetic _ _ _ _ _ _ false 64 a b
    (SliceBytesAir.scalar_size env reg a (by omega) found) constant]
  have contains := Scalar.unsigned_nat_valid (a + b) 64 bound
  change (Scalar.Ty.int false 64).contains (a + b : Nat) = true at contains
  simp [Scalar.Arithmetic.eval, ← Int.natCast_add, Scalar.integer, contains]

namespace Round

def bufferSite : Code := fillBody.dropBindings 27

def bufferPreparation : Code :=
  .bind 83 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 84 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 85 (.pointer true false (.array 48 ByteSlice.byte)) (.primitive (.fieldPointer (.local 84) 56)) $
  .bind 86 (WordRead.arrayPointer 48)
    (.primitive (.memory (.pointerCast (WordRead.arrayPointer 48) (.local 85)))) (parameterSite false)

def bufferEnv (env : Env) (id : Nat) : Env :=
  let env := env.set 83 (.value (selfPointer id))
  let env := env.set 84 (.value (selfPointer id))
  let env := env.set 85 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  env.set 86 (.value (.pointer (WordRead.arrayPointer 48) ⟨id, 56⟩))

theorem generated_buffer_preparation : bufferSite = bufferPreparation := by decide +kernel

theorem buffer_prepare_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType) (selfSlot : Nat)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (args : List Register) (env : Env) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (found : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨bufferSite, env, state, frames⟩)
      (.suspended ⟨parameterSite false, bufferEnv env id, state, frames⟩) := by
  let e83 := env.set 83 (.value (selfPointer id))
  let e84 := e83.set 84 (.value (selfPointer id))
  let e85 := e84.set 85 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  have p83 := eval_load (.local 4) args env state _ _ (value_local _ _ _ found rfl)
    (congrArg (Except.map Register.value) selfRead)
  have p84 := eval_load (.local 4) args e83 state (slot false (.pointer true false objectType) selfSlot) _
    (value_local _ _ _ (by simpa [e83, Control.Env.set] using found) rfl)
    (congrArg (Except.map Register.value) selfRead)
  have field := field_pointer frame frame.cell.cells typed 56 (.array 48 ByteSlice.byte) (by rfl)
  rw [frame.install_current valid] at field
  have p85 := eval_field (.local 84) 56 args e84 state _ _
    (value_local _ _ _ (by simp [e84, Control.Env.set]) rfl) field
  have access := frame.field_read_access frame.cell.cells 56 ⟨48, 1⟩ (by decide)
    (by rw [WyhashInit.object_frame_layout frame typed]; decide) (by decide) (Nat.mod_one _)
  rw [frame.install_current valid] at access
  have cast : Memory.pointerCast state (WordRead.arrayPointer 48)
      (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩) =
      .ok (.pointer (WordRead.arrayPointer 48) ⟨id, 56⟩) := by
    simp only [Memory.pointerCast, Memory.pointerCompatible, WordRead.arrayPointer,
      ByteSlice.byte, Ty.layout, Ty.leafLayout, Bool.false_and, decide_true, Bool.true_or,
      Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
      Nat.mul_one, access, bind, Except.bind]
  have p86 : (AggregateAir.Prim.memory (.pointerCast (WordRead.arrayPointer 48) (.local 85))).eval args e85 state =
      (.ok (.value (.pointer (WordRead.arrayPointer 48) ⟨id, 56⟩)), state) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e85 85
      (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩) (by simp [e85, Control.Env.set]) rfl
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, cast, bind, Except.bind]
  rw [generated_buffer_preparation]
  exact AggregateCall.primitive_steps args p83 (by rfl) <|
    AggregateCall.primitive_steps args p84 (by rfl) <|
    AggregateCall.primitive_steps args p85 (by rfl) <|
    AggregateCall.primitive_steps args p86 (by rfl) (.refl _)

def externalPreparation : Code :=
  .bind 337 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 338 usize (.primitive (.load (.local 50))) $
  .bind 339 inputType (.primitive (.load (.local 7))) $
  .bind 340 WordRead.bytePointer (.primitive (.memory (.slicePtr (.local 339)))) $
  .bind 341 WordRead.bytePointer (.primitive (.memory (.offsetPointer false (.local 340) (.local 338)))) $
  .bind 342 usize (.primitive (.memory (.scalar (.arithmetic .add .unchecked (.local 338) (.constant (.int false 64 48)))))) $
  .bind 667 (.scalar .unit) (.primitive (.memory (.checkBounds (.local 338) (.local 342) (.slice (.local 339))))) $
  .bind 343 (WordRead.arrayPointer 48)
    (.primitive (.memory (.pointerCast (WordRead.arrayPointer 48) (.local 341)))) (parameterSite true)

def externalEnv (env : Env) (id : Nat) (address : Address) (index count : Nat) : Env :=
  let env := env.set 337 (.value (selfPointer id))
  let env := env.set 338 (size index)
  let env := env.set 339 (.value (.slice inputType address count))
  let env := env.set 340 (.value (.pointer WordRead.bytePointer address))
  let env := env.set 341 (.value (.pointer WordRead.bytePointer ⟨address.allocation, address.offset + index⟩))
  let env := env.set 342 (size (index + 48))
  let env := env.set 667 (.value (.scalar .unit))
  env.set 343 (.value (.pointer (WordRead.arrayPointer 48) ⟨address.allocation, address.offset + index⟩))

theorem generated_external_preparation : loopBody = externalPreparation := by decide +kernel

theorem external_prepare_steps (state : State) (id : Nat) (address : Address) (index count : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address count bytes)
    (inside : index + 48 ≤ count) (bound : count < addressLimit)
    (selfSlot inputSlot indexSlot : Nat)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address count))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨loopBody, env, state, frames⟩)
      (.suspended ⟨parameterSite true, externalEnv env id address index count, state, frames⟩) := by
  let e337 := env.set 337 (.value (selfPointer id))
  let e338 := e337.set 338 (size index)
  let e339 := e338.set 339 (.value (.slice inputType address count))
  let e340 := e339.set 340 (.value (.pointer WordRead.bytePointer address))
  let e341 := e340.set 341 (.value (.pointer WordRead.bytePointer ⟨address.allocation, address.offset + index⟩))
  let e342 := e341.set 342 (size (index + 48))
  let e667 := e342.set 667 (.value (.scalar .unit))
  have p337 := eval_load (.local 4) args env state _ _ (value_local _ _ _ foundSelf rfl)
    (congrArg (Except.map Register.value) selfRead)
  have p338 := eval_load (.local 50) args e337 state (slot true usize indexSlot) _
    (value_local _ _ _ (by simpa [e337, Control.Env.set] using foundIndex) rfl)
    (congrArg (Except.map Register.value) indexRead)
  have p339 := eval_load (.local 7) args e338 state (slot false inputType inputSlot) _
    (value_local _ _ _ (by simpa [e338, e337, Control.Env.set] using foundInput) rfl)
    (congrArg (Except.map Register.value) inputRead)
  have sliceValid : (Value.slice inputType address count).valid = true := by
    simpa only [Value.valid, decide_eq_true_eq] using bound
  have p340 : (AggregateAir.Prim.memory (.slicePtr (.local 339))).eval args e339 state =
      (.ok (.value (.pointer WordRead.bytePointer address)), state) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e339 339 (.slice inputType address count)
      (by simp [e339, Control.Env.set]) sliceValid
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, bind, Except.bind]
  have p341 : (AggregateAir.Prim.memory (.offsetPointer false (.local 340) (.local 338))).eval args e340 state =
      (.ok (.value (.pointer WordRead.bytePointer ⟨address.allocation, address.offset + index⟩)), state) := by
    have data := SliceBytesAir.memory_local e340 340 (.pointer WordRead.bytePointer address)
      (by simp [e340, Control.Env.set]) rfl
    have number := SliceBytesAir.natural_size e340 338 index (by omega)
      (by simp [e340, e339, e338, Control.Env.set])
    have advance := reads.offset_pointer 0 index (by omega) (by omega)
    exact eval_offset _ _ args e340 state _ _ _ data number (by simpa only [Nat.add_zero, Nat.zero_add] using advance)
  have p342 := size_add_constant state index 48 338 args e341 (by omega)
    (by simp [e341, e340, e339, e338, Control.Env.set])
  have p667 : (AggregateAir.Prim.memory (.checkBounds (.local 338) (.local 342) (.slice (.local 339)))).eval args e342 state =
      (.ok (.value (.scalar .unit)), state) := by
    have first := SliceBytesAir.natural_size e342 338 index (by omega)
      (by simp [e342, e341, e340, e339, e338, Control.Env.set])
    have last := SliceBytesAir.natural_size e342 342 (index + 48) (by omega) (by simp [e342, Control.Env.set])
    have data := SliceBytesAir.memory_local e342 339 (.slice inputType address count)
      (by simp [e342, e341, e340, e339, Control.Env.set]) sliceValid
    apply eval_bounds _ _ _ args e342 state index (index + 48) (some count) first last
    · simp only [MemoryAir.Bound.eval, data, bind, Except.bind]
    · simp [checkSliceBounds, inside]
  have p343 : (AggregateAir.Prim.memory (.pointerCast (WordRead.arrayPointer 48) (.local 341))).eval args e667 state =
      (.ok (.value (.pointer (WordRead.arrayPointer 48) ⟨address.allocation, address.offset + index⟩)), state) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e667 341
      (.pointer WordRead.bytePointer ⟨address.allocation, address.offset + index⟩)
      (by simp [e667, e342, e341, Control.Env.set]) rfl
    have cast : Memory.pointerCast state (WordRead.arrayPointer 48)
        (.pointer WordRead.bytePointer ⟨address.allocation, address.offset + index⟩) =
        .ok (.pointer (WordRead.arrayPointer 48) ⟨address.allocation, address.offset + index⟩) :=
      reads.array_cast index 48 (by omega) inside
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, cast, bind, Except.bind]
  rw [generated_external_preparation]
  exact AggregateCall.primitive_steps args p337 (by rfl) <|
    AggregateCall.primitive_steps args p338 (SliceBytesAir.size_typed index (by omega)) <|
    AggregateCall.primitive_steps args p339 sliceValid <|
    AggregateCall.primitive_steps args p340 (by rfl) <|
    AggregateCall.primitive_steps args p341 (by rfl) <|
    AggregateCall.primitive_steps args p342 (SliceBytesAir.size_typed (index + 48) (by omega)) <|
    AggregateCall.primitive_steps args p667 (by rfl) <|
    AggregateCall.primitive_steps args p343 (by rfl) (.refl _)

end Round
end Compiler.ZigAir.WyhashUpdateAir
