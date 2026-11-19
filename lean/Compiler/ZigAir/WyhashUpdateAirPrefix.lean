/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirEntry

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction Control.Machine
open WyhashInit (object_word_read object_word_store)

theorem count_pointer (state : State) (args : List Register) (env : Env) (inputSlot reg : Nat)
    (found : env reg = some (.value (slot false inputType inputSlot))) :
    (AggregateAir.Prim.memory (.pointerField true (.local reg))).eval args env state =
      (.ok (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩)), state) := by
  apply eval_memory
  have data := SliceBytesAir.memory_local env reg (slot false inputType inputSlot) found rfl
  simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, Memory.pointerField, bind, Except.bind,
    ↓reduceIte, Nat.zero_add]

def counterEnv (env : Env) (id inputSlot total count : Nat) : Env :=
  let env := env.set 8 (.value (selfPointer id))
  let env := env.set 9 (.value (.pointer (.pointer true false usize) ⟨id, 40⟩))
  let env := env.set 10 (size total)
  let env := env.set 11 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let env := env.set 12 (size count)
  let env := env.set 13 (size (total + count))
  env.set 14 (.value (.scalar .unit))

/-- The captured unchecked addition is justified by the update's explicit
arithmetic admission, then the native store changes the same counted cells. -/
theorem counter_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (total count selfSlot inputSlot : Nat)
    (bound : total + count < addressLimit)
    (countField : cells.lookup 40 = some (WyhashLocal.word (BitVec.ofNat 64 total)))
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
      .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (h4 : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (h7 : env 7 = some (.value (slot false inputType inputSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨remaining 8, env, frame.install cells, frames⟩)
      (.suspended ⟨remaining 15, counterEnv env id inputSlot total count,
        frame.install (cells.set 40 (WyhashLocal.word (BitVec.ofNat 64 (total + count)))), frames⟩) := by
  have savedSelf := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have savedCount := load_saved frame cells inputSlot usize 8 _ inputApart countRead
  have current := object_word_read frame cells typed 40 (by simp) (BitVec.ofNat 64 total) countField
  have totalBound : total < 2 ^ 64 := by change total < addressLimit; omega
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt totalBound] at current
  have written := object_word_store frame cells typed 40 (by simp) (BitVec.ofNat 64 (total + count))
  have sumBound : total + count < 2 ^ 64 := bound
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumBound] at written
  let e8 := env.set 8 (.value (selfPointer id))
  let e9 := e8.set 9 (.value (.pointer (.pointer true false usize) ⟨id, 40⟩))
  let e10 := e9.set 10 (size total)
  let e11 := e10.set 11 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let e12 := e11.set 12 (size count)
  let e13 := e12.set 13 (size (total + count))
  have p8 := eval_load (.local 4) args env (frame.install cells) _ (.value (selfPointer id))
    (value_local env 4 _ h4 rfl) (congrArg (Except.map Register.value) savedSelf)
  have p9 := eval_field (.local 8) 40 args e8 (frame.install cells) _ _
    (value_local e8 8 _ (by simp [e8, Control.Env.set]) rfl)
    (field_pointer frame cells typed 40 usize (by decide))
  have p10 := eval_load (.local 9) args e9 (frame.install cells)
    (.pointer (.pointer true false usize) ⟨id, 40⟩) (size total)
    (value_local e9 9 _ (by simp [e9, Control.Env.set]) rfl) (congrArg (Except.map Register.value) current)
  have p11 := count_pointer (frame.install cells) args e10 inputSlot 7
    (by simp [e10, e9, e8, Control.Env.set, h7])
  have p12 := eval_load (.local 11) args e11 (frame.install cells)
    (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) (size count)
    (value_local e11 11 _ (by simp [e11, Control.Env.set]) rfl) (congrArg (Except.map Register.value) savedCount)
  have p13 := size_add (frame.install cells) total count 10 12 args e12 bound
    (by simp [e12, e11, e10, Control.Env.set]) (by simp [e12, Control.Env.set])
  have sumValid : (size (total + count)).valid = true := SliceBytesAir.size_valid _ bound
  have p14 := eval_store (.local 9) (.local 13) args e13 (frame.install cells) _
    (.pointer (.pointer true false usize) ⟨id, 40⟩) (size (total + count))
    (value_local e13 9 _ (by simp [e13, e12, e11, e10, e9, Control.Env.set]) rfl)
    (ref_local e13 13 _ (by simp [e13, Control.Env.set]) sumValid) written
  apply AggregateCall.primitive_steps args p8 rfl
  apply AggregateCall.primitive_steps args p9 rfl
  apply AggregateCall.primitive_steps args p10 (SliceBytesAir.size_typed _ (by omega))
  apply AggregateCall.primitive_steps args p11 rfl
  apply AggregateCall.primitive_steps args p12 (SliceBytesAir.size_typed _ (by omega))
  apply AggregateCall.primitive_steps args p13 (SliceBytesAir.size_typed _ bound)
  apply AggregateCall.primitive_steps args p14 rfl
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumBound]
  exact .refl _

def guardBody : Control.Code Ty AggregateCall.Prim Ref true :=
  (GeneratedWyhashUpdate.update.body.blockBody? 15).getD (.ret (.constant (.value (.scalar .unit))))

def longBody : Control.Code Ty AggregateCall.Prim Ref true :=
  match remaining 15 with
  | .block _ _ _ next => next
  | _ => .ret (.constant (.value (.scalar .unit)))

theorem generated_guard : remaining 15 = .block 15 (.scalar .unit) guardBody longBody := by decide +kernel

def guardEnv (env : Env) (id inputSlot length count : Nat) : Env :=
  let env := env.set 16 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let env := env.set 17 (size count)
  let env := env.set 18 (.value (selfPointer id))
  let env := env.set 19 (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  env.set 20 (size length)

theorem guard_loads {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (length count selfSlot inputSlot : Nat)
    (lengthBound : length < addressLimit) (countBound : count < addressLimit)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
      .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (h4 : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (h7 : env 7 = some (.value (slot false inputType inputSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨guardBody, env, frame.install cells, frames⟩)
      (.suspended ⟨guardBody.dropBindings 5, guardEnv env id inputSlot length count, frame.install cells, frames⟩) := by
  have savedSelf := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have savedCount := load_saved frame cells inputSlot usize 8 _ inputApart countRead
  have current := object_word_read frame cells typed 48 (by simp) (BitVec.ofNat 64 length) lengthField
  have wordBound : length < 2 ^ 64 := lengthBound
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound] at current
  let e16 := env.set 16 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let e17 := e16.set 17 (size count)
  let e18 := e17.set 18 (.value (selfPointer id))
  let e19 := e18.set 19 (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  have p16 := count_pointer (frame.install cells) args env inputSlot 7 h7
  have p17 := eval_load (.local 16) args e16 (frame.install cells)
    (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) (size count)
    (value_local e16 16 _ (by simp [e16, Control.Env.set]) rfl) (congrArg (Except.map Register.value) savedCount)
  have p18 := eval_load (.local 4) args e17 (frame.install cells)
    (slot false (.pointer true false objectType) selfSlot) (.value (selfPointer id))
    (value_local e17 4 _ (by simp [e17, e16, Control.Env.set, h4]) rfl)
    (congrArg (Except.map Register.value) savedSelf)
  have p19 := eval_field (.local 18) 48 args e18 (frame.install cells) _ _
    (value_local e18 18 _ (by simp [e18, Control.Env.set]) rfl)
    (field_pointer frame cells typed 48 usize (by decide))
  have p20 := eval_load (.local 19) args e19 (frame.install cells)
    (.pointer (.pointer true false usize) ⟨id, 48⟩) (size length)
    (value_local e19 19 _ (by simp [e19, Control.Env.set]) rfl) (congrArg (Except.map Register.value) current)
  apply AggregateCall.primitive_steps args p16 rfl
  apply AggregateCall.primitive_steps args p17 (SliceBytesAir.size_typed _ countBound)
  apply AggregateCall.primitive_steps args p18 rfl
  apply AggregateCall.primitive_steps args p19 rfl
  apply AggregateCall.primitive_steps args p20 (SliceBytesAir.size_typed _ lengthBound)
  exact .refl _

theorem size_bitcast (state : State) (args : List Register) (env : Env) (reg n : Nat)
    (bound : n < addressLimit) (found : env reg = some (size n)) :
    (AggregateAir.Prim.memory (.scalar (.cast .bitcast (.int false 64) (.local reg)))).eval args env state =
      (.ok (size n), state) := by
  have number := Scalar.unsigned_nat_valid n 64 bound
  have modulo : (n : Int) % 2 ^ 64 = n := Int.emod_eq_of_lt (by omega) (by exact_mod_cast bound)
  apply eval_scalar
  simp only [Scalar.Prim.eval, Scalar.Ref.eval, MemoryAir.scalarEnv, values, found, size,
    number, ↓reduceIte, bind, Except.bind, Scalar.integer, Scalar.normalize,
    Bool.false_and, Bool.false_eq_true, modulo]

theorem buffer_remaining (state : State) (args : List Register) (env : Env) (reg length : Nat)
    (bound : length ≤ 48) (found : env reg = some (size length)) :
    (AggregateAir.Prim.memory (.scalar (.arithmetic .sub .unchecked
      (.constant (.int false 64 48)) (.local reg)))).eval args env state =
        (.ok (size (48 - length)), state) := by
  have limit : 48 < addressLimit := by decide
  have width : length < addressLimit := by omega
  have number := Scalar.unsigned_nat_valid length 64 width
  have contains := Scalar.unsigned_nat_valid (48 - length) 64 (by omega)
  change (Scalar.Ty.int false 64).contains (48 - length : Nat) = true at contains
  have difference : (48 : Int) - length = (48 - length : Nat) := by omega
  apply eval_scalar
  simp [Scalar.Prim.eval, Scalar.Ref.eval, MemoryAir.scalarEnv, values, found, size,
    number, show (Scalar.Value.int false 64 48).valid = true from rfl, ↓reduceIte, bind, Except.bind,
    and_self, Scalar.Arithmetic.eval, Scalar.integer, difference, contains]

theorem size_le (state : State) (args : List Register) (env : Env) (left right a b : Nat)
    (aBound : a < addressLimit) (bBound : b < addressLimit)
    (ha : env left = some (size a)) (hb : env right = some (size b)) :
    (AggregateAir.Prim.memory (.scalar (.comparison .le (.local left) (.local right)))).eval args env state =
      (.ok (.value (.scalar (.bool (decide (a ≤ b))))), state) := by
  have va := Scalar.unsigned_nat_valid a 64 aBound
  have vb := Scalar.unsigned_nat_valid b 64 bBound
  apply eval_scalar
  simp only [Scalar.Prim.eval, Scalar.Ref.eval, MemoryAir.scalarEnv, values, ha, hb, size,
    va, vb, ↓reduceIte, bind, Except.bind, and_self, Scalar.Comparison.eval, Int.ofNat_le]

def chosenEnv (env : Env) (length count : Nat) : Env :=
  let env := env.set 21 (size (48 - length))
  let env := env.set 22 (size count)
  let env := env.set 23 (size (48 - length))
  env.set 24 (.value (.scalar (.bool true)))

def decisionEnv (env : Env) (length count : Nat) : Env :=
  let env := env.set 21 (size (48 - length))
  let env := env.set 22 (size count)
  let env := env.set 23 (size (48 - length))
  env.set 24 (.value (.scalar (.bool (decide (count ≤ 48 - length)))))

/-- Both outcomes use the same native comparison and instruction sequence. -/
theorem guard_select (state : State) (length count : Nat) (bounded : length ≤ 48)
    (countBound : count < addressLimit) (args : List Register) (env : Env)
    (frames : List (Frame Ty AggregateCall.Prim Ref))
    (h17 : env 17 = some (size count)) (h20 : env 20 = some (size length)) :
    Steps AggregateCall.semantics args (.suspended ⟨guardBody.dropBindings 5, env, state, frames⟩)
      (.suspended ⟨if count ≤ 48 - length then bufferedBody.enableLoops else .jump 15 (.constant (.value (.scalar .unit))),
        decisionEnv env length count, state, frames⟩) := by
  have limit : 48 < addressLimit := by decide
  let e21 := env.set 21 (size (48 - length))
  let e22 := e21.set 22 (size count)
  let e23 := e22.set 23 (size (48 - length))
  have p21 := buffer_remaining state args env 20 length bounded h20
  have p22 := size_bitcast state args e21 17 count (by omega) (by simp [e21, Control.Env.set, h17])
  have p23 := size_bitcast state args e22 21 (48 - length) (by omega) (by simp [e22, e21, Control.Env.set])
  have p24 := size_le state args e23 22 23 count (48 - length) (by omega) (by omega)
    (by simp [e23, e22, Control.Env.set]) (by simp [e23, Control.Env.set])
  apply AggregateCall.primitive_steps args p21 (SliceBytesAir.size_typed _ (by omega))
  apply AggregateCall.primitive_steps args p22 (SliceBytesAir.size_typed _ (by omega))
  apply AggregateCall.primitive_steps args p23 (SliceBytesAir.size_typed _ (by omega))
  apply AggregateCall.primitive_steps args p24 rfl
  apply Steps.step
  have shape : guardBody.dropBindings 9 = .branch (.local 24) bufferedBody.enableLoops
      (.jump 15 (.constant (.value (.scalar .unit)))) := by decide +kernel
  change Steps AggregateCall.semantics args
    (step AggregateCall.semantics args ⟨guardBody.dropBindings 9, decisionEnv env length count, state, frames⟩) _
  rw [shape]
  by_cases fits : count ≤ 48 - length <;>
    simp only [step, AggregateCall.semantics, Ref.eval, decisionEnv, Control.Env.set, ↓reduceIte,
      Register.valid, Value.valid, Scalar.Value.valid, bind, Except.bind, fits, decide_true, decide_false] <;>
    exact .refl _

/-- The actual source comparison selects the buffered branch, including empty
updates at a full buffer. No branch choice is passed in as an execution fact. -/
theorem guard_choose (state : State) (length count : Nat) (bounded : length ≤ 48)
    (fits : count ≤ 48 - length) (args : List Register) (env : Env)
    (frames : List (Frame Ty AggregateCall.Prim Ref))
    (h17 : env 17 = some (size count)) (h20 : env 20 = some (size length)) :
    Steps AggregateCall.semantics args (.suspended ⟨guardBody.dropBindings 5, env, state, frames⟩)
      (.suspended ⟨bufferedBody.enableLoops, chosenEnv env length count, state, frames⟩) := by
  have bound : count < addressLimit := by
    have : 48 < addressLimit := by decide
    omega
  simpa only [fits, ↓reduceIte, decisionEnv, chosenEnv, decide_true] using
    guard_select state length count bounded bound args env frames h17 h20

end Compiler.ZigAir.WyhashUpdateAir
