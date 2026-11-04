/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedExpressionHashSlice
import Compiler.ZigAir.AggregateSavedValue
import Compiler.ZigAir.MemoryWordByteSlice

set_option maxRecDepth 4096

namespace Compiler.ZigAir.SliceBytesAir
open Memory Memory.WordArray AggregateAir

abbrev wordSlice : Ty := .slice false word
abbrev bytePointer : Ty := .pointer false true ByteAccess.byte
abbrev byteSlice : Ty := .slice false ByteAccess.byte
abbrev slot (writable : Bool) (child : Ty) (id : Nat) : Value :=
  .pointer (.pointer writable false child) ⟨id, 0⟩
abbrev size (n : Nat) : Register := .value (.scalar (.int false 64 n))

def constructCode : Code :=
  .bind 40 usize (.memory (.scalar (.arithmetic .sub .unchecked (.local 37) (.constant (.int false 64 0)))))
  (.bind 43 (.scalar .unit) (.memory (.checkBounds (.constant (.scalar (.int false 64 0))) (.local 37) .unbounded))
  (.bind 41 byteSlice (.memory (.slice byteSlice (.local 39) (.local 40)))
  (.ret (.local 41))))

def advanceCode : Code :=
  .bind 38 bytePointer (.load (.local 34))
  (.bind 39 bytePointer (.memory (.offsetPointer false (.local 38) (.constant (.scalar (.int false 64 0))))) constructCode)

def finishCode : Code :=
  .bind 34 (.pointer false false bytePointer) (.memory (.pointerCast (.pointer false false bytePointer) (.local 32)))
  (.bind 35 (.pointer false false usize) (.memory (.pointerField true (.local 3)))
  (.bind 36 usize (.load (.local 35))
  (.bind 37 usize (.memory (.scalar (.arithmetic .mul .unchecked (.local 36) (.constant (.int false 64 4))))) advanceCode)))

def nonemptyCode : Code :=
  .bind 30 (.pointer false true word) (.memory (.slicePtr (.local 0)))
  (.bind 31 bytePointer (.memory (.wordByteCast false true 4 (.local 30)))
  (.bind 32 (.pointer true false bytePointer) (.memory (.alloc bytePointer))
  (.bind 33 (.scalar .unit) (.store (.local 32) (.local 31)) finishCode)))

def branchCode : Code :=
  .block 14 (.scalar .bool)
    (.branch (.local 13) (.jump 14 (.constant (.value (.scalar (.bool true)))))
      (.jump 14 (.constant (.value (.scalar (.bool false))))))
    (.branch (.local 14) (.ret (.constant .emptyBytes)) (.jump 9 (.constant (.value (.scalar .unit)))))

def compareCode : Code :=
  .bind 13 (.scalar .bool) (.memory (.scalar (.comparison .eq (.local 12) (.constant (.int false 64 0))))) branchCode

def checkCode : Code :=
  .bind 12 usize (.memory (.scalar (.cast .bitcast (.int false 64) (.local 11)))) compareCode

def chooseCode (next : Code) : Code :=
  .bind 3 (.pointer false false wordSlice) (.memory (.pointerCast (.pointer false false wordSlice) (.local 1)))
  (.block 9 (.scalar .unit)
    (.bind 10 (.pointer false false usize) (.memory (.pointerField true (.local 3)))
    (.bind 11 usize (.load (.local 10)) checkCode)) next)

theorem generated_body : GeneratedExpressionHashSlice.arguments.body =
    .bind 0 wordSlice (.argument 0)
    (.bind 1 (.pointer true false wordSlice) (.memory (.alloc wordSlice))
    (.bind 2 (.scalar .unit) (.store (.local 1) (.local 0)) (chooseCode nonemptyCode))) := rfl

theorem slice_valid (view : View) (bound : view.length < addressLimit) : view.readonlySlice.valid = true := by
  simpa only [View.readonlySlice, Value.valid, addressLimit, decide_eq_true_eq] using bound

theorem size_valid (n : Nat) (bound : n < addressLimit) : (size n).valid = true :=
  Scalar.unsigned_nat_valid n 64 bound

theorem size_typed (n : Nat) (bound : n < addressLimit) : (size n).hasType usize = true := by
  simpa only [Register.hasType, Register.type, Register.valid, Value.type, Scalar.Value.type,
    Value.valid, usize, decide_true, Bool.true_and] using Scalar.unsigned_nat_valid n 64 bound

def checkEnv (env : Env) (length : Nat) : Env :=
  let e := env.set 12 (size length)
  (e.set 13 (.value (.scalar (.bool (decide (length = 0)))))).set 14
    (.value (.scalar (.bool (decide (length = 0)))))

def chooseHeadEnv (env : Env) (id length : Nat) : Env :=
  let e := env.set 3 (.value (slot false wordSlice id))
  let e := e.set 10 (.value (.pointer (.pointer false false usize) ⟨id, 8⟩))
  e.set 11 (size length)

def chooseEnv (env : Env) (id length : Nat) : Env :=
  (checkEnv (chooseHeadEnv env id length) length).set 9 (.value (.scalar .unit))

theorem branch_steps (state : State) (flag : Bool) (args : List Register) (env : Env)
    (h13 : env 13 = some (.value (.scalar (.bool flag)))) :
    branchCode.eval semantics args env state =
      if flag then .returned .emptyBytes state
      else .jumped 9 (.value (.scalar .unit)) (env.set 14 (.value (.scalar (.bool flag)))) state := by
  cases flag <;> simp [branchCode, Control.Code.eval, semantics, Ref.eval, h13, Control.Env.set,
    Register.hasType, Register.type, Register.valid, Value.type, Value.valid, Scalar.Value.type, Scalar.Value.valid,
    bind, Except.bind]

theorem compare_steps (state : State) (length : Nat) (args : List Register) (env : Env)
    (width : length < addressLimit) (h12 : env 12 = some (size length)) :
    compareCode.eval semantics args env state =
      if length = 0 then .returned .emptyBytes state
      else .jumped 9 (.value (.scalar .unit))
        ((env.set 13 (.value (.scalar (.bool (decide (length = 0)))))).set 14
          (.value (.scalar (.bool (decide (length = 0)))))) state := by
  have number := Scalar.unsigned_nat_valid length 64 width
  have compared : (Prim.memory (.scalar (.comparison .eq (.local 12) (.constant (.int false 64 0))))).eval
      args env state = (.ok (.value (.scalar (.bool (decide (length = 0))))), state) := by
    apply eval_scalar
    simp only [Scalar.Prim.eval, Scalar.Ref.eval, MemoryAir.scalarEnv, values, h12,
      size, number, ↓reduceIte, bind, Except.bind, and_self, Scalar.Comparison.eval, Int.natCast_eq_zero,
      show (Scalar.Value.int false 64 0).valid = true from rfl]
  rw [compareCode, bind_ok _ _ _ _ _ _ _ _ _ compared (by rfl),
    branch_steps state (decide (length = 0)) args _ (by simp [Control.Env.set])]
  simp

theorem check_steps (state : State) (length : Nat) (args : List Register) (env : Env)
    (width : length < addressLimit) (h11 : env 11 = some (size length)) :
    checkCode.eval semantics args env state =
      if length = 0 then .returned .emptyBytes state
      else .jumped 9 (.value (.scalar .unit)) (checkEnv env length) state := by
  have number := Scalar.unsigned_nat_valid length 64 width
  have bound : (length : Int) < 2 ^ 64 := by exact_mod_cast width
  have modulo : (length : Int) % 2 ^ 64 = length := Int.emod_eq_of_lt (by omega) bound
  have casted : (Prim.memory (.scalar (.cast .bitcast (.int false 64) (.local 11)))).eval args env state =
      (.ok (size length), state) := by
    apply eval_scalar
    simp only [Scalar.Prim.eval, Scalar.Ref.eval, MemoryAir.scalarEnv, values, h11, size,
      number, ↓reduceIte, bind, Except.bind, Scalar.integer, Scalar.normalize,
      Bool.false_and, Bool.false_eq_true, modulo]
  have typed : (size length).hasType usize = true := by
    simp only [Register.hasType, Register.type, Register.valid, Value.type, Scalar.Value.type,
      Value.valid, usize, decide_true, Bool.true_and, number]
  rw [checkCode, bind_ok _ _ _ _ _ _ _ _ _ casted typed]
  exact compare_steps state length args _ width (by simp [Control.Env.set])

theorem choose_steps (next : Code) (state : State) (view : View) (id : Nat) (args : List Register) (env : Env)
    (width : view.length < addressLimit)
    (h1 : env 1 = some (.value (slot true wordSlice id)))
    (read : Memory.load state (slot true wordSlice id) = .ok view.readonlySlice)
    (owner : (state.heap.lookup id).map Allocation.type = some wordSlice) :
    (chooseCode next).eval semantics args env state =
      if view.length = 0 then .returned .emptyBytes state
      else next.eval semantics args (chooseEnv env id view.length) state := by
  have cast := pointerCast_readonly_of_load state true false wordSlice ⟨id, 0⟩ view.readonlySlice read
  have length := SavedValue.slice_length state id false word (view.address 0) view.length read owner
  let e3 := env.set 3 (.value (slot false wordSlice id))
  let e10 := e3.set 10 (.value (.pointer (.pointer false false usize) ⟨id, 8⟩))
  have casted : (Prim.memory (.pointerCast (.pointer false false wordSlice) (.local 1))).eval args env state =
      (.ok (.value (slot false wordSlice id)), state) := by
    simp only [Prim.eval, Prim.transition, MemoryAir.Prim.transition, MemoryAir.Ref.eval, values,
      h1, Value.valid, ↓reduceIte, cast, bind, Except.bind]
  have field : (Prim.memory (.pointerField true (.local 3))).eval args e3 state =
      (.ok (.value (.pointer (.pointer false false usize) ⟨id, 8⟩)), state) := by
    simp only [Prim.eval, Prim.transition, MemoryAir.Prim.transition, MemoryAir.Ref.eval, values,
      e3, Control.Env.set, ↓reduceIte, Value.valid, Memory.pointerField, bind, Except.bind, Nat.zero_add]
  have loaded : (Prim.load (.local 10)).eval args e10 state = (.ok (size view.length), state) := by
    apply eval_load _ _ _ _ (.pointer (.pointer false false usize) ⟨id, 8⟩)
    · exact value_local e10 10 _ (by simp [e10, Control.Env.set]) rfl
    · simp only [AggregateAir.load, show aggregateType usize = false from rfl, Bool.false_eq_true, ↓reduceIte,
        length, bind, Except.bind, pure, Except.pure]
  have typed : (size view.length).hasType usize = true := by
    simpa only [Register.hasType, Register.type, Register.valid, Value.type, Scalar.Value.type,
      Value.valid, usize, decide_true, Bool.true_and] using Scalar.unsigned_nat_valid view.length 64 width
  rw [chooseCode, bind_ok _ _ _ _ _ _ _ _ _ casted (by rfl), Control.Code.eval,
    bind_ok _ _ _ _ _ _ _ _ _ field (by rfl), bind_ok _ _ _ _ _ _ _ _ _ loaded typed,
    check_steps state view.length args _ width (by simp [e10, Control.Env.set])]
  by_cases empty : view.length = 0
  all_goals simp only [empty, ↓reduceIte, semantics, chooseEnv, chooseHeadEnv, e10, e3,
    Register.hasType, Register.type, Register.valid, Value.type, Value.valid, Scalar.Value.type,
    Scalar.Value.valid, decide_true, Bool.true_and]

theorem memory_local (env : Env) (id : Nat) (value : Value)
    (found : env id = some (.value value)) (valid : value.valid = true) :
    (MemoryAir.Ref.local id).eval (values env) = .ok value := by
  rw [MemoryAir.Ref.eval_local]
  simp only [values, found, valid, ↓reduceIte]

theorem scalar_size (env : Env) (id n : Nat) (bound : n < addressLimit)
    (found : env id = some (size n)) :
    (Scalar.Ref.local id).eval (MemoryAir.scalarEnv (values env)) = .ok (.int false 64 n) := by
  have small : n < 2 ^ 64 := bound
  have read := scalar_local env id (BitVec.ofNat 64 n)
    (by simpa only [AggregateAir.number, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using found)
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using read

theorem natural_size (env : Env) (id n : Nat) (bound : n < addressLimit)
    (found : env id = some (size n)) :
    (MemoryAir.Ref.local id).natural (values env) = .ok n := by
  have read := memory_local env id (.scalar (.int false 64 n)) found (Scalar.unsigned_nat_valid n 64 bound)
  simpa only [Int.toNat_natCast] using MemoryAir.Ref.natural_of_eval _ _ _ read

theorem subtract_zero (state : State) (n id : Nat) (args : List Register) (env : Env)
    (bounded : n < addressLimit) (found : env id = some (size n)) :
    (Prim.memory (.scalar (.arithmetic .sub .unchecked (.local id) (.constant (.int false 64 0))))).eval
      args env state = (.ok (size n), state) := by
  have read := scalar_size env id n bounded found
  have zeroValid := Scalar.unsigned_nat_valid 0 64 (by decide)
  simp only [Int.natCast_zero] at zeroValid
  have zero : (Scalar.Ref.constant (.int false 64 0)).eval (MemoryAir.scalarEnv (values env)) = .ok (.int false 64 0) := by
    simp only [Scalar.Ref.eval, zeroValid, ↓reduceIte]
  have contains : (Scalar.Ty.int false 64).contains (n : Int) = true := Scalar.unsigned_nat_valid n 64 bounded
  have arithmetic := scalar_arithmetic .sub .unchecked (.local id) (.constant (.int false 64 0))
    [] (MemoryAir.scalarEnv (values env)) false 64 n 0 read zero
  have integer : Scalar.integer false 64 n .unchecked = .ok (.int false 64 n) := by
    simp [Scalar.integer, contains]
  apply eval_scalar
  rw [arithmetic, Scalar.Arithmetic.eval, Int.sub_zero, integer]

theorem bounds_zero (state : State) (n id : Nat) (args : List Register) (env : Env)
    (bounded : n < addressLimit) (found : env id = some (size n)) :
    (Prim.memory (.checkBounds (.constant (.scalar (.int false 64 0))) (.local id) .unbounded)).eval
      args env state = (.ok (.value (.scalar .unit)), state) := by
  apply eval_memory
  have read := natural_size env id n bounded found
  have zero : (MemoryAir.Ref.constant (.scalar (.int false 64 0))).natural (values env) = .ok 0 := by
    exact MemoryAir.Ref.natural_of_eval _ _ 0
      (MemoryAir.Ref.eval_constant_of_valid _ _ (Scalar.unsigned_nat_valid 0 64 (by decide)))
  rw [MemoryAir.Prim.eval_bounds, read, zero]
  simp only [MemoryAir.Bound.eval, checkSliceBounds, bind, Except.bind, Nat.zero_le,
    Option.isNone_none, true_or, and_self, ↓reduceIte, pure, Except.pure]

theorem make_slice (state : State) (view : View) (items : List (BitVec 32))
    (args : List Register) (env : Env) (represented : Represents state view items)
    (positive : 0 < view.length) (bounded : view.length * 4 < addressLimit)
    (lengthId pointerId : Nat) (length : env lengthId = some (size (view.length * 4)))
    (pointer : env pointerId = some (.value (ByteAccess.pointer false true (view.address 0)))) :
    (Prim.memory (.slice byteSlice (.local pointerId) (.local lengthId))).eval args env state =
      (.ok (.value view.byteSlice), state) := by
  apply eval_memory
  have count := natural_size env lengthId (view.length * 4) bounded length
  have data := memory_local env pointerId (ByteAccess.pointer false true (view.address 0)) pointer rfl
  rw [MemoryAir.Prim.eval_slice, data, count]
  simp only [bind, Except.bind, represented.byte_slice state view items positive bounded]

theorem construct_steps (state : State) (view : View) (items : List (BitVec 32))
    (args : List Register) (env : Env) (represented : Represents state view items)
    (positive : 0 < view.length) (bounded : view.length * 4 < addressLimit)
    (h37 : env 37 = some (size (view.length * 4)))
    (h39 : env 39 = some (.value (ByteAccess.pointer false true (view.address 0)))) :
    constructCode.eval semantics args env state = .returned (.value view.byteSlice) state := by
  let e40 := env.set 40 (size (view.length * 4))
  let e43 := e40.set 43 (.value (.scalar .unit))
  have subtracted := subtract_zero state (view.length * 4) 37 args env bounded h37
  have checked := bounds_zero state (view.length * 4) 37 args e40 bounded (by simp [e40, Control.Env.set, h37])
  have made := make_slice state view items args e43 represented positive bounded 40 39
    (by simp [e43, e40, Control.Env.set]) (by simp [e43, e40, Control.Env.set, h39])
  have typed : (size (view.length * 4)).hasType usize = true := by
    simpa only [Register.hasType, Register.type, Register.valid, Value.type, Scalar.Value.type,
      Value.valid, usize, decide_true, Bool.true_and] using Scalar.unsigned_nat_valid (view.length * 4) 64 bounded
  have sliceValid : (Register.value view.byteSlice).valid = true := by
    simpa only [Register.valid, View.byteSlice, Value.valid, decide_eq_true_eq] using bounded
  have sliceTyped : (Register.value view.byteSlice).hasType byteSlice = true := by
    simp only [Register.hasType, Register.type, View.byteSlice, Value.type, decide_true, Bool.true_and]
    exact sliceValid
  rw [constructCode, bind_ok _ _ _ _ _ _ _ _ _ subtracted typed,
    bind_ok _ _ _ _ _ _ _ _ _ checked (by rfl), bind_ok _ _ _ _ _ _ _ _ _ made sliceTyped]
  exact ret_ok _ _ _ _ _ (ref_local _ 41 _ (by simp [Control.Env.set]) sliceValid)

theorem advance_steps (state : State) (view : View) (items : List (BitVec 32)) (pointerId : Nat)
    (args : List Register) (env : Env) (represented : Represents state view items)
    (positive : 0 < view.length) (bounded : view.length * 4 < addressLimit)
    (h34 : env 34 = some (.value (slot false bytePointer pointerId)))
    (h37 : env 37 = some (size (view.length * 4)))
    (pointerRead : Memory.load state (slot false bytePointer pointerId) =
      .ok (ByteAccess.pointer false true (view.address 0))) :
    advanceCode.eval semantics args env state = .returned (.value view.byteSlice) state := by
  let e38 := env.set 38 (.value (ByteAccess.pointer false true (view.address 0)))
  have loaded : (Prim.load (.local 34)).eval args env state =
      (.ok (.value (ByteAccess.pointer false true (view.address 0))), state) := by
    apply eval_load _ _ _ _ (slot false bytePointer pointerId)
    · exact value_local env 34 _ h34 rfl
    · simp only [AggregateAir.load, show aggregateType bytePointer = false from rfl,
        Bool.false_eq_true, ↓reduceIte, pointerRead, bind, Except.bind, pure, Except.pure]
  have shifted : (Prim.memory (.offsetPointer false (.local 38) (.constant (.scalar (.int false 64 0))))).eval
      args e38 state = (.ok (.value (ByteAccess.pointer false true (view.address 0))), state) := by
    apply eval_memory
    have data := memory_local e38 38 (ByteAccess.pointer false true (view.address 0))
      (by simp [e38, Control.Env.set]) rfl
    have zero : (MemoryAir.Ref.constant (.scalar (.int false 64 0))).natural (values e38) = .ok 0 := by
      exact MemoryAir.Ref.natural_of_eval _ _ 0
        (MemoryAir.Ref.eval_constant_of_valid _ _ (Scalar.unsigned_nat_valid 0 64 (by decide)))
    rw [MemoryAir.Prim.eval_offset, data, zero]
    simp only [bind, Except.bind, represented.byte_offset_zero state view items positive]
  rw [advanceCode, bind_ok _ _ _ _ _ _ _ _ _ loaded (by rfl), bind_ok _ _ _ _ _ _ _ _ _ shifted (by rfl)]
  exact construct_steps state view items args _ represented positive bounded
    (by simp [e38, Control.Env.set, h37]) (by simp [Control.Env.set])

theorem multiply_four (state : State) (n id : Nat) (args : List Register) (env : Env)
    (bounded : n * 4 < addressLimit) (found : env id = some (size n)) :
    (Prim.memory (.scalar (.arithmetic .mul .unchecked (.local id) (.constant (.int false 64 4))))).eval
      args env state = (.ok (size (n * 4)), state) := by
  have read := scalar_size env id n (by omega) found
  have four : (Scalar.Ref.constant (.int false 64 4)).eval (MemoryAir.scalarEnv (values env)) = .ok (.int false 64 4) := by
    simp only [Scalar.Ref.eval, show (Scalar.Value.int false 64 4).valid = true from rfl, ↓reduceIte]
  have arithmetic := scalar_arithmetic .mul .unchecked (.local id) (.constant (.int false 64 4))
    [] (MemoryAir.scalarEnv (values env)) false 64 n 4 read four
  have contains : (Scalar.Ty.int false 64).contains ((n * 4 : Nat) : Int) = true :=
    Scalar.unsigned_nat_valid (n * 4) 64 bounded
  simp only [Int.natCast_mul] at contains
  change (Scalar.Ty.int false 64).contains ((n : Int) * 4) = true at contains
  have integer : Scalar.integer false 64 ((n : Int) * 4) .unchecked = .ok (.int false 64 (n * 4 : Nat)) := by
    simp [Scalar.integer, contains, Int.natCast_mul]
  apply eval_scalar
  rw [arithmetic, Scalar.Arithmetic.eval, integer]

theorem finish_steps (state : State) (view : View) (items : List (BitVec 32)) (sliceId pointerId : Nat)
    (args : List Register) (env : Env) (represented : Represents state view items)
    (positive : 0 < view.length) (bounded : view.length * 4 < addressLimit)
    (h3 : env 3 = some (.value (slot false wordSlice sliceId)))
    (h32 : env 32 = some (.value (slot true bytePointer pointerId)))
    (lengthRead : Memory.load state (.pointer (.pointer false false usize) ⟨sliceId, 8⟩) =
      .ok (.scalar (.int false 64 view.length)))
    (pointerRead : Memory.load state (slot true bytePointer pointerId) =
      .ok (ByteAccess.pointer false true (view.address 0))) :
    finishCode.eval semantics args env state = .returned (.value view.byteSlice) state := by
  let e34 := env.set 34 (.value (slot false bytePointer pointerId))
  let e35 := e34.set 35 (.value (.pointer (.pointer false false usize) ⟨sliceId, 8⟩))
  let e36 := e35.set 36 (size view.length)
  have casted : (Prim.memory (.pointerCast (.pointer false false bytePointer) (.local 32))).eval
      args env state = (.ok (.value (slot false bytePointer pointerId)), state) := by
    apply eval_memory
    rw [MemoryAir.Prim.eval_cast, memory_local env 32 (slot true bytePointer pointerId) h32 rfl]
    simp only [bind, Except.bind, pointerCast_readonly_of_load state true false bytePointer ⟨pointerId, 0⟩ _ pointerRead]
  have field : (Prim.memory (.pointerField true (.local 3))).eval args e34 state =
      (.ok (.value (.pointer (.pointer false false usize) ⟨sliceId, 8⟩)), state) := by
    have data := memory_local e34 3 (slot false wordSlice sliceId) (by simp [e34, Control.Env.set, h3]) rfl
    simp only [Prim.eval, Prim.transition, MemoryAir.Prim.transition, data, Memory.pointerField,
      bind, Except.bind, ↓reduceIte, Nat.zero_add]
  have loaded : (Prim.load (.local 35)).eval args e35 state = (.ok (size view.length), state) := by
    apply eval_load _ _ _ _ (.pointer (.pointer false false usize) ⟨sliceId, 8⟩)
    · exact value_local e35 35 _ (by simp [e35, Control.Env.set]) rfl
    · simp only [AggregateAir.load, show aggregateType usize = false from rfl, Bool.false_eq_true,
        ↓reduceIte, lengthRead, bind, Except.bind, pure, Except.pure]
  have multiplied := multiply_four state view.length 36 args e36 bounded (by simp [e36, Control.Env.set])
  rw [finishCode, bind_ok _ _ _ _ _ _ _ _ _ casted (by rfl), bind_ok _ _ _ _ _ _ _ _ _ field (by rfl),
    bind_ok _ _ _ _ _ _ _ _ _ loaded (size_typed view.length (by omega)),
    bind_ok _ _ _ _ _ _ _ _ _ multiplied (size_typed (view.length * 4) bounded)]
  exact advance_steps state view items pointerId args _ represented positive bounded
    (by simp [e36, e35, e34, Control.Env.set]) (by simp [Control.Env.set]) pointerRead

theorem nonempty_verified (state : State) (view : View) (items : List (BitVec 32)) (sliceId : Nat)
    (args : List Register) (env : Env) (initial : state.valid = true)
    (represented : Represents state view items) (positive : 0 < view.length)
    (bounded : view.length * 4 < addressLimit)
    (h0 : env 0 = some (.value view.readonlySlice))
    (h3 : env 3 = some (.value (slot false wordSlice sliceId)))
    (lengthRead : Memory.load state (.pointer (.pointer false false usize) ⟨sliceId, 8⟩) =
      .ok (.scalar (.int false 64 view.length))) :
    ∃ after, StackFrame state after ∧
      (nonemptyCode.eval semantics args env state = .returned (.value view.byteSlice) after ∨
       nonemptyCode.eval semantics args env state = .fault .outOfMemory after) := by
  let wordPointer := Value.pointer (.pointer false true word) (view.address 0)
  let bytes := ByteAccess.pointer false true (view.address 0)
  let e30 := env.set 30 (.value wordPointer)
  let e31 := e30.set 31 (.value bytes)
  have extracted : (Prim.memory (.slicePtr (.local 0))).eval args env state = (.ok (.value wordPointer), state) := by
    have data := memory_local env 0 view.readonlySlice h0 (slice_valid view (by omega))
    simp only [Prim.eval, Prim.transition, MemoryAir.Prim.transition, data, View.readonlySlice, bind, Except.bind]
    rfl
  have casted : (Prim.memory (.wordByteCast false true 4 (.local 30))).eval args e30 state =
      (.ok (.value bytes), state) := by
    have data := memory_local e30 30 wordPointer (by simp [e30, Control.Env.set]) rfl
    simp only [Prim.eval, Prim.transition, MemoryAir.Prim.transition, data, wordPointer,
      represented.byte_cast state view items positive, bind, Except.bind]
    rfl
  have head : nonemptyCode.eval semantics args env state =
      match SavedValue.save state bytes with
      | (.error fault, after) => .fault fault after
      | (.ok (), after) => finishCode.eval semantics args
          ((e31.set 32 (.value (slot true bytePointer state.nextId))).set 33 (.value (.scalar .unit))) after := by
    rw [nonemptyCode, bind_ok _ _ _ _ _ _ _ _ _ extracted (by rfl), bind_ok _ _ _ _ _ _ _ _ _ casted (by rfl)]
    exact SavedValue.bindings bytes (.local 31) 32 33 finishCode args e31 state
      (ref_local _ 31 _ (by simp [e31, Control.Env.set]) rfl)
  obtain ⟨result, after, saved, frame, failed | ⟨success, read, _⟩⟩ :=
    SavedValue.verified state bytes ⟨8, 8⟩ initial rfl rfl (by decide)
  · exact ⟨after, frame, Or.inr (by rw [head, saved, failed])⟩
  · refine ⟨after, frame, Or.inl ?_⟩
    rw [head, saved, success]
    exact finish_steps after view items sliceId state.nextId args _ (represented.extend frame) positive bounded
      (by simp [e31, e30, Control.Env.set, h3]) (by simp [Control.Env.set])
      (frame.old_load false false usize _ _ lengthRead) read

def result (view : View) : Register :=
  if view.length = 0 then .emptyBytes else .value view.byteSlice

theorem result_typed (view : View) (bounded : view.length * 4 < addressLimit) :
    (result view).hasType byteSlice = true := by
  by_cases empty : view.length = 0
  · simp only [result, if_pos empty]; rfl
  · simp only [result, if_neg empty, Register.hasType, Register.type, Register.valid,
      View.byteSlice, Value.type, Value.valid, bounded, decide_true, Bool.true_and]

/-- Complete captured execution, with both stack allocations, both source
branches and the original slice guard. Allocation failures are retained, and
cleanup restores the caller heap without rewinding either allocation cursor. -/
theorem verified (state : State) (view : View) (items : List (BitVec 32))
    (initial : state.valid = true) (represented : Represents state view items)
    (bounded : view.length * 4 < addressLimit) :
    ∃ output after, GeneratedExpressionHashSlice.arguments.run [.value view.readonlySlice] state = (output, after) ∧
      StackFrame state after ∧ after.heap = state.heap ∧
      (output = .ok (result view) ∨ output = .error .outOfMemory) := by
  have width : view.length < addressLimit := by omega
  have inputValid := slice_valid view width
  have inputTyped : (Register.value view.readonlySlice).hasType wordSlice = true := by
    simp only [Register.hasType, Register.type, View.readonlySlice, Value.type, decide_true, Bool.true_and]
    exact inputValid
  let args := [Register.value view.readonlySlice]
  let env : Env := Control.Env.set (fun _ => none) 0 (.value view.readonlySlice)
  have admitted : (state.valid && decide (args.length = GeneratedExpressionHashSlice.arguments.parameters.length) &&
      (args.zip GeneratedExpressionHashSlice.arguments.parameters).all (fun (value, type) => value.hasType type)) = true := by
    simp only [args, GeneratedExpressionHashSlice.arguments, initial, List.length_cons, List.length_nil,
      decide_true, List.zip_cons_cons, List.zip_nil_left, List.all_cons, List.all_nil, inputTyped,
      Bool.and_self]
  have head : GeneratedExpressionHashSlice.arguments.body.eval semantics args (fun _ => none) state =
      match SavedValue.save state view.readonlySlice with
      | (.error fault, after) => .fault fault after
      | (.ok (), after) => (chooseCode nonemptyCode).eval semantics args
          ((env.set 1 (.value (slot true wordSlice state.nextId))).set 2 (.value (.scalar .unit))) after := by
    rw [generated_body, bind_ok _ _ _ _ _ _ state state (.value view.readonlySlice)
      (by simp only [Prim.eval, Prim.transition, args, List.getElem?_cons_zero]) inputTyped]
    exact SavedValue.bindings view.readonlySlice (.local 0) 1 2 (chooseCode nonemptyCode) args env state
      (ref_local _ 0 _ (by simp [env, Control.Env.set]) inputValid)
  obtain ⟨saved, middle, savedRun, frame, failed | ⟨success, read, owner⟩⟩ :=
    SavedValue.verified state view.readonlySlice ⟨16, 8⟩ initial inputValid rfl (by decide)
  · have ran : GeneratedExpressionHashSlice.arguments.body.eval semantics args (fun _ => none) state =
        .fault .outOfMemory middle := by rw [head, savedRun, failed]
    exact ⟨_, _, run_fault _ _ _ _ _ admitted ran, frame.cleaned, frame.cleanup_heap, Or.inr rfl⟩
  · let savedEnv := (env.set 1 (.value (slot true wordSlice state.nextId))).set 2 (.value (.scalar .unit))
    have chosen := choose_steps nonemptyCode middle view state.nextId args savedEnv width
      (by simp [savedEnv, Control.Env.set]) read owner
    have body : GeneratedExpressionHashSlice.arguments.body.eval semantics args (fun _ => none) state =
        if view.length = 0 then .returned .emptyBytes middle
        else nonemptyCode.eval semantics args (chooseEnv savedEnv state.nextId view.length) middle := by
      rw [head, savedRun, success]
      exact chosen
    by_cases empty : view.length = 0
    · have ran : GeneratedExpressionHashSlice.arguments.body.eval semantics args (fun _ => none) state =
          .returned (result view) middle := by simpa only [empty, ↓reduceIte, result] using body
      exact ⟨_, _, run_return _ _ _ _ _ admitted ran (result_typed view bounded),
        frame.cleaned, frame.cleanup_heap, Or.inl rfl⟩
    · obtain ⟨after, remaining, returned | failed⟩ := nonempty_verified middle view items state.nextId args
        (chooseEnv savedEnv state.nextId view.length) frame.valid (represented.extend frame) (by omega) bounded
        (by simp [chooseEnv, chooseHeadEnv, checkEnv, savedEnv, env, Control.Env.set])
        (by simp [chooseEnv, chooseHeadEnv, checkEnv, Control.Env.set])
        (SavedValue.slice_length middle state.nextId false word (view.address 0) view.length read owner)
      · have ran : GeneratedExpressionHashSlice.arguments.body.eval semantics args (fun _ => none) state =
            .returned (result view) after := by simpa only [empty, ↓reduceIte, result, returned] using body
        exact ⟨_, _, run_return _ _ _ _ _ admitted ran (result_typed view bounded),
          (frame.trans remaining).cleaned, (frame.trans remaining).cleanup_heap, Or.inl rfl⟩
      · have ran : GeneratedExpressionHashSlice.arguments.body.eval semantics args (fun _ => none) state =
            .fault .outOfMemory after := by simpa only [if_neg empty, failed] using body
        exact ⟨_, _, run_fault _ _ _ _ _ admitted ran,
          (frame.trans remaining).cleaned, (frame.trans remaining).cleanup_heap, Or.inr rfl⟩

end Compiler.ZigAir.SliceBytesAir
