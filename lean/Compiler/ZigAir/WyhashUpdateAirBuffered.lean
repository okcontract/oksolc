/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAir
import Compiler.ZigAir.AggregateExecutionProofs
import Compiler.ZigAir.SliceBytesAir

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction
open WyhashInit (object_word_read object_word_store)

abbrev inputType : Ty := .slice false ByteSlice.byte
abbrev slot (writable : Bool) (child : Ty) (id : Nat) : Value :=
  .pointer (.pointer writable false child) ⟨id, 0⟩
abbrev size := SliceBytesAir.size

/-- Checked projection of the complete early-return branch. The equations
below bind it back to the original body and locate the remaining instructions. -/
def bufferedBody : AggregateCall.Code :=
  (do
    let body ← GeneratedWyhashUpdate.update.body.blockBody? 15
    let .branch _ yes _ := body.dropBindings 9 | none
    yes.finite?).getD (.ret (.constant (.value (.scalar .unit))))

def bufferedReturn : AggregateCall.Code :=
  .bind 40 (.pointer true false objectType) (.primitive (.load (.local 4)))
  (.bind 41 (.pointer true false usize) (.primitive (.fieldPointer (.local 40) 48))
  (.bind 42 usize (.primitive (.load (.local 41)))
  (.bind 43 (.pointer false false usize) (.primitive (.memory (.pointerField true (.local 7))))
  (.bind 44 usize (.primitive (.load (.local 43)))
  (.bind 45 usize (.primitive (.memory (.scalar (.arithmetic .add .unchecked (.local 42) (.local 44)))))
  (.bind 46 (.scalar .unit) (.primitive (.store (.local 41) (.local 45)))
  (.ret (.constant (.value (.scalar .unit))))))))))

theorem generated_buffered_branch :
    (GeneratedWyhashUpdate.update.body.blockBody? 15).map (fun body => body.dropBindings 9) =
      some (.branch (.local 24) bufferedBody.enableLoops (.jump 15 (.constant (.value (.scalar .unit))))) := by
  decide +kernel

theorem generated_buffered_return : bufferedBody.dropBindings 16 = bufferedReturn := by
  decide +kernel

def bufferedCopy : AggregateCall.Code :=
  .bind 25 (.pointer true false objectType) (.primitive (.load (.local 4)))
  (.bind 26 (.pointer true false (.array 48 ByteSlice.byte)) (.primitive (.fieldPointer (.local 25) 56))
  (.bind 27 (.pointer true false objectType) (.primitive (.load (.local 4)))
  (.bind 28 (.pointer true false usize) (.primitive (.fieldPointer (.local 27) 48))
  (.bind 29 usize (.primitive (.load (.local 28)))
  (.bind 30 (.pointer false false usize) (.primitive (.memory (.pointerField true (.local 7))))
  (.bind 31 usize (.primitive (.load (.local 30)))
  (.bind 32 (.pointer true true ByteSlice.byte)
    (.primitive (.memory (.pointerCast (.pointer true true ByteSlice.byte) (.local 26))))
  (.bind 33 (.pointer true true ByteSlice.byte) (.primitive (.memory (.offsetPointer false (.local 32) (.local 29))))
  (.bind 34 usize (.primitive (.memory (.scalar (.arithmetic .add .unchecked (.local 29) (.local 31)))))
  (.bind 652 (.scalar .unit) (.primitive (.memory (.checkBounds (.local 29) (.local 34) (.array 48))))
  (.bind 35 (.slice true ByteSlice.byte) (.primitive (.memory (.slice (.slice true ByteSlice.byte) (.local 33) (.local 31))))
  (.bind 36 usize (.primitive (.memory (.sliceLen (.local 35))))
  (.bind 37 usize (.primitive (.memory (.sliceLen (.local 1))))
  (.bind 38 (.pointer false true ByteSlice.byte) (.primitive (.memory (.slicePtr (.local 1))))
  (.bind 39 (.scalar .unit) (.copyBytes (.local 35) (.local 38)) bufferedReturn)))))))))))))))

theorem generated_buffered_body : bufferedBody = bufferedCopy := by decide +kernel

theorem size_add (state : State) (a b left right : Nat) (args : List Register) (env : Env)
    (bound : a + b < addressLimit) (ha : env left = some (size a)) (hb : env right = some (size b)) :
    (AggregateAir.Prim.memory (.scalar (.arithmetic .add .unchecked (.local left) (.local right)))).eval
      args env state = (.ok (size (a + b)), state) := by
  apply eval_scalar
  rw [scalar_arithmetic _ _ _ _ _ _ false 64 a b
    (SliceBytesAir.scalar_size env left a (by omega) ha)
    (SliceBytesAir.scalar_size env right b (by omega) hb)]
  have contains := Scalar.unsigned_nat_valid (a + b) 64 bound
  change (Scalar.Ty.int false 64).contains (a + b : Nat) = true at contains
  simp [Scalar.Arithmetic.eval, ← Int.natCast_add, Scalar.integer, contains]

/-- Saved descriptors belong to different allocations from the hasher, so
copying or updating its cells cannot alter later descriptor loads. -/
theorem load_saved {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (saved : Nat) (child : Ty) (offset : Nat) (value : Value) (apart : saved ≠ id)
    (read : Memory.load state (.pointer (.pointer false false child) ⟨saved, offset⟩) = .ok value) :
    Memory.load (frame.install cells) (.pointer (.pointer false false child) ⟨saved, offset⟩) = .ok value :=
  (load_eq_of_lookup _ _ false false child ⟨saved, offset⟩ (frame.outside cells saved apart)).trans read

theorem buffered_return {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (length count selfSlot inputSlot : Nat)
    (bound : length + count < addressLimit)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
      .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env)
    (h4 : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (h7 : env 7 = some (.value (slot false inputType inputSlot))) :
    bufferedReturn.eval AggregateCall.semantics args env (frame.install cells) =
      .returned (.value (.scalar .unit))
        (frame.install (cells.set 48 (WyhashLocal.word (BitVec.ofNat 64 (length + count))))) := by
  have savedSelf := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have savedCount := load_saved frame cells inputSlot usize 8 _ inputApart countRead
  have currentLength := object_word_read frame cells typed 48 (by simp) (BitVec.ofNat 64 length) lengthField
  have lengthBound : length < 2 ^ 64 := by change length < addressLimit; omega
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound] at currentLength
  have written := object_word_store frame cells typed 48 (by simp) (BitVec.ofNat 64 (length + count))
  have sumBound : length + count < 2 ^ 64 := bound
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumBound] at written
  let e40 := env.set 40 (.value (selfPointer id))
  let e41 := e40.set 41 (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  let e42 := e41.set 42 (size length)
  let e43 := e42.set 43 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let e44 := e43.set 44 (size count)
  let e45 := e44.set 45 (size (length + count))
  have loadSelf : (AggregateAir.Prim.load (.local 4)).eval args env (frame.install cells) =
      (.ok (.value (selfPointer id)), frame.install cells) := by
    apply eval_load _ _ _ _ (slot false (.pointer true false objectType) selfSlot)
    · exact value_local env 4 _ h4 rfl
    · exact congrArg (Except.map Register.value) savedSelf
  have field := eval_field (.local 40) 48 args e40 (frame.install cells) _ _
    (value_local e40 40 _ (by simp [e40, Control.Env.set]) rfl)
    (field_pointer frame cells typed 48 usize (by decide))
  have loadLength := eval_load (.local 41) args e41 (frame.install cells)
    (.pointer (.pointer true false usize) ⟨id, 48⟩) (size length)
    (value_local e41 41 _ (by simp [e41, Control.Env.set]) rfl)
    (congrArg (Except.map Register.value) currentLength)
  have lengthPointer : (AggregateAir.Prim.memory (.pointerField true (.local 7))).eval args e42 (frame.install cells) =
      (.ok (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩)), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e42 7 (slot false inputType inputSlot)
      (by simp [e42, e41, e40, Control.Env.set, h7]) rfl
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, Memory.pointerField, bind, Except.bind,
      ↓reduceIte, Nat.zero_add]
  have loadCount := eval_load (.local 43) args e43 (frame.install cells)
    (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) (size count)
    (value_local e43 43 _ (by simp [e43, Control.Env.set]) rfl)
    (congrArg (Except.map Register.value) savedCount)
  have added := size_add (frame.install cells) length count 42 44 args e44 bound
    (by simp [e44, e43, e42, Control.Env.set]) (by simp [e44, Control.Env.set])
  have sumValid : (size (length + count)).valid = true := by
    exact Scalar.unsigned_nat_valid (length + count) 64 bound
  have stored := eval_store (.local 41) (.local 45) args e45 (frame.install cells) _
    (.pointer (.pointer true false usize) ⟨id, 48⟩) (size (length + count))
    (value_local e45 41 _ (by simp [e45, e44, e43, e42, e41, Control.Env.set]) rfl)
    (ref_local e45 45 (size (length + count)) (by simp [e45, Control.Env.set])
      sumValid) written
  rw [bufferedReturn, AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ loadSelf (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ field (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ loadLength (SliceBytesAir.size_typed _ (by omega)),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ lengthPointer (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ loadCount (SliceBytesAir.size_typed _ (by omega)),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ added (SliceBytesAir.size_typed _ bound),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ stored (by rfl)]
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumBound]
  rfl



def bufferedLoaded (env : Env) (id inputSlot length count : Nat) : Env :=
  let e25 := env.set 25 (.value (selfPointer id))
  let e26 := e25.set 26 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  let e27 := e26.set 27 (.value (selfPointer id))
  let e28 := e27.set 28 (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  let e29 := e28.set 29 (size length)
  let e30 := e29.set 30 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let e31 := e30.set 31 (size count)
  e31

theorem buffered_loads {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (length count selfSlot inputSlot : Nat)
    (lengthBound : length < addressLimit) (countBound : count < addressLimit)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
      .ok (.scalar (.int false 64 count)))
    (next : AggregateCall.Code) (args : List Register) (env : Env)
    (h4 : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (h7 : env 7 = some (.value (slot false inputType inputSlot))) :
    (bufferedBody.prefixBindings 7 next).eval AggregateCall.semantics args env (frame.install cells) =
      next.eval AggregateCall.semantics args (bufferedLoaded env id inputSlot length count) (frame.install cells) := by
  let e25 := env.set 25 (.value (selfPointer id))
  let e26 := e25.set 26 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  let e27 := e26.set 27 (.value (selfPointer id))
  let e28 := e27.set 28 (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  let e29 := e28.set 29 (size length)
  let e30 := e29.set 30 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let e31 := e30.set 31 (size count)
  have savedSelf := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have savedCount := load_saved frame cells inputSlot usize 8 _ inputApart countRead
  have currentLength := object_word_read frame cells typed 48 (by simp) (BitVec.ofNat 64 length) lengthField
  have lengthWidth : length < 2 ^ 64 := lengthBound
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthWidth] at currentLength
  have p25 := eval_load (.local 4) args env (frame.install cells)
    (slot false (.pointer true false objectType) selfSlot) (.value (selfPointer id))
    (value_local env 4 _ h4 rfl) (congrArg (Except.map Register.value) savedSelf)
  have p26 := eval_field (.local 25) 56 args e25 (frame.install cells) (selfPointer id) _
    (value_local e25 25 _ (by simp [e25, Control.Env.set]) rfl)
    (field_pointer frame cells typed 56 (.array 48 ByteSlice.byte) (by decide))
  have p27 := eval_load (.local 4) args e26 (frame.install cells)
    (slot false (.pointer true false objectType) selfSlot) (.value (selfPointer id))
    (value_local e26 4 _ (by simp [e26, e25, Control.Env.set, h4]) rfl)
    (congrArg (Except.map Register.value) savedSelf)
  have p28 := eval_field (.local 27) 48 args e27 (frame.install cells) (selfPointer id) _
    (value_local e27 27 _ (by simp [e27, Control.Env.set]) rfl)
    (field_pointer frame cells typed 48 usize (by decide))
  have p29 := eval_load (.local 28) args e28 (frame.install cells)
    (.pointer (.pointer true false usize) ⟨id, 48⟩) (size length)
    (value_local e28 28 _ (by simp [e28, Control.Env.set]) rfl)
    (congrArg (Except.map Register.value) currentLength)
  have p30 : (AggregateAir.Prim.memory (.pointerField true (.local 7))).eval args e29 (frame.install cells) =
      (.ok (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩)), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e29 7 (slot false inputType inputSlot)
      (by simp [e29, e28, e27, e26, e25, Control.Env.set, h7]) rfl
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, Memory.pointerField,
      bind, Except.bind, ↓reduceIte, Nat.zero_add]
  have p31 := eval_load (.local 30) args e30 (frame.install cells)
    (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) (size count)
    (value_local e30 30 _ (by simp [e30, Control.Env.set]) rfl)
    (congrArg (Except.map Register.value) savedCount)
  rw [generated_buffered_body]
  simp only [bufferedCopy, Control.Code.prefixBindings]
  rw [AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p25 (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p26 (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p27 (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p28 (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p29 (SliceBytesAir.size_typed _ lengthBound),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p30 (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p31 (SliceBytesAir.size_typed _ countBound)]
  rfl

def bufferedPrepared (env : Env) (id length count : Nat) : Env :=
  let e32 := env.set 32 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let e33 := e32.set 33 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + length⟩))
  (e33.set 34 (size (length + count))).set 652 (.value (.scalar .unit))

theorem buffer_offset_eval {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit) (length : Nat) (bounded : length ≤ 48)
    (args : List Register) (env : Env)
    (pointer : env 32 = some (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)))
    (count : env 29 = some (size length)) :
    (AggregateAir.Prim.memory (.offsetPointer false (.local 32) (.local 29))).eval args env (frame.install cells) =
      (.ok (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + length⟩)), frame.install cells) := by
  apply eval_memory
  have limit : 48 < addressLimit := by decide
  have data := SliceBytesAir.memory_local env 32 (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩) pointer rfl
  have offset := SliceBytesAir.natural_size env 29 length (by omega) count
  rw [MemoryAir.Prim.eval_offset, data, offset]
  simp only [bind, Except.bind, buffer_offset frame cells valid typed endBound length bounded]

theorem buffer_bounds_eval (state : State) (length count : Nat) (fits : length + count ≤ 48)
    (args : List Register) (env : Env)
    (start : env 29 = some (size length)) (finish : env 34 = some (size (length + count))) :
    (AggregateAir.Prim.memory (.checkBounds (.local 29) (.local 34) (.array 48))).eval args env state =
      (.ok (.value (.scalar .unit)), state) := by
  apply eval_memory
  have limit : 48 < addressLimit := by decide
  have first := SliceBytesAir.natural_size env 29 length (by omega) start
  have last := SliceBytesAir.natural_size env 34 (length + count) (by omega) finish
  simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, first, last, MemoryAir.Bound.eval,
    Memory.checkSliceBounds, Nat.le_add_right, Option.isNone, Option.any,
    fits, or_true, and_self, ↓reduceIte, bind, Except.bind, decide_true]

theorem buffer_cast_eval {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit) (args : List Register) (env : Env)
    (pointer : env 26 = some (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))) :
    (AggregateAir.Prim.memory (.pointerCast (.pointer true true ByteSlice.byte) (.local 26))).eval
      args env (frame.install cells) =
      (.ok (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)), frame.install cells) := by
  apply eval_memory
  have data := SliceBytesAir.memory_local env 26
    (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩) pointer rfl
  simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data,
    buffer_cast frame cells valid typed endBound, bind, Except.bind]

theorem buffered_prepare {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit) (length count : Nat) (fits : length + count ≤ 48)
    (next : AggregateCall.Code) (args : List Register) (env : Env)
    (h26 : env 26 = some (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩)))
    (h29 : env 29 = some (size length)) (h31 : env 31 = some (size count)) :
    ((bufferedBody.dropBindings 7).prefixBindings 4 next).eval AggregateCall.semantics args env (frame.install cells) =
      next.eval AggregateCall.semantics args (bufferedPrepared env id length count) (frame.install cells) := by
  have limit : 48 < addressLimit := by decide
  have sumBound : length + count < addressLimit := by omega
  have bounded : length ≤ 48 := by omega
  let e32 := env.set 32 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let e33 := e32.set 33 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + length⟩))
  let e34 := e33.set 34 (size (length + count))
  let e652 := e34.set 652 (.value (.scalar .unit))
  have p32 := buffer_cast_eval frame cells valid typed endBound args env h26
  have p33 := buffer_offset_eval frame cells valid typed endBound length bounded args e32
    (by simp [e32, Control.Env.set]) (by simp [e32, Control.Env.set, h29])
  have p34 := size_add (frame.install cells) length count 29 31 args e33 sumBound
    (by simp [e33, e32, Control.Env.set, h29]) (by simp [e33, e32, Control.Env.set, h31])
  have p652 := buffer_bounds_eval (frame.install cells) length count fits args e34
    (by simp [e34, e33, e32, Control.Env.set, h29]) (by simp [e34, Control.Env.set])
  rw [generated_buffered_body]
  simp only [bufferedCopy, Control.Code.dropBindings, Control.Code.prefixBindings]
  rw [AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p32 (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p33 (by rfl),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p34 (SliceBytesAir.size_typed _ sumBound),
    AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p652 (by rfl)]
  rfl

/-- The complete captured buffered branch refines the existing update body
for arbitrary admitted byte inputs and hasher cells. Source reads, destination
stores and the declared slice guard are all executed. -/
theorem buffered_copy_tail {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length selfSlot inputSlot : Nat) (core : WyhashUpdate.Core cells total)
    (bounded : length ≤ 48) (fits : view.length ≤ 48 - length)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
      .ok (.scalar (.int false 64 view.length)))
    (args : List Register) (env : Env)
    (h1 : env 1 = some (.value (.slice inputType address view.length)))
    (h4 : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (h7 : env 7 = some (.value (slot false inputType inputSlot)))
    (h33 : env 33 = some (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + length⟩)))
    (h31 : env 31 = some (size view.length)) :
    ∃ after, (bufferedBody.dropBindings 11).eval AggregateCall.semantics args env (frame.install cells) =
        .returned (.value (.scalar .unit)) (frame.install after) ∧
      WyhashUpdate.updateBody source view length cells = .ok after := by
  have limit : 48 < addressLimit := by decide
  have sumBound : length + view.length < addressLimit := by omega
  have countBound : view.length < addressLimit := by omega
  have inputValid : (Value.slice inputType address view.length).valid = true := by
    simpa only [Value.valid, decide_eq_true_eq] using countBound
  let target := Value.slice (.slice true ByteSlice.byte) ⟨id, 56 + length⟩ view.length
  have targetValid : target.valid = true := by
    simpa only [target, Value.valid, decide_eq_true_eq] using countBound
  let e35 := env.set 35 (.value target)
  let e36 := e35.set 36 (size view.length)
  let e37 := e36.set 37 (size view.length)
  let e38 := e37.set 38 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  let e39 := e38.set 39 (.value (.scalar .unit))
  have p35 : (AggregateAir.Prim.memory (.slice (.slice true ByteSlice.byte) (.local 33) (.local 31))).eval
      args env (frame.install cells) = (.ok (.value target), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local env 33 (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + length⟩)
      h33 rfl
    have count := SliceBytesAir.natural_size env 31 view.length countBound
      h31
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, count,
      buffer_slice frame cells valid typed endBound length view.length (by omega), bind, Except.bind, target]
  have p36 : (AggregateAir.Prim.memory (.sliceLen (.local 35))).eval args e35 (frame.install cells) =
      (.ok (size view.length), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e35 35 target (by simp [e35, Control.Env.set]) targetValid
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, target, bind, Except.bind]
  have p37 : (AggregateAir.Prim.memory (.sliceLen (.local 1))).eval args e36 (frame.install cells) =
      (.ok (size view.length), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e36 1 (.slice inputType address view.length)
      (by simp [e36, e35, Control.Env.set, h1]) inputValid
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, bind, Except.bind]
  have p38 : (AggregateAir.Prim.memory (.slicePtr (.local 1))).eval args e37 (frame.install cells) =
      (.ok (.value (.pointer (.pointer false true ByteSlice.byte) address)), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e37 1 (.slice inputType address view.length)
      (by simp [e37, e36, e35, Control.Env.set, h1]) inputValid
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, bind, Except.bind]
  obtain ⟨copied, nativeCopy, localCopy, _, _, outside⟩ := copy_buffer frame typed address source cells view bytes
    geometry represented reads apart total 0 length view.length core (by omega) (by omega)
  have p39 : (AggregateCall.Prim.copyBytes (.local 35) (.local 38)).eval args e38 (frame.install cells) =
      (.ok (.value (.scalar .unit)), frame.install copied) := by
    have dest := value_local e38 35 target (by simp [e38, e37, e36, e35, Control.Env.set]) targetValid
    have src := value_local e38 38 (.pointer (.pointer false true ByteSlice.byte) address)
      (by simp [e38, Control.Env.set]) rfl
    have copied : ByteRange.copy (frame.install cells) target
      (.pointer (.pointer false true ByteSlice.byte) address) = (.ok (), frame.install copied) := by
      simpa only [target, Nat.add_zero] using nativeCopy
    simp only [AggregateCall.Prim.eval, dest, src, bind, Except.bind, pure, Except.pure, copied]
    rfl
  have finalLength : copied.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)) :=
    (outside 48 (Or.inl (by omega))).trans lengthField
  have returned := buffered_return frame copied typed length view.length selfSlot inputSlot sumBound finalLength
    selfApart inputApart selfRead countRead args e39
    (by simp [e39, e38, e37, e36, e35, Control.Env.set, h4])
    (by simp [e39, e38, e37, e36, e35, Control.Env.set, h7])
  refine ⟨copied.set 48 (WyhashLocal.word (BitVec.ofNat 64 (length + view.length))), ?_, ?_⟩
  ·
    rw [generated_buffered_body]
    simp only [bufferedCopy, Control.Code.dropBindings]
    rw [
      AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p35 (by exact targetValid),
      AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p36 (SliceBytesAir.size_typed _ countBound),
      AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p37 (SliceBytesAir.size_typed _ countBound),
      AggregateCall.primitive_bind _ _ _ _ _ _ _ _ _ p38 (by rfl),
      AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ p39 (by rfl)]
    exact returned
  · simp only [WyhashUpdate.updateBody, if_pos fits, localCopy, bind, Except.bind]
    exact WyhashUpdate.store_eq _ 48 _ (by simp)

/-- Complete early-return branch, with the loads, pointer arithmetic, source
guard, copy and final store composed in captured instruction order. -/
theorem buffered_body {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length selfSlot inputSlot : Nat) (core : WyhashUpdate.Core cells total)
    (bounded : length ≤ 48) (fits : view.length ≤ 48 - length)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
      .ok (.scalar (.int false 64 view.length)))
    (args : List Register) (env : Env)
    (h1 : env 1 = some (.value (.slice inputType address view.length)))
    (h4 : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (h7 : env 7 = some (.value (slot false inputType inputSlot))) :
    ∃ after, bufferedBody.eval AggregateCall.semantics args env (frame.install cells) =
        .returned (.value (.scalar .unit)) (frame.install after) ∧
      WyhashUpdate.updateBody source view length cells = .ok after := by
  have limit : 48 < addressLimit := by decide
  let loaded := bufferedLoaded env id inputSlot length view.length
  let prepared := bufferedPrepared loaded id length view.length
  have head := buffered_loads frame cells typed length view.length selfSlot inputSlot (by omega) (by omega)
    lengthField selfApart inputApart selfRead countRead (bufferedBody.dropBindings 7) args env h4 h7
  rw [Control.Code.prefix_drop] at head
  have prep := buffered_prepare frame cells valid typed endBound length view.length (by omega)
    ((bufferedBody.dropBindings 7).dropBindings 4) args loaded
    (by simp [loaded, bufferedLoaded, Control.Env.set])
    (by simp [loaded, bufferedLoaded, Control.Env.set])
    (by simp [loaded, bufferedLoaded, Control.Env.set])
  have cut : (bufferedBody.dropBindings 7).dropBindings 4 = bufferedBody.dropBindings 11 := by
    rw [generated_buffered_body]
    rfl
  rw [Control.Code.prefix_drop, cut] at prep
  obtain ⟨after, tail, logical⟩ := buffered_copy_tail frame valid typed endBound address source cells view bytes
    geometry represented reads apart total length selfSlot inputSlot core bounded fits lengthField
    selfApart inputApart selfRead countRead args prepared
    (by simp [prepared, bufferedPrepared, loaded, bufferedLoaded, Control.Env.set, h1])
    (by simp [prepared, bufferedPrepared, loaded, bufferedLoaded, Control.Env.set, h4])
    (by simp [prepared, bufferedPrepared, loaded, bufferedLoaded, Control.Env.set, h7])
    (by simp [prepared, bufferedPrepared, Control.Env.set])
    (by simp [prepared, bufferedPrepared, loaded, bufferedLoaded, Control.Env.set])
  exact ⟨after, head.trans (prep.trans tail), logical⟩

end Compiler.ZigAir.WyhashUpdateAir
