/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedWordByteAccess
import Compiler.ZigAir.MemoryBytePointers
import Compiler.ZigAir.MemoryByteAirLaws
import Compiler.ZigAir.MemoryStackPrefix
import Compiler.ZigAir.MemoryFill

namespace Compiler.ZigAir.MemoryByteInvocation
open Memory MemoryAir GeneratedMemory
open Memory.WordArray (View Writable Represents word)
open MemoryFill (size size_valid size_typed)

abbrev wordPointer (writable : Bool) (address : Address) : Value :=
  .pointer (.pointer writable false word) address
abbrev slotType (writable : Bool) : Ty := .slice writable ByteAccess.byte
abbrev slot (writable : Bool) (id : Nat) : Value :=
  .pointer (.pointer true false (slotType writable)) ⟨id, 0⟩
abbrev readonly (writable : Bool) (id : Nat) : Value :=
  .pointer (.pointer false false (slotType writable)) ⟨id, 0⟩

def readArguments (address : Address) (offset : Fin 4) : List Value :=
  [wordPointer false address, size offset.val]
def writeArguments (address : Address) (offset : Fin 4) (value : BitVec 8) : List Value :=
  [wordPointer true address, size offset.val, ByteAccess.number value]

theorem pointer_valid (writable many : Bool) (child : Ty) (address : Address) :
    (Value.pointer (.pointer writable many child) address).valid = true := rfl
theorem pointer_typed (writable many : Bool) (child : Ty) (address : Address) :
    (Value.pointer (.pointer writable many child) address).hasType (.pointer writable many child) = true := by
  simp [Value.hasType, Value.type, Value.valid]
theorem byte_slice_valid (writable : Bool) (address : Address) : (ByteAccess.slice writable address).valid = true := rfl
theorem byte_slice_typed (writable : Bool) (address : Address) :
    (ByteAccess.slice writable address).hasType (slotType writable) = true := by
  unfold Value.hasType
  rw [byte_slice_valid]
  simp [Value.type, ByteAccess.slice, slotType]
theorem byte_pointer_valid (writable many : Bool) (address : Address) :
    (ByteAccess.pointer writable many address).valid = true := rfl
theorem byte_pointer_typed (writable many : Bool) (address : Address) :
    (ByteAccess.pointer writable many address).hasType (.pointer writable many ByteAccess.byte) = true :=
  pointer_typed writable many ByteAccess.byte address
private theorem unit_typed : (Value.scalar .unit).hasType (.scalar .unit) = true := rfl
private theorem offset_width (offset : Fin 4) : offset.val < addressLimit := by
  have small := offset.isLt
  have limit : 4 < addressLimit := by decide
  omega

theorem cast_word (state : State) (view : View) (index : Nat) (writable : Bool)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    ByteAccess.cast state writable true 4 (wordPointer writable (view.address index)) =
      .ok (ByteAccess.pointer writable true (view.address index)) := by
  have cast := ByteAccess.cast_array state view index 4 writable true initial cap inside (Or.inr (Or.inr rfl))
  cases writable <;> simpa [ByteAccess.cast, wordPointer, View.pointer] using cast

-- These common fragments are definitionally equal to the captured bodies.
-- Their shared slice-save path is proved once despite the extra write argument.
def readTail : Code :=
  .bind 9 ByteAccess.byte (.wordByteLoad .little (.local 8)) (.ret (.local 9))
def writeTail : Code :=
  .bind 10 (.scalar .unit) (.wordByteStore .little (.local 9) (.local 2)) (.ret (.constant (.scalar .unit)))
def savedCode (shift : Nat) (writable : Bool) (tail : Code) : Code :=
  .bind (5 + shift) (.scalar .unit) (.store (.local (4 + shift)) (.local (3 + shift)))
    (.bind (6 + shift) (.pointer false false (slotType writable))
      (.pointerCast (.pointer false false (slotType writable)) (.local (4 + shift)))
    (.bind (7 + shift) (slotType writable) (.load (.local (6 + shift)))
    (.bind (8 + shift) (.pointer writable false ByteAccess.byte)
      (.sliceElementPointer (.local (7 + shift)) (.local 1)) tail)))
def allocCode (shift : Nat) (writable : Bool) (tail : Code) : Code :=
  .bind (4 + shift) (.pointer true false (slotType writable)) (.alloc (slotType writable)) (savedCode shift writable tail)
def accessCode (shift : Nat) (writable : Bool) (tail : Code) : Code :=
  .bind (2 + shift) (.pointer writable true ByteAccess.byte) (.wordByteCast writable true 4 (.local 0))
    (.bind (3 + shift) (slotType writable)
      (.slice (slotType writable) (.local (2 + shift)) (.constant (size 4))) (allocCode shift writable tail))

theorem generated_read_body : fn_read_word_byte.body =
    .bind 0 (.pointer false false word) (.argument 0)
      (.bind 1 usize (.argument 1) (accessCode 0 false readTail)) := rfl
theorem generated_write_body : fn_write_word_byte.body =
    .bind 0 (.pointer true false word) (.argument 0)
      (.bind 1 usize (.argument 1) (.bind 2 ByteAccess.byte (.argument 2) (accessCode 1 true writeTail))) := rfl

def sourceEnv (writable : Bool) (address : Address) (offset : Fin 4) : Env :=
  ((Control.Env.set (fun _ => none) 0 (wordPointer writable address)).set 1 (size offset.val))
def accessEnv (shift : Nat) (writable : Bool) (address : Address) (env : Env) : Env :=
  (env.set (2 + shift) (ByteAccess.pointer writable true address)).set (3 + shift) (ByteAccess.slice writable address)
def savedEnv (shift : Nat) (writable : Bool) (address : Address) (offset : Fin 4) (id : Nat) (env : Env) : Env :=
  (((env.set (5 + shift) (.scalar .unit)).set (6 + shift) (readonly writable id)).set
    (7 + shift) (ByteAccess.slice writable address)).set (8 + shift)
      (ByteAccess.pointer writable false (ByteAccess.atByte address offset))

attribute [local simp] pointer_valid pointer_typed byte_slice_valid byte_slice_typed unit_typed
  ByteAccess.number_valid ByteAccess.number_typed byte_pointer_valid byte_pointer_typed

theorem access_steps (shift : Nat) (writable : Bool) (tail : Code) (args : List Value) (env : Env)
    (state : State) (view : View) (index : Nat)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length)
    (h0 : env 0 = some (wordPointer writable (view.address index))) :
    (accessCode shift writable tail).eval semantics args env state =
      (allocCode shift writable tail).eval semantics args (accessEnv shift writable (view.address index) env) state := by
  have cast := cast_word state view index writable initial cap inside
  have slicing := ByteAccess.make_byte_slice state view index writable initial cap inside
  have four : ∀ env, (Ref.constant (size 4)).natural env = .ok 4 := fun _ => rfl
  simp only [accessCode, Code.eval_bind, Prim.eval_word_byte_cast, Prim.eval_slice,
    Ref.eval_local, h0, wordPointer, pointer_valid, ↓reduceIte,
    bind, Except.bind, cast, byte_pointer_valid, byte_pointer_typed, Control.Env.set,
    four, slotType, slicing, byte_slice_typed, accessEnv]

theorem saved_steps (shift : Nat) (writable : Bool) (tail : Code) (args : List Value) (env : Env)
    (state after : State) (view : View) (index id : Nat) (offset : Fin 4)
    (initial : after.valid = true) (cap : Writable after view) (inside : index < view.length)
    (h1 : env 1 = some (size offset.val))
    (h3 : env (3 + shift) = some (ByteAccess.slice writable (view.address index)))
    (h4 : env (4 + shift) = some (slot writable id))
    (written : store state (slot writable id) (ByteAccess.slice writable (view.address index)) = .ok after) :
    (savedCode shift writable tail).eval semantics args env state =
      tail.eval semantics args (savedEnv shift writable (view.address index) offset id env) after := by
  have read := load_alias_after_store state true false (slotType writable) ⟨id, 0⟩
    (ByteAccess.slice writable (view.address index)) after false false written
  have cast := pointerCast_readonly_of_load after true false (slotType writable) ⟨id, 0⟩
    (ByteAccess.slice writable (view.address index)) (load_after_store state _ _ after written)
  have element := ByteAccess.byte_element after view index offset writable initial cap inside
  have width := size_valid offset.val (offset_width offset)
  simp only [size] at width
  simp only [savedCode, Code.eval_bind, Prim.eval_store, Prim.eval_cast, Prim.eval_load,
    Prim.eval_slice_element, Ref.eval_local, Ref.natural_eq, h3, h4, slot, readonly,
    pointer_valid, byte_slice_valid, ↓reduceIte, bind, Except.bind, written,
    pointer_typed, unit_typed, Control.Env.set, Nat.add_right_cancel_iff, Nat.reduceEqDiff, cast, read, byte_slice_typed,
    show ¬(1 = 7 + shift) by omega, show ¬(1 = 6 + shift) by omega, show ¬(1 = 5 + shift) by omega,
    h1, width, size, Int.toNat_natCast, element, byte_pointer_typed, savedEnv]


def readHeadEnv (address : Address) (offset : Fin 4) : Env :=
  accessEnv 0 false address (sourceEnv false address offset)
def writeHeadEnv (address : Address) (offset : Fin 4) (value : BitVec 8) : Env :=
  accessEnv 1 true address ((sourceEnv true address offset).set 2 (ByteAccess.number value))

theorem read_head (state : State) (view : View) (index : Nat) (offset : Fin 4)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    fn_read_word_byte.body.eval semantics (readArguments (view.address index) offset) (fun _ => none) state =
      (allocCode 0 false readTail).eval semantics (readArguments (view.address index) offset)
        (readHeadEnv (view.address index) offset) state := by
  rw [generated_read_body]
  simp only [Code.eval_bind, Prim.eval_argument, readArguments, List.getElem?_cons_zero,
    List.getElem?_cons_succ, pointer_typed, size_typed _ (offset_width offset), ↓reduceIte]
  exact access_steps 0 false readTail _ _ state view index initial cap inside (by simp [Control.Env.set])

theorem write_head (state : State) (view : View) (index : Nat) (offset : Fin 4) (value : BitVec 8)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    fn_write_word_byte.body.eval semantics (writeArguments (view.address index) offset value) (fun _ => none) state =
      (allocCode 1 true writeTail).eval semantics (writeArguments (view.address index) offset value)
        (writeHeadEnv (view.address index) offset value) state := by
  rw [generated_write_body]
  simp only [Code.eval_bind, Prim.eval_argument, writeArguments, List.getElem?_cons_zero,
    List.getElem?_cons_succ, pointer_typed, size_typed _ (offset_width offset), ByteAccess.number_typed, ↓reduceIte]
  exact access_steps 1 true writeTail _ _ state view index initial cap inside (by simp [Control.Env.set])

theorem read_tail (args : List Value) (env : Env) (state : State) (address : Address) (value : BitVec 8)
    (h8 : env 8 = some (ByteAccess.pointer false false address))
    (read : ByteAccess.read .little state (ByteAccess.pointer false false address) = .ok (ByteAccess.number value)) :
    readTail.eval semantics args env state = .returned (ByteAccess.number value) state := by
  simp only [readTail, Code.eval_bind, Code.eval_ret, Prim.eval_word_byte_load, Ref.eval_local,
    h8, byte_pointer_valid, ↓reduceIte, bind, Except.bind, read, ByteAccess.number_typed,
    Control.Env.set, ByteAccess.number_valid]

theorem write_tail (args : List Value) (env : Env) (state after : State) (address : Address) (value : BitVec 8)
    (h9 : env 9 = some (ByteAccess.pointer true false address)) (h2 : env 2 = some (ByteAccess.number value))
    (written : ByteAccess.write .little state (ByteAccess.pointer true false address) (ByteAccess.number value) = .ok after) :
    writeTail.eval semantics args env state = .returned (.scalar .unit) after := by
  simp only [writeTail, Code.eval_bind, Code.eval_ret, Prim.eval_word_byte_store, Ref.eval_local,
    Ref.eval_constant, h9, h2, byte_pointer_valid, ByteAccess.number_valid, ↓reduceIte,
    bind, Except.bind, written, unit_typed]
  rfl

theorem read_accepts (state : State) (address : Address) (offset : Fin 4) (initial : state.valid = true) :
    fn_read_word_byte.accepts (readArguments address offset) state = true := by
  have sized : (size offset.val).hasType (.scalar (.int false 64)) = true := size_typed _ (offset_width offset)
  simp [Program.accepts, fn_read_word_byte, readArguments, initial, sized]

theorem write_accepts (state : State) (address : Address) (offset : Fin 4) (value : BitVec 8)
    (initial : state.valid = true) : fn_write_word_byte.accepts (writeArguments address offset value) state = true := by
  have sized : (size offset.val).hasType (.scalar (.int false 64)) = true := size_typed _ (offset_width offset)
  have byteTyped : (ByteAccess.number value).hasType (.scalar (.int false 8)) = true := ByteAccess.number_typed value
  simp [Program.accepts, fn_write_word_byte, writeArguments, initial, sized, byteTyped]

/-- Complete captured read: valid initialized caller storage gives the selected
byte or allocation exhaustion. Every outcome retains the exact ordered caller
heap, including all cells outside the view. No intermediate success is assumed. -/
theorem read_result (state : State) (view : View) (items : List (BitVec 32)) (index : Nat) (offset : Fin 4)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (inside : index < items.length) :
    ∃ result after, fn_read_word_byte.run (readArguments (view.address index) offset) state = (result, after) ∧
      after.valid = true ∧ after.heap = state.heap ∧
      (result = .ok (ByteAccess.number (WordBytes.read .little items[index] offset)) ∨ result = .error .outOfMemory) := by
  have bound : index < view.length := by simpa only [represented.1] using inside
  rw [Program.run, if_pos (read_accepts state (view.address index) offset initial),
    read_head state view index offset initial cap bound]
  cases allocation : allocate state (slotType false) with
  | error reason =>
    have oom := allocate_fault_of_layout state (slotType false) ⟨16, 8⟩ reason initial rfl allocation
    subst reason
    refine ⟨.error .outOfMemory, state, ?_, initial, rfl, Or.inr rfl⟩
    simp only [allocCode, Code.eval_bind, Prim.eval_alloc_fault _ _ _ _ _ allocation, Program.finish,
      cleanup_initial state initial]
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨pointerEq, _⟩ := allocate_pointer state (slotType false) pointer allocated allocation
    subst pointer
    obtain ⟨saved, written⟩ := fresh_store_total state allocated (ByteAccess.slice false (view.address index)) _
      ⟨16, 8⟩ (byte_slice_valid _ _) rfl (by decide) allocation
    have allocatedValid := allocate_preserves_valid state (slotType false) _ allocated allocation
    have savedValid := store_preserves_valid allocated _ _ saved allocatedValid written
    have savedCap := WordArray.writable_store allocated saved view _ _ written
      (WordArray.writable_allocate state allocated view (slotType false) _ initial cap allocation)
    let env := (readHeadEnv (view.address index) offset).set 4 (slot false state.nextId)
    have stored := saved_steps 0 false readTail (readArguments (view.address index) offset) env allocated saved view index
      state.nextId offset savedValid savedCap bound
      (by simp [env, readHeadEnv, accessEnv, sourceEnv, Control.Env.set])
      (by simp [env, readHeadEnv, accessEnv, Control.Env.set]) (by simp [env, Control.Env.set]) written
    obtain ⟨cell, stack, savedShape⟩ := saved_slot_prefix state allocated saved (ByteAccess.slice false (view.address index))
      initial allocation written
    obtain ⟨extent, originalCell, found, _, _, _⟩ := cap
    have older := (valid_lookup state view.allocation originalCell initial found).1
    have apart : (ByteAccess.atByte (view.address index) offset).allocation ≠ state.nextId := by
      simp only [ByteAccess.atByte, View.address]
      omega
    have readCaller := (ByteAccess.read_alias .little state (ByteAccess.atByte (view.address index) offset)
      false false true false).trans (ByteAccess.read_refines .little state view items index offset represented inside)
    have readSaved := (congrArg (fun s => ByteAccess.read .little s (ByteAccess.pointer false false
      (ByteAccess.atByte (view.address index) offset))) savedShape).trans
      ((ByteAccess.read_prepend .little state state.nextId cell saved.nextId saved.nextAddress false false _ apart).trans readCaller)
    have tail := read_tail (readArguments (view.address index) offset) (savedEnv 0 false (view.address index) offset state.nextId env) saved _ _
      (by simp [savedEnv, Control.Env.set]) readSaved
    have cleaned := (congrArg (fun s => (cleanup state.nextId s).heap) savedShape).trans
      (cleanup_prepend state cell saved.nextId saved.nextAddress initial stack)
    refine ⟨.ok (ByteAccess.number (WordBytes.read .little items[index] offset)), cleanup state.nextId saved,
      ?_, cleanup_preserves_valid _ _ savedValid, cleaned, Or.inl rfl⟩
    rw [allocCode, Code.eval_bind_ok (Prim.eval_alloc_ok _ _ _ _ _ _ allocation) (pointer_typed true false _ _), stored, tail]
    simp only [Program.finish, show fn_read_word_byte.returnType = ByteAccess.byte from rfl,
      ByteAccess.number_typed, ↓reduceIte]


/-- Complete captured write: on success its caller heap is exactly the heap
from one proved byte update. The direct effect supplies the full word/list
refinement and outside-view frame. Invocation allocation counters retain their
history; allocation exhaustion leaves the caller heap unchanged. -/
theorem write_result (state : State) (view : View) (items : List (BitVec 32)) (index : Nat)
    (offset : Fin 4) (value : BitVec 8)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (inside : index < items.length) :
    ∃ result after, fn_write_word_byte.run (writeArguments (view.address index) offset value) state = (result, after) ∧
      after.valid = true ∧
      ((result = .error .outOfMemory ∧ after.heap = state.heap) ∨
        ∃ direct, result = .ok (.scalar .unit) ∧
          ByteAccess.write .little state (ByteAccess.pointer true false (ByteAccess.atByte (view.address index) offset))
            (ByteAccess.number value) = .ok direct ∧ after.heap = direct.heap ∧
          Writable after view ∧ Represents after view (items.set index (WordBytes.write .little items[index] offset value)) ∧
          WordArray.Frame view state direct) := by
  have bound : index < view.length := by simpa only [represented.1] using inside
  rw [Program.run, if_pos (write_accepts state (view.address index) offset value initial),
    write_head state view index offset value initial cap bound]
  cases allocation : allocate state (slotType true) with
  | error reason =>
    have oom := allocate_fault_of_layout state (slotType true) ⟨16, 8⟩ reason initial rfl allocation
    subst reason
    refine ⟨.error .outOfMemory, state, ?_, initial, Or.inl ⟨rfl, rfl⟩⟩
    simp only [allocCode, Code.eval_bind, Prim.eval_alloc_fault _ _ _ _ _ allocation, Program.finish,
      cleanup_initial state initial]
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨pointerEq, _⟩ := allocate_pointer state (slotType true) pointer allocated allocation
    subst pointer
    obtain ⟨saved, written⟩ := fresh_store_total state allocated (ByteAccess.slice true (view.address index)) _
      ⟨16, 8⟩ (byte_slice_valid _ _) rfl (by decide) allocation
    have allocatedValid := allocate_preserves_valid state (slotType true) _ allocated allocation
    have savedValid := store_preserves_valid allocated _ _ saved allocatedValid written
    have savedCap := WordArray.writable_store allocated saved view _ _ written
      (WordArray.writable_allocate state allocated view (slotType true) _ initial cap allocation)
    let env := (writeHeadEnv (view.address index) offset value).set 5 (slot true state.nextId)
    have stored := saved_steps 1 true writeTail (writeArguments (view.address index) offset value) env allocated saved view index
      state.nextId offset savedValid savedCap bound
      (by simp [env, writeHeadEnv, accessEnv, sourceEnv, Control.Env.set])
      (by simp [env, writeHeadEnv, accessEnv, Control.Env.set]) (by simp [env, Control.Env.set]) written
    obtain ⟨cell, stack, savedShape⟩ := saved_slot_prefix state allocated saved (ByteAccess.slice true (view.address index))
      initial allocation written
    obtain ⟨direct, directWrite, directValid, directCap, directRep, directFrame⟩ :=
      ByteAccess.write_refines .little state view items index offset value initial cap represented inside
    obtain ⟨extent, originalCell, found, _, _, _⟩ := cap
    have older := (valid_lookup state view.allocation originalCell initial found).1
    have apart : (ByteAccess.atByte (view.address index) offset).allocation ≠ state.nextId := by
      simp only [ByteAccess.atByte, View.address]
      omega
    let updated := prepend state.nextId cell saved.nextId saved.nextAddress direct
    have writeSaved : ByteAccess.write .little saved (ByteAccess.pointer true false (ByteAccess.atByte (view.address index) offset))
        (ByteAccess.number value) = .ok updated := by
      rw [savedShape, ByteAccess.write_prepend .little state state.nextId cell saved.nextId saved.nextAddress true false _ _ apart,
        directWrite]
      rfl
    obtain ⟨target, contents, byteStore⟩ := ByteAccess.write_store .little saved updated _ _ writeSaved
    have updatedValid := store_preserves_valid saved target contents updated savedValid byteStore
    have tail := write_tail (writeArguments (view.address index) offset value)
      (savedEnv 1 true (view.address index) offset state.nextId env) saved updated _ value
      (by simp [savedEnv, Control.Env.set])
      (by simp [savedEnv, env, writeHeadEnv, accessEnv, sourceEnv, Control.Env.set]) writeSaved
    have cleaned : (cleanup state.nextId updated).heap = direct.heap := by
      have exactHeap := cleanup_prepend direct cell saved.nextId saved.nextAddress directValid stack
      simpa only [directFrame.nextId, updated] using exactHeap
    refine ⟨.ok (.scalar .unit), cleanup state.nextId updated, ?_, cleanup_preserves_valid _ _ updatedValid,
      Or.inr ⟨direct, rfl, directWrite, cleaned,
        WordArray.writable_heap_eq direct _ view cleaned directCap,
        WordArray.represents_heap_eq direct _ view _ cleaned directRep, directFrame⟩⟩
    rw [allocCode, Code.eval_bind_ok (Prim.eval_alloc_ok _ _ _ _ _ _ allocation) (pointer_typed true false _ _), stored, tail]
    rfl

end Compiler.ZigAir.MemoryByteInvocation
