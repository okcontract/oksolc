/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapLoop

namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents word)
open MemoryFill (size size_valid size_typed counter unitRef)

def bytesCode (argument raw sliceId : Nat) (next : Control.Code Ty Prim Ref true) : Control.Code Ty Prim Ref true :=
  .bind raw (.pointer true true ByteAccess.byte) (.wordByteCast true true 4 (.local argument))
    (.bind sliceId (.slice true ByteAccess.byte)
      (.slice (.slice true ByteAccess.byte) (.local raw) (.constant (size 4))) next)

def bytesEnv (env : Env) (raw sliceId : Nat) (address : Address) : Env :=
  (env.set raw (ByteAccess.pointer true true address)).set sliceId (ByteAccess.slice true address)

def storedCode : Control.Code Ty Prim Ref true :=
  .bind 8 (.scalar .unit) (.store (.local 7) (.constant (size 0)))
    (.bind 9 usize (.sliceLen (.local 4)) (.bind 10 usize (.sliceLen (.local 6)) entry))
def allocatedCode : Control.Code Ty Prim Ref true := .bind 7 (.pointer true false usize) (.alloc usize) storedCode
def accessCode : Control.Code Ty Prim Ref true := bytesCode 0 3 4 (bytesCode 1 5 6 allocatedCode)
def prologue : Control.Code Ty Prim Ref true :=
  .bind 0 (.pointer true false word) (.argument 0) (.bind 1 (.pointer true false word) (.argument 1) accessCode)

def arguments (view : View) (left right : Nat) : List Value := [view.pointer left, view.pointer right]
def sourceEnv (view : View) (left right : Nat) : Env :=
  ((Control.Env.set (fun _ => none) 0 (view.pointer left)).set 1 (view.pointer right))
def accessEnv (view : View) (left right : Nat) : Env :=
  bytesEnv (bytesEnv (sourceEnv view left right) 3 4 (view.address left)) 5 6 (view.address right)

theorem generated_prologue : GeneratedMemory.fn_swap_u32.program.body = prologue := rfl

theorem bytes_steps (args : List Value) (env : Env) (state : State) (view : View) (index argument raw sliceId : Nat)
    (next : Control.Code Ty Prim Ref true) (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length)
    (source : env argument = some (view.pointer index)) :
    Steps semantics args (.suspended ⟨bytesCode argument raw sliceId next, env, state, []⟩)
      (.suspended ⟨next, bytesEnv env raw sliceId (view.address index), state, []⟩) := by
  have cast := ByteAccess.cast_array state view index 4 true true initial cap inside (Or.inr (Or.inr rfl))
  have castEval : (Prim.wordByteCast true true 4 (.local argument)).eval args env state =
      (.ok (ByteAccess.pointer true true (view.address index)), state) := by
    simp only [Prim.eval_word_byte_cast, Ref.eval_local, source, View.pointer, Value.valid, ↓reduceIte, bind, Except.bind]
    exact congrArg (fun result => (result, state)) cast
  have slicing := ByteAccess.make_byte_slice state view index true initial cap inside
  have sliceEval : (Prim.slice (.slice true ByteAccess.byte) (.local raw) (.constant (size 4))).eval args
      (env.set raw (ByteAccess.pointer true true (view.address index))) state =
      (.ok (ByteAccess.slice true (view.address index)), state) := by
    have four : ∀ env, (Ref.constant (size 4)).natural env = .ok 4 := fun _ => rfl
    simp only [Prim.eval_slice, Ref.eval_local, Control.Env.set, ↓reduceIte,
      MemoryByteInvocation.byte_pointer_valid, four, bind, Except.bind, slicing]
  apply Steps.bind_ok semantics args castEval (by rfl)
  apply Steps.bind_ok semantics args sliceEval (by rfl)
  exact .refl _

theorem access_steps (caller : State) (view : View) (left right : Nat)
    (initial : caller.valid = true) (cap : Writable caller view) (hl : left < view.length) (hr : right < view.length) :
    Steps semantics (arguments view left right)
      (.suspended ⟨GeneratedMemory.fn_swap_u32.program.body, fun _ => none, caller, []⟩)
      (.suspended ⟨allocatedCode, accessEnv view left right, caller, []⟩) := by
  rw [generated_prologue]
  have first : (Prim.argument 0).eval (arguments view left right) (fun _ => none) caller =
      (.ok (view.pointer left), caller) := rfl
  apply Steps.bind_ok semantics (arguments view left right) (prim := .argument 0)
    (env := fun _ => none) (state := caller) (value := view.pointer left) first (by rfl)
  have second : (Prim.argument 1).eval (arguments view left right)
      (Control.Env.set (fun _ => none) 0 (view.pointer left)) caller = (.ok (view.pointer right), caller) := rfl
  apply Steps.bind_ok semantics (arguments view left right) (prim := .argument 1)
    (env := Control.Env.set (fun _ => none) 0 (view.pointer left)) (state := caller) (value := view.pointer right) second (by rfl)
  exact (bytes_steps (arguments view left right) (sourceEnv view left right) caller view left 0 3 4
    (bytesCode 1 5 6 allocatedCode) initial cap hl (by simp [sourceEnv, Control.Env.set])).trans semantics _
    (bytes_steps _ _ caller view right 1 5 6 allocatedCode initial cap hr
      (by simp [bytesEnv, sourceEnv, Control.Env.set]))

/-- Allocation success supplies the exact initialized prefix; failure remains
an explicit allocator outcome. No successful store is assumed by the caller. -/
theorem initialize_counter (caller allocated : State) (pointer : Value)
    (initial : caller.valid = true) (allocation : allocate caller usize = .ok (pointer, allocated)) :
    ∃ base, pointer = counter ⟨caller.nextId, 0⟩ ∧
      store allocated pointer (size 0) = .ok (withCounter base 0 caller) ∧ (withCounter base 0 caller).valid = true := by
  obtain ⟨layout, base, shape, pointerEq, allocatedEq⟩ := allocate_shape caller usize pointer allocated allocation
  have layoutEq : layout = ⟨8, 8⟩ := Option.some.inj shape.symm
  subst layout
  obtain ⟨saved, written⟩ := fresh_store_total caller allocated (size 0) pointer ⟨8, 8⟩ rfl rfl (by decide) allocation
  obtain ⟨_, _, _, _, cell, contents, same, _, _, accessed, cellsWritten, savedEq⟩ := store_success allocated pointer (size 0) saved written
  rw [pointerEq] at same
  cases same
  have found := (access_success_region allocated ⟨caller.nextId, 0⟩ _ true cell accessed).1
  rw [allocatedEq] at found
  simp only [Heap.lookup_cons, ↓reduceIte] at found
  cases Option.some.inj found
  have contentsEq : contents = [(0, size 0)] := (Except.ok.inj cellsWritten).symm
  subst contents
  have absent : ∀ entry ∈ caller.heap, entry.1 ≠ caller.nextId :=
    fun entry present => Nat.ne_of_lt (valid_heap_ids caller initial entry present)
  have savedShape : saved = withCounter base 0 caller := by
    rw [savedEq, allocatedEq]
    simp only [withCounter, prepend, counterCell, Heap.replace_cons, ↓reduceIte,
      Heap.replace_absent caller.heap caller.nextId _ absent]
  refine ⟨base, pointerEq, by simpa only [savedShape] using written, ?_⟩
  rw [← savedShape]
  exact store_preserves_valid allocated pointer (size 0) saved (allocate_preserves_valid caller usize pointer allocated allocation) written

def allocatedEnv (view : View) (left right id : Nat) : Env :=
  (accessEnv view left right).set 7 (counter ⟨id, 0⟩)
def storedEnv (view : View) (left right id : Nat) : Env :=
  (((allocatedEnv view left right id).set 8 (.scalar .unit)).set 9 (size 4)).set 10 (size 4)

theorem stored_locals (view : View) (left right id : Nat) : Locals (storedEnv view left right id) view left right ⟨id, 0⟩ := by
  simp [Locals, storedEnv, allocatedEnv, accessEnv, bytesEnv, Control.Env.set]

theorem stored_steps (caller allocated : State) (view : View) (left right base : Nat)
    (written : store allocated (counter ⟨caller.nextId, 0⟩) (size 0) = .ok (withCounter base 0 caller)) :
    Steps semantics (arguments view left right)
      (.suspended ⟨storedCode, allocatedEnv view left right caller.nextId, allocated, []⟩)
      (.suspended ⟨entry, storedEnv view left right caller.nextId, withCounter base 0 caller, []⟩) := by
  have pointer : (Ref.local 7).eval (allocatedEnv view left right caller.nextId) =
      .ok (counter ⟨caller.nextId, 0⟩) := rfl
  have zero : (Ref.constant (size 0)).eval (allocatedEnv view left right caller.nextId) = .ok (size 0) := rfl
  apply Steps.bind_ok semantics (arguments view left right)
    (Prim.eval_store_ok _ _ _ _ _ _ _ _ pointer zero written) (by rfl)
  have leftLength : (Prim.sliceLen (.local 4)).eval (arguments view left right)
      ((allocatedEnv view left right caller.nextId).set 8 (.scalar .unit)) (withCounter base 0 caller) =
      (.ok (size 4), withCounter base 0 caller) := rfl
  apply Steps.bind_ok semantics (arguments view left right) (prim := .sliceLen (.local 4))
    (env := (allocatedEnv view left right caller.nextId).set 8 (.scalar .unit))
    (state := withCounter base 0 caller) (value := size 4) leftLength (by rfl)
  have rightLength : (Prim.sliceLen (.local 6)).eval (arguments view left right)
      (((allocatedEnv view left right caller.nextId).set 8 (.scalar .unit)).set 9 (size 4)) (withCounter base 0 caller) =
      (.ok (size 4), withCounter base 0 caller) := rfl
  apply Steps.bind_ok semantics (arguments view left right) (prim := .sliceLen (.local 6))
    (env := ((allocatedEnv view left right caller.nextId).set 8 (.scalar .unit)).set 9 (size 4))
    (state := withCounter base 0 caller) (value := size 4) rightLength (by rfl)
  exact .refl _

theorem body_steps (caller : State) (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : caller.valid = true) (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right) :
    ∃ outcome, Steps semantics (arguments view left right)
        (.suspended ⟨GeneratedMemory.fn_swap_u32.program.body, fun _ => none, caller, []⟩) (.finished outcome) ∧
      (outcome = .fault .outOfMemory caller ∨ ∃ base after,
        outcome = .returned (.scalar .unit) (withCounter base 4 after) ∧
        after.valid = true ∧ (withCounter base 4 after).valid = true ∧ Writable after view ∧
        Represents after view ((items.set left items[right]).set right items[left]) ∧ WordArray.Frame view caller after) := by
  have first := access_steps caller view left right initial cap
    (by simpa only [represented.1] using hl) (by simpa only [represented.1] using hr)
  cases allocation : allocate caller usize with
  | error reason =>
    have same := allocate_fault_of_layout caller usize ⟨8, 8⟩ reason initial rfl allocation
    subst reason
    refine ⟨.fault .outOfMemory caller, first.trans semantics _ ?_, Or.inl rfl⟩
    exact Steps.bind_fault semantics _ (Prim.eval_alloc_fault usize _ _ caller .outOfMemory allocation)
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨base, pointerEq, written, live⟩ := initialize_counter caller allocated pointer initial allocation
    obtain ⟨after, loop, valid, finalLive, writable, rep, frame⟩ :=
      initialized_swap (arguments view left right) (storedEnv view left right caller.nextId) caller base view items left right
        initial live cap represented hl hr apart (stored_locals view left right caller.nextId)
    refine ⟨.returned (.scalar .unit) (withCounter base 4 after), first.trans semantics _ ?_,
      Or.inr ⟨base, after, rfl, valid, finalLive, writable, rep, frame⟩⟩
    rw [pointerEq] at allocation written
    apply Steps.bind_ok semantics _ (Prim.eval_alloc_ok usize _ _ caller allocated _ allocation) (by rfl)
    exact (stored_steps caller allocated view left right base written).trans semantics _ loop

end Compiler.ZigAir.MemoryWordSwap
