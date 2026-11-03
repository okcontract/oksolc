/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedSliceElement
import Compiler.ZigAir.MemorySliceElements
import Compiler.ZigAir.MemorySlots
import Compiler.ZigAir.MemoryFill

namespace Compiler.ZigAir.MemorySliceInvocation
open Memory MemoryAir Memory.WordArray GeneratedMemory
open MemoryFill (size size_valid size_typed scalar_read_size)

def arguments (view : View) (index : Nat) : List Value :=
  [view.buffer, size view.length, size index]
private abbrev slot (child : Ty) (id : Nat) : Value := .pointer (.pointer true false child) ⟨id, 0⟩
private abbrev readonly (child : Ty) (id : Nat) : Value := .pointer (.pointer false false child) ⟨id, 0⟩

private theorem unit_typed : (Value.scalar .unit).hasType (.scalar .unit) = true := rfl

private theorem pointer_valid (writable many : Bool) (child : Ty) (address : Address) :
    (Value.pointer (.pointer writable many child) address).valid = true := rfl
private theorem pointer_typed (writable many : Bool) (child : Ty) (address : Address) :
    (Value.pointer (.pointer writable many child) address).hasType (.pointer writable many child) = true := by simp [Value.hasType, Value.type, Value.valid]
private theorem buffer_valid (view : View) : view.buffer.valid = true := rfl
private theorem buffer_typed (view : View) : view.buffer.hasType (.pointer true true word) = true := rfl
private theorem slice_valid (view : View) (bound : view.length < addressLimit) : view.slice.valid = true := by
  simpa [View.slice, Value.valid, addressLimit] using bound
private theorem slice_typed (view : View) (bound : view.length < addressLimit) :
    view.slice.hasType (.slice true word) = true := by
  simpa [Value.hasType, View.slice, Value.type] using slice_valid view bound

private theorem subtract_eval (left right : Scalar.Ref) (env : Scalar.Env) (x y : Int)
    (readLeft : left.eval env = .ok (.int false 64 x))
    (readRight : right.eval env = .ok (.int false 64 y)) :
    (Scalar.Prim.arithmetic .sub .unchecked left right).eval [] env =
      Scalar.integer false 64 (x - y) .unchecked := by
  simp only [Scalar.Prim.eval, readLeft, readRight, bind, Except.bind, and_self, ↓reduceIte,
    Scalar.Arithmetic.eval]

private theorem subtract_zero (env : Env) (id n : Nat) (bound : n < addressLimit)
    (found : env id = some (size n)) :
    (Scalar.Prim.arithmetic .sub .unchecked (.local id) (.constant (.int false 64 0))).eval [] (scalarEnv env) =
      .ok (.int false 64 n) := by
  have read := scalar_read_size env id n bound found
  have valid := size_valid n bound
  change (Scalar.Value.int false 64 n).valid = true at valid
  simp only [Scalar.Value.valid] at valid
  have zeroValid : (Scalar.Value.int false 64 0).valid = true := by decide +kernel
  have zero : (Scalar.Ref.constant (.int false 64 0)).eval (scalarEnv env) = .ok (.int false 64 0) := by
    simp [Scalar.Ref.eval, zeroValid]
  have integer : Scalar.integer false 64 n .unchecked = .ok (.int false 64 n) := by
    simp [Scalar.integer, valid]
  rw [subtract_eval _ _ _ _ _ read zero, Int.sub_zero]
  exact integer

private theorem check_zero (env : Env) (args : List Value) (state : State) (n : Nat)
    (bound : n < addressLimit) (found : env 1 = some (size n)) :
    (Prim.checkBounds (.constant (size 0)) (.local 1) .unbounded).eval args env state =
      (.ok (.scalar .unit), state) := by
  have read : (Ref.local 1).eval env = .ok (size n) := by
    simp only [Ref.eval_local, found, size_valid n bound, ↓reduceIte]
  have number := Ref.natural_of_eval (.local 1) env n read
  have zero : (Ref.constant (size 0)).natural env = .ok 0 := rfl
  rw [Prim.eval_bounds, number, zero]
  simp only [Bound.eval, checkSliceBounds, bind, Except.bind, Int.toNat_natCast, Nat.zero_le]
  rfl

attribute [local simp] Code.eval_bind Code.eval_ret Prim.eval_argument Prim.eval_cast Prim.eval_offset
  Prim.eval_store Prim.eval_load Prim.eval_scalar Prim.eval_slice Prim.eval_slice_element
  Ref.eval_local Ref.eval_constant Ref.natural_eq Control.Env.set pointer_valid pointer_typed buffer_valid buffer_typed

/-- This invariant records only invocation-local changes. In particular, the
caller's complete ordered heap is retained, including uninitialized cells. -/
private structure Setup (origin current : State) (view : View) : Prop where
  valid : current.valid = true
  cap : Writable current view
  stack : current.heap.StackSince origin.nextId
  older : current.heap.older origin.nextId = origin.heap
  fresh : origin.nextId ≤ current.nextId

private theorem Setup.initial (state : State) (view : View) (valid : state.valid = true) (cap : Writable state view) :
    Setup state state view :=
  ⟨valid, cap, (valid_initial_frame state valid).1, (valid_initial_frame state valid).2, Nat.le_refl _⟩

private theorem Setup.saved (origin current allocated after : State) (view : View) (value : Value)
    (before : Setup origin current view)
    (allocation : allocate current value.type = .ok (slot value.type current.nextId, allocated))
    (written : store allocated (slot value.type current.nextId) value = .ok after) : Setup origin after view := by
  have valid := allocate_preserves_valid current value.type _ allocated allocation
  have cap := writable_allocate current allocated view value.type _ before.valid before.cap allocation
  have af := allocate_frame current allocated value.type _ origin.nextId allocation before.fresh before.stack
  have sf := store_frame allocated after true false value.type ⟨current.nextId, 0⟩ value origin.nextId
    written before.fresh af.1
  have counters := store_keeps_counters allocated _ value after written
  have next := (allocate_pointer current value.type _ allocated allocation).2
  have fresh := before.fresh
  exact ⟨store_preserves_valid allocated _ value after valid written,
    writable_store allocated after view _ value written cap, sf.1, sf.2.trans (af.2.trans before.older), by omega⟩

private theorem Setup.cleaned (origin current : State) (view : View) (setup : Setup origin current view) :
    (cleanup origin.nextId current).valid = true ∧ (cleanup origin.nextId current).heap = origin.heap :=
  ⟨cleanup_preserves_valid origin.nextId current setup.valid,
    (cleanup_eq_older current origin.nextId setup.stack).trans setup.older⟩

def returnCode : Code :=
  .bind 11 (.scalar .unit) (.store (.local 10) (.local 9))
    (.bind 12 (.pointer false false (.slice true word))
      (.pointerCast (.pointer false false (.slice true word)) (.local 10))
    (.bind 13 (.slice true word) (.load (.local 12))
    (.bind 14 (.pointer true false word) (.sliceElementPointer (.local 13) (.local 2))
    (.ret (.local 14)))))
def sliceCode : Code := .bind 10 (.pointer true false (.slice true word)) (.alloc (.slice true word)) returnCode
def constructCode : Code :=
  .bind 8 usize (.scalar (.arithmetic .sub .unchecked (.local 1) (.constant (.int false 64 0))))
    (.bind 16 (.scalar .unit) (.checkBounds (.constant (size 0)) (.local 1) .unbounded)
    (.bind 9 (.slice true word) (.slice (.slice true word) (.local 7) (.local 8)) sliceCode))
def prepareCode : Code :=
  .bind 5 (.pointer false false (.pointer true true word))
    (.pointerCast (.pointer false false (.pointer true true word)) (.local 3))
    (.bind 6 (.pointer true true word) (.load (.local 5))
    (.bind 7 (.pointer true true word) (.offsetPointer false (.local 6) (.constant (size 0))) constructCode))
def storeCode : Code := .bind 4 (.scalar .unit) (.store (.local 3) (.local 0)) prepareCode
def allocCode : Code := .bind 3 (.pointer true false (.pointer true true word)) (.alloc (.pointer true true word)) storeCode

theorem generated_body : fn_slice_element.body =
    .bind 0 (.pointer true true word) (.argument 0)
      (.bind 1 usize (.argument 1) (.bind 2 usize (.argument 2) allocCode)) := rfl

def inputEnv (view : View) (index : Nat) : Env :=
  ((Control.Env.set (fun _ => none) 0 view.buffer).set 1 (size view.length)).set 2 (size index)

private theorem body_head (state : State) (view : View) (index : Nat)
    (width : view.length < addressLimit) (indexWidth : index < addressLimit) :
    fn_slice_element.body.eval semantics (arguments view index) (fun _ => none) state =
      allocCode.eval semantics (arguments view index) (inputEnv view index) state := by
  rw [generated_body]
  simp only [Code.eval_bind, Prim.eval_argument, arguments, List.getElem?_cons_zero,
    List.getElem?_cons_succ, View.buffer, pointer_typed, size_typed _ width, size_typed _ indexWidth,
    ↓reduceIte, inputEnv]

private theorem construct_steps (state : State) (view : View) (index : Nat) (args : List Value) (env : Env)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length)
    (h1 : env 1 = some (size view.length)) (h2 : env 2 = some (size index)) (h7 : env 7 = some view.buffer) :
    ∃ next, constructCode.eval semantics args env state = sliceCode.eval semantics args next state ∧
      next 2 = some (size index) ∧ next 9 = some view.slice := by
  have width := view_width state view initial cap
  have slice := make_slice state view initial cap (by omega)
  let e8 := env.set 8 (size view.length)
  let e16 := e8.set 16 (.scalar .unit)
  refine ⟨e16.set 9 view.slice, ?_, by simp [e16, e8, h2], by simp⟩
  have sub := subtract_zero env 1 view.length width h1
  have bounds := check_zero e8 args state view.length width (by simp [e8, h1])
  have subtraction : (Prim.scalar (.arithmetic .sub .unchecked (.local 1) (.constant (.int false 64 0)))).eval args env state =
      (.ok (size view.length), state) := by
    rw [Prim.eval_scalar, sub]; rfl
  have slicing : (Prim.slice (.slice true word) (.local 7) (.local 8)).eval args e16 state = (.ok view.slice, state) := by
    have pointer : (Ref.local 7).eval e16 = .ok view.buffer := by
      simp only [Ref.eval_local, e16, e8, Control.Env.set, Nat.reduceEqDiff, ↓reduceIte, h7, buffer_valid]
    have length : (Ref.local 8).eval e16 = .ok (size view.length) := by
      simp only [Ref.eval_local, e16, e8, Control.Env.set, Nat.reduceEqDiff, ↓reduceIte, size_valid _ width]
    rw [Prim.eval_slice, pointer, Ref.natural_of_eval _ _ _ length]
    simpa only [bind, Except.bind, Int.toNat_natCast] using congrArg (fun r => (r, state)) slice
  rw [constructCode, Code.eval_bind_ok subtraction (size_typed _ width),
    Code.eval_bind_ok bounds (by rfl), Code.eval_bind_ok slicing (slice_typed _ width)]

private theorem prepare_steps (state : State) (view : View) (index id : Nat) (args : List Value) (env : Env)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length)
    (h1 : env 1 = some (size view.length)) (h2 : env 2 = some (size index))
    (h3 : env 3 = some (slot (.pointer true true word) id))
    (cast : pointerCast state (.pointer false false (.pointer true true word)) (slot (.pointer true true word) id) =
      .ok (readonly (.pointer true true word) id))
    (read : load state (readonly (.pointer true true word) id) = .ok view.buffer) :
    ∃ next, prepareCode.eval semantics args env state = sliceCode.eval semantics args next state ∧
      next 2 = some (size index) ∧ next 9 = some view.slice := by
  have offset := offset_zero state view initial cap (by omega)
  let e5 := env.set 5 (readonly (.pointer true true word) id)
  let e6 := e5.set 6 view.buffer
  let e7 := e6.set 7 view.buffer
  obtain ⟨next, tail, h2', h9'⟩ := construct_steps state view index args e7 initial cap inside
    (by simp [e7, e6, e5, h1]) (by simp [e7, e6, e5, h2]) (by simp [e7])
  refine ⟨next, ?_, h2', h9'⟩
  have beginning : prepareCode.eval semantics args env state = constructCode.eval semantics args e7 state := by
    have zeroValid : (Value.scalar (.int false 64 0)).valid = true := by decide +kernel
    dsimp only [slot, readonly] at cast read
    simp only [prepareCode, Code.eval_bind, Prim.eval_cast, Prim.eval_load, Prim.eval_offset,
      Ref.eval_local, Ref.eval_constant, Ref.natural_eq, Control.Env.set, h3, slot, pointer_valid,
      bind, Except.bind, cast, read, buffer_valid, buffer_typed, pointer_typed, ↓reduceIte,
      size, Int.natCast_zero, zeroValid, Int.toNat_zero, offset]
    rfl
  exact beginning.trans tail

private theorem return_steps (state after : State) (view : View) (index id : Nat) (args : List Value) (env : Env)
    (initial : after.valid = true) (cap : Writable after view) (inside : index < view.length)
    (h2 : env 2 = some (size index)) (h9 : env 9 = some view.slice)
    (h10 : env 10 = some (slot (.slice true word) id))
    (written : store state (slot (.slice true word) id) view.slice = .ok after) :
    returnCode.eval semantics args env state = .returned (view.pointer index) after := by
  have width := view_width after view initial cap
  have indexWidth : index < addressLimit := by omega
  have read := load_alias_after_store state true false (.slice true word) ⟨id, 0⟩ view.slice after false false written
  have cast := pointerCast_readonly_of_load after true false (.slice true word) ⟨id, 0⟩ view.slice
    (load_after_store state _ view.slice after written)
  have element := slice_element after view index initial cap inside
  dsimp only [slot] at written
  simp only [returnCode, Code.eval_bind, Prim.eval_store, Prim.eval_cast, Prim.eval_load,
    Prim.eval_slice_element, Code.eval_ret, Ref.eval_local, Ref.natural_eq,
    Control.Env.set, h10, h9, h2, slot, pointer_valid, slice_valid _ width,
    size_valid _ indexWidth, bind, Except.bind, written, cast, read,
    pointer_typed, slice_typed _ width, ↓reduceIte, Nat.reduceEqDiff]
  simp only [size, Int.toNat_natCast, element, View.pointer, pointer_valid, pointer_typed, unit_typed, ↓reduceIte]

/-- Complete captured invocation: only exhaustion can interrupt a valid,
in-bounds array access, and cleanup preserves the exact caller heap. Counters
retain allocation history. Native ABI and Zig source/backend preservation
remain separate obligations. -/
theorem run_preserves (state : State) (view : View) (index : Nat)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    ∃ result after, fn_slice_element.run (arguments view index) state = (result, after) ∧
      after.valid = true ∧ after.heap = state.heap ∧
      (result = .ok (view.pointer index) ∨ result = .error .outOfMemory) := by
  have width := view_width state view initial cap
  have indexWidth : index < addressLimit := by omega
  have lengthTyped : (size view.length).hasType (.scalar (.int false 64)) = true := size_typed _ width
  have indexTyped : (size index).hasType (.scalar (.int false 64)) = true := size_typed _ indexWidth
  have inputs : fn_slice_element.accepts (arguments view index) state = true := by
    simp [Program.accepts, arguments, fn_slice_element, initial, lengthTyped, indexTyped]
  have setup := Setup.initial state view initial cap
  rw [Program.run, if_pos inputs, body_head state view index width indexWidth]
  cases allocation : allocate state (.pointer true true word) with
  | error reason =>
    have same := allocate_fault_of_layout state _ ⟨8, 8⟩ reason initial rfl allocation
    subst reason
    refine ⟨.error .outOfMemory, cleanup state.nextId state, ?_, setup.cleaned.1, setup.cleaned.2, Or.inr rfl⟩
    simp only [allocCode, Code.eval_bind, Prim.eval_alloc_fault _ _ _ _ _ allocation, Program.finish]
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨pointerEq, _⟩ := allocate_pointer state _ pointer allocated allocation
    subst pointer
    obtain ⟨saved, written⟩ := fresh_store_total state allocated view.buffer _ ⟨8, 8⟩ rfl rfl (by decide) allocation
    have prepared := Setup.saved state state allocated saved view view.buffer setup allocation written
    let env := (inputEnv view index).set 3 (slot (.pointer true true word) state.nextId)
    have refSlot : (Ref.local 3).eval env = .ok (slot (.pointer true true word) state.nextId) := by
      simp [env, slot]
    have refBuffer : (Ref.local 0).eval env = .ok view.buffer := by simp [env, inputEnv]
    have stored := Prim.eval_store_ok (.local 3) (.local 0) (arguments view index) env allocated saved
      _ _ refSlot refBuffer written
    rw [allocCode, Code.eval_bind_ok (Prim.eval_alloc_ok _ _ _ _ _ _ allocation) (by rfl),
      storeCode, Code.eval_bind_ok stored unit_typed]
    have read := load_after_store allocated _ view.buffer saved written
    have cast := pointerCast_readonly_of_load saved true false (.pointer true true word) ⟨state.nextId, 0⟩ view.buffer read
    have readonlyRead := load_alias_after_store allocated true false (.pointer true true word) ⟨state.nextId, 0⟩
      view.buffer saved false false written
    obtain ⟨next, steps, h2, h9⟩ := prepare_steps saved view index state.nextId (arguments view index)
      (env.set 4 (.scalar .unit)) prepared.valid prepared.cap inside
      (by simp [env, inputEnv]) (by simp [env, inputEnv]) (by simp [env]) cast readonlyRead
    rw [steps]
    cases sliceAllocation : allocate saved (.slice true word) with
    | error reason =>
      have same := allocate_fault_of_layout saved _ ⟨16, 8⟩ reason prepared.valid rfl sliceAllocation
      subst reason
      refine ⟨.error .outOfMemory, cleanup state.nextId saved, ?_, prepared.cleaned.1, prepared.cleaned.2, Or.inr rfl⟩
      simp only [sliceCode, Code.eval_bind, Prim.eval_alloc_fault _ _ _ _ _ sliceAllocation, Program.finish]
    | ok pair =>
      obtain ⟨pointer, sliceAllocated⟩ := pair
      obtain ⟨pointerEq, _⟩ := allocate_pointer saved _ pointer sliceAllocated sliceAllocation
      subst pointer
      obtain ⟨after, sliceWritten⟩ := fresh_store_total saved sliceAllocated view.slice _ ⟨16, 8⟩
        (slice_valid view width) rfl (by decide) sliceAllocation
      have ready := Setup.saved state saved sliceAllocated after view view.slice prepared sliceAllocation sliceWritten
      rw [sliceCode, Code.eval_bind_ok (Prim.eval_alloc_ok _ _ _ _ _ _ sliceAllocation) (by rfl),
        return_steps sliceAllocated after view index saved.nextId (arguments view index) _ ready.valid ready.cap inside
          (by simp [h2]) (by simp [h9]) (by simp [slot]) sliceWritten]
      refine ⟨.ok (view.pointer index), cleanup state.nextId after, ?_, ready.cleaned.1, ready.cleaned.2, Or.inl rfl⟩
      simp only [Program.finish, fn_slice_element, View.pointer, word, pointer_typed, ↓reduceIte]

end Compiler.ZigAir.MemorySliceInvocation
