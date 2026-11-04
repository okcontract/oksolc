/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirEntry
import Compiler.ZigAir.AggregateByteRead

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.WordRead
open Memory AggregateAir Control.Machine

abbrev arrayPointer (count : Nat) : Ty := .pointer false false (.array count ByteSlice.byte)
abbrev bytePointer : Ty := .pointer false true ByteSlice.byte
abbrev Code := Control.Code Ty AggregateCall.Prim Ref true

/-- The same seventeen captured instructions occur at every lane read in both
the fill round and the full-block loop. Registers and byte offsets vary; native
allocation, assertion, bounds and read operations are retained. -/
def finish (base guard : Nat) (next : Code) : Code :=
  .bind (base + 8) (.pointer false false inputType)
    (.primitive (.memory (.pointerCast (.pointer false false inputType) (.local (base + 6)))))
  (.bind (base + 9) (.scalar .unit)
    (.invoke GeneratedWyhashUpdate.assertion [.constant (.value (.scalar (.bool true)))])
  (.bind (base + 10) inputType (.primitive (.load (.local (base + 8))))
  (.bind (base + 11) bytePointer (.primitive (.memory (.slicePtr (.local (base + 10)))))
  (.bind (base + 12) bytePointer
    (.primitive (.memory (.offsetPointer false (.local (base + 11)) (.constant (.scalar (.int false 64 0))))))
  (.bind (guard + 1) (.scalar .unit)
    (.primitive (.memory (.checkBounds (.constant (.scalar (.int false 64 0)))
      (.constant (.scalar (.int false 64 8))) (.slice (.local (base + 10))))))
  (.bind (base + 13) (arrayPointer 8)
    (.primitive (.memory (.pointerCast (arrayPointer 8) (.local (base + 12)))))
  (.bind (base + 15) (.array 8 ByteSlice.byte) (.primitive (.loadBytes (.local (base + 13))))
  (.bind (base + 16) usize (.primitive (.bytesToWord (.local (base + 15)))) next))))))))

def save (base guard : Nat) (next : Code) : Code :=
  .bind (base + 6) (.pointer true false inputType) (.primitive (.memory (.alloc inputType)))
  (.bind (base + 7) (.scalar .unit) (.primitive (.store (.local (base + 6)) (.local (base + 4))))
    (finish base guard next))

def prepare (base guard saved offset : Nat) (next : Code) : Code :=
  .bind base (arrayPointer 48) (.primitive (.load (.local saved))) $
  .bind (base + 1) bytePointer (.primitive (.memory (.pointerCast bytePointer (.local base)))) $
  .bind (base + 2) bytePointer (.primitive (.memory (.offsetPointer false (.local (base + 1))
    (.constant (.scalar (.int false 64 offset)))))) $
  .bind guard (.scalar .unit) (.primitive (.memory (.checkBounds (.constant (.scalar (.int false 64 offset)))
    (.constant (.scalar (.int false 64 48))) (.array 48)))) $
  .bind (base + 3) (arrayPointer (48 - offset))
    (.primitive (.memory (.pointerCast (arrayPointer (48 - offset)) (.local (base + 2))))) $
  .bind (base + 4) inputType (.primitive (.arrayToSlice (.local (base + 3)))) next

def code (base guard saved offset : Nat) (next : Code) : Code :=
  prepare base guard saved offset (save base guard next)

def prepareEnv (env : Env) (base guard : Nat) (address : Address) (offset : Nat) : Env :=
  let env := env.set base (.value (.pointer (arrayPointer 48) address))
  let env := env.set (base + 1) (.value (.pointer bytePointer address))
  let env := env.set (base + 2) (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩))
  let env := env.set guard (.value (.scalar .unit))
  let env := env.set (base + 3) (.value (.pointer (arrayPointer (48 - offset))
    ⟨address.allocation, address.offset + offset⟩))
  env.set (base + 4) (.value (.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset)))

theorem assertion (state : State) (valid : state.valid = true) :
    GeneratedWyhashUpdate.assertion.run [.value (.scalar (.bool true))] state =
      (.ok (.value (.scalar .unit)), state) := by
  simp [GeneratedWyhashUpdate.assertion, Program.run, Program.finish, Control.Code.eval,
    AggregateAir.semantics, Prim.eval, Prim.transition, Ref.eval, Ref.value, Control.Env.set,
    Register.hasType, Register.type, Register.valid, Value.type, Value.valid,
    Scalar.Value.type, Scalar.Value.valid, valid, cleanup_initial state valid, bind, Except.bind,
    pure, Except.pure]

theorem block_limit : 48 < addressLimit := by decide +kernel

theorem natural_constant (env : MemoryAir.Env) (offset : Nat) (bound : offset < addressLimit) :
    (MemoryAir.Ref.constant (.scalar (.int false 64 offset))).natural env = .ok offset := by
  have valid : (Value.scalar (.int false 64 offset)).valid = true :=
    Scalar.unsigned_nat_valid offset 64 bound
  simpa only [Int.toNat_natCast] using MemoryAir.Ref.natural_of_eval _ env offset
    (MemoryAir.Ref.eval_constant_of_valid _ env valid)

theorem offset_eval (state : State) (address : Address) (bytes : Nat → BitVec 8)
    (reads : ByteRange.Reads state address 48 bytes) (start offset : Nat)
    (first : start < 48) (inside : start + offset < 48)
    (args : List Register) (env : Env) (reg : Nat)
    (found : env reg = some (.value (.pointer bytePointer ⟨address.allocation, address.offset + start⟩))) :
    (Prim.memory (.offsetPointer false (.local reg) (.constant (.scalar (.int false 64 offset))))).eval
      args env state = (.ok (.value (.pointer bytePointer
        ⟨address.allocation, address.offset + (start + offset)⟩)), state) := by
  have data := SliceBytesAir.memory_local env reg
    (.pointer bytePointer ⟨address.allocation, address.offset + start⟩) found rfl
  have advance : offsetPointer state false
      (.pointer bytePointer ⟨address.allocation, address.offset + start⟩) offset =
      .ok (.pointer bytePointer ⟨address.allocation, address.offset + (start + offset)⟩) :=
    reads.offset_pointer start offset first inside
  have limit : 48 < addressLimit := block_limit
  have count := natural_constant (values env) offset (Nat.lt_trans (by omega : offset < 48) limit)
  exact eval_offset _ _ args env state _ _ offset data count advance

theorem array_bounds_eval (state : State) (offset : Nat) (inside : offset ≤ 48)
    (args : List Register) (env : Env) :
    (Prim.memory (.checkBounds (.constant (.scalar (.int false 64 offset)))
      (.constant (.scalar (.int false 64 48))) (.array 48))).eval args env state =
        (.ok (.value (.scalar .unit)), state) := by
  have limit : 48 < addressLimit := block_limit
  have first := natural_constant (values env) offset (Nat.lt_of_le_of_lt inside limit)
  have last : (MemoryAir.Ref.constant (.scalar (.int false 64 48))).natural (values env) = .ok 48 :=
    natural_constant (values env) 48 limit
  exact eval_bounds _ _ _ args env state offset 48 (some 48) first last rfl
    (by simp [checkSliceBounds, inside])

theorem prepare_steps (base guard saved offset savedId : Nat) (separate : base + 16 < guard)
    (next : Code) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (state : State) (address : Address) (bytes : Nat → BitVec 8)
    (reads : ByteRange.Reads state address 48 bytes) (inside : offset + 8 ≤ 48)
    (read : Memory.load state (slot false (arrayPointer 48) savedId) =
      .ok (.pointer (arrayPointer 48) address))
    (args : List Register) (env : Env)
    (found : env saved = some (.value (slot false (arrayPointer 48) savedId))) :
    Steps AggregateCall.semantics args
      (.suspended ⟨prepare base guard saved offset next, env, state, frames⟩)
      (.suspended ⟨next, prepareEnv env base guard address offset, state, frames⟩) := by
  let e0 := env.set base (.value (.pointer (arrayPointer 48) address))
  let e1 := e0.set (base + 1) (.value (.pointer bytePointer address))
  let e2 := e1.set (base + 2) (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩))
  let eg := e2.set guard (.value (.scalar .unit))
  let e3 := eg.set (base + 3) (.value (.pointer (arrayPointer (48 - offset))
    ⟨address.allocation, address.offset + offset⟩))
  have p0 := eval_load (.local saved) args env state _ _ (value_local env saved _ found rfl)
    (congrArg (Except.map Register.value) read)
  have p1 : (Prim.memory (.pointerCast bytePointer (.local base))).eval args e0 state =
      (.ok (.value (.pointer bytePointer address)), state) := by
    as_aux_lemma =>
      apply eval_memory
      have data := SliceBytesAir.memory_local e0 base (.pointer (arrayPointer 48) address)
        (by simp [e0, Control.Env.set]) rfl
      have cast : pointerCast state bytePointer (.pointer (arrayPointer 48) address) =
        .ok (.pointer bytePointer address) := by
        simpa only [Nat.add_zero] using reads.byte_cast 0 48 (by decide)
      simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, cast, bind, Except.bind]
  have p2 : (Prim.memory (.offsetPointer false (.local (base + 1))
      (.constant (.scalar (.int false 64 offset))))).eval args e1 state =
        (.ok (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩)), state) := by
    simpa only [Nat.add_zero, Nat.zero_add] using offset_eval state address bytes reads 0 offset
      (by decide) (by omega) args e1 (base + 1) (by simp [e1, Control.Env.set])
  have pg := array_bounds_eval state offset (by omega) args e2
  have limit : 48 < addressLimit := block_limit
  have p3 : (Prim.memory (.pointerCast (arrayPointer (48 - offset)) (.local (base + 2)))).eval args eg state =
      (.ok (.value (.pointer (arrayPointer (48 - offset)) ⟨address.allocation, address.offset + offset⟩)), state) := by
    as_aux_lemma =>
      apply eval_memory
      have data := SliceBytesAir.memory_local eg (base + 2)
        (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩)
        (by simp [eg, e2, Control.Env.set, show base + 2 ≠ guard by omega]) rfl
      have cast : pointerCast state (arrayPointer (48 - offset))
          (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩) =
            .ok (.pointer (arrayPointer (48 - offset)) ⟨address.allocation, address.offset + offset⟩) :=
        reads.array_cast offset (48 - offset) (by omega) (by omega)
      simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, cast, bind, Except.bind]
  have sliceValid : (Value.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset)).valid = true := by
    as_aux_lemma =>
      simp only [Value.valid, decide_eq_true_eq]; omega
  have p4 : (Prim.arrayToSlice (.local (base + 3))).eval args e3 state =
      (.ok (.value (.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset))), state) := by
    as_aux_lemma =>
      have data := value_local e3 (base + 3)
        (.pointer (arrayPointer (48 - offset)) ⟨address.allocation, address.offset + offset⟩)
        (by simp [e3, Control.Env.set]) rfl
      simp only [Prim.eval, Prim.transition, data, ScalarBytes.arrayToSlice, sliceValid,
        ↓reduceIte, bind, Except.bind, pure, Except.pure]
  exact AggregateCall.primitive_steps args p0 (by rfl) <|
    AggregateCall.primitive_steps args p1 (by rfl) <|
    AggregateCall.primitive_steps args p2 (by rfl) <|
    AggregateCall.primitive_steps args pg (by rfl) <|
    AggregateCall.primitive_steps args p3 (by
      simp [Register.hasType, Register.type, Register.valid, Value.type, Value.valid]) <|
    AggregateCall.primitive_steps args p4 sliceValid (.refl _)

def finishEnv (env : Env) (base guard savedId : Nat) (address : Address)
    (offset : Nat) (bytes : Nat → BitVec 8) : Env :=
  let env := env.set (base + 8) (.value (slot false inputType savedId))
  let env := env.set (base + 9) (.value (.scalar .unit))
  let env := env.set (base + 10) (.value (.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset)))
  let env := env.set (base + 11) (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩))
  let env := env.set (base + 12) (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩))
  let env := env.set (guard + 1) (.value (.scalar .unit))
  let env := env.set (base + 13) (.value (.pointer (arrayPointer 8) ⟨address.allocation, address.offset + offset⟩))
  let env := env.set (base + 15) (.bytes ((List.range 8).map fun i => bytes (offset + i)))
  env.set (base + 16) (number (ByteSlice.decode bytes offset 8))

theorem finish_steps (base guard savedId offset : Nat) (separate : base + 16 < guard)
    (next : Code) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (state : State) (valid : state.valid = true) (address : Address) (bytes : Nat → BitVec 8)
    (reads : ByteRange.Reads state address 48 bytes) (inside : offset + 8 ≤ 48)
    (read : Memory.load state (slot true inputType savedId) =
      .ok (.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset)))
    (args : List Register) (env : Env)
    (found : env (base + 6) = some (.value (slot true inputType savedId))) :
    Steps AggregateCall.semantics args
      (.suspended ⟨finish base guard next, env, state, frames⟩)
      (.suspended ⟨next, finishEnv env base guard savedId address offset bytes, state, frames⟩) := by
  let e8 := env.set (base + 8) (.value (slot false inputType savedId))
  let e9 := e8.set (base + 9) (.value (.scalar .unit))
  let e10 := e9.set (base + 10) (.value (.slice inputType
    ⟨address.allocation, address.offset + offset⟩ (48 - offset)))
  let e11 := e10.set (base + 11) (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩))
  let e12 := e11.set (base + 12) (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩))
  let eg := e12.set (guard + 1) (.value (.scalar .unit))
  let e13 := eg.set (base + 13) (.value (.pointer (arrayPointer 8) ⟨address.allocation, address.offset + offset⟩))
  let e15 := e13.set (base + 15) (.bytes ((List.range 8).map fun i => bytes (offset + i)))
  have sliceValid : (Value.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset)).valid = true := by
    have := block_limit
    simp only [Value.valid, decide_eq_true_eq]; omega
  have p8 := saved_cast state inputType savedId (base + 6) _ read args env found
  have p9 : (AggregateCall.Prim.invoke GeneratedWyhashUpdate.assertion
      [.constant (.value (.scalar (.bool true)))]).eval args e8 state =
        (.ok (.value (.scalar .unit)), state) :=
    (AggregateCall.invoke_constant _ _ args e8 state rfl).trans (assertion state valid)
  have p10 := eval_load (.local (base + 8)) args e9 state (slot false inputType savedId) _
    (value_local e9 (base + 8) _ (by simp [e9, e8, Control.Env.set]) rfl)
    (congrArg (Except.map Register.value) (saved_readonly state inputType savedId _ read))
  have p11 : (Prim.memory (.slicePtr (.local (base + 10)))).eval args e10 state =
      (.ok (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩)), state) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e10 (base + 10)
      (.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset))
      (by simp [e10, Control.Env.set]) sliceValid
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, bind, Except.bind]
  have p12 : (Prim.memory (.offsetPointer false (.local (base + 11))
      (.constant (.scalar (.int false 64 0))))).eval args e11 state =
        (.ok (.value (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩)), state) := by
    simpa only [Nat.add_zero] using offset_eval state address bytes reads offset 0
      (by omega) (by omega) args e11 (base + 11) (by simp [e11, Control.Env.set])
  have pg : (Prim.memory (.checkBounds (.constant (.scalar (.int false 64 0)))
      (.constant (.scalar (.int false 64 8))) (.slice (.local (base + 10))))).eval args e12 state =
        (.ok (.value (.scalar .unit)), state) := by
    have data := SliceBytesAir.memory_local e12 (base + 10)
      (.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset))
      (by simp [e12, e11, e10, Control.Env.set]) sliceValid
    apply eval_bounds _ _ _ args e12 state 0 8 (some (48 - offset)) rfl rfl
    · simp only [MemoryAir.Bound.eval, data, bind, Except.bind]
    · simp [checkSliceBounds, show 8 ≤ 48 - offset by omega]
  have p13 : (Prim.memory (.pointerCast (arrayPointer 8) (.local (base + 12)))).eval args eg state =
      (.ok (.value (.pointer (arrayPointer 8) ⟨address.allocation, address.offset + offset⟩)), state) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local eg (base + 12)
      (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩)
      (by simp [eg, e12, Control.Env.set, show base + 12 ≠ guard + 1 by omega]) rfl
    have cast : pointerCast state (arrayPointer 8)
        (.pointer bytePointer ⟨address.allocation, address.offset + offset⟩) =
          .ok (.pointer (arrayPointer 8) ⟨address.allocation, address.offset + offset⟩) :=
      reads.array_cast offset 8 (by omega) inside
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, cast, bind, Except.bind]
  have p15 := eval_load_bytes state address 48 offset 8 bytes reads inside args e13 (base + 13)
    (by simp [e13, Control.Env.set])
  have p16 := eval_bytes_word state bytes offset args e15 (base + 15) (by simp [e15, Control.Env.set])
  exact AggregateCall.primitive_steps args p8 (by rfl) <|
    Steps.bind_ok AggregateCall.semantics args p9 (by rfl) <|
    AggregateCall.primitive_steps args p10 sliceValid <|
    AggregateCall.primitive_steps args p11 (by rfl) <|
    AggregateCall.primitive_steps args p12 (by rfl) <|
    AggregateCall.primitive_steps args pg (by rfl) <|
    AggregateCall.primitive_steps args p13 (by rfl) <|
    AggregateCall.primitive_steps args p15 (by
      simp [Register.hasType, Register.type, Register.valid, ByteSlice.byte]) <|
    AggregateCall.primitive_steps args p16 (number_typed _) (.refl _)

def savedEnv (env : Env) (base id : Nat) : Env :=
  (env.set (base + 6) (.value (slot true inputType id))).set (base + 7) (.value (.scalar .unit))

def resultEnv (env : Env) (base guard id : Nat) (address : Address)
    (offset : Nat) (bytes : Nat → BitVec 8) : Env :=
  finishEnv (savedEnv (prepareEnv env base guard address offset) base id)
    base guard id address offset bytes

/-- Allocation failure is an explicit reached execution. On success, the
original bytes survive the actual saved-slice allocation and supply the decoded
word. No allocation outcome, wider load or byte-to-word callback is assumed. -/
theorem steps (base guard saved offset savedId : Nat) (separate : base + 16 < guard)
    (next : Code) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (state : State) (valid : state.valid = true) (address : Address) (bytes : Nat → BitVec 8)
    (reads : ByteRange.Reads state address 48 bytes) (inside : offset + 8 ≤ 48)
    (read : Memory.load state (slot false (arrayPointer 48) savedId) =
      .ok (.pointer (arrayPointer 48) address))
    (args : List Register) (env : Env)
    (found : env saved = some (.value (slot false (arrayPointer 48) savedId))) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics args
          (.suspended ⟨code base guard saved offset next, env, state, frames⟩)
          (.finished (.fault .outOfMemory after)) ∨
       Steps AggregateCall.semantics args
          (.suspended ⟨code base guard saved offset next, env, state, frames⟩)
          (.suspended ⟨next, resultEnv env base guard state.nextId address offset bytes, after, frames⟩)) := by
  let prepared := prepareEnv env base guard address offset
  let value := Value.slice inputType ⟨address.allocation, address.offset + offset⟩ (48 - offset)
  have valueValid : value.valid = true := by
    have := block_limit
    simp only [value, Value.valid, decide_eq_true_eq]; omega
  have head := prepare_steps base guard saved offset savedId separate (save base guard next)
    frames state address bytes reads inside read args env found
  have allocate := AggregateCall.save_steps value (.local (base + 4)) (base + 6) (base + 7)
    (finish base guard next) frames args prepared state
    (ref_local _ _ (.value value) (by simp [prepared, prepareEnv, Control.Env.set, value]) valueValid)
  obtain ⟨outcome, after, ran, stack, failed | ⟨success, loaded, _⟩⟩ :=
    SavedValue.verified state value ⟨16, 8⟩ valid valueValid rfl (by decide)
  · rw [failed] at ran
    rw [ran] at allocate
    exact ⟨after, stack, Or.inl (head.trans AggregateCall.semantics args allocate)⟩
  · rw [success] at ran
    rw [ran] at allocate
    have tail := finish_steps base guard state.nextId offset separate next frames after stack.valid address bytes
      (reads.extend stack address 48 bytes) inside loaded args (savedEnv prepared base state.nextId)
      (by simp [savedEnv, Control.Env.set])
    exact ⟨after, stack, Or.inr (head.trans AggregateCall.semantics args
      (allocate.trans AggregateCall.semantics args tail))⟩

theorem result_word (env : Env) (base guard id : Nat) (address : Address)
    (offset : Nat) (bytes : Nat → BitVec 8) :
    resultEnv env base guard id address offset bytes (base + 16) =
      some (number (ByteSlice.decode bytes offset 8)) := by
  simp [resultEnv, finishEnv, Control.Env.set]

theorem result_before (env : Env) (base guard id query : Nat) (address : Address)
    (offset : Nat) (bytes : Nat → BitVec 8) (earlier : query < base) (separate : base + 16 < guard) :
    resultEnv env base guard id address offset bytes query = env query := by
  simp (disch := omega) only [resultEnv, finishEnv, savedEnv, prepareEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.WordRead
