/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRound
import Compiler.ZigAir.WyhashMixAllocation
import Compiler.ZigAir.WyhashInitReturn

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Lane
open Memory AggregateAir Compiler.Extraction Control.Machine
abbrev Code := WordRead.Code

def prepare (base selfReg aReg bReg : Nat) (index : Fin 3) (next : Code) : Code :=
  .bind base (.pointer true false objectType) (.primitive (.load (.local selfReg))) $
  .bind (base + 1) (.pointer true false (.array 3 usize)) (.primitive (.fieldPointer (.local base) 16)) $
  .bind (base + 2) (.pointer true false usize) (.primitive (.arrayElementPointer (.local (base + 1))
    (.constant (.value (.scalar (.int false 64 index.val)))))) $
  .bind (base + 3) usize (.primitive (.memory (.scalar (.bitXor (.local aReg)
    (.constant (.int false 64 (WyhashUpdate.secret index).toNat)))))) $
  .bind (base + 4) (.pointer true false objectType) (.primitive (.load (.local selfReg))) $
  .bind (base + 5) (.pointer true false (.array 3 usize)) (.primitive (.fieldPointer (.local (base + 4)) 16)) $
  .bind (base + 6) (.pointer true false usize) (.primitive (.arrayElementPointer (.local (base + 5))
    (.constant (.value (.scalar (.int false 64 index.val)))))) $
  .bind (base + 7) usize (.primitive (.load (.local (base + 6)))) $
  .bind (base + 8) usize (.primitive (.memory (.scalar (.bitXor (.local bReg) (.local (base + 7)))))) next

def prepareEnv (env : Env) (base id : Nat) (index : Fin 3) (a b old : BitVec 64) : Env :=
  let env := env.set base (WyhashInit.objectPointer id)
  let env := env.set (base + 1) (WyhashInit.lanesPointer id)
  let env := env.set (base + 2) (WyhashInit.lanePointer id index.val)
  let env := env.set (base + 3) (number (a ^^^ WyhashUpdate.secret index))
  let env := env.set (base + 4) (WyhashInit.objectPointer id)
  let env := env.set (base + 5) (WyhashInit.lanesPointer id)
  let env := env.set (base + 6) (WyhashInit.lanePointer id index.val)
  let env := env.set (base + 7) (number old)
  env.set (base + 8) (number (b ^^^ old))

/-- Select the admitted lane and derive both mix operands by the captured
native loads, array-index checks and XOR instructions. -/
theorem prepare_steps (base selfReg aReg bReg savedId : Nat)
    (selfBefore : selfReg < base) (aBefore : aReg < base) (bBefore : bReg < base)
    (next : Code) (frames : List (Frame Ty AggregateCall.Prim Ref))
    {state : State} {id : Nat} (frame : CellFrame state id) (valid : state.valid = true)
    (typed : frame.cell.type = objectType) (index : Fin 3) (a b old : BitVec 64)
    (lane : frame.cell.cells.lookup (16 + index.val * 8) = some (WyhashLocal.word old))
    (selfRead : Memory.load state (slot false (.pointer true false objectType) savedId) = .ok (selfPointer id))
    (args : List Register) (env : Env)
    (foundSelf : env selfReg = some (.value (slot false (.pointer true false objectType) savedId)))
    (foundA : env aReg = some (number a)) (foundB : env bReg = some (number b)) :
    Steps AggregateCall.semantics args
      (.suspended ⟨prepare base selfReg aReg bReg index next, env, state, frames⟩)
      (.suspended ⟨next, prepareEnv env base id index a b old, state, frames⟩) := by
  let e0 := env.set base (WyhashInit.objectPointer id)
  let e1 := e0.set (base + 1) (WyhashInit.lanesPointer id)
  let e2 := e1.set (base + 2) (WyhashInit.lanePointer id index.val)
  let e3 := e2.set (base + 3) (number (a ^^^ WyhashUpdate.secret index))
  let e4 := e3.set (base + 4) (WyhashInit.objectPointer id)
  let e5 := e4.set (base + 5) (WyhashInit.lanesPointer id)
  let e6 := e5.set (base + 6) (WyhashInit.lanePointer id index.val)
  let e7 := e6.set (base + 7) (number old)
  have current := frame.install_current valid
  have p0 := eval_load (.local selfReg) args env state _ _
    (value_local _ _ _ foundSelf rfl) (congrArg (Except.map Register.value) selfRead)
  have p1 := WyhashInit.field_step frame frame.cell.cells typed args e0 base
    (by simp [e0, Control.Env.set])
  rw [current] at p1
  have p2 := WyhashInit.element_step frame frame.cell.cells typed args e1 (base + 1) index
    (by simp [e1, Control.Env.set])
  rw [current] at p2
  have p3 : (Prim.memory (.scalar (.bitXor (.local aReg)
      (.constant (.int false 64 (WyhashUpdate.secret index).toNat))))).eval args e2 state =
        (.ok (number (a ^^^ WyhashUpdate.secret index)), state) := by
    apply eval_scalar
    apply scalar_xor _ _ _ _ a (WyhashUpdate.secret index)
    · exact scalar_local e2 aReg a (by
        simpa [e2, e1, e0, Control.Env.set, show aReg ≠ base by omega,
          show aReg ≠ base + 1 by omega, show aReg ≠ base + 2 by omega] using foundA)
    · simp only [Scalar.Ref.eval, scalar_bitvec_valid, ↓reduceIte]
  have p4 := eval_load (.local selfReg) args e3 state (slot false (.pointer true false objectType) savedId) _
    (value_local _ _ _ (by
      simpa [e3, e2, e1, e0, Control.Env.set, show selfReg ≠ base by omega,
        show selfReg ≠ base + 1 by omega, show selfReg ≠ base + 2 by omega,
        show selfReg ≠ base + 3 by omega] using foundSelf) rfl)
    (congrArg (Except.map Register.value) selfRead)
  have p5 := WyhashInit.field_step frame frame.cell.cells typed args e4 (base + 4)
    (by simp [e4, Control.Env.set])
  rw [current] at p5
  have p6 := WyhashInit.element_step frame frame.cell.cells typed args e5 (base + 5) index
    (by simp [e5, Control.Env.set])
  rw [current] at p6
  have p7 := WyhashInit.lane_load_step frame frame.cell.cells typed args e6 (base + 6) index old
    (by simp [e6, Control.Env.set]) lane
  rw [current] at p7
  have p8 : (Prim.memory (.scalar (.bitXor (.local bReg) (.local (base + 7))))).eval args e7 state =
      (.ok (number (b ^^^ old)), state) := by
    apply eval_scalar
    apply scalar_xor _ _ _ _ b old
    · apply scalar_local e7 bReg b
      simpa (disch := omega) only [e7, e6, e5, e4, e3, e2, e1, e0, Control.Env.set, if_neg] using foundB
    · exact scalar_local e7 (base + 7) old (by simp [e7, Control.Env.set])
  exact AggregateCall.primitive_steps args p0 (by rfl) <|
    AggregateCall.primitive_steps args p1 (by rfl) <|
    AggregateCall.primitive_steps args p2 (by rfl) <|
    AggregateCall.primitive_steps args p3 (number_typed _) <|
    AggregateCall.primitive_steps args p4 (by rfl) <|
    AggregateCall.primitive_steps args p5 (by rfl) <|
    AggregateCall.primitive_steps args p6 (by rfl) <|
    AggregateCall.primitive_steps args p7 (number_typed _) <|
    AggregateCall.primitive_steps args p8 (number_typed _) (.refl _)

def finish (base : Nat) (next : Code) : Code :=
  .bind (base + 32) (.scalar .unit)
    (.primitive (.store (.local (base + 2)) (.local (base + 30)))) next

def body (base selfReg aReg bReg : Nat) (index : Fin 3) (next : Code) : Code :=
  prepare base selfReg aReg bReg index
    (WyhashMixAllocation.code (base + 10) (base + 3) (base + 8) (finish base next))

def updatedCells (cells : Cells) (index : Fin 3) (a b old : BitVec 64) : Cells :=
  cells.set (16 + index.val * 8)
    (WyhashLocal.word (WyhashLocal.mix (a ^^^ WyhashUpdate.secret index) (b ^^^ old)))

theorem updated_valid (cells : Cells) (index : Fin 3) (a b old : BitVec 64)
    (valid : cells.valid objectType = true) : (updatedCells cells index a b old).valid objectType = true := by
  apply WyhashUpdate.store_valid cells _ _ valid
  have := index.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

def bodyEnv (env : Env) (base id : Nat) (index : Fin 3) (a b old : BitVec 64) (left right : Nat) : Env :=
  (WyhashMixAllocation.resultEnv (prepareEnv env base id index a b old) (base + 10) left right
    (a ^^^ WyhashUpdate.secret index) (b ^^^ old)).set (base + 32) WyhashInit.unit

theorem body_before (env : Env) (base id : Nat) (index : Fin 3) (a b old : BitVec 64)
    (left right query : Nat) (earlier : query < base) :
    bodyEnv env base id index a b old left right query = env query := by
  simp only [bodyEnv, Control.Env.set, if_neg (by omega : query ≠ base + 32)]
  rw [WyhashMixAllocation.result_before _ (base + 10) left right query _ _ (by omega)]
  simp (disch := omega) only [prepareEnv, Control.Env.set, if_neg]

/-- Preserve the caller's actual hasher update while framing the scratch slots.
An OOM precedes this lane's store; success changes exactly the selected word. -/
theorem body_steps (base selfReg aReg bReg savedId : Nat)
    (selfBefore : selfReg < base) (aBefore : aReg < base) (bBefore : bReg < base)
    (next : Code) (frames : List (Frame Ty AggregateCall.Prim Ref))
    {state : State} {id : Nat} (frame : CellFrame state id) (valid : state.valid = true)
    (typed : frame.cell.type = objectType) (cellsValid : frame.cell.cells.valid objectType = true)
    (index : Fin 3) (a b old : BitVec 64)
    (lane : frame.cell.cells.lookup (16 + index.val * 8) = some (WyhashLocal.word old))
    (selfRead : Memory.load state (slot false (.pointer true false objectType) savedId) = .ok (selfPointer id))
    (args : List Register) (env : Env)
    (foundSelf : env selfReg = some (.value (slot false (.pointer true false objectType) savedId)))
    (foundA : env aReg = some (number a)) (foundB : env bReg = some (number b)) :
    ∃ after,
      (StackFrame state after ∧ Steps AggregateCall.semantics args
        (.suspended ⟨body base selfReg aReg bReg index next, env, state, frames⟩)
        (.finished (.fault .outOfMemory after))) ∨
      (StackFrame (frame.install (updatedCells frame.cell.cells index a b old)) after ∧
       Steps AggregateCall.semantics args
        (.suspended ⟨body base selfReg aReg bReg index next, env, state, frames⟩)
        (.suspended ⟨next, bodyEnv env base id index a b old state.nextId (state.nextId + 1), after, frames⟩)) := by
  let prepared := prepareEnv env base id index a b old
  have head := prepare_steps base selfReg aReg bReg savedId selfBefore aBefore bBefore
    (WyhashMixAllocation.code (base + 10) (base + 3) (base + 8) (finish base next)) frames
    frame valid typed index a b old lane selfRead args env foundSelf foundA foundB
  obtain ⟨middle, stack, failed | mixed⟩ := WyhashMixAllocation.steps (base + 10) (base + 3) (base + 8)
    (by omega) (by omega) (finish base next) frames state valid (a ^^^ WyhashUpdate.secret index) (b ^^^ old)
    args prepared (by simp [prepared, prepareEnv, Control.Env.set]) (by simp [prepared, prepareEnv, Control.Env.set])
  · exact ⟨middle, Or.inl ⟨stack, head.trans AggregateCall.semantics args failed⟩⟩
  · let current := frame.extend stack
    let mixedEnv := WyhashMixAllocation.resultEnv prepared (base + 10) state.nextId (state.nextId + 1)
      (a ^^^ WyhashUpdate.secret index) (b ^^^ old)
    have pointer : mixedEnv (base + 2) = some (WyhashInit.lanePointer id index.val) := by
      exact (WyhashMixAllocation.result_before prepared (base + 10) state.nextId (state.nextId + 1)
        (base + 2) (a ^^^ WyhashUpdate.secret index) (b ^^^ old) (by omega)).trans
        (by simp [prepared, prepareEnv, Control.Env.set])
    have result : mixedEnv (base + 30) =
        some (number (WyhashLocal.mix (a ^^^ WyhashUpdate.secret index) (b ^^^ old))) := by
      simpa only [Nat.add_assoc] using WyhashMixAllocation.result_word prepared (base + 10)
        state.nextId (state.nextId + 1) (a ^^^ WyhashUpdate.secret index) (b ^^^ old)
    have written := WyhashInit.lane_store_step current current.cell.cells typed args mixedEnv
      (base + 2) (base + 30) index (WyhashLocal.mix (a ^^^ WyhashUpdate.secret index) (b ^^^ old)) pointer result
    rw [current.install_current stack.valid] at written
    have initialized : (updatedCells frame.cell.cells index a b old).valid frame.cell.type = true := by
      rw [typed]
      exact updated_valid frame.cell.cells index a b old cellsValid
    have tail : Steps AggregateCall.semantics args
        (.suspended ⟨finish base next, mixedEnv, middle, frames⟩)
        (.suspended ⟨next, bodyEnv env base id index a b old state.nextId (state.nextId + 1),
          current.install (updatedCells frame.cell.cells index a b old), frames⟩) :=
      AggregateCall.primitive_steps args written (by rfl) (.refl _)
    exact ⟨_, Or.inr ⟨stack.install_old frame _ initialized,
      head.trans AggregateCall.semantics args (mixed.trans AggregateCall.semantics args tail)⟩⟩

def base (loop : Bool) (index : Fin 3) : Nat := Round.readBase loop index false + 42
def selfReg (loop : Bool) : Nat := if loop then 347 else 90
def inputReg (loop : Bool) : Nat := if loop then 350 else 93
def site (loop : Bool) (index : Fin 3) : Code := (Round.readSite loop index false).dropBindings 34
def next (loop : Bool) (index : Fin 3) : Code := (Round.readSite loop index false).dropBindings 61

theorem generated_second : ∀ loop index,
    (Round.readSite loop index false).dropBindings 17 = Round.readSite loop index true := by
  decide +kernel

theorem generated_body : ∀ loop index,
    (Round.readSite loop index true).dropBindings 17 = site loop index ∧
    site loop index = body (base loop index) (selfReg loop)
      (Round.readBase loop index false + 16) (Round.readBase loop index true + 16) index (next loop index) := by
  decide +kernel

theorem register_bounds : ∀ loop index,
    selfReg loop < Round.readBase loop index false ∧
    inputReg loop < Round.readBase loop index false ∧
    Round.readBase loop index false + 16 < Round.readBase loop index true ∧
    Round.readBase loop index true + 16 < base loop index := by
  decide +kernel

def word (bytes : Nat → BitVec 8) (index : Fin 3) (second : Bool) : BitVec 64 :=
  ByteSlice.decode bytes (Round.readOffset index second) 8

/-- Complete captured lane execution, for either round and every valid native
input. All four allocations and both original-byte reads are executed. The
success frame retains exactly the model lane update; OOM retains earlier lanes
and allocation history without inventing rollback. -/
theorem steps (loop : Bool) (index : Fin 3) (frames : List (Frame Ty AggregateCall.Prim Ref))
    {state : State} {id : Nat} (frame : CellFrame state id) (valid : state.valid = true)
    (typed : frame.cell.type = objectType) (cellsValid : frame.cell.cells.valid objectType = true)
    (address : Address) (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address 48 bytes)
    (old : BitVec 64) (lane : frame.cell.cells.lookup (16 + index.val * 8) = some (WyhashLocal.word old))
    (inputSlot selfSlot : Nat)
    (inputRead : Memory.load state (slot false (WordRead.arrayPointer 48) inputSlot) =
      .ok (.pointer (WordRead.arrayPointer 48) address))
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (args : List Register) (env : Env)
    (foundInput : env (inputReg loop) = some (.value (slot false (WordRead.arrayPointer 48) inputSlot)))
    (foundSelf : env (selfReg loop) = some (.value (slot false (.pointer true false objectType) selfSlot))) :
    ∃ after,
      (StackFrame state after ∧ Steps AggregateCall.semantics args
        (.suspended ⟨Round.readSite loop index false, env, state, frames⟩)
        (.finished (.fault .outOfMemory after))) ∨
      ∃ afterEnv, StackFrame (frame.install (updatedCells frame.cell.cells index
          (word bytes index false) (word bytes index true) old)) after ∧
        Steps AggregateCall.semantics args
          (.suspended ⟨Round.readSite loop index false, env, state, frames⟩)
          (.suspended ⟨next loop index, afterEnv, after, frames⟩) ∧
        ∀ query < Round.readBase loop index false, afterEnv query = env query := by
  obtain ⟨selfBefore, inputBefore, secondAfter, bodyAfter⟩ := register_bounds loop index
  have guardA := (Round.read_bounds loop index false).1
  have guardB := (Round.read_bounds loop index true).1
  obtain ⟨firstState, firstStack, failed | first⟩ := Round.read_steps loop index false frames state valid
    address bytes reads inputSlot inputRead args env foundInput
  · exact ⟨firstState, Or.inl ⟨firstStack, failed⟩⟩
  · let eA := WordRead.resultEnv env (Round.readBase loop index false) (Round.readGuard loop index false)
      state.nextId address (Round.readOffset index false) bytes
    have beforeA (query : Nat) (earlier : query < Round.readBase loop index false) : eA query = env query :=
      WordRead.result_before env _ _ _ query address _ bytes earlier guardA
    have inputA : eA (inputReg loop) = some (.value (slot false (WordRead.arrayPointer 48) inputSlot)) :=
      (beforeA _ inputBefore).trans foundInput
    obtain ⟨secondState, secondStack, failed | second⟩ := Round.read_steps loop index true frames firstState firstStack.valid
      address bytes (reads.extend firstStack address 48 bytes) inputSlot
      (firstStack.old_load false false (WordRead.arrayPointer 48) ⟨inputSlot, 0⟩ _ inputRead) args eA inputA
    · rw [generated_second loop index] at first
      exact ⟨secondState, Or.inl ⟨firstStack.trans secondStack,
        first.trans AggregateCall.semantics args failed⟩⟩
    · let eB := WordRead.resultEnv eA (Round.readBase loop index true) (Round.readGuard loop index true)
        firstState.nextId address (Round.readOffset index true) bytes
      have beforeB (query : Nat) (earlier : query < Round.readBase loop index false) : eB query = env query :=
        (WordRead.result_before eA _ _ _ query address _ bytes (by omega) guardB).trans (beforeA query earlier)
      let stack := firstStack.trans secondStack
      let current := frame.extend stack
      have aReg : eB (Round.readBase loop index false + 16) = some (number (word bytes index false)) :=
        (WordRead.result_before eA _ _ _ _ address _ bytes secondAfter guardB).trans
          (WordRead.result_word env _ _ _ address _ bytes)
      have bReg : eB (Round.readBase loop index true + 16) = some (number (word bytes index true)) :=
        WordRead.result_word eA _ _ _ address _ bytes
      have selfRegFound : eB (selfReg loop) = some (.value (slot false (.pointer true false objectType) selfSlot)) :=
        (beforeB _ selfBefore).trans foundSelf
      rw [generated_second loop index] at first
      rw [(generated_body loop index).1, (generated_body loop index).2] at second
      have head := first.trans AggregateCall.semantics args second
      obtain ⟨after, ⟨failedStack, failed⟩ | ⟨successStack, success⟩⟩ := body_steps (base loop index) (selfReg loop)
        (Round.readBase loop index false + 16) (Round.readBase loop index true + 16) selfSlot
        (by omega) (by omega) bodyAfter (next loop index) frames current stack.valid typed cellsValid index
        (word bytes index false) (word bytes index true) old lane
        (stack.old_load false false (.pointer true false objectType) ⟨selfSlot, 0⟩ _ selfRead)
        args eB selfRegFound aReg bReg
      · exact ⟨after, Or.inl ⟨stack.trans failedStack, head.trans AggregateCall.semantics args failed⟩⟩
      · have initialized : (updatedCells frame.cell.cells index (word bytes index false)
            (word bytes index true) old).valid frame.cell.type = true := by
          rw [typed]
          exact updated_valid _ _ _ _ _ cellsValid
        refine ⟨after, Or.inr ⟨_, (stack.install_old frame _ initialized).trans successStack,
          head.trans AggregateCall.semantics args success, ?_⟩⟩
        intro query earlier
        exact (body_before eB (base loop index) id index (word bytes index false) (word bytes index true)
          old secondState.nextId (secondState.nextId + 1) query (by omega)).trans (beforeB query earlier)

end Compiler.ZigAir.WyhashUpdateAir.Lane
