/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashInitReturn
import Compiler.ZigAir.MemoryStackFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Compiler.ZigAir.WyhashInit
open Memory AggregateAir Compiler.Extraction

def remaining (start : Nat) : Code := GeneratedWyhashInit.fn_init.body.dropBindings start

def completion (result : Except Fault Register) (after : State) : Control.Outcome Register Fault State :=
  match result with | .ok value => .returned value after | .error fault => .fault fault after

/-- The actual captured arithmetic and return sequence. Slot admission and
initialization are obtained from the allocator in the enclosing theorem. -/
theorem mix_return {caller state : State} {selfId left right : Nat}
    (stack : StackFrame caller state) (selfFrame : CellFrame state selfId)
    (leftFrame : CellFrame state left) (rightFrame : CellFrame state right)
    (selfType : selfFrame.cell.type = objectType) (leftType : leftFrame.cell.type = usize)
    (rightType : rightFrame.cell.type = usize) (seed : BitVec 64)
    (selfCells : selfFrame.cell.cells = partialCells)
    (leftCells : leftFrame.cell.cells = [(0, WyhashLocal.word (seed ^^^ WyhashLocal.secret0))])
    (rightCells : rightFrame.cell.cells = [(0, WyhashLocal.word WyhashLocal.secret1)])
    (leftFresh : caller.nextId ≤ left) (rightFresh : caller.nextId ≤ right) (selfFresh : caller.nextId ≤ selfId)
    (apart : left ≠ right) (selfLeft : selfId ≠ left) (selfRight : selfId ≠ right)
    (args : List Register) (env : Env)
    (seedReg : env 0 = some (number seed)) (selfReg : env 1 = some (objectPointer selfId))
    (firstReg : env 5 = some (lanePointer selfId 0))
    (leftReg : env 8 = some (slot left)) (rightReg : env 11 = some (slot right)) :
    ∃ after, (remaining 10).eval semantics args env state = .returned (result seed) after ∧ StackFrame caller after := by
  let a := seed ^^^ WyhashLocal.secret0
  let b := WyhashLocal.secret1
  let p := WyhashLocal.product a b
  let lo : Cells := [(0, WyhashLocal.word (WyhashLocal.lo p))]
  let hi : Cells := [(0, WyhashLocal.word (WyhashLocal.hi p))]
  have loValid : lo.valid usize = true := bitvec_cells_valid _
  have hiValid : hi.valid usize = true := bitvec_cells_valid _
  have writeA : Memory.store state (.pointer (.pointer true false usize) ⟨left, 0⟩)
      (WyhashLocal.word (WyhashLocal.lo p)) = .ok (leftFrame.install lo) := by
    simpa only [leftCells] using word_frame_store leftFrame (WyhashLocal.lo p) leftType
  let rightNext := leftFrame.after_other rightFrame lo apart.symm
  have writeB : Memory.store (leftFrame.install lo) (.pointer (.pointer true false usize) ⟨right, 0⟩)
      (WyhashLocal.word (WyhashLocal.hi p)) = .ok (rightNext.install hi) := by
    simpa only [show rightNext.cell.cells = [(0, WyhashLocal.word b)] from rightCells] using
      word_frame_store rightNext (WyhashLocal.hi p) rightType
  have firstStack := stack.install left leftFrame lo leftFresh (leftType ▸ loValid)
  have secondStack := firstStack.install right rightNext hi rightFresh (rightType ▸ hiValid)
  let selfNext := rightNext.after_other (leftFrame.after_other selfFrame lo selfLeft) hi selfRight
  have selfNextType : selfNext.cell.type = objectType := selfType
  have current : selfNext.install partialCells = rightNext.install hi := by
    have same := selfNext.install_current secondStack.valid
    rw [show selfNext.cell.cells = partialCells from selfCells] at same
    exact same
  let e1 := mixedEnv env a b
  let e2 := e1.set 30 (number (WyhashUpdate.seedState seed))
  have mixed := mix_prefix args env (remaining 23) state (leftFrame.install lo) (rightNext.install hi)
    left right a b apart leftReg rightReg (word_frame_read leftFrame a leftType leftCells)
    (word_frame_read rightFrame b rightType rightCells) writeA writeB
  have xored : (remaining 23).eval semantics args e1 (rightNext.install hi) =
      (remaining 24).eval semantics args e2 (rightNext.install hi) := by
    apply bind_ok
    · apply eval_scalar
      exact scalar_xor _ _ _ _ seed (WyhashLocal.mix a b)
        (scalar_local e1 0 seed (by simpa [e1, mixedEnv, Control.Env.set] using seedReg))
        (scalar_local e1 28 (WyhashLocal.mix a b) rfl)
    · exact number_typed _
  have returned := return_tail selfNext selfNextType (WyhashUpdate.seedState seed) args e2
    (by simpa [e2, e1, mixedEnv, Control.Env.set] using selfReg)
    (by simpa [e2, e1, mixedEnv, Control.Env.set] using firstReg) rfl
  rw [current] at returned
  exact ⟨_, mixed.trans (xored.trans returned),
    secondStack.install selfId selfNext _ selfFresh (selfNextType ▸ initialized_valid _)⟩

def fillCells (cells : Cells) (_ : Cells) : Except Fault (Unit × Cells) := .ok ((), cells)

theorem word_store_law (bits : BitVec 64) {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = usize) (empty : frame.cell.cells = []) :
    AggregateAir.store state (.pointer (.pointer true false usize) ⟨id, 0⟩) (number bits) =
      .ok (frame.install [(0, WyhashLocal.word bits)]) := by
  simpa only [empty] using word_frame_store frame bits typed

/-- Allocate both inlined mix operands. The two exhaustion branches retain the
reached state and are propagated through the same native control sequence. -/
theorem scratch_return {caller state : State} {selfId : Nat} (stack : StackFrame caller state)
    (cell : Allocation) (found : state.heap.lookup selfId = some cell)
    (typed : cell.type = objectType) (contents : cell.cells = partialCells) (writable : cell.writable = true)
    (fresh : caller.nextId ≤ selfId) (seed : BitVec 64) (args : List Register) (env : Env)
    (seedReg : env 0 = some (number seed)) (selfReg : env 1 = some (objectPointer selfId))
    (firstReg : env 5 = some (lanePointer selfId 0))
    (xorReg : env 6 = some (number (seed ^^^ WyhashLocal.secret0))) :
    ∃ resultValue after, (remaining 6).eval semantics args env state = completion resultValue after ∧
      StackFrame caller after ∧ (resultValue = .ok (result seed) ∨ resultValue = .error .outOfMemory) := by
  let a := seed ^^^ WyhashLocal.secret0
  let b := WyhashLocal.secret1
  let cellsA : Cells := [(0, WyhashLocal.word a)]
  let cellsB : Cells := [(0, WyhashLocal.word b)]
  have aValid : cellsA.valid usize = true := bitvec_cells_valid a
  have bValid : cellsB.valid usize = true := bitvec_cells_valid b
  obtain ⟨resA, mid, createA, stackA, outcomeA⟩ := StackFrame.create state usize ⟨8, 8⟩ (fillCells cellsA)
    () cellsA stack.valid rfl (by decide) rfl aValid
  have first := create_bindings usize ⟨8, 8⟩ cellsA (number a) (.local 6) 8 9 (remaining 8) args env state
    rfl (by decide) aValid
    (ref_local _ _ _ (by simpa [Control.Env.set] using xorReg) (number_valid a)) (word_store_law a)
  change (remaining 6).eval semantics args env state = _ at first
  change CellFrame.create state usize (fun _ => .ok ((), cellsA)) = _ at createA
  rw [createA] at first
  rcases outcomeA with failure | ⟨success, cellA, foundA, typeA, contentA, writableA⟩
  · rw [failure] at first
    exact ⟨.error .outOfMemory, mid, first, stack.trans stackA, Or.inr rfl⟩
  · rw [success] at first
    let e1 := (env.set 8 (slot state.nextId)).set 9 unit
    have selfMid := stackA.old_lookup selfId cell found
    have selfOld := (valid_lookup state selfId cell stack.valid found).1
    have leftOld := (valid_lookup mid state.nextId cellA stackA.valid foundA).1
    obtain ⟨resB, after, createB, stackB, outcomeB⟩ := StackFrame.create mid usize ⟨8, 8⟩ (fillCells cellsB)
      () cellsB stackA.valid rfl (by decide) rfl bValid
    have second := create_bindings usize ⟨8, 8⟩ cellsB (number b) (.constant (number b)) 11 12
      (remaining 10) args e1 mid rfl (by decide) bValid
      (by simp only [Ref.eval, number_valid, bind, Except.bind, ↓reduceIte]) (word_store_law b)
    change (remaining 8).eval semantics args e1 mid = _ at second
    change CellFrame.create mid usize (fun _ => .ok ((), cellsB)) = _ at createB
    rw [createB] at second
    rcases outcomeB with failure | ⟨success, cellB, foundB, typeB, contentB, writableB⟩
    · rw [failure] at second
      exact ⟨.error .outOfMemory, after, first.trans second, (stack.trans stackA).trans stackB, Or.inr rfl⟩
    · rw [success] at second
      let e2 := (e1.set 11 (slot mid.nextId)).set 12 unit
      let frameSelf := CellFrame.of_valid after selfId cell ⟨104, 8⟩ stackB.valid
        (stackB.old_lookup selfId cell selfMid) (typed ▸ object_layout) (by decide) writable
      let frameA := CellFrame.of_valid after state.nextId cellA ⟨8, 8⟩ stackB.valid
        (stackB.old_lookup state.nextId cellA foundA) (typeA ▸ rfl) (by decide) writableA
      let frameB := CellFrame.of_valid after mid.nextId cellB ⟨8, 8⟩ stackB.valid
        foundB (typeB ▸ rfl) (by decide) writableB
      obtain ⟨finished, ran, framed⟩ := mix_return ((stack.trans stackA).trans stackB) frameSelf frameA frameB
        typed typeA typeB seed contents contentA contentB stack.nextId (Nat.le_trans stack.nextId stackA.nextId)
        fresh (by omega) (by omega) (by omega) args e2
        (by simpa [e2, e1, Control.Env.set] using seedReg)
        (by simpa [e2, e1, Control.Env.set] using selfReg)
        (by simpa [e2, e1, Control.Env.set] using firstReg) (by rfl) (by rfl)
      exact ⟨.ok (result seed), finished, first.trans (second.trans ran), framed, Or.inl rfl⟩

def preparedEnv (env : Env) (id : Nat) (seed : BitVec 64) : Env :=
  ((env.set 4 (lanesPointer id)).set 5 (lanePointer id 0)).set 6 (number (seed ^^^ WyhashLocal.secret0))

theorem prepare_execution {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (cells : Cells) (seed : BitVec 64) (args : List Register) (env : Env)
    (seedReg : env 0 = some (number seed)) (selfReg : env 1 = some (objectPointer id)) :
    (remaining 3).eval semantics args env (frame.install cells) =
      (remaining 6).eval semantics args (preparedEnv env id seed) (frame.install cells) := by
  let e1 := env.set 4 (lanesPointer id)
  let e2 := e1.set 5 (lanePointer id 0)
  refine (bind_ok _ _ _ _ _ _ _ _ _ (field_step frame cells typed args env 1 selfReg) (by rfl)).trans ?_
  refine (bind_ok _ _ _ _ _ _ _ _ _ (element_step frame cells typed args e1 4 0 rfl) (by rfl)).trans ?_
  apply bind_ok
  · apply eval_scalar
    exact scalar_xor _ _ _ _ seed WyhashLocal.secret0
      (scalar_local e2 0 seed (by simpa [e2, e1, Control.Env.set] using seedReg)) (by rfl)
  · exact number_typed _

theorem partial_store_law {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (_ : frame.cell.cells = []) :
    AggregateAir.store state (.pointer (.pointer true false objectType) ⟨id, 0⟩) (.aggregate objectType partialCells) =
      .ok (frame.install partialCells) := by
  simpa only [typed] using store_root frame partialCells (typed ▸ object_aggregate) (typed ▸ partial_valid)

/-- Complete captured initializer for every seed and valid caller heap. No
successful native operation, chosen digest, poststate or spare allocation budget
is supplied by the caller. All three allocation failures remain explicit. -/
theorem body_verified (state : State) (seed : BitVec 64) (valid : state.valid = true) :
    ∃ resultValue after,
      GeneratedWyhashInit.fn_init.body.eval semantics [number seed] emptyEnv state = completion resultValue after ∧
      StackFrame state after ∧ (resultValue = .ok (result seed) ∨ resultValue = .error .outOfMemory) := by
  let args := [number seed]
  let e0 := emptyEnv.set 0 (number seed)
  have argument : GeneratedWyhashInit.fn_init.body.eval semantics args emptyEnv state =
      (remaining 1).eval semantics args e0 state :=
    bind_ok _ _ _ _ _ _ _ _ _ rfl (number_typed seed)
  obtain ⟨res, mid, created, stack, outcome⟩ := StackFrame.create state objectType ⟨104, 8⟩ (fillCells partialCells)
    () partialCells valid object_layout (by decide) rfl partial_valid
  have first := create_bindings objectType ⟨104, 8⟩ partialCells (.aggregate objectType partialCells)
    (.constant (.aggregate objectType partialCells)) 1 2 (remaining 3) args e0 state object_layout
    (by decide) partial_valid (ref_constant _ (by decide +kernel)) partial_store_law
  change (remaining 1).eval semantics args e0 state = _ at first
  change CellFrame.create state objectType (fun _ => .ok ((), partialCells)) = _ at created
  rw [created] at first
  rcases outcome with failure | ⟨success, cell, found, typed, contents, writable⟩
  · rw [failure] at first
    exact ⟨.error .outOfMemory, mid, argument.trans first, stack, Or.inr rfl⟩
  · rw [success] at first
    let e1 := (e0.set 1 (objectPointer state.nextId)).set 2 unit
    let e2 := preparedEnv e1 state.nextId seed
    let frame := CellFrame.of_valid mid state.nextId cell ⟨104, 8⟩ stack.valid found
      (typed ▸ object_layout) (by decide) writable
    have current : frame.install partialCells = mid := by
      simpa only [show frame.cell.cells = partialCells from contents] using frame.install_current stack.valid
    have prepare := prepare_execution frame typed partialCells seed args e1 rfl rfl
    rw [current] at prepare
    obtain ⟨resultValue, after, ran, framed, resultKind⟩ := scratch_return stack cell found typed contents writable
      (Nat.le_refl _) seed args e2 rfl rfl rfl rfl
    exact ⟨resultValue, after, argument.trans (first.trans (prepare.trans ran)), framed, resultKind⟩

theorem admitted_arguments (state : State) (seed : BitVec 64) (valid : state.valid = true) :
    (state.valid && decide ([number seed].length = GeneratedWyhashInit.fn_init.parameters.length) &&
      ([number seed].zip GeneratedWyhashInit.fn_init.parameters).all (fun (value, type) => value.hasType type)) = true := by
  change (state.valid && true && ((number seed).hasType (.scalar (.int false 64)) && true)) = true
  rw [valid, number_typed]; rfl

theorem run_framed (state : State) (seed : BitVec 64) (valid : state.valid = true) :
    ∃ value after, GeneratedWyhashInit.fn_init.run [number seed] state = (value, after) ∧
      StackFrame state after ∧ (value = .ok (result seed) ∨ value = .error .outOfMemory) := by
  obtain ⟨value, after, ran, stack, outcome⟩ := body_verified state seed valid
  have checked := admitted_arguments state seed valid
  rcases outcome with rfl | rfl
  · exact ⟨_, _, run_return _ _ _ _ _ checked ran (result_typed _), stack.cleaned, Or.inl rfl⟩
  · exact ⟨_, _, run_fault _ _ _ _ _ checked ran, stack.cleaned, Or.inr rfl⟩

/-- Call cleanup retires every initializer local while preserving both reached
allocator cursors, also on resource exhaustion. The returned sparse value is
independent of the retired local addresses. -/
theorem run_verified (state : State) (seed : BitVec 64) (valid : state.valid = true) :
    (GeneratedWyhashInit.fn_init.run [number seed] state).2.valid = true ∧
    (GeneratedWyhashInit.fn_init.run [number seed] state).2.heap = state.heap ∧
    ((GeneratedWyhashInit.fn_init.run [number seed] state).1 = .ok (result seed) ∨
      (GeneratedWyhashInit.fn_init.run [number seed] state).1 = .error .outOfMemory) := by
  obtain ⟨value, after, ran, stack, outcome⟩ := body_verified state seed valid
  have checked := admitted_arguments state seed valid
  rcases outcome with rfl | rfl
  · rw [run_return _ _ _ _ _ checked ran (result_typed _)]
    exact ⟨stack.cleanup_valid, stack.cleanup_heap, Or.inl rfl⟩
  · rw [run_fault _ _ _ _ _ checked ran]
    exact ⟨stack.cleanup_valid, stack.cleanup_heap, Or.inr rfl⟩

end Compiler.ZigAir.WyhashInit
