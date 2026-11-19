/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRoundInput

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Round
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- A prefix of the existing three model lanes records the writes that survive
OOM. At three lanes it is exactly `WyhashUpdate.round`. -/
def lanePrefix (input : WyhashUpdate.Input) (offset : Nat) : Nat → Cells → Except Fault Cells
  | 0, cells => .ok cells
  | count + 1, cells =>
    if inside : count < 3 then do
      let cells ← lanePrefix input offset count cells
      WyhashUpdate.lane input offset ⟨count, inside⟩ cells
    else .error .sourceBounds

theorem prefix_complete (input : WyhashUpdate.Input) (offset : Nat) (cells : Cells) :
    lanePrefix input offset 3 cells = WyhashUpdate.round input offset cells := by
  change ((WyhashUpdate.lane input offset 0 cells >>= WyhashUpdate.lane input offset 1) >>=
      WyhashUpdate.lane input offset 2) =
    (WyhashUpdate.lane input offset 0 cells >>= fun first =>
      WyhashUpdate.lane input offset 1 first >>= WyhashUpdate.lane input offset 2)
  simp only [bind_assoc]

def lanesAt (loop : Bool) (count : Nat) : Code :=
  (readSite loop 0 false).dropBindings (61 * count)

theorem generated_lane_chain : ∀ loop (index : Fin 3),
    lanesAt loop index.val = readSite loop index false ∧
    Lane.next loop index = lanesAt loop (index.val + 1) := by
  decide +kernel

/-- Compose actual lanes while retaining the exact completed prefix on OOM.
The same proof handles fill-buffer and external-input rounds. Original byte
admission is transported or rederived after each hasher store; saved parameter
loads survive because their allocation identities differ from the hasher. -/
theorem prefix_steps (loop : Bool) (count : Nat) (bounded : count ≤ 3)
    (frames : List (Frame Ty AggregateCall.Prim Ref))
    {state : State} {id : Nat} (frame : CellFrame state id) (valid : state.valid = true)
    (typed : frame.cell.type = objectType) (input : WyhashUpdate.Input) (offset total : Nat)
    (core : WyhashUpdate.Core frame.cell.cells total) (ready : input.Ready frame.cell.cells)
    (address : Address) (bytes : Nat → BitVec 8)
    (represented : ByteSlice.Represents (input.cells frame.cell.cells) input.view bytes)
    (inside : offset + 48 ≤ input.view.length)
    (admitted : InputAdmitted state id input offset address bytes)
    (inputSlot selfSlot : Nat) (inputApart : inputSlot ≠ id) (selfApart : selfSlot ≠ id)
    (inputRead : Memory.load state (slot false (WordRead.arrayPointer 48) inputSlot) =
      .ok (.pointer (WordRead.arrayPointer 48) address))
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (args : List Register) (env : Env)
    (foundInput : env (Lane.inputReg loop) = some (.value (slot false (WordRead.arrayPointer 48) inputSlot)))
    (foundSelf : env (Lane.selfReg loop) = some (.value (slot false (.pointer true false objectType) selfSlot))) :
    ∃ after,
      (∃ completed cells, completed < count ∧ lanePrefix input offset completed frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ StackFrame (frame.install cells) after ∧ Steps AggregateCall.semantics args
          (.suspended ⟨lanesAt loop 0, env, state, frames⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ cells afterEnv, lanePrefix input offset count frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ input.Ready cells ∧
        (∀ query, query < 16 ∨ 40 ≤ query → cells.lookup query = frame.cell.cells.lookup query) ∧
        StackFrame (frame.install cells) after ∧ Steps AggregateCall.semantics args
          (.suspended ⟨lanesAt loop 0, env, state, frames⟩)
          (.suspended ⟨lanesAt loop count, afterEnv, after, frames⟩) ∧
        ∀ query < readBase loop 0 false, afterEnv query = env query := by
  induction count with
  | zero =>
    refine ⟨state, Or.inr ⟨frame.cell.cells, env, rfl, core, ready, ?_, ?_, .refl _, ?_⟩⟩
    · intro query outside; rfl
    · rw [frame.install_current valid]
      exact StackFrame.refl state valid
    · intro query earlier; rfl
  | succ count ih =>
    have laneBound : count < 3 := by omega
    let index : Fin 3 := ⟨count, laneBound⟩
    obtain ⟨middle, ⟨completed, cells, earlier, ran, failedCore, stack, path⟩ |
        ⟨cells, middleEnv, ran, coreNext, readyNext, retained, stack, path, before⟩⟩ := ih (by omega)
    · exact ⟨middle, Or.inl ⟨completed, cells, by omega, ran, failedCore, stack, path⟩⟩
    · let current := (frame.replaced cells).extend stack
      have representation := represented_frame input frame.cell.cells cells bytes represented retained
      have admission := InputAdmitted.extend stack input offset address bytes
        (InputAdmitted.install frame cells input offset address bytes admitted)
      have reads := InputAdmitted.reads current stack.valid typed input offset address bytes admission representation inside
      have inputLoaded : Memory.load middle (slot false (WordRead.arrayPointer 48) inputSlot) =
          .ok (.pointer (WordRead.arrayPointer 48) address) :=
        stack.old_load false false (WordRead.arrayPointer 48) ⟨inputSlot, 0⟩ _
          ((frame.load_outside cells ⟨inputSlot, 0⟩ inputApart false false _).trans inputRead)
      have selfLoaded : Memory.load middle (slot false (.pointer true false objectType) selfSlot) =
          .ok (selfPointer id) :=
        stack.old_load false false (.pointer true false objectType) ⟨selfSlot, 0⟩ _
          ((frame.load_outside cells ⟨selfSlot, 0⟩ selfApart false false _).trans selfRead)
      have bounds := Lane.register_bounds loop 0
      have hInput := (before _ bounds.2.1).trans foundInput
      have hSelf := (before _ bounds.1).trans foundSelf
      obtain ⟨after, ⟨failedStack, failed⟩ |
          ⟨nextCells, nextEnv, laneRan, nextCore, nextReady, nextRetained, nextStack, nextPath, nextBefore⟩⟩ :=
        Lane.model_steps loop index frames current stack.valid typed input offset total coreNext readyNext
          address bytes representation inside reads inputSlot selfSlot inputLoaded selfLoaded args middleEnv hInput hSelf
      · rw [← (generated_lane_chain loop index).1] at failed
        exact ⟨after, Or.inl ⟨count, cells, by omega, ran, coreNext, stack.trans failedStack,
          path.trans AggregateCall.semantics args failed⟩⟩
      · have initialized : nextCells.valid frame.cell.type = true := by rw [typed]; exact nextCore.valid
        have installed := stack.install_old (frame.replaced cells) nextCells initialized
        rw [frame.replaced_install] at installed
        have nextModel : lanePrefix input offset (count + 1) frame.cell.cells = .ok nextCells := by
          simp only [lanePrefix, dif_pos laneBound, ran, bind, Except.bind]
          exact laneRan
        rw [← (generated_lane_chain loop index).1, (generated_lane_chain loop index).2] at nextPath
        refine ⟨after, Or.inr ⟨nextCells, nextEnv, nextModel, nextCore, nextReady, ?_,
          installed.trans nextStack, path.trans AggregateCall.semantics args nextPath, ?_⟩⟩
        · intro query outside
          exact (nextRetained query outside).trans (retained query outside)
        · intro query earlier
          apply (nextBefore query ?_).trans (before query earlier)
          dsimp [readBase] at earlier ⊢
          omega

end Compiler.ZigAir.WyhashUpdateAir.Round
