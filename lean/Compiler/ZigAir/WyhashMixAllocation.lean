/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashInit
import Compiler.ZigAir.AggregateExecutionProofs

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashMixAllocation
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- The writable scratch region and initialized word come from the actual
allocation/store, not merely a subsequent successful read. -/
theorem saved_word (state after : State) (bits : BitVec 64) (valid : after.valid = true)
    (ran : SavedValue.save state (WyhashLocal.word bits) = (.ok (), after)) :
    ∃ frame : CellFrame after state.nextId,
      frame.cell.type = usize ∧ frame.cell.cells = [(0, WyhashLocal.word bits)] := by
  cases allocated : Memory.allocate state usize with
  | error fault => simp only [SavedValue.save, WyhashLocal.word_type, allocated] at ran; cases ran
  | ok pair =>
    obtain ⟨pointer, middle⟩ := pair
    obtain ⟨frame, typed, empty, shaped⟩ := CellFrame.allocated state usize ⟨8, 8⟩ pointer middle
      rfl (by decide) allocated
    have pointerEq := (allocate_pointer state usize pointer middle allocated).1
    have written : Memory.store middle pointer (WyhashLocal.word bits) =
        .ok (frame.install [(0, WyhashLocal.word bits)]) := by
      rw [pointerEq]
      simpa only [empty] using WyhashInit.word_frame_store frame bits typed
    simp only [SavedValue.save, WyhashLocal.word_type, allocated, written, Prod.mk.injEq, true_and] at ran
    subst after
    obtain ⟨_, _, _, _, _, _, _, _, writable⟩ := access_success_region _ _ _ _ _ frame.admitted
    let current := CellFrame.of_valid (frame.install [(0, WyhashLocal.word bits)]) state.nextId
      { frame.cell with cells := [(0, WyhashLocal.word bits)] } ⟨8, 8⟩ valid
      (frame.lookup _) (typed ▸ rfl) (by decide) (writable rfl)
    exact ⟨current, typed, rfl⟩

abbrev Code := Control.Code Ty AggregateCall.Prim Ref true

def code (base aReg bReg : Nat) (next : Code) : Code :=
  .bind base (.pointer true false usize) (.primitive (.memory (.alloc usize))) $
  .bind (base + 1) (.scalar .unit) (.primitive (.store (.local base) (.local aReg))) $
  .bind (base + 3) (.pointer true false usize) (.primitive (.memory (.alloc usize))) $
  .bind (base + 4) (.scalar .unit) (.primitive (.store (.local (base + 3)) (.local bReg))) $
  WyhashInit.mixCode AggregateCall.Prim.primitive base next

def allocatedEnv (env : Env) (base left right : Nat) : Env :=
  let env := (env.set base (WyhashInit.slot left)).set (base + 1) WyhashInit.unit
  (env.set (base + 3) (WyhashInit.slot right)).set (base + 4) WyhashInit.unit

def resultEnv (env : Env) (base left right : Nat) (a b : BitVec 64) : Env :=
  WyhashInit.mixedEnvAt base (allocatedEnv env base left right) a b

theorem result_word (env : Env) (base left right : Nat) (a b : BitVec 64) :
    resultEnv env base left right a b (base + 20) = some (number (WyhashLocal.mix a b)) := by
  simp only [resultEnv, WyhashInit.mixedEnvAt, Control.Env.set, ↓reduceIte]

theorem result_before (env : Env) (base left right query : Nat) (a b : BitVec 64) (earlier : query < base) :
    resultEnv env base left right a b query = env query := by
  simp (disch := omega) only [resultEnv, WyhashInit.mixedEnvAt, allocatedEnv, Control.Env.set, if_neg]

/-- Execute both captured scratch allocations and the shared mix. The result
preserves the caller heap on either allocation outcome; completed local effects
remain until the enclosing invocation cleans up. -/
theorem steps (base aReg bReg : Nat) (aBefore : aReg < base) (bBefore : bReg < base)
    (next : Code) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (state : State) (valid : state.valid = true) (a b : BitVec 64)
    (args : List Register) (env : Env)
    (foundA : env aReg = some (number a)) (foundB : env bReg = some (number b)) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics args (.suspended ⟨code base aReg bReg next, env, state, frames⟩)
          (.finished (.fault .outOfMemory after)) ∨
       Steps AggregateCall.semantics args (.suspended ⟨code base aReg bReg next, env, state, frames⟩)
          (.suspended ⟨next, resultEnv env base state.nextId (state.nextId + 1) a b, after, frames⟩)) := by
  let secondCode := (code base aReg bReg next).dropBindings 2
  have first := AggregateCall.save_steps (WyhashLocal.word a) (.local aReg) base (base + 1)
    secondCode frames args env state
    (ref_local _ _ _ (by simpa [Control.Env.set, show aReg ≠ base by omega] using foundA) (number_valid a))
  obtain ⟨firstResult, middle, firstRun, firstStack, failed | ⟨success, _, _⟩⟩ :=
    SavedValue.verified state (WyhashLocal.word a) ⟨8, 8⟩ valid (WyhashLocal.word_valid a) rfl (by decide)
  · rw [failed] at firstRun
    rw [firstRun] at first
    exact ⟨middle, firstStack, Or.inl first⟩
  · rw [success] at firstRun
    rw [firstRun] at first
    have cursors := SavedValue.success_cursors state middle (WyhashLocal.word a) firstRun
    let eA := (env.set base (WyhashInit.slot state.nextId)).set (base + 1) WyhashInit.unit
    have second := AggregateCall.save_steps (WyhashLocal.word b) (.local bReg) (base + 3) (base + 4)
      (WyhashInit.mixCode AggregateCall.Prim.primitive base next) frames args eA middle
      (ref_local _ _ _ (by simpa [eA, Control.Env.set, show bReg ≠ base by omega,
        show bReg ≠ base + 1 by omega, show bReg ≠ base + 3 by omega] using foundB) (number_valid b))
    obtain ⟨secondResult, reached, secondRun, secondStack, failed | ⟨success, _, _⟩⟩ :=
      SavedValue.verified middle (WyhashLocal.word b) ⟨8, 8⟩ firstStack.valid (WyhashLocal.word_valid b) rfl (by decide)
    · rw [failed] at secondRun
      rw [secondRun] at second
      exact ⟨reached, firstStack.trans secondStack, Or.inl (first.trans AggregateCall.semantics args second)⟩
    · rw [success] at secondRun
      rw [secondRun] at second
      obtain ⟨originalA, typeA, cellsA⟩ := saved_word state middle a firstStack.valid firstRun
      obtain ⟨frameB, typeB, cellsB⟩ := saved_word middle reached b secondStack.valid secondRun
      let frameA := originalA.extend secondStack
      let lo : Cells := [(0, WyhashLocal.word (WyhashLocal.lo (WyhashLocal.product a b)))]
      let hi : Cells := [(0, WyhashLocal.word (WyhashLocal.hi (WyhashLocal.product a b)))]
      have apart : state.nextId ≠ middle.nextId := by omega
      let nextB := frameA.after_other frameB lo apart.symm
      have writeA : Memory.store reached (.pointer (.pointer true false usize) ⟨state.nextId, 0⟩)
          (WyhashLocal.word (WyhashLocal.lo (WyhashLocal.product a b))) = .ok (frameA.install lo) := by
        simpa only [show frameA.cell.cells = [(0, WyhashLocal.word a)] from cellsA] using
          WyhashInit.word_frame_store frameA (WyhashLocal.lo (WyhashLocal.product a b)) typeA
      have writeB : Memory.store (frameA.install lo) (.pointer (.pointer true false usize) ⟨middle.nextId, 0⟩)
          (WyhashLocal.word (WyhashLocal.hi (WyhashLocal.product a b))) = .ok (nextB.install hi) := by
        simpa only [show nextB.cell.cells = [(0, WyhashLocal.word b)] from cellsB] using
          WyhashInit.word_frame_store nextB (WyhashLocal.hi (WyhashLocal.product a b)) typeB
      have framedA := (firstStack.trans secondStack).install state.nextId frameA lo (Nat.le_refl _)
        (typeA ▸ bitvec_cells_valid _)
      have framedB := framedA.install middle.nextId nextB hi firstStack.nextId (typeB ▸ bitvec_cells_valid _)
      let eB := allocatedEnv env base state.nextId middle.nextId
      have mixed := WyhashInit.mix_steps AggregateCall.semantics AggregateCall.Prim.primitive rfl
        (by intros; rfl) base args eB next frames reached (frameA.install lo) (nextB.install hi)
        state.nextId middle.nextId a b apart
        (by simp [eB, allocatedEnv, Control.Env.set]) (by simp [eB, allocatedEnv, Control.Env.set])
        (WyhashInit.word_frame_read frameA a typeA cellsA) (WyhashInit.word_frame_read frameB b typeB cellsB)
        writeA writeB
      have path := first.trans AggregateCall.semantics args (second.trans AggregateCall.semantics args mixed)
      exact ⟨nextB.install hi, framedB, Or.inr (by
        simpa only [resultEnv, eB, cursors.1] using path)⟩

end Compiler.ZigAir.WyhashMixAllocation
