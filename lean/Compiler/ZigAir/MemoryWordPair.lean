/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExecutionProofs
import Compiler.ZigAir.MemoryWordExchange

/-! An executable entry contract for two initialized writable u32 subobjects.
The checked physical regions are disjoint. This is an entry obligation in the
typed heap model, not a proof of LLVM's whole-invocation noalias condition.
The body's access footprint and native pointer provenance require separate
proofs. Rejection happens before allocation or execution and retains the state.
-/
namespace Compiler.ZigAir.Memory.WordPair
open WordArray (word)

def region (state : State) (pointer : Value) : Except Fault Nat := do
  let .pointer (.pointer true false (.scalar (.int false 32))) address := pointer
    | .error .malformed
  let cell ← access state address ⟨4, 4⟩ true
  let _ ← load state pointer
  .ok (cell.base + address.offset)

def validate (state : State) (args : List Value) : Except Fault Unit := do
  if !state.valid then .error .malformed else
  let [left, right] := args | .error .malformed
  let a ← region state left
  let b ← region state right
  if a + 4 ≤ b ∨ b + 4 ≤ a then .ok () else .error .memoryValidity

/-- A contract result includes actual successful accesses and initialized
loads; distinct pointer values alone do not discharge it. -/
theorem region_sound (state : State) (pointer : Value) (base : Nat)
    (accepted : region state pointer = .ok base) :
    ∃ address cell value,
      pointer = .pointer (.pointer true false word) address ∧
      access state address ⟨4, 4⟩ true = .ok cell ∧
      load state pointer = .ok value ∧ base = cell.base + address.offset := by
  unfold region at accepted
  split at accepted
  · rename_i address
    cases accessed : access state address ⟨4, 4⟩ true with
    | error fault => simp [accessed, bind, Except.bind] at accepted
    | ok cell =>
      cases loaded : load state (.pointer (.pointer true false word) address) with
      | error fault => simp [accessed, loaded, bind, Except.bind] at accepted
      | ok value =>
        simp only [accessed, loaded, bind, Except.bind, Except.ok.injEq] at accepted
        exact ⟨address, cell, value, rfl, accessed, rfl, accepted.symm⟩
  · contradiction

theorem validate_sound (state : State) (args : List Value)
    (accepted : validate state args = .ok ()) :
    state.valid = true ∧ ∃ left right a b,
      args = [left, right] ∧ region state left = .ok a ∧ region state right = .ok b ∧
      (a + 4 ≤ b ∨ b + 4 ≤ a) := by
  unfold validate at accepted
  split at accepted
  · contradiction
  · rename_i initial
    have valid : state.valid = true := by simpa using initial
    split at accepted
    · rename_i left right
      cases first : region state left with
      | error fault => simp [first, bind, Except.bind] at accepted
      | ok a =>
        cases second : region state right with
        | error fault => simp [first, second, bind, Except.bind] at accepted
        | ok b =>
          simp only [first, second, bind, Except.bind] at accepted
          split at accepted
          · exact ⟨valid, left, right, a, b, rfl, first, second, by assumption⟩
          · contradiction
    · contradiction

theorem validated_bytes_apart (state : State) (args : List Value)
    (accepted : validate state args = .ok ()) :
    ∃ left right a b, args = [left, right] ∧
      region state left = .ok a ∧ region state right = .ok b ∧
      ∀ i j : Fin 4, a + i.val ≠ b + j.val := by
  obtain ⟨_, left, right, a, b, argsEq, first, second, apart⟩ := validate_sound state args accepted
  refine ⟨left, right, a, b, argsEq, first, second, ?_⟩
  intro i j
  have := i.isLt
  have := j.isLt
  omega

theorem aliases_rejected (state : State) (pointer : Value) :
    validate state [pointer, pointer] ≠ .ok () := by
  intro accepted
  obtain ⟨_, left, right, a, b, argsEq, first, second, apart⟩ := validate_sound state _ accepted
  have eqs : pointer = left ∧ pointer = right := by simpa using argsEq
  obtain ⟨rfl, rfl⟩ := eqs
  have same := Except.ok.inj (first.symm.trans second)
  omega

theorem region_view (state : State) (view : WordArray.View) (items : List (BitVec 32)) (index : Nat)
    (initial : state.valid = true) (cap : WordArray.Writable state view)
    (represented : WordArray.Represents state view items) (inside : index < items.length) :
    ∃ cell, state.heap.lookup view.allocation = some cell ∧
      region state (view.pointer index) = .ok (cell.base + (view.address index).offset) := by
  obtain ⟨_, cell, found, _, _, _, accessed⟩ := WordArray.element_access state view index 4
    initial cap (by simpa only [represented.1] using inside) (by omega) true
  refine ⟨cell, found, ?_⟩
  have loaded : load state (.pointer (.pointer true false word) (view.address index)) =
      .ok (WordArray.number items[index]) := represented.2 index inside
  simp only [region, WordArray.View.pointer, accessed, loaded, bind, Except.bind]

theorem validate_view (state : State) (view : WordArray.View) (items : List (BitVec 32)) (left right : Nat)
    (initial : state.valid = true) (cap : WordArray.Writable state view)
    (represented : WordArray.Represents state view items) (hl : left < items.length) (hr : right < items.length)
    (apart : left ≠ right) : validate state [view.pointer left, view.pointer right] = .ok () := by
  obtain ⟨cell, found, _, _, _, _, separated⟩ := WordArray.element_regions state view left right initial cap
    (by simpa only [represented.1] using hl) (by simpa only [represented.1] using hr) apart
  obtain ⟨leftCell, leftFound, first⟩ := region_view state view items left initial cap represented hl
  obtain ⟨rightCell, rightFound, second⟩ := region_view state view items right initial cap represented hr
  have leftEq : leftCell = cell := Option.some.inj (leftFound.symm.trans found)
  have rightEq : rightCell = cell := Option.some.inj (rightFound.symm.trans found)
  subst leftCell
  subst rightCell
  simp only [validate, initial, Bool.not_true, Bool.false_eq_true, ↓reduceIte, first, second, bind, Except.bind]
  exact if_pos separated

end Compiler.ZigAir.Memory.WordPair

namespace Compiler.ZigAir.MemoryAir
open Memory

/-- The underlying AIR is exposed for proof, while invocation retains the
entry contract. Generators must not emit this body as an unrestricted Program. -/
structure WordPairProgram where
  program : Program true

def WordPairProgram.start (program : WordPairProgram) (args : List Value) (state : State) : Invocation :=
  match WordPair.validate state args with
  | .error fault => .finished (.error fault) state
  | .ok () => program.program.start args state

def WordPairProgram.runFuel (program : WordPairProgram) (fuel : Nat) (args : List Value) (state : State) : Invocation :=
  (program.start args state).resume fuel

theorem WordPairProgram.rejection_retains_state (program : WordPairProgram) (fuel : Nat)
    (args : List Value) (state : State) (fault : Fault)
    (rejected : WordPair.validate state args = .error fault) :
    program.runFuel fuel args state = .finished (.error fault) state := by
  simp only [runFuel, start, rejected, Invocation.resume_finished]

theorem WordPairProgram.accepted_run (program : WordPairProgram) (fuel : Nat)
    (args : List Value) (state : State) (accepted : WordPair.validate state args = .ok ()) :
    program.runFuel fuel args state = program.program.runFuel fuel args state := by
  simp only [runFuel, start, accepted, Program.runFuel]

theorem WordPairProgram.resume_add (program : WordPairProgram) (first second : Nat)
    (args : List Value) (state : State) :
    (program.runFuel first args state).resume second = program.runFuel (first + second) args state :=
  (Invocation.resume_add first second (program.start args state)).symm

theorem WordPairProgram.preserves_valid (program : WordPairProgram) (fuel : Nat)
    (args : List Value) (state : State) (initial : state.valid = true) :
    (program.runFuel fuel args state).state.valid = true := by
  cases checked : WordPair.validate state args with
  | error fault => rw [program.rejection_retains_state fuel args state fault checked]; exact initial
  | ok value =>
    cases value
    rw [program.accepted_run fuel args state checked]
    exact Program.runFuel_preserves_valid program.program fuel args state initial

end Compiler.ZigAir.MemoryAir
