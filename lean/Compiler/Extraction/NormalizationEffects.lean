/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NormalizationOwnershipProofs

namespace Compiler.Extraction.Cache.NormalizationOwnership

/-- A live lookup either owns its allocated temporary or only borrows its items.
The token tracked by `owner` later denotes the independent duplicate on the
borrowed path; it never grants ownership of the input or scratch borrow. -/
def Ready (state : State) : Prop :=
  state.dead = false ∧ state.invalid = false ∧
    if state.owned then state.origin = .allocation ∧ state.owner = .lookup else state.owner = .absent

def Taken (state : State) : Prop :=
  state.dead = false ∧ state.invalid = false ∧ state.owned = false ∧ state.owner = .caller

/-- The initializer establishes the local handle invariant for every length,
buffer size, commutativity decision and stateful allocation outcome. -/
theorem init_with_ready (commutative : Bool) (length bufferLength : Nat)
    (allocate : σ → Bool × σ) (effects after : σ) (state : State)
    (initialized : normalizationOwnershipCode.initWith commutative length bufferLength allocate effects =
      (some state, after)) : Ready state := by
  by_cases small : length < 2
  · cases commutative <;>
      simp [normalizationOwnershipCode, Code.initWith, small] at initialized <;>
      rcases initialized with ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  · by_cases fits : length ≤ bufferLength
    · have large : ¬bufferLength < length := by omega
      cases commutative <;>
        simp [normalizationOwnershipCode, Code.initWith, Comparison.test, small, fits, large] at initialized <;>
        rcases initialized with ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
    · have large : bufferLength < length := by omega
      cases step : allocate effects with
      | mk ok cursor =>
        cases commutative <;> cases ok <;>
          simp [normalizationOwnershipCode, Code.initWith, Comparison.test, small, fits, large, step] at initialized <;>
          rcases initialized with ⟨rfl, rfl⟩ <;> first | exact ⟨rfl, rfl, rfl⟩ | exact ⟨rfl, rfl, rfl, rfl⟩

theorem take_with_success (duplicate : σ → Bool × σ) (effects after : σ)
    (before state : State) (ready : Ready before)
    (taken : normalizationOwnershipCode.takeWith duplicate before effects = ((true, state), after)) : Taken state := by
  rcases ready with ⟨alive, valid, owner⟩
  cases owned : before.owned with
  | true =>
    have owns := (by simpa only [owned, ↓reduceIte] using owner : before.origin = .allocation ∧ before.owner = .lookup)
    simp [normalizationOwnershipCode, Code.takeWith, owned, State.move, owns.2] at taken
    rcases taken with ⟨rfl, rfl⟩
    exact ⟨alive, valid, rfl, rfl⟩
  | false =>
    have owns : before.owner = .absent := by simpa only [owned, Bool.false_eq_true, ↓reduceIte] using owner
    cases step : duplicate effects with
    | mk ok cursor =>
      cases ok <;> simp [Code.takeWith, owned, step, State.move, owns] at taken
      rcases taken with ⟨rfl, rfl⟩
      exact ⟨alive, valid, rfl, rfl⟩

theorem take_with_failure (code : Code) (duplicate : σ → Bool × σ) (effects after : σ)
    (before state : State) (failed : code.takeWith duplicate before effects = ((false, state), after)) : state = before := by
  cases owned : before.owned with
  | true => simp [Code.takeWith, owned] at failed
  | false =>
    cases step : duplicate effects with
    | mk ok cursor => cases ok <;> simp [Code.takeWith, owned, step] at failed; exact failed.1.symm

theorem deinit_with_ready (release : State → σ → σ) (effects : σ) (state : State) (ready : Ready state) :
    let after := (normalizationOwnershipCode.deinitWith release state effects).1
    after.dead = true ∧ after.invalid = false ∧ (after.owner = .absent ∨ after.owner = .released) := by
  rcases ready with ⟨alive, valid, owner⟩
  cases owned : state.owned <;>
    simp [owned] at owner
  · simp [normalizationOwnershipCode, Code.deinitWith, owned, valid, owner]
  · simp [normalizationOwnershipCode, Code.deinitWith, owned, State.move, owner.2, valid]

/-- After transfer, lookup deinit does not free the caller's buffer or change
private effects. The caller or downstream owner must eventually consume it. -/
theorem deinit_with_taken (release : State → σ → σ) (effects : σ) (state : State) (taken : Taken state) :
    normalizationOwnershipCode.deinitWith release state effects = ({ state with dead := true }, effects) := by
  simp [normalizationOwnershipCode, Code.deinitWith, taken.2.2.1]

/-- Temporary allocation and duplication are mutually exclusive in this
ownership-only interpreter. It omits copy/sort effects, so ghost outcomes can
both be read at the initial private state. This projection must not be reused
across preparation; runPrepared continues with the actual reached effects. -/
theorem run_with_projection (commutative : Bool) (length bufferLength : Nat)
    (p : Primitives σ) (exit : Exit) (effects : σ) :
    (normalizationOwnershipCode.runWith commutative length bufferLength p exit effects).1 =
      normalizationOwnershipCode.run commutative length bufferLength
        (p.allocate .temporary effects).1 (p.allocate .duplicate effects).1 exit := by
  cases temporary : p.allocate .temporary effects with
  | mk a sa =>
    cases duplicate : p.allocate .duplicate effects with
    | mk d sd =>
      by_cases small : length < 2
      · cases commutative <;> cases a <;> cases d <;> cases exit <;>
          simp [normalizationOwnershipCode, Code.run, Code.runWith, Code.continueWith, Code.finishWith,
            Code.initWith, Code.takeWith, Code.deinitWith, State.move, small, duplicate]
      · by_cases fits : length ≤ bufferLength
        · have large : ¬bufferLength < length := by omega
          cases commutative <;> cases a <;> cases d <;> cases exit <;>
            simp [normalizationOwnershipCode, Code.run, Code.runWith, Code.continueWith, Code.finishWith,
              Code.initWith, Code.takeWith, Code.deinitWith, State.move, Comparison.test,
              small, fits, large, duplicate]
        · have large : bufferLength < length := by omega
          cases commutative <;> cases a <;> cases d <;> cases exit <;>
            simp [normalizationOwnershipCode, Code.run, Code.runWith, Code.continueWith, Code.finishWith,
              Code.initWith, Code.takeWith, Code.deinitWith, State.move, Comparison.test,
              small, fits, large, temporary, duplicate]

theorem run_with_safe (commutative : Bool) (length bufferLength : Nat)
    (p : Primitives σ) (exit : Exit) (effects : σ) :
    Safe (normalizationOwnershipCode.runWith commutative length bufferLength p exit effects).1 := by
  rw [run_with_projection]
  exact run_safe _ _ _ _ _ _

end Compiler.Extraction.Cache.NormalizationOwnership
