/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalProduction
import Compiler.Extraction.InternerCallerTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

/-- A concrete semantic fixture, not a claim about native graph storage.
The child executes normalization on the parent's slice. An existing ID is
returned only after checking its denotation against the actual key. Insertion
consumes its slice and fails ordinarily. -/
def callbacks (meaning : Meaning) (known : NodeId) : Primitives Nat where
  simplify := fun key slice before =>
    let (result, after) := nested success 7 slice before
    match result with
    | .error fault => (.error fault, after)
    | .ok () => (.ok (if before.graph.read known = key.eval meaning before.graph.read then some known else none), after)
  publish := (OwnedCall.Tests.callbacks .unchanged false true).publish
  insert := (OwnedCall.Tests.callbacks .unchanged false true).insert

theorem nested_graph (slice : ArgumentSlice) (before : World Nat) :
    (nested success 7 slice before).2.graph = before.graph := by
  unfold nested
  cases Normalization.run normalizationOwnershipCode success 0 7 false (view slice) ⟨0, 0, 0⟩ slice.items .cleanup before.memory with
  | mk result memory => cases result <;> rfl

theorem ownership (meaning : Meaning) (known : NodeId) (source : View) (values : List NodeId) :
    OwnedCall.Contracts 7 source values (callbacks meaning known) := by
  have previous := OwnedCall.Tests.callbacks_contracts .unchanged false true source values
  refine ⟨⟨previous.publish, previous.insert⟩, ?_⟩
  intro key slice before _ held
  have checked := nested_held success 7 source values slice before held (external_admitted _)
  cases ran : nested success 7 slice before with
  | mk result after =>
    rw [ran] at checked
    cases result with
    | error fault => simpa only [callbacks, ran] using fun (_ : ordinary (.error fault : Except Fault (Option NodeId)) = true) => checked.2
    | ok returned =>
      cases returned
      simp only [callbacks, ran]
      exact fun _ => checked.2

theorem release_graph (slice : ArgumentSlice) (before : World Nat) :
    (OwnedCall.Tests.releaseSlice success 7 slice before).2.graph = before.graph := rfl

theorem semantics (meaning : Meaning) (known : NodeId) (source : View) (values : List NodeId) :
    Contracts 7 source values meaning (callbacks meaning known) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro key slice deterministic before value _ held valid _
    obtain ⟨after, released, _⟩ := OwnedCall.Tests.release_good success 7 source values slice before held
    have same := release_graph slice before
    rw [released] at same
    dsimp only at same
    simpa only [callbacks, OwnedCall.Tests.callbacks, OwnedCall.Tests.callbacksWith, released, ↓reduceIte, same] using
      Ensures.error meaning before.graph (.language .outOfMemory) (fun id after => after.read id = some value) valid
  · intro key slice id before value _ held valid _ _
    obtain ⟨after, released, _⟩ := OwnedCall.Tests.release_good success 7 source values slice before held
    have same := release_graph slice before
    rw [released] at same
    dsimp only at same
    simpa only [callbacks, OwnedCall.Tests.callbacks, OwnedCall.Tests.callbacksWith, Bool.false_eq_true, ↓reduceIte, released, same] using
      Ensures.pure meaning before.graph () (fun _ _ => True) valid trivial
  · intro key slice before value _ _ _ valid evaluated
    have same := nested_graph slice before
    cases ran : nested success 7 slice before with
    | mk result after =>
      rw [ran] at same
      dsimp only at same
      cases result with
      | error fault =>
        simpa only [callbacks, ran, same] using Ensures.error meaning before.graph fault _ valid
      | ok returned =>
        cases returned
        simp only [callbacks, ran, same]
        apply Ensures.pure meaning before.graph _ _ valid
        intro id found
        split at found
        · rename_i equal
          cases found
          exact equal.trans evaluated
        · cases found

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic.Tests
