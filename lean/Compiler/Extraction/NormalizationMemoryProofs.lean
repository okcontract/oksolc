/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryInit
import Compiler.Extraction.NormalizationMemoryLifetime

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

def Result (allocator : Nat) (commutative : Bool) (source : View) (values : List NodeId)
    (exit : NormalizationOwnership.Exit) (result : Except Failure Outcome) (after : Session σ) : Prop :=
  match result with
  | .error (.preparation reason) => (reason = .incomplete ∨ reason = .memory .outOfMemory) ∧
      after.memory.valid = true ∧ Injected after.heap after.memory
  | .error .outOfMemory => Valid after ∧ Represents after.memory source values
  | .error _ => False
  | .ok outcome => Valid after ∧ Represents after.memory source values ∧
    match outcome with
    | .lookup => exit = .lookup
    | .cleaned => exit = .cleanup
    | .transferred slice => exit = .transfer ∧ slice.items = normalized commutative source values ∧
        Represents after.memory (view slice) (normalized commutative source values) ∧ SliceValid allocator after.heap slice

/-- The public contents/ownership conclusion and the same execution's lifecycle
witness. The latter records actual initialization, transfer identity, lookup
cleanup, borrowed duplication OOM and caller cleanup, including dead aliases.
No initialized handle escapes this complete scoped operation. -/
structure Post (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ)
    (result : Except Failure Outcome) (after : Session σ) : Prop where
  verified : Result allocator commutative source values exit result after
  lifecycle :
    (∃ fault, init normalizationOwnershipCode external budget allocator commutative source buffer values before = (.error fault, after) ∧
      result = .error fault ∧ InitPost allocator commutative source values before (.error fault) after) ∨
    (∃ handle prepared, init normalizationOwnershipCode external budget allocator commutative source buffer values before = (.ok handle, prepared) ∧
      Ready allocator source values handle prepared ∧ handle.values = normalized commutative source values ∧
      continueWith normalizationOwnershipCode external allocator exit handle prepared = (result, after) ∧
      Closed external allocator source values exit handle prepared result after)

theorem closed_result (external : External σ) (allocator : Nat) (commutative : Bool) (source : View) (values : List NodeId)
    (exit : NormalizationOwnership.Exit) (handle : Handle) (before after : Session σ) (result : Except Failure Outcome)
    (closed : Closed external allocator source values exit handle before result after)
    (normalizedValues : handle.values = normalized commutative source values) :
    Result allocator commutative source values exit result after := by
  cases result with
  | error fault =>
    cases fault with
    | allocation | preparation | release => exact False.elim closed.outcome
    | outOfMemory => exact ⟨closed.valid, closed.source⟩
  | ok outcome =>
    cases outcome with
    | lookup => exact ⟨closed.valid, closed.source, closed.outcome.1⟩
    | cleaned => exact ⟨closed.valid, closed.source, closed.outcome.1⟩
    | transferred slice =>
      obtain ⟨exit, items, contents, live, _⟩ := closed.outcome
      exact ⟨closed.valid, closed.source, exit, items.trans normalizedValues, by simpa only [normalizedValues] using contents, live⟩

/-- One composed theorem for selection, allocation, actual captured copy/sort,
takeOwned, deinit and caller cleanup. The only allocator premise is its region
contract; sorting, contents and transfer correctness are proved dependencies.
Both ordinary OOM sites and semantic resource/suspension outcomes are explicit.
This is relative to the reviewed source exporter and native memory contracts. -/
theorem run_refines (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ)
    (valid : Valid before) (represented : Represents before.memory source values)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before)
    (admitted : Admitted external) :
    ∃ result after, run normalizationOwnershipCode external budget allocator commutative source buffer values exit before = (result, after) ∧
      Post external budget allocator commutative source buffer values exit before result after := by
  obtain ⟨initialized, prepared, initializedRun, initPost⟩ := init_refines external budget allocator commutative source buffer values before
    valid represented scratch admitted
  cases initialized with
  | error fault =>
    refine ⟨.error fault, prepared, ?_, ?_, Or.inl ⟨fault, initializedRun, rfl, initPost⟩⟩
    · simp only [run, initializedRun]
    · cases fault with
      | allocation | release => contradiction
      | preparation reason => exact initPost
      | outOfMemory =>
        obtain ⟨_, sameMemory, afterValid⟩ := initPost
        exact ⟨afterValid, by simpa only [sameMemory] using represented⟩
  | ok handle =>
    obtain ⟨ready, normalizedValues⟩ := initPost
    obtain ⟨result, after, continued, closed⟩ := continue_refines external allocator source values exit handle prepared ready admitted
    refine ⟨result, after, ?_, closed_result external allocator commutative source values exit handle prepared after result closed normalizedValues,
      Or.inr ⟨handle, prepared, initializedRun, ready, normalizedValues, continued, closed⟩⟩
    simp only [run, initializedRun, continued]

theorem run_result (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before after : Session σ) (result : Except Failure Outcome)
    (valid : Valid before) (represented : Represents before.memory source values)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before)
    (admitted : Admitted external)
    (executed : run normalizationOwnershipCode external budget allocator commutative source buffer values exit before = (result, after)) :
    Post external budget allocator commutative source buffer values exit before result after := by
  obtain ⟨expected, final, checked, post⟩ := run_refines external budget allocator commutative source buffer values exit before valid represented scratch admitted
  have same := Prod.mk.inj (checked.symm.trans executed)
  rcases same with ⟨rfl, rfl⟩
  exact post

end Compiler.Extraction.Memory.Arguments.Normalization
