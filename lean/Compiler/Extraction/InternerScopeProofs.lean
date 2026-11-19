/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerScope

namespace Compiler.Extraction.Interner.Scoped
open Compiler.Algebraic Compiler.Extraction.Cache

def Checked (action : Action α) (scope : Scope) (post : α → Scope → Prop) : Prop :=
  ∀ heap result after, action ⟨scope, heap⟩ = (result, after) → Live after.scope ∧
    match result with | .error _ => True | .ok value => post value after.scope

theorem Checked.pure (scope : Scope) (value : α) (post : α → Scope → Prop)
    (live : Live scope) (fact : post value scope) : Checked (pure value) scope post := by
  intro heap result after ran
  cases ran
  exact ⟨live, fact⟩

theorem Checked.bind (first : Action α) (next : α → Action β) (scope : Scope)
    (middle : α → Scope → Prop) (post : β → Scope → Prop) (initial : Checked first scope middle)
    (continuation : ∀ value scope, Live scope → middle value scope → Checked (next value) scope post) :
    Checked (first >>= next) scope post := by
  intro heap result after ran
  change Effect.bind first next ⟨scope, heap⟩ = (result, after) at ran
  cases step : first ⟨scope, heap⟩ with
  | mk outcome current =>
    have checked := initial heap outcome current step
    cases outcome with
    | error error =>
      simp only [Effect.bind, step] at ran
      cases ran
      exact ⟨checked.1, trivial⟩
    | ok value =>
      exact continuation value current.scope checked.1 checked.2 current.heap result after
        (by simpa only [Effect.bind, step] using ran)

theorem Checked.weaken (action : Action α) (scope : Scope) (p q : α → Scope → Prop)
    (checked : Checked action scope p) (implies : ∀ value scope, p value scope → q value scope) :
    Checked action scope q := by
  intro heap result after ran
  have checked := checked heap result after ran
  refine ⟨checked.1, ?_⟩
  cases result with
  | error _ => trivial
  | ok value => exact implies value after.scope checked.2

theorem lift_graph_checked (action : Interner.Action α) (scope : Scope) (live : Live scope) :
    Checked (liftGraph action) scope (fun _ after => after = scope) := by
  intro heap result after ran
  cases step : action heap with
  | mk outcome current =>
    simp only [liftGraph, step] at ran
    cases ran
    refine ⟨live, ?_⟩
    cases result <;> trivial

theorem commutative_projection (sort : List NodeId → List NodeId) (item : Item) (args : List NodeId) :
    normalizeCode.run sort item args = match commutative item with
      | .error _ => none
      | .ok commutes => some (if commutes && decide (normalizeCode.threshold ≤ args.length)
          then sort args else args) := by
  cases guard : normalizeCode.guard.run item with
  | false => simp [NormalizeCode.run, commutative, guard]
  | true =>
    cases instruction : item.instruction <;>
      simp [NormalizeCode.run, commutative, guard, instruction]

/-- Successful initialization refines the previously verified normalization
value projection; allocation failure cannot manufacture a normalized value. -/
theorem initialize_projection (r : Resources) (request : Request) (before after : Session) (args : List NodeId)
    (ran : initScope r request before = (.ok args, after)) :
    normalizeCode.run r.sort request.item request.arguments = some args := by
  rw [commutative_projection]
  cases decision : commutative request.item with
  | error error => simp [initScope, decision] at ran
  | ok commutes =>
    cases initialized : normalizationOwnershipCode.initWith commutes request.arguments.length 2
        (r.allocate .temporary request.arguments) before.heap.allocationCursor with
    | mk lookup cursor =>
      cases lookup with
      | none => simp [initScope, decision, initialized] at ran
      | some lookup =>
        simp only [initScope, decision, initialized, Prod.mk.injEq, Except.ok.injEq] at ran
        exact congrArg some ran.1

/-- Preparation observes destination selection's actual effects. Its cursor
is then visible to lookup, duplicate and any intervening recursive graph call.
This projection concerns successful preparation; concrete faults must be rejected
outside the resource model, without inventing ordinary-error cleanup. -/
theorem initialize_effects (r : Resources) (request : Request) (before : Session)
    (commutes : Bool) (lookup : NormalizationOwnership.State) (cursor : Nat)
    (decoded : commutative request.item = .ok commutes)
    (selected : normalizationOwnershipCode.initWith commutes request.arguments.length 2
      (r.allocate .temporary request.arguments) before.heap.allocationCursor = (some lookup, cursor)) :
    (initScope r request before).2.heap.allocationCursor =
      if lookup.origin = .input then cursor else r.prepare request.arguments lookup cursor := by
  simp only [initScope, decoded, selected]

theorem initialize_oom_effects (r : Resources) (request : Request) (before : Session)
    (commutes : Bool) (cursor : Nat) (decoded : commutative request.item = .ok commutes)
    (selected : normalizationOwnershipCode.initWith commutes request.arguments.length 2
      (r.allocate .temporary request.arguments) before.heap.allocationCursor = (none, cursor)) :
    initScope r request before = (.error .outOfMemory, { before with heap := { before.heap with allocationCursor := cursor } }) := by
  simp only [initScope, decoded, selected]

theorem initialize_checked (r : Resources) (request : Request) (scope : Scope)
    (empty : scope.lookup = none) (phase : scope.phase = .lookup) :
    Checked (initScope r request) scope (fun _ after => Ready after) := by
  intro heap result after ran
  have live : Live scope := Or.inl ⟨empty, phase⟩
  cases decision : commutative request.item with
  | error error =>
    simp only [initScope, decision] at ran
    cases ran
    exact ⟨live, trivial⟩
  | ok commutes =>
    cases initialized : normalizationOwnershipCode.initWith commutes request.arguments.length 2
        (r.allocate .temporary request.arguments) heap.allocationCursor with
    | mk lookup cursor =>
      cases lookup with
      | none =>
        simp only [initScope, decision, initialized] at ran
        cases ran
        exact ⟨live, trivial⟩
      | some state =>
        have ready := NormalizationOwnership.init_with_ready commutes request.arguments.length 2
          (r.allocate .temporary request.arguments) heap.allocationCursor cursor state initialized
        simp only [initScope, decision, initialized] at ran
        cases ran
        exact ⟨Or.inr (Or.inl ⟨state, rfl, rfl, ready⟩), ⟨state, rfl, rfl, ready⟩⟩

theorem take_checked (r : Resources) (scope : Scope) (ready : Ready scope) :
    Checked (take r) scope (fun _ after => Taken after) := by
  rcases ready with ⟨lookup, present, phase, ready⟩
  intro heap result after ran
  cases taken : normalizationOwnershipCode.takeWith (r.allocate .duplicate scope.items) lookup heap.allocationCursor with
  | mk pair cursor =>
    rcases pair with ⟨ok, state⟩
    cases ok with
    | false =>
      have same := NormalizationOwnership.take_with_failure normalizationOwnershipCode
        (r.allocate .duplicate scope.items) heap.allocationCursor cursor lookup state taken
      subst state
      simp only [take, present, taken, Bool.false_eq_true, ↓reduceIte] at ran
      cases ran
      exact ⟨Or.inr (Or.inl ⟨lookup, rfl, phase, ready⟩), trivial⟩
    | true =>
      have owned := NormalizationOwnership.take_with_success (r.allocate .duplicate scope.items)
        heap.allocationCursor cursor lookup state ready taken
      simp only [take, present, taken, ↓reduceIte] at ran
      cases ran
      exact ⟨Or.inr (Or.inr (Or.inl ⟨state, rfl, rfl, owned⟩)), ⟨state, rfl, rfl, owned⟩⟩

theorem handoff_checked (scope : Scope) (taken : Taken scope) :
    Checked handoff scope (fun _ after => Transferred after) := by
  rcases taken with ⟨lookup, present, _, taken⟩
  intro heap result after ran
  cases ran
  exact ⟨Or.inr (Or.inr (Or.inr ⟨lookup, present, rfl, taken⟩)), ⟨lookup, present, rfl, taken⟩⟩

theorem close_frame (r : Resources) (before : Session) :
    (close r before).heap.read = before.heap.read ∧
    (close r before).heap.table = before.heap.table ∧
    (close r before).heap.representatives = before.heap.representatives := by
  cases present : before.scope.lookup <;> simp [close, present]

theorem close_closed (r : Resources) (before : Session) (live : Live before.scope) :
    Closed (close r before).scope := by
  rcases live with empty | ready | taken | transferred
  · simp [Closed, close, empty.1, empty.2]
  · rcases ready with ⟨lookup, present, phase, ready⟩
    have closed := NormalizationOwnership.deinit_with_ready (r.release before.scope.items)
      before.heap.allocationCursor lookup ready
    simpa [close, present, phase, Closed, NormalizationOwnership.Safe] using closed
  · rcases taken with ⟨lookup, present, phase, taken⟩
    rcases taken with ⟨alive, valid, notOwned, owner⟩
    simp [close, present, phase, Closed, normalizationOwnershipCode,
      NormalizationOwnership.Code.deinitWith, NormalizationOwnership.State.move,
      NormalizationOwnership.Safe, alive, valid, notOwned, owner]
  · rcases transferred with ⟨lookup, present, phase, taken⟩
    rw [show close r before = ⟨{ before.scope with lookup := some { lookup with dead := true } },
      before.heap⟩ by simp [close, present, phase,
        NormalizationOwnership.deinit_with_taken (r.release before.scope.items) before.heap.allocationCursor lookup taken]]
    exact ⟨rfl, taken.2.1, by simpa [phase] using taken.2.2.2⟩

end Compiler.Extraction.Interner.Scoped
