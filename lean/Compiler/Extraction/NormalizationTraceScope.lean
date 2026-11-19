/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceRun
import Compiler.Extraction.InternerScope
import Compiler.Extraction.InternerScopeProofs
import Compiler.Extraction.InsertionSortProofs

namespace Compiler.Extraction.Cache.NormalizationOwnership.Trace
open Compiler.Algebraic Compiler.Extraction.InsertionSort
namespace Scope

/-- A cursor indexes a bound invocation trace. Semantic preparation faults
are checked before entering this total resource projection. Argument contents
are supplied by the existing proved sort; trace events do not certify contents. -/
def resources (events : List (Event ε)) (mismatch : ε) : Interner.Scoped.Resources := {
  sort := sortIds
  allocate := fun site _ cursor => Trace.allocate events site cursor
  release := fun _ lookup cursor => Trace.release events lookup cursor
  prepare := fun _ lookup cursor => (Trace.prepare events mismatch lookup cursor).2 }

/-- The resource-only lifecycle of a scope, using the recursive model's actual
operations. Intervening graph calls and their cursor changes are separate. -/
def continueWith (r : Interner.Scoped.Resources) (exit : Exit) (before : Interner.Scoped.Session) :
    Except Interner.Error Outcome × Interner.Scoped.Session :=
  match exit with
  | .lookup => (.ok .lookup, Interner.Scoped.close r before)
  | .transfer | .cleanup =>
    let (result, after) := Interner.Scoped.take r before
    match result with
    | .error error => (.error error, Interner.Scoped.close r after)
    | .ok () =>
      let final := if exit = .transfer then (Interner.Scoped.handoff after).2 else after
      (.ok (if exit = .transfer then .transferred else .cleaned), Interner.Scoped.close r final)

def run (r : Interner.Scoped.Resources) (request : Interner.Request) (exit : Exit) (before : Interner.Heap) :
    Except Interner.Error Outcome × Interner.Scoped.Session :=
  let (result, after) := Interner.Scoped.initScope r request ⟨{}, before⟩
  match result with
  | .error error => (.error error, after)
  | .ok _ => continueWith r exit after

def observe (execution : Except Interner.Error Outcome × Interner.Scoped.Session) : Option (Outcome × State) × Nat :=
  let result := match execution.1 with
    | .ok outcome => some outcome
    | .error .outOfMemory => some .allocationFailure
    | .error _ => none
  (result.map (fun outcome => (outcome, execution.2.scope.lookup.getD { dead := true })), execution.2.heap.allocationCursor)

theorem close_items (r : Interner.Scoped.Resources) (before : Interner.Scoped.Session) :
    (Interner.Scoped.close r before).scope.items = before.scope.items := by
  cases present : before.scope.lookup <;> simp [Interner.Scoped.close, present]

theorem continue_items (r : Interner.Scoped.Resources) (exit : Exit) (before : Interner.Scoped.Session) :
    (continueWith r exit before).2.scope.items = before.scope.items := by
  cases exit with
  | lookup => exact close_items r before
  | transfer | cleanup =>
    cases present : before.scope.lookup with
    | none => simp [continueWith, Interner.Scoped.take, present, close_items]
    | some lookup =>
      cases taken : normalizationOwnershipCode.takeWith (r.allocate .duplicate before.scope.items) lookup before.heap.allocationCursor with
      | mk pair cursor =>
        rcases pair with ⟨ok, lookup⟩
        cases ok <;> simp [continueWith, Interner.Scoped.take, present, taken, Interner.Scoped.handoff, close_items]

/-- Every successful local scope exposes the actual initializer's contents.
Transfer and cleanup only change ownership; they cannot rewrite the list. -/
theorem run_contents (r : Interner.Scoped.Resources) (request : Interner.Request) (exit : Exit)
    (before : Interner.Heap) (outcome : Outcome) (succeeded : (run r request exit before).1 = .ok outcome) :
    normalizeCode.run r.sort request.item request.arguments = some (run r request exit before).2.scope.items := by
  cases decoded : Interner.Scoped.commutative request.item with
  | error error => simp [run, Interner.Scoped.initScope, decoded] at succeeded
  | ok commutative =>
    cases initialized : normalizationOwnershipCode.initWith commutative request.arguments.length 2
        (r.allocate .temporary request.arguments) before.allocationCursor with
    | mk lookup cursor =>
      cases lookup with
      | none => simp [run, Interner.Scoped.initScope, decoded, initialized] at succeeded
      | some lookup =>
        simp only [run, Interner.Scoped.initScope, decoded, initialized, continue_items]
        simp [Interner.Scoped.commutative_projection, decoded]

theorem observe_transferred (execution : Except Interner.Error Outcome × Interner.Scoped.Session)
    (lookup : State) (cursor : Nat) (observed : observe execution = (some (.transferred, lookup), cursor)) :
    execution.1 = .ok .transferred := by
  rcases execution with ⟨result, after⟩
  cases result with
  | error error => cases error <;> simp [observe] at observed
  | ok outcome =>
    simp only [observe, Option.map_some, Prod.mk.injEq, Option.some.injEq] at observed
    exact congrArg Except.ok observed.1.1

theorem continue_projection (events : List (Event ε)) (mismatch : ε) (exit : Exit) (lookup : State)
    (items : List NodeId) (before : Interner.Heap) :
    observe (continueWith (resources events mismatch) exit ⟨⟨some lookup, items, .lookup⟩, before⟩) =
      let (result, cursor) := normalizationOwnershipCode.continueWith (replay events mismatch).toPrimitives exit lookup before.allocationCursor
      (some result, cursor) := by
  cases exit with
  | lookup =>
    cases owned : lookup.owned <;>
      simp [continueWith, observe, resources, replay, Interner.Scoped.close, Code.continueWith, Code.finishWith,
        Code.deinitWith, normalizationOwnershipCode, owned]
  | transfer | cleanup =>
    cases owned : lookup.owned
    · cases allocated : Trace.allocate events .duplicate before.allocationCursor with
      | mk succeeded after =>
        cases succeeded <;>
          simp [continueWith, observe, resources, replay, Interner.Scoped.take, Interner.Scoped.close,
            Interner.Scoped.handoff, Code.continueWith, Code.finishWith, Code.takeWith, Code.deinitWith,
            normalizationOwnershipCode, owned, allocated, move_owned]
    · simp [continueWith, observe, resources, replay, Interner.Scoped.take, Interner.Scoped.close,
        Interner.Scoped.handoff, Code.continueWith, Code.finishWith, Code.takeWith, Code.deinitWith,
        normalizationOwnershipCode, owned, move_owned]

/-- The live projection retains the exact token, normalized items and reached
cursor. Semantic preparation failure cannot satisfy this ordinary-result premise. -/
theorem init_projection (events : List (Event ε)) (mismatch : ε) (request : Interner.Request)
    (before : Interner.Heap) (commutative : Bool) (lookup : Option State) (cursor : Nat)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (executed : normalizationOwnershipCode.initPrepared commutative request.arguments.length 2
      (replay events mismatch) before.allocationCursor = (.ok lookup, cursor)) :
    Interner.Scoped.initScope (resources events mismatch) request ⟨{}, before⟩ =
      match lookup with
      | none => (.error .outOfMemory, ⟨{}, { before with allocationCursor := cursor }⟩)
      | some lookup =>
        let items := if commutative && decide (normalizeCode.threshold ≤ request.arguments.length)
          then sortIds request.arguments else request.arguments
        (.ok items, ⟨⟨some lookup, items, .lookup⟩, { before with allocationCursor := cursor }⟩) := by
  cases initialized : normalizationOwnershipCode.initWith commutative request.arguments.length 2
      (Trace.allocate events .temporary) before.allocationCursor with
  | mk selected reached =>
    cases selected with
    | none =>
      simp only [Code.initPrepared, replay, initialized, Prod.mk.injEq, Except.ok.injEq] at executed
      rcases executed with ⟨rfl, rfl⟩
      simp [resources, Interner.Scoped.initScope, decoded, initialized]
    | some selected =>
      by_cases borrowed : selected.origin = .input
      · simp only [Code.initPrepared, replay, initialized, if_pos borrowed, Prod.mk.injEq, Except.ok.injEq] at executed
        rcases executed with ⟨rfl, rfl⟩
        simp [resources, Interner.Scoped.initScope, decoded, initialized, borrowed]
      · cases prepared : Trace.prepare events mismatch selected reached with
        | mk result after =>
          cases result with
          | error reason => simp [Code.initPrepared, replay, initialized, borrowed, prepared] at executed
          | ok returned =>
            cases returned
            simp only [Code.initPrepared, replay, initialized, if_neg borrowed, prepared, Prod.mk.injEq, Except.ok.injEq] at executed
            rcases executed with ⟨rfl, rfl⟩
            simp [resources, Interner.Scoped.initScope, decoded, initialized, borrowed, prepared]

/-- The complete lifecycle consumes the shared live initialization projection. -/
theorem run_projection (events : List (Event ε)) (mismatch : ε) (request : Interner.Request) (exit : Exit)
    (before : Interner.Heap) (commutative : Bool) (result : Outcome × State) (cursor : Nat)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (executed : normalizationOwnershipCode.runPrepared commutative request.arguments.length 2
      (replay events mismatch) exit before.allocationCursor = (.ok result, cursor)) :
    observe (run (resources events mismatch) request exit before) = (some result, cursor) := by
  cases initialized : normalizationOwnershipCode.initPrepared commutative request.arguments.length 2
      (replay events mismatch) before.allocationCursor with
  | mk lookup reached =>
    cases lookup with
    | error failure => simp [Code.runPrepared, initialized] at executed
    | ok lookup =>
      have projected := init_projection events mismatch request before commutative lookup reached decoded initialized
      cases lookup with
      | none =>
        simp only [Code.runPrepared, initialized, Prod.mk.injEq, Except.ok.injEq] at executed
        rcases executed with ⟨rfl, rfl⟩
        simp [run, projected, observe]
      | some lookup =>
        simp only [Code.runPrepared, initialized, Prod.mk.injEq, Except.ok.injEq] at executed
        simp only [run, projected]
        rw [continue_projection]
        exact Prod.ext (congrArg some executed.1) executed.2

/-- Admission failure is separate from ordinary compiler allocation failure.
The retained token/cursor identify semantic preparation failure without cleanup. -/
inductive Rejection (ε : Type) where
  | entry (reason : Interner.Error)
  | preparation (reason : ε) (lookup : State) (cursor : Nat)
  | mismatch (cursor : Nat)
  deriving Repr

/-- One admission boundary for live prefixes and completed lifecycles.
Never project a semantic fault or an out-of-trace cursor into total resources. -/
def admit (events : List (Event ε)) (execution : Except (ε × State) α × Nat) (projection : β) : Except (Rejection ε) β :=
  let (result, cursor) := execution
  if events.length < cursor then .error (.mismatch cursor) else
  match result with
  | .error (reason, lookup) => .error (.preparation reason lookup cursor)
  | .ok _ => .ok projection

theorem admit_sound (events : List (Event ε)) (execution : Except (ε × State) α × Nat)
    (projection output : β) (accepted : admit events execution projection = .ok output) :
    ∃ result, execution.1 = .ok result ∧ execution.2 ≤ events.length ∧ output = projection := by
  rcases execution with ⟨result, cursor⟩
  by_cases outside : events.length < cursor
  · simp [admit, outside] at accepted
  · cases result with
    | error failure => cases failure; simp [admit, outside] at accepted
    | ok result =>
      simp only [admit, if_neg outside, Except.ok.injEq] at accepted
      exact ⟨result, rfl, by omega, accepted.symm⟩

def checked (events : List (Event ε)) (mismatch : ε) (request : Interner.Request) (exit : Exit)
    (before : Interner.Heap) : Except (Rejection ε) (Except Interner.Error Outcome × Interner.Scoped.Session) :=
  match Interner.Scoped.commutative request.item with
  | .error error => .error (.entry error)
  | .ok commutative =>
    admit events (normalizationOwnershipCode.runPrepared commutative request.arguments.length 2
      (replay events mismatch) exit before.allocationCursor) (run (resources events mismatch) request exit before)

def checkedInit (events : List (Event ε)) (mismatch : ε) (request : Interner.Request)
    (before : Interner.Heap) : Except (Rejection ε) (Except Interner.Error (List NodeId) × Interner.Scoped.Session) :=
  match Interner.Scoped.commutative request.item with
  | .error error => .error (.entry error)
  | .ok commutative =>
    admit events (normalizationOwnershipCode.initPrepared commutative request.arguments.length 2
      (replay events mismatch) before.allocationCursor) (Interner.Scoped.initScope (resources events mismatch) request ⟨{}, before⟩)

theorem checked_success (events : List (Event ε)) (mismatch : ε) (request : Interner.Request) (exit : Exit)
    (before : Interner.Heap) (commutative : Bool) (result : Outcome × State) (cursor : Nat)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (executed : normalizationOwnershipCode.runPrepared commutative request.arguments.length 2
      (replay events mismatch) exit before.allocationCursor = (.ok result, cursor)) (within : cursor ≤ events.length) :
    checked events mismatch request exit before = .ok (run (resources events mismatch) request exit before) ∧
      observe (run (resources events mismatch) request exit before) = (some result, cursor) := by
  exact ⟨by simp [checked, admit, decoded, executed, Nat.not_lt.mpr within],
    run_projection events mismatch request exit before commutative result cursor decoded executed⟩

theorem checked_sound (events : List (Event ε)) (mismatch : ε) (request : Interner.Request) (exit : Exit)
    (before : Interner.Heap) (execution : Except Interner.Error Outcome × Interner.Scoped.Session)
    (accepted : checked events mismatch request exit before = .ok execution) :
    ∃ commutative result cursor, Interner.Scoped.commutative request.item = .ok commutative ∧
      normalizationOwnershipCode.runPrepared commutative request.arguments.length 2
        (replay events mismatch) exit before.allocationCursor = (.ok result, cursor) ∧
      cursor ≤ events.length ∧ observe execution = (some result, cursor) ∧
      execution = run (resources events mismatch) request exit before := by
  cases decoded : Interner.Scoped.commutative request.item with
  | error error => simp [checked, decoded] at accepted
  | ok commutative =>
    simp only [checked, decoded] at accepted
    obtain ⟨result, ran, within, rfl⟩ := admit_sound _ _ _ _ accepted
    have executed : normalizationOwnershipCode.runPrepared commutative request.arguments.length 2
        (replay events mismatch) exit before.allocationCursor =
        (.ok result, (normalizationOwnershipCode.runPrepared commutative request.arguments.length 2
          (replay events mismatch) exit before.allocationCursor).2) := Prod.ext ran rfl
    exact ⟨commutative, result, _, rfl, executed, within,
      run_projection events mismatch request exit before commutative result _ decoded executed, rfl⟩

theorem checked_init_sound (events : List (Event ε)) (mismatch : ε) (request : Interner.Request)
    (before : Interner.Heap) (execution : Except Interner.Error (List NodeId) × Interner.Scoped.Session)
    (accepted : checkedInit events mismatch request before = .ok execution) :
    ∃ commutative lookup cursor, Interner.Scoped.commutative request.item = .ok commutative ∧
      normalizationOwnershipCode.initPrepared commutative request.arguments.length 2
        (replay events mismatch) before.allocationCursor = (.ok lookup, cursor) ∧
      cursor ≤ events.length ∧
      execution = Interner.Scoped.initScope (resources events mismatch) request ⟨{}, before⟩ := by
  cases decoded : Interner.Scoped.commutative request.item with
  | error error => simp [checkedInit, decoded] at accepted
  | ok commutative =>
    simp only [checkedInit, decoded] at accepted
    obtain ⟨lookup, ran, within, rfl⟩ := admit_sound _ _ _ _ accepted
    exact ⟨commutative, lookup, _, rfl, Prod.ext ran rfl, within, rfl⟩

theorem checked_init_scope (events : List (Event ε)) (mismatch : ε) (request : Interner.Request)
    (before : Interner.Heap) (execution : Except Interner.Error (List NodeId) × Interner.Scoped.Session)
    (accepted : checkedInit events mismatch request before = .ok execution) :
    execution.2.scope.items = execution.1.toOption.getD [] ∧ execution.2.scope.phase = .lookup := by
  obtain ⟨commutative, lookup, cursor, decoded, ran, _, projected⟩ := checked_init_sound _ _ _ _ _ accepted
  rw [projected, init_projection events mismatch request before commutative lookup cursor decoded ran]
  cases lookup <;> exact ⟨rfl, rfl⟩

end Scope
end Compiler.Extraction.Cache.NormalizationOwnership.Trace
