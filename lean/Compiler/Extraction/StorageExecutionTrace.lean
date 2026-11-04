/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecutionEffects

namespace Compiler.Extraction.Storage.Trace

private def resourceEquality [DecidableEq α] (a b : Resource → α) : Decidable (a = b) :=
  decidable_of_iff (a .normalized = b .normalized ∧ a .arguments = b .arguments ∧
    a .allocation = b .allocation ∧ a .value = b .value) (by
      constructor
      · rintro ⟨h₁, h₂, h₃, h₄⟩; funext r; cases r <;> assumption
      · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩)

local instance [DecidableEq α] : DecidableEq (Resource → α) := resourceEquality
deriving instance DecidableEq for State

/-- Insertion protocol calls, not physical allocator calls. A callback may
perform several host operations or none. Record its exact reached owner and
complete result, including semantic rejection. -/
inductive Event (ε : Type) where
  | attempt (site : Allocation) (owner : State) (result : Except ε Bool)
  | release (action : Release) (owner : State) (result : Except ε Unit)
  /-- A slot owned by another protocol in a shared stream. Replay rejects it
  without skipping ahead; insertion recorders never emit this constructor. -/
  | foreign

structure Recorded (σ ε : Type) where
  effects : σ
  events : List (Event ε)

def record (ops : Operations σ ε) : Operations (Recorded σ ε) ε where
  attempt site owner before :=
    let (result, after) := ops.attempt site owner before.effects
    (result, ⟨after, before.events ++ [.attempt site owner result]⟩)
  release action owner before :=
    let (result, after) := ops.release action owner before.effects
    (result, ⟨after, before.events ++ [.release action owner result]⟩)

/-- Wrong site, owner, event kind or exhausted input is a semantic rejection.
The sentinel lies beyond the stream and cannot be mistaken for native OOM. -/
def replay (events : List (Event ε)) (mismatch : ε) : Operations Nat ε where
  attempt site owner cursor :=
    match events[cursor]? with
    | some (.attempt expected reached result) =>
      if site = expected ∧ owner = reached then (result, cursor + 1)
      else (.error mismatch, events.length + 1)
    | _ => (.error mismatch, events.length + 1)
  release action owner cursor :=
    match events[cursor]? with
    | some (.release expected reached result) =>
      if action = expected ∧ owner = reached then (result, cursor + 1)
      else (.error mismatch, events.length + 1)
    | _ => (.error mismatch, events.length + 1)

theorem transport (ops : Operations σ ε) :
    Operations.Transport (record ops) ops Recorded.effects := ⟨by intro site owner before; rfl, by intro action owner before; rfl⟩

theorem rejected_absorbs (events : List (Event ε)) (mismatch : ε) (site : Allocation)
    (action : Release) (owner : State) :
    (replay events mismatch).attempt site owner (events.length + 1) = (.error mismatch, events.length + 1) ∧
    (replay events mismatch).release action owner (events.length + 1) = (.error mismatch, events.length + 1) := by
  simp [replay]

/-- A proof combinator for the existing interpreter, not a second executor.
The same actual transcript replays between arbitrary earlier and later events. -/
private abbrev Call (ε α : Type) := {τ : Type} → Operations τ ε → τ → α × τ

private def Tracks (ops : Operations σ ε) (mismatch : ε) (call : Call ε α) : Prop :=
  ∀ before, ∃ events : List (Event ε),
    (∀ history, call (record ops) ⟨before, history⟩ =
      ((call ops before).1, ⟨(call ops before).2, history ++ events⟩)) ∧
    (∀ leading trailing, call (replay (leading ++ events ++ trailing) mismatch) leading.length =
      ((call ops before).1, leading.length + events.length))

private theorem tracks_pure (ops : Operations σ ε) (mismatch : ε) (value : α) :
    Tracks ops mismatch (fun _ before => (value, before)) := by
  intro before
  exact ⟨[], by simp⟩

private theorem tracks_bind (ops : Operations σ ε) (mismatch : ε)
    (first : Call ε α) (next : α → Call ε β)
    (one : Tracks ops mismatch first) (two : ∀ value, Tracks ops mismatch (next value)) :
    Tracks ops mismatch (fun calls before =>
      let (value, reached) := first calls before
      next value calls reached) := by
  intro before
  obtain ⟨xs, hx, rx⟩ := one before
  obtain ⟨ys, hy, ry⟩ := two (first ops before).1 (first ops before).2
  refine ⟨xs ++ ys, ?_, ?_⟩
  · intro history
    simp only [hx, hy, List.append_assoc]
  · intro leading trailing
    have firstReplay := rx leading (ys ++ trailing)
    have nextReplay := ry (leading ++ xs) trailing
    simp only [List.append_assoc, List.length_append] at firstReplay nextReplay ⊢
    rw [firstReplay]
    simpa only [Nat.add_assoc] using nextReplay

private theorem tracks_attempt (ops : Operations σ ε) (mismatch : ε) (site : Allocation) (owner : State) :
    Tracks ops mismatch (fun calls => calls.attempt site owner) := by
  intro before
  refine ⟨[.attempt site owner (ops.attempt site owner before).1], ?_, ?_⟩
  · intro history; rfl
  · intro leading trailing
    simp [replay]

private theorem tracks_release (ops : Operations σ ε) (mismatch : ε) (action : Release) (owner : State) :
    Tracks ops mismatch (fun calls => calls.release action owner) := by
  intro before
  refine ⟨[.release action owner (ops.release action owner before).1], ?_, ?_⟩
  · intro history; rfl
  · intro leading trailing
    simp [replay]

private theorem release_tracks (ops : Operations σ ε) (mismatch : ε) (action : Release) (owner : State) :
    Tracks ops mismatch (fun calls => action.execute calls owner) := by
  refine tracks_bind ops mismatch _ (fun result {_} _ reached => match result with
    | .error fault => ((Except.error fault, owner), reached)
    | .ok () => ((Except.ok (ε := ε) (), action.run owner), reached)) (tracks_release ops mismatch action owner) ?_
  intro result
  cases result with
  | error fault => exact tracks_pure ops mismatch (Except.error fault, owner)
  | ok value => cases value; exact tracks_pure ops mismatch (Except.ok (), action.run owner)

private theorem releaseAll_tracks (ops : Operations σ ε) (mismatch : ε) (actions : List Release) (owner : State) :
    Tracks ops mismatch (fun calls => releaseAll calls actions owner) := by
  induction actions generalizing owner with
  | nil => exact tracks_pure ops mismatch (Except.ok (), owner)
  | cons action rest continued =>
    refine tracks_bind ops mismatch _ (fun (result, after) {_} calls reached => match result with
      | .error fault => ((.error fault, after), reached)
      | .ok () => releaseAll calls rest after reached) (release_tracks ops mismatch action owner) ?_
    rintro ⟨result, reached⟩
    cases result with
    | error fault => exact tracks_pure ops mismatch (Except.error fault, reached)
    | ok value => cases value; exact continued reached

private theorem cleanup_tracks (ops : Operations σ ε) (mismatch : ε) (cleanup : Cleanup) (owner : State) :
    Tracks ops mismatch (fun calls => cleanup.execute calls owner) := by
  cases cleanup with
  | guarded flag action =>
    change Tracks ops mismatch (fun calls before =>
      if owner.flag flag then action.execute calls owner before else ((Except.ok (), owner), before))
    cases selected : owner.flag flag with
    | false => simpa only [selected, Bool.false_eq_true, ↓reduceIte] using
        tracks_pure ops mismatch (Except.ok (), owner)
    | true => simpa only [selected, ↓reduceIte] using
        release_tracks ops mismatch action owner
  | sequence actions => exact releaseAll_tracks ops mismatch actions owner

private theorem execute_tracks (ops : Operations σ ε) (mismatch : ε) (input : Input)
    (program : Program) (owner : State) :
    Tracks ops mismatch (fun calls => program.execute input calls owner) := by
  induction program generalizing owner with
  | done => exact tracks_pure ops mismatch (Except.ok none, owner)
  | ret =>
    exact tracks_pure ops mismatch
      (Except.ok (some Outcome.success), { owner with invalid := owner.invalid || !owner.capturedId })
  | capacityError => exact tracks_pure ops mismatch (Except.ok (some Outcome.capacityFailure), owner)
  | command action next continued =>
    cases allocated : action.allocation
    · simpa only [Program.execute, allocated] using continued (action.success input owner)
    · rename_i site
      simp only [Program.execute, allocated]
      refine tracks_bind ops mismatch _ (fun result {_} calls reached => match result with
        | .error fault => ((Except.error fault, owner), reached)
        | .ok false => ((.ok (some .allocationFailure), owner), reached)
        | .ok true => next.execute input calls (action.success input owner) reached)
        (tracks_attempt ops mismatch site owner) ?_
      intro result
      cases result with
      | error fault => exact tracks_pure ops mismatch (Except.error fault, owner)
      | ok succeeded => cases succeeded with
        | false => exact tracks_pure ops mismatch (Except.ok (some Outcome.allocationFailure), owner)
        | true => exact continued (action.success input owner)
  | branch test yes no next yesTracked noTracked nextTracked =>
    have selected : Tracks ops mismatch (fun calls before =>
      if test.eval input then yes.execute input calls owner before else no.execute input calls owner before) := by
      cases test.eval input <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact noTracked owner
      · exact yesTracked owner
    refine tracks_bind ops mismatch _ (fun (result, after) {_} calls reached => match result with
      | .error fault => ((.error fault, after), reached)
      | .ok none => next.execute input calls after reached
      | .ok (some outcome) => ((.ok (some outcome), after), reached)) selected ?_
    rintro ⟨result, reached⟩
    cases result with
    | error fault => exact tracks_pure ops mismatch (Except.error fault, reached)
    | ok returned => cases returned with
      | none => exact nextTracked reached
      | some outcome => exact tracks_pure ops mismatch (Except.ok (some outcome), reached)
  | scope errorOnly cleanup body bodyTracked =>
    refine tracks_bind ops mismatch _ (fun (result, after) {_} calls reached => match result with
      | .error fault => ((.error fault, after), reached)
      | .ok outcome =>
        if errorOnly && (outcome == some .success || outcome == none) then ((.ok outcome, after), reached)
        else
          let ((closed, final), effects) := cleanup.execute calls after reached
          ((closed.map (fun _ => outcome), final), effects)) (bodyTracked owner) ?_
    rintro ⟨result, reached⟩
    cases result with
    | error fault => exact tracks_pure ops mismatch (Except.error fault, reached)
    | ok outcome =>
      dsimp only
      by_cases skipped : (errorOnly && (outcome == some .success || outcome == none)) = true
      · simp only [skipped, ↓reduceIte]
        exact tracks_pure ops mismatch (Except.ok outcome, reached)
      · simp only [skipped]
        refine tracks_bind ops mismatch _ (fun (closed, final) {_} _ effects =>
          ((closed.map (fun _ => outcome), final), effects)) (cleanup_tracks ops mismatch cleanup reached) ?_
        rintro ⟨closed, final⟩
        exact tracks_pure ops mismatch (closed.map (fun _ => outcome), final)

/-- The recorded execution keeps exactly the original result, owner and private
effects. Its actual event list replays with an exact advancing cursor, including
ordinary OOM cleanup and semantic faults. No allocation policy is supplied. -/
theorem execute_recorded (ops : Operations σ ε) (mismatch : ε) (input : Input)
    (program : Program) (owner : State) (before : σ)
    (history leading trailing : List (Event ε)) :
    let actual := program.execute input ops owner before
    let captured := program.execute input (record ops) owner ⟨before, []⟩
    (captured.1, captured.2.effects) = actual ∧
    program.execute input (record ops) owner ⟨before, history⟩ =
      (actual.1, ⟨actual.2, history ++ captured.2.events⟩) ∧
    program.execute input (replay (leading ++ captured.2.events ++ trailing) mismatch) owner leading.length =
      (actual.1, leading.length + captured.2.events.length) := by
  obtain ⟨events, recorded, replayed⟩ := execute_tracks ops mismatch input program owner before
  have captured := recorded []
  simp only [List.nil_append] at captured
  refine ⟨((transport ops).execute input program owner ⟨before, []⟩).symm, ?_, ?_⟩
  · simpa only [captured] using recorded history
  · simpa only [captured] using replayed leading trailing

end Compiler.Extraction.Storage.Trace
