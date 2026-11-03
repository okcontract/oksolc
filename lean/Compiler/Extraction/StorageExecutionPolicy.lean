/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Lean
import Compiler.Extraction.StoragePreparationFailure
import Compiler.Extraction.StorageTransferredInsertion
import Compiler.Extraction.StorageEffects

namespace Compiler.Extraction.Storage

/-- Select the existing source ownership state at each allocation site. The
transferred path never uses the duplication or publication observations. -/
def executionOwner (deterministic : Bool) : Allocation → State
  | .arguments => normalizedOwnership
  | .item => if deterministic then duplicatedOwnership else transferredArguments
  | .clone => if deterministic then createdOwnership else transferredCreated
  | .append => if deterministic then preparationOwnership else transferredPreparation
  | .publish => publicationOwnership

/-- Boolean observations of the actual source callbacks, used only to select
the existing ghost policy. A rejected callback supplies no ordinary execution:
the projection theorem separately requires actual ordinary completion. Later
entries after a failure are hypothetical, as in `effectPolicy`. -/
def executionAttempt (calls : Operations σ ε) (deterministic : Bool)
    (site : Allocation) (before : σ) : Bool × σ :=
  let observed := calls.attempt site (executionOwner deterministic site) before
  (observed.1.toOption.getD false, observed.2)

def executionPolicy (calls : Operations σ ε) (deterministic : Bool)
    (before : σ) : Allocation → Bool :=
  effectPolicy deterministic (executionAttempt calls deterministic) before

/-- Select the reached clone result using the same allocation prefix as
`effectPolicy`. On an earlier failure this continuation is hypothetical; only a
successful execution may use it as an installed candidate. -/
def executionPreparation (calls : Operations σ ε) (deterministic : Bool) (before : σ) : σ :=
  let duplicated := (if deterministic then executionAttempt calls deterministic .arguments before else (true, before)).2
  let made := (executionAttempt calls deterministic .item duplicated).2
  (executionAttempt calls deterministic .clone made).2

/-- Ordinary completion of a scope retains its body's outcome, even when
cleanup changes private effects. A cleanup rejection cannot satisfy this premise. -/
theorem Program.scope_completed (calls : Operations σ ε) (input : Input)
    (errorOnly : Bool) (cleanup : Cleanup) (body : Program) (owner : State) (before : σ)
    (outcome : Option Outcome)
    (completed : ((Program.scope errorOnly cleanup body).execute input calls owner before).1.1 = .ok outcome) :
    (body.execute input calls owner before).1.1 = .ok outcome := by
  cases ran : body.execute input calls owner before with
  | mk result reached =>
    rcases result with ⟨result, after⟩
    cases result with
    | error fault =>
      simp only [Program.execute, ran] at completed
      cases completed
    | ok observed =>
      simp only [Program.execute, ran] at completed ⊢
      split at completed
      · exact completed
      · cases released : cleanup.execute calls after reached with
        | mk closed final =>
          rcases closed with ⟨closed, state⟩
          cases closed with
          | error fault =>
            simp only [released, Except.map] at completed
            cases completed
          | ok value => simpa only [released, Except.map] using completed

/-- Capacity is observed before the first allocation callback. The actual
outer cleanup may change private effects or reject; ordinary completion keeps
the source capacity outcome in either ownership mode. -/
theorem insert_execution_capacity_outcome (deterministic : Bool) (ignored : Allocation → Bool)
    (calls : Operations σ ε) (before : σ) (outcome : Option Outcome)
    (completed : (insertProgram.execute ⟨deterministic, false, ignored⟩ calls {} before).1.1 = .ok outcome) :
    outcome = some .capacityFailure := by
  unfold insertProgram at completed
  rw [Program.execute] at completed
  dsimp only [Command.allocation, Command.success] at completed
  have bodyOutcome := Program.scope_completed calls ⟨deterministic, false, ignored⟩ false
    (.guarded .normalized .normalized) _ normalizedOwnership before outcome completed
  simpa only [Program.execute, Test.eval, Bool.not_false, ↓reduceIte, Except.ok.injEq] using bodyOutcome.symm

open Lean Meta Elab Tactic

/-- Proof automation only exposes the existing execution and cases actual
callback results. In particular, it never splits an opaque child execution into
unconstrained outcomes. Scope inversion avoids enumerating irrelevant cleanup
effects; all resulting proof terms are checked by the kernel. -/
private def completionLeft (h : Syntax) : TacticM Expr := do
  let type ← instantiateMVars (← inferType (← elabTerm h none))
  unless type.isAppOfArity ``Eq 3 do throwError "expected completion equality"
  return type.getAppArgs[1]!

local elab "storage_policy_head " h:ident : tactic => withMainContext do
  let rec peel : Expr → Expr
    | .mdata _ value => peel value
    | .proj _ _ value => peel value
    | .app f value => if f.isAppOf ``Prod.fst then peel value else .app f value
    | value => value
  let call := peel (← completionLeft h)
  unless call.isAppOf ``Program.execute && call.getAppNumArgs >= 3 do throwError "not an execution head"
  let args := call.getAppArgs
  let program := args[args.size - 3]!
  let loc ← `(Lean.Parser.Tactic.locationHyp| $h:ident)
  if program.isAppOf ``Program.scope then
    evalTactic (← `(tactic| replace $h := Program.scope_completed _ _ _ _ _ _ _ _ $h))
  else
    evalTactic (← `(tactic|
      (rw [Program.execute] at $loc
       try dsimp only [Command.allocation, Command.success, Test.eval] at $loc
       try simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at $loc)))

private def callbackResult? (e : Expr) : Option Expr :=
  let value? := match e with
    | .proj ``Prod 0 value => some value
    | e => if e.isAppOfArity ``Prod.fst 3 then some e.getAppArgs[2]! else none
  if let some value := value? then
    let isCallback := match value.getAppFn with
      | .const ``Operations.attempt _ | .const ``Operations.release _ => true
      | .proj ``Operations 0 _ | .proj ``Operations 1 _ => true
      | _ => false
    if isCallback && !e.hasLooseBVars then some e else none
  else none

private def findCallback : Expr → Option Expr
  | e@(.app f a) => callbackResult? e <|> findCallback a <|> findCallback f
  | e@(.proj _ _ value) => callbackResult? e <|> findCallback value
  | e@(.letE _ _ value body _) => callbackResult? e <|> findCallback value <|> findCallback body
  | e@(.lam _ _ body _) => callbackResult? e <|> findCallback body
  | .mdata _ body => findCallback body
  | e => callbackResult? e

local elab "storage_policy_call " h:ident : tactic => withMainContext do
  let some call := findCallback (← completionLeft h) | throwError "no exposed callback"
  let id ← getFVarId h
  let (_, observed, goal) ← (← getMainGoal).generalizeHyp
    #[{expr := call, xName? := some `observed, hName? := some `observedEq}] #[id]
  unless observed.size > 0 do throwError "callback generalization produced no result variable"
  let alternatives ← goal.cases observed[0]!
  let mut goals := []
  for alternative in alternatives do
    if alternative.ctorName == ``Except.ok then
      unless alternative.fields.size == 1 do throwError "unexpected callback result fields"
      let .fvar field := alternative.fields[0]! | throwError "callback result field is not a variable"
      let successes ← alternative.mvarId.cases field
      goals := goals ++ successes.toList.map (·.mvarId)
    else
      goals := goals ++ [alternative.mvarId]
  replaceMainGoal goals

local elab "storage_policy_finish " h:ident : tactic => withMainContext do
  let left ← completionLeft h
  unless left.isAppOf ``Except.ok || left.isAppOf ``Except.error do
    throwError "not a terminal outcome"
  if left.isAppOf ``Except.error then
    evalTactic (← `(tactic| contradiction))
  else
    evalTactic (← `(tactic|
      (solve |
        simp_all only [Program.execute, Test.eval, Command.allocation, Command.success,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
          Except.ok.injEq]
        try subst_vars
        all_goals simp_all [executionPolicy, effectPolicy, executionAttempt, executionOwner,
          normalizedOwnership, duplicatedOwnership, createdOwnership, preparationOwnership,
          publicationOwnership, transferredArguments, transferredCreated, transferredPreparation,
          expectedOutcome, allocationPolicy, Except.map, Except.toOption, Option.getD, Command.success])))

/-- Ordinary completion reaches either an actual preparation refusal or all
successful source-selected preparation callbacks. Later callbacks and cleanup are left
unconstrained; rejected preparation cannot manufacture an ordinary completion. -/
theorem insert_execution_preparation (calls : Operations σ ε) (deterministic : Bool) (before : σ)
    (outcome : Option Outcome)
    (completed : (insertProgram.execute ⟨deterministic, true, fun _ => false⟩ calls {} before).1.1 = .ok outcome) :
    let duplicate := calls.attempt .arguments normalizedOwnership before
    let duplicated := if deterministic then duplicate.2 else before
    let create := calls.attempt .item (executionOwner deterministic .item) duplicated
    let clone := calls.attempt .clone (executionOwner deterministic .clone) create.2
    (deterministic = true ∧ duplicate.1 = .ok false) ∨
      (deterministic = true → duplicate.1 = .ok true) ∧
        (create.1 = .ok false ∨ create.1 = .ok true ∧ (clone.1 = .ok false ∨ clone.1 = .ok true)) := by
  unfold insertProgram at completed
  cases deterministic
  all_goals
    repeat first
      | dsimp only at completed
      | storage_policy_finish completed
      | storage_policy_head completed
      | storage_policy_call completed
      | (rw [Program.execute] at completed
         try dsimp only [Command.allocation, Command.success, Test.eval] at completed
         try simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at completed)

/-- Once the actual preparation calls succeed, ordinary completion reaches an
ordinary append result and, on the published branch, an ordinary probe result.
Cleanup rejection cannot masquerade as either allocation refusal or success. -/
theorem insert_execution_append (calls : Operations σ ε) (deterministic : Bool) (before : σ)
    (outcome : Option Outcome)
    (completed : (insertProgram.execute ⟨deterministic, true, fun _ => false⟩ calls {} before).1.1 = .ok outcome) :
    let duplicate := calls.attempt .arguments normalizedOwnership before
    let duplicated := if deterministic then duplicate.2 else before
    let create := calls.attempt .item (executionOwner deterministic .item) duplicated
    let clone := calls.attempt .clone (executionOwner deterministic .clone) create.2
    let append := calls.attempt .append (executionOwner deterministic .append) clone.2
    let publish := calls.attempt .publish publicationOwnership append.2
    (deterministic = true → duplicate.1 = .ok true) → create.1 = .ok true → clone.1 = .ok true →
      append.1 = .ok false ∨ append.1 = .ok true ∧
        (deterministic = true → publish.1 = .ok false ∨ publish.1 = .ok true) := by
  dsimp only
  intro duplicateCall createCall cloneCall
  unfold insertProgram at completed
  cases deterministic
  all_goals
    repeat first
      | dsimp only at completed
      | storage_policy_finish completed
      | storage_policy_head completed
      | storage_policy_call completed
      | (rw [Program.execute] at completed
         try dsimp only [Command.allocation, Command.success, Test.eval] at completed
         try simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at completed)

/-- Every ordinary source completion has the outcome selected by the actual
allocation observations. This covers both argument-ownership modes, arbitrary
private effects, every allocation site and cleanup rejection. -/
theorem insert_execution_outcome (input : Input) (calls : Operations σ ε) (before : σ)
    (outcome : Option Outcome)
    (completed : (insertProgram.execute input calls {} before).1.1 = .ok outcome) :
    outcome = some (expectedOutcome input.deterministic input.room
      (executionPolicy calls input.deterministic before .arguments)
      (executionPolicy calls input.deterministic before .item)
      (executionPolicy calls input.deterministic before .clone)
      (executionPolicy calls input.deterministic before .append)
      (executionPolicy calls input.deterministic before .publish)) := by
  rcases input with ⟨deterministic, room, ignored⟩
  cases room with
  | false =>
    simpa only [expectedOutcome, Bool.not_false, ↓reduceIte] using
      insert_execution_capacity_outcome deterministic ignored calls before outcome completed
  | true =>
    unfold insertProgram at completed
    cases deterministic
    all_goals
      repeat first
        | dsimp only at completed
        | storage_policy_finish completed
        | storage_policy_head completed
        | storage_policy_call completed
        | (rw [Program.execute] at completed
           try dsimp only [Command.allocation, Command.success, Test.eval] at completed
           try simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at completed)

/-- The ordinary outcome agrees with the existing logical insertion program
under the observed policy. No equality of private effects is asserted. -/
theorem insert_execution_policy (input : Input) (calls : Operations σ ε) (before : σ)
    (outcome : Option Outcome)
    (completed : (insertProgram.execute input calls {} before).1.1 = .ok outcome) :
    (insertProgram.run { input with succeeds := executionPolicy calls input.deterministic before } {}).1 = outcome := by
  rw [insert_outcome_any]
  exact (insert_execution_outcome input calls before outcome completed).symm

private theorem expectedOutcome_success (deterministic room arguments item clone append publish : Bool)
    (successful : expectedOutcome deterministic room arguments item clone append publish = .success) :
    room = true ∧ (deterministic = true → arguments = true) ∧ item = true ∧ clone = true ∧ append = true ∧
      (deterministic = true → publish = true) := by
  cases deterministic <;> cases room <;> cases arguments <;> cases item <;> cases clone <;> cases append <;> cases publish <;>
    simp_all [expectedOutcome]

private theorem executionAttempt_accepted (calls : Operations σ ε) (deterministic : Bool) (site : Allocation) (before : σ)
    (accepted : (executionAttempt calls deterministic site before).1 = true) :
    (calls.attempt site (executionOwner deterministic site) before).1 = .ok true := by
  cases result : (calls.attempt site (executionOwner deterministic site) before).1 with
  | error fault => simp only [executionAttempt, result, Except.toOption, Option.getD, Bool.false_eq_true] at accepted
  | ok value => cases value <;> simp_all [executionAttempt, Except.toOption, Option.getD]

/-- Success identifies the actual append and publication calls and the full
returned state, in both ownership modes. No callback is assumed ownership-blind;
its canonical reached owner and returned private state select the next call. -/
theorem insert_execution_success (calls : Operations σ ε) (deterministic room : Bool) (before : σ)
    (completed : (insertProgram.execute ⟨deterministic, room, fun _ => false⟩ calls {} before).1.1 = .ok (some .success)) :
    let ready := executionPreparation calls deterministic before
    let appended := calls.attempt .append (executionOwner deterministic .append) ready
    let published := calls.attempt .publish publicationOwnership appended.2
    appended.1 = .ok true ∧ (deterministic = true → published.1 = .ok true) ∧
      insertProgram.execute ⟨deterministic, room, fun _ => false⟩ calls {} before =
        ((.ok (some .success), if deterministic then publishedOwnership else transferredOwnership),
          if deterministic then published.2 else appended.2) := by
  have outcome := insert_execution_outcome ⟨deterministic, room, fun _ => false⟩ calls before (some .success) completed
  have bits := expectedOutcome_success deterministic room
    (executionPolicy calls deterministic before .arguments)
    (executionPolicy calls deterministic before .item)
    (executionPolicy calls deterministic before .clone)
    (executionPolicy calls deterministic before .append)
    (executionPolicy calls deterministic before .publish) (Option.some.inj outcome.symm)
  have roomTrue := bits.1
  subst room
  let duplicated := (if deterministic then executionAttempt calls deterministic .arguments before else (true, before)).2
  let made := (executionAttempt calls deterministic .item duplicated).2
  let ready := executionPreparation calls deterministic before
  let appended := calls.attempt .append (executionOwner deterministic .append) ready
  let published := calls.attempt .publish publicationOwnership appended.2
  have itemAccepted := executionAttempt_accepted calls deterministic .item duplicated (by
    simpa only [executionPolicy, effectPolicy, allocationPolicy, duplicated] using bits.2.2.1)
  have cloneAccepted := executionAttempt_accepted calls deterministic .clone made (by
    simpa only [executionPolicy, effectPolicy, allocationPolicy, made, duplicated] using bits.2.2.2.1)
  have appendAccepted := executionAttempt_accepted calls deterministic .append ready (by
    simpa only [executionPolicy, effectPolicy, allocationPolicy, ready, executionPreparation, made, duplicated] using bits.2.2.2.2.1)
  have publishAccepted : deterministic = true → published.1 = .ok true := by
    intro deterministicTrue
    apply executionAttempt_accepted calls deterministic .publish appended.2
    simpa only [executionPolicy, effectPolicy, allocationPolicy, appended, ready, executionPreparation,
      executionAttempt] using bits.2.2.2.2.2 deterministicTrue
  refine ⟨appendAccepted, publishAccepted, ?_⟩
  cases deterministic with
  | false =>
    exact insert_transferred_success_at_owners calls before made ready appended.2
      (Prod.ext itemAccepted rfl) (Prod.ext cloneAccepted rfl) (Prod.ext appendAccepted rfl)
  | true =>
    have argumentsAccepted := executionAttempt_accepted calls true .arguments before (by
      simpa only [executionPolicy, effectPolicy, allocationPolicy] using bits.2.1 rfl)
    exact insert_prepared_success_at_owners calls before duplicated made ready appended.2 published.2
      (Prod.ext argumentsAccepted rfl) (Prod.ext itemAccepted rfl) (Prod.ext cloneAccepted rfl)
      (Prod.ext appendAccepted rfl) (Prod.ext (publishAccepted rfl) rfl)

end Compiler.Extraction.Storage
