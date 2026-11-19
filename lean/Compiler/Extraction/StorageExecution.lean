/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageProgram

namespace Compiler.Extraction.Storage

/-- Operations for the complete insertion control program. Both allocation and
cleanup see the reached ownership state and may change private effects. `false`
is ordinary allocation failure; `Except.error` is a rejected semantic fault.
Native clone/container/memory refinement remains a compiler obligation. -/
structure Operations (σ ε : Type) where
  attempt : Allocation → State → σ → Except ε Bool × σ
  release : Release → State → σ → Except ε Unit × σ

abbrev Execution (σ ε α : Type) := (Except ε α × State) × σ

def Release.execute (operations : Operations σ ε) (release : Release) (state : State)
    (effects : σ) : Execution σ ε Unit :=
  let (result, reached) := operations.release release state effects
  match result with
  | .error fault => ((.error fault, state), reached)
  | .ok () => ((.ok (), release.run state), reached)

def releaseAll (operations : Operations σ ε) : List Release → State → σ → Execution σ ε Unit
  | [], state, effects => ((.ok (), state), effects)
  | release :: rest, state, effects =>
    let ((result, after), reached) := release.execute operations state effects
    match result with
    | .error fault => ((.error fault, after), reached)
    | .ok () => releaseAll operations rest after reached

def Cleanup.execute (operations : Operations σ ε) (cleanup : Cleanup) (state : State)
    (effects : σ) : Execution σ ε Unit :=
  match cleanup with
  | .guarded flag release =>
    if state.flag flag then release.execute operations state effects else ((.ok (), state), effects)
  | .sequence releases => releaseAll operations releases state effects

/-- The same source-bound `Program`, with effectful deferred cleanup. A fault
retains the reached state and stops; it is not converted to native OOM and does
not invent further unwinding. Ordinary errors execute all applicable defers. -/
def Program.execute (input : Input) (operations : Operations σ ε) :
    Program → State → σ → Execution σ ε (Option Outcome)
  | .done, state, effects => ((.ok none, state), effects)
  | .ret, state, effects =>
    ((.ok (some .success), { state with invalid := state.invalid || !state.capturedId }), effects)
  | .capacityError, state, effects => ((.ok (some .capacityFailure), state), effects)
  | .command action next, state, effects =>
    let (result, reached) : Except ε Bool × σ := match action.allocation with
      | none => (.ok true, effects)
      | some site => operations.attempt site state effects
    match result with
    | .error fault => ((.error fault, state), reached)
    | .ok false => ((.ok (some .allocationFailure), state), reached)
    | .ok true => next.execute input operations (action.success input state) reached
  | .branch test yes no next, state, effects =>
    let ((result, after), reached) :=
      if test.eval input then yes.execute input operations state effects else no.execute input operations state effects
    match result with
    | .error fault => ((.error fault, after), reached)
    | .ok none => next.execute input operations after reached
    | .ok (some outcome) => ((.ok (some outcome), after), reached)
  | .scope errorOnly cleanup body, state, effects =>
    let ((result, after), reached) := body.execute input operations state effects
    match result with
    | .error fault => ((.error fault, after), reached)
    | .ok outcome =>
      if errorOnly && (outcome == some .success || outcome == none) then ((.ok outcome, after), reached)
      else
        let ((closed, final), effects) := cleanup.execute operations after reached
        ((closed.map (fun _ => outcome), final), effects)

/-- A finite verification condition for ordinary outcomes, independent of
private effects. Both outcomes of every allocation are checked. -/
def Program.condition (input : Input) : Program → (Option Outcome → State → Prop) → State → Prop
  | .done, post, state => post none state
  | .ret, post, state => post (some .success) { state with invalid := state.invalid || !state.capturedId }
  | .capacityError, post, state => post (some .capacityFailure) state
  | .command action next, post, state =>
    next.condition input post (action.success input state) ∧
      (action.allocation ≠ none → post (some .allocationFailure) state)
  | .branch test yes no next, post, state =>
    let continuation := fun outcome after => match outcome with
        | none => next.condition input post after
        | some result => post (some result) after
    if test.eval input then yes.condition input continuation state else no.condition input continuation state
  | .scope errorOnly cleanup body, post, state =>
    body.condition input (fun outcome after =>
      post outcome (if errorOnly && (outcome == some .success || outcome == none) then after else cleanup.run after)) state

end Compiler.Extraction.Storage
