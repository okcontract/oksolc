/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecutionProofs

namespace Compiler.Extraction.Storage

/-- Reached ownership states of the source preparation prefix, before each
fallible operation. Cleanup consumes precisely the owners established so far. -/
def normalizedOwnership : State := ({} : State).setFlag .normalized true
def duplicatedOwnership : State :=
  (Command.duplicateArguments.success ⟨true, true, fun _ => false⟩ normalizedOwnership).setFlag .arguments true
def createdOwnership : State :=
  (Command.createItem.success ⟨true, true, fun _ => false⟩ duplicatedOwnership).setFlag .allocation true

/-- The successful production ownership transitions up to captureId. -/
def preparationOwnership : State :=
  let input : Input := ⟨true, true, fun _ => false⟩
  let normalized := ({} : State).setFlag .normalized true
  let duplicated := (Command.duplicateArguments.success input normalized).setFlag .arguments true
  let created := (Command.createItem.success input duplicated).setFlag .allocation true
  let cloned := (Command.cloneItem.success input created).setFlag .value true
  Command.captureId.success input cloned

def publicationOwnership : State :=
  (((Command.append.success ⟨true, true, fun _ => false⟩ preparationOwnership).setFlag
    .arguments false).setFlag .allocation false).setFlag .value false

/-- Successful publication transfers the normalized key; the enclosing defers
do not release the published key or the appended representative. -/
def publishedOwnership : State :=
  (Command.publish.success ⟨true, true, fun _ => false⟩ publicationOwnership).setFlag .normalized false

/-- The exact source owners suffice; callbacks need not ignore ownership. -/
theorem insert_prepared_success_at_owners (calls : Operations σ ε) (start dupe made ready appended after : σ)
    (duplicateCall : calls.attempt .arguments normalizedOwnership start = (.ok true, dupe))
    (createCall : calls.attempt .item duplicatedOwnership dupe = (.ok true, made))
    (cloneCall : calls.attempt .clone createdOwnership made = (.ok true, ready))
    (appendCall : calls.attempt .append preparationOwnership ready = (.ok true, appended))
    (publishCall : calls.attempt .publish publicationOwnership appended = (.ok true, after)) :
    insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start =
      ((.ok (some .success), publishedOwnership), after) := by
  simp only [normalizedOwnership, duplicatedOwnership, createdOwnership, preparationOwnership, publicationOwnership,
    Command.success, Bool.not_true] at duplicateCall createCall cloneCall appendCall publishCall
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, duplicateCall, createCall, cloneCall, appendCall, publishCall,
    Cleanup.execute, publishedOwnership, publicationOwnership, preparationOwnership, Except.map]
  rfl

theorem insert_prepared_success (calls : Operations σ ε) (start dupe made ready appended after : σ)
    (duplicateCall : ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe))
    (createCall : ∀ owner, calls.attempt .item owner dupe = (.ok true, made))
    (cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok true, ready))
    (appendCall : calls.attempt .append preparationOwnership ready = (.ok true, appended))
    (publishCall : calls.attempt .publish publicationOwnership appended = (.ok true, after)) :
    insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start =
      ((.ok (some .success), publishedOwnership), after) :=
  insert_prepared_success_at_owners calls start dupe made ready appended after
    (duplicateCall _) (createCall _) (cloneCall _) appendCall publishCall

/-- The full source program uses the reached callback states and unwinds the
appended row before the outer normalized buffer on ordinary publication OOM. -/
theorem insert_prepared_oom (calls : Operations σ ε) (start dupe made ready appended failed popped after : σ)
    (duplicateCall : ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe))
    (createCall : ∀ owner, calls.attempt .item owner dupe = (.ok true, made))
    (cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok true, ready))
    (appendCall : calls.attempt .append preparationOwnership ready = (.ok true, appended))
    (publishCall : calls.attempt .publish publicationOwnership appended = (.ok false, failed))
    (rolled : (Cleanup.sequence [.lastValue, .pop]).execute calls publicationOwnership failed =
      ((.ok (), (Cleanup.sequence [.lastValue, .pop]).run publicationOwnership), popped))
    (cleaned : (Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls publicationOwnership failed =
      ((.ok (), (Cleanup.sequence [.lastValue, .pop, .normalized]).run publicationOwnership), after)) :
    insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start =
      ((.ok (some .allocationFailure), (Cleanup.sequence [.lastValue, .pop, .normalized]).run publicationOwnership), after) := by
  have joined := releaseAll_append calls [.lastValue, .pop] [.normalized] publicationOwnership failed
  change releaseAll calls [.lastValue, .pop] publicationOwnership failed = _ at rolled
  change releaseAll calls [.lastValue, .pop, .normalized] publicationOwnership failed = _ at cleaned
  simp only [List.cons_append, List.nil_append, rolled, cleaned] at joined
  have normalizedRun : Release.normalized.execute calls
      ((Cleanup.sequence [.lastValue, .pop]).run publicationOwnership) popped =
      ((.ok (), (Cleanup.sequence [.lastValue, .pop, .normalized]).run publicationOwnership), after) := by
    cases returned : Release.normalized.execute calls
        ((Cleanup.sequence [.lastValue, .pop]).run publicationOwnership) popped with
    | mk result effects =>
      rcases result with ⟨result, owner⟩
      cases result <;> simpa only [releaseAll, returned] using joined.symm
  have flags : ((Cleanup.sequence [.lastValue, .pop]).run publicationOwnership).flag =
      fun r => r == .normalized := by
    funext r
    cases r <;> rfl
  simp only [preparationOwnership, publicationOwnership, Command.success, Bool.not_true]
    at appendCall publishCall rolled normalizedRun flags
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, duplicateCall, createCall, cloneCall,
    appendCall, publishCall, Cleanup.execute, rolled,
    show (some Outcome.allocationFailure == some .success) = false from rfl,
    show (some Outcome.allocationFailure == none) = false from rfl,
    Bool.false_or, Bool.true_and, flags,
    show (Resource.value == .normalized) = false from rfl,
    show (Resource.allocation == .normalized) = false from rfl,
    show (Resource.arguments == .normalized) = false from rfl,
    show (Resource.normalized == .normalized) = true from rfl, Except.map]
  rw [normalizedRun]
  rfl

/-- Compare the actual insertion program after shared preparation. Only its
reached append, subsequent publication and cleanup callbacks must agree. -/
theorem insert_prepared_congr (calls other : Operations σ ε) (start dupe made ready : σ)
    (duplicateCall : ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe))
    (createCall : ∀ owner, calls.attempt .item owner dupe = (.ok true, made))
    (cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok true, ready))
    (duplicateOther : ∀ owner, other.attempt .arguments owner start = (.ok true, dupe))
    (createOther : ∀ owner, other.attempt .item owner dupe = (.ok true, made))
    (cloneOther : ∀ owner, other.attempt .clone owner made = (.ok true, ready))
    (appendSame : calls.attempt .append preparationOwnership ready = other.attempt .append preparationOwnership ready)
    (publishSame : calls.attempt .publish = other.attempt .publish)
    (releaseSame : calls.release = other.release) :
    insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start =
      insertProgram.execute ⟨true, true, fun _ => false⟩ other {} start := by
  simp only [preparationOwnership, Command.success, Bool.not_true] at appendSame
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, duplicateCall, createCall, cloneCall,
    duplicateOther, createOther, cloneOther, appendSame, publishSame,
    Cleanup.execute, Release.execute, releaseAll, releaseSame]

end Compiler.Extraction.Storage
