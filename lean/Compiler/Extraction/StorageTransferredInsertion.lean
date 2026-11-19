/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecutionProofs

namespace Compiler.Extraction.Storage

/-- The source transfers the normalized buffer before creating the item. There
is one argument owner, and its enclosing normalized defer is disabled. -/
def transferredArguments : State :=
  let input : Input := ⟨false, true, fun _ => false⟩
  let normalized := (({} : State).setFlag .normalized true).setFlag .normalized false
  (Command.aliasArguments.success input normalized).setFlag .arguments true

def transferredCreated : State :=
  (Command.createItem.success ⟨false, true, fun _ => false⟩ transferredArguments).setFlag .allocation true

def transferredPreparation : State :=
  let input : Input := ⟨false, true, fun _ => false⟩
  let cloned := (Command.cloneItem.success input transferredCreated).setFlag .value true
  Command.captureId.success input cloned

def transferredOwnership : State :=
  (((Command.append.success ⟨false, true, fun _ => false⟩ transferredPreparation).setFlag
    .arguments false).setFlag .allocation false).setFlag .value false

/-- Successful transferred insertion needs only the reached ownership states. -/
theorem insert_transferred_success_at_owners (calls : Operations σ ε) (start made ready after : σ)
    (createCall : calls.attempt .item transferredArguments start = (.ok true, made))
    (cloneCall : calls.attempt .clone transferredCreated made = (.ok true, ready))
    (appendCall : calls.attempt .append transferredPreparation ready = (.ok true, after)) :
    insertProgram.execute ⟨false, true, fun _ => false⟩ calls {} start =
      ((.ok (some .success), transferredOwnership), after) := by
  simp only [transferredPreparation, transferredCreated, transferredArguments, Command.success, Bool.not_true]
    at createCall cloneCall appendCall
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, createCall, cloneCall, appendCall,
    Cleanup.execute, transferredOwnership, transferredPreparation, transferredCreated, transferredArguments, Except.map]
  rfl

/-- The exact source program skips duplication and publication. Successful
append transfers its only argument owner to the graph; no cleanup callback runs. -/
theorem insert_transferred_success (calls : Operations σ ε) (start made ready after : σ)
    (createCall : ∀ owner, calls.attempt .item owner start = (.ok true, made))
    (cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok true, ready))
    (appendCall : calls.attempt .append transferredPreparation ready = (.ok true, after)) :
    insertProgram.execute ⟨false, true, fun _ => false⟩ calls {} start =
      ((.ok (some .success), transferredOwnership), after) :=
  insert_transferred_success_at_owners calls start made ready after (createCall _) (cloneCall _) appendCall

/-- Append OOM occurs after the normalized owner was selected as arguments.
Only value, object and arguments unwind; the normalized defer is already off. -/
theorem insert_transferred_append_oom (calls : Operations σ ε) (start made ready failed valueFreed destroyed after : σ)
    (createCall : ∀ owner, calls.attempt .item owner start = (.ok true, made))
    (cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok true, ready))
    (appendCall : calls.attempt .append transferredPreparation ready = (.ok false, failed))
    (valueCall : calls.release .value transferredPreparation failed = (.ok (), valueFreed))
    (allocationCall : calls.release .allocation (Release.value.run transferredPreparation) valueFreed = (.ok (), destroyed))
    (argumentCall : calls.release .arguments (Release.allocation.run (Release.value.run transferredPreparation)) destroyed = (.ok (), after)) :
    insertProgram.execute ⟨false, true, fun _ => false⟩ calls {} start =
      ((.ok (some .allocationFailure), (Cleanup.sequence [.value, .allocation, .arguments]).run transferredPreparation), after) := by
  have valueFlag : transferredPreparation.flag .value = true := rfl
  have allocationFlag : (Release.value.run transferredPreparation).flag .allocation = true := rfl
  have argumentFlag : (Release.allocation.run (Release.value.run transferredPreparation)).flag .arguments = true := rfl
  have normalizedFlag : (Release.arguments.run (Release.allocation.run (Release.value.run transferredPreparation))).flag .normalized = false := rfl
  simp only [transferredPreparation, transferredCreated, transferredArguments, Command.success, Bool.not_true]
    at appendCall valueCall allocationCall argumentCall valueFlag allocationFlag argumentFlag normalizedFlag
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, createCall, cloneCall, appendCall,
    show (some Outcome.allocationFailure == some .success) = false from rfl,
    show (some Outcome.allocationFailure == none) = false from rfl,
    Bool.false_or, Bool.true_and, Cleanup.execute, valueFlag, allocationFlag, argumentFlag, normalizedFlag,
    Release.execute, valueCall, allocationCall, argumentCall, Except.map]
  rfl

/-- Creation OOM precedes object ownership. Only the transferred argument
errdefer runs; the normalized defer is already disabled. -/
theorem insert_transferred_create_oom (calls : Operations σ ε) (start failed after : σ)
    (createCall : ∀ owner, calls.attempt .item owner start = (.ok false, failed))
    (argumentCall : calls.release .arguments transferredArguments failed = (.ok (), after)) :
    insertProgram.execute ⟨false, true, fun _ => false⟩ calls {} start =
      ((.ok (some .allocationFailure), (Cleanup.sequence [.arguments]).run transferredArguments), after) := by
  have argumentFlag : transferredArguments.flag .arguments = true := rfl
  have normalizedFlag : (Release.arguments.run transferredArguments).flag .normalized = false := rfl
  simp only [transferredArguments, Command.success] at argumentCall argumentFlag normalizedFlag
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, createCall,
    show (some Outcome.allocationFailure == some .success) = false from rfl,
    show (some Outcome.allocationFailure == none) = false from rfl,
    Bool.false_or, Bool.true_and, Cleanup.execute, argumentFlag, normalizedFlag,
    Release.execute, argumentCall, Except.map]
  rfl

/-- Clone OOM releases the created object and transferred argument buffer.
No payload has been installed, so neither value cleanup nor publication runs. -/
theorem insert_transferred_clone_oom (calls : Operations σ ε) (start made failed destroyed after : σ)
    (createCall : ∀ owner, calls.attempt .item owner start = (.ok true, made))
    (cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok false, failed))
    (allocationCall : calls.release .allocation transferredCreated failed = (.ok (), destroyed))
    (argumentCall : calls.release .arguments (Release.allocation.run transferredCreated) destroyed = (.ok (), after)) :
    insertProgram.execute ⟨false, true, fun _ => false⟩ calls {} start =
      ((.ok (some .allocationFailure), (Cleanup.sequence [.allocation, .arguments]).run transferredCreated), after) := by
  have allocationFlag : transferredCreated.flag .allocation = true := rfl
  have argumentFlag : (Release.allocation.run transferredCreated).flag .arguments = true := rfl
  have normalizedFlag : (Release.arguments.run (Release.allocation.run transferredCreated)).flag .normalized = false := rfl
  simp only [transferredCreated, transferredArguments, Command.success]
    at allocationCall argumentCall allocationFlag argumentFlag normalizedFlag
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, createCall, cloneCall,
    show (some Outcome.allocationFailure == some .success) = false from rfl,
    show (some Outcome.allocationFailure == none) = false from rfl,
    Bool.false_or, Bool.true_and, Cleanup.execute, allocationFlag, argumentFlag, normalizedFlag,
    Release.execute, allocationCall, argumentCall, Except.map]
  rfl

end Compiler.Extraction.Storage
