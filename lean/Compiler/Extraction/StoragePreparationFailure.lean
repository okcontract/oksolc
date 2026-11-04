/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StoragePreparedRollback

namespace Compiler.Extraction.Storage

/-- The source's second capacity check precedes either argument-ownership
branch. Its only cleanup is the incoming normalized defer. -/
theorem insert_capacity_failure (calls : Operations σ ε) (deterministic : Bool) (start after : σ)
    (normalizedCall : ∀ owner, calls.release .normalized owner start = (.ok (), after)) :
    insertProgram.execute ⟨deterministic, false, fun _ => false⟩ calls {} start =
      ((.ok (some .capacityFailure), Release.normalized.run normalizedOwnership), after) := by
  have flag : normalizedOwnership.flag .normalized = true := rfl
  simp only [normalizedOwnership] at flag
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_false, ↓reduceIte, Cleanup.execute, flag, Release.execute, normalizedCall, Except.map]
  rfl

theorem insert_duplicate_oom (calls : Operations σ ε) (start failed after : σ)
    (duplicateCall : ∀ owner, calls.attempt .arguments owner start = (.ok false, failed))
    (normalizedCall : ∀ owner, calls.release .normalized owner failed = (.ok (), after)) :
    insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start =
      ((.ok (some .allocationFailure), Release.normalized.run normalizedOwnership), after) := by
  have flag : normalizedOwnership.flag .normalized = true := rfl
  simp only [normalizedOwnership] at flag
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, Bool.false_and, ↓reduceIte, duplicateCall, Cleanup.execute, flag,
    Release.execute, normalizedCall, Except.map]
  rfl


theorem insert_create_oom (calls : Operations σ ε) (start dupe failed freed after : σ)
    (duplicateCall : ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe))
    (createCall : ∀ owner, calls.attempt .item owner dupe = (.ok false, failed))
    (argumentCall : calls.release .arguments duplicatedOwnership failed = (.ok (), freed))
    (normalizedCall : ∀ owner, calls.release .normalized owner freed = (.ok (), after)) :
    insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start =
      ((.ok (some .allocationFailure), (Cleanup.sequence [.arguments, .normalized]).run duplicatedOwnership), after) := by
  have argumentFlag : duplicatedOwnership.flag .arguments = true := rfl
  have normalizedFlag : (Release.arguments.run duplicatedOwnership).flag .normalized = true := rfl
  simp only [duplicatedOwnership, normalizedOwnership, Command.success]
    at argumentCall argumentFlag normalizedFlag
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, duplicateCall, createCall,
    show (some Outcome.allocationFailure == some .success) = false from rfl,
    show (some Outcome.allocationFailure == none) = false from rfl,
    Bool.false_or, Bool.true_and, Cleanup.execute, argumentFlag, normalizedFlag,
    Release.execute, argumentCall, normalizedCall, Except.map]
  rfl


theorem insert_clone_oom (calls : Operations σ ε) (start dupe made failed destroyed freed after : σ)
    (duplicateCall : ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe))
    (createCall : ∀ owner, calls.attempt .item owner dupe = (.ok true, made))
    (cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok false, failed))
    (allocationCall : calls.release .allocation createdOwnership failed = (.ok (), destroyed))
    (argumentCall : calls.release .arguments (Release.allocation.run createdOwnership) destroyed = (.ok (), freed))
    (normalizedCall : ∀ owner, calls.release .normalized owner freed = (.ok (), after)) :
    insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start =
      ((.ok (some .allocationFailure), (Cleanup.sequence [.allocation, .arguments, .normalized]).run createdOwnership), after) := by
  have allocationFlag : createdOwnership.flag .allocation = true := rfl
  have argumentFlag : (Release.allocation.run createdOwnership).flag .arguments = true := rfl
  have normalizedFlag : (Release.arguments.run (Release.allocation.run createdOwnership)).flag .normalized = true := rfl
  simp only [createdOwnership, duplicatedOwnership, normalizedOwnership, Command.success]
    at allocationCall argumentCall allocationFlag argumentFlag normalizedFlag
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, duplicateCall, createCall, cloneCall,
    show (some Outcome.allocationFailure == some .success) = false from rfl,
    show (some Outcome.allocationFailure == none) = false from rfl,
    Bool.false_or, Bool.true_and, Cleanup.execute, allocationFlag, argumentFlag, normalizedFlag,
    Release.execute, allocationCall, argumentCall, normalizedCall, Except.map]
  rfl

/-- An append OOM occurs before transfer to the vector. Unwind the native value,
object and duplicated arguments before the outer normalized-argument defer. -/
theorem insert_append_oom (calls : Operations σ ε) (start dupe made ready failed valueFreed destroyed freed after : σ)
    (duplicateCall : ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe))
    (createCall : ∀ owner, calls.attempt .item owner dupe = (.ok true, made))
    (cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok true, ready))
    (appendCall : calls.attempt .append preparationOwnership ready = (.ok false, failed))
    (valueCall : calls.release .value preparationOwnership failed = (.ok (), valueFreed))
    (allocationCall : calls.release .allocation (Release.value.run preparationOwnership) valueFreed = (.ok (), destroyed))
    (argumentCall : calls.release .arguments (Release.allocation.run (Release.value.run preparationOwnership)) destroyed = (.ok (), freed))
    (normalizedCall : ∀ owner, calls.release .normalized owner freed = (.ok (), after)) :
    insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start =
      ((.ok (some .allocationFailure), (Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) := by
  have valueFlag : preparationOwnership.flag .value = true := rfl
  have allocationFlag : (Release.value.run preparationOwnership).flag .allocation = true := rfl
  have argumentFlag : (Release.allocation.run (Release.value.run preparationOwnership)).flag .arguments = true := rfl
  have normalizedFlag : (Release.arguments.run (Release.allocation.run (Release.value.run preparationOwnership))).flag .normalized = true := rfl
  simp only [preparationOwnership, Command.success, Bool.not_true]
    at appendCall valueCall allocationCall argumentCall valueFlag allocationFlag argumentFlag normalizedFlag
  simp only [insertProgram, Program.execute, Test.eval, Command.allocation, Command.success,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, duplicateCall, createCall, cloneCall, appendCall,
    show (some Outcome.allocationFailure == some .success) = false from rfl,
    show (some Outcome.allocationFailure == none) = false from rfl,
    Bool.false_or, Bool.true_and, Cleanup.execute, valueFlag, allocationFlag, argumentFlag, normalizedFlag,
    Release.execute, valueCall, allocationCall, argumentCall, normalizedCall, Except.map]
  rfl

end Compiler.Extraction.Storage
