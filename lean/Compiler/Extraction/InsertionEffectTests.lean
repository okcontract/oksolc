/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InsertionEffects
import Compiler.Extraction.ObservedStorageTests
import Compiler.Extraction.RecursiveFrameTests

namespace Compiler.Extraction.Interner.InsertEffectTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Recursive Contract.Yul
open ObservedTests (model caller callerHeap caller_valid)
open ObservedStorageTests (cell key binding denotation)
set_option maxRecDepth 8192

-- This controlled stream assigns one event to each fallible primitive call.
-- It tests shared state and source call order, not native allocation counts.
def attempt (failAt cursor : Nat) : Bool × Nat := (cursor != failAt, cursor + 1)
def allocation (failAt : Nat) (_ : Storage.Allocation) := attempt failAt
def before := { callerHeap with allocationCursor := 2 }
def inserted := observedInsertWith cell key true (allocation 7) before
def repeated := observedInsertWith cell key true (allocation 7) inserted.2
def rollback := observedInsertWith cell key true (allocation 6) before

theorem inserted_safe : Invariant model inserted.2 ∧ Stable before inserted.2 ∧
    inserted.2.read 1 = some cell.value :=
  observed_insert_with_safe model cell key true (allocation 7) before (caller_valid.with_cursor 2)
    binding denotation (.ok 1) inserted.2 rfl
theorem repeated_safe : Invariant model repeated.2 ∧ Stable inserted.2 repeated.2 := by
  have checked := observed_insert_with_safe model cell key true (allocation 7) inserted.2
    inserted_safe.1 binding (by rfl) (.error .outOfMemory) repeated.2 rfl
  exact ⟨checked.1, checked.2.1⟩
theorem rollback_safe : Invariant model rollback.2 ∧ Stable before rollback.2 := by
  have checked := observed_insert_with_safe model cell key true (allocation 6) before
    (caller_valid.with_cursor 2) binding denotation (.error .outOfMemory) rollback.2 rfl
  exact ⟨checked.1, checked.2.1⟩

example : inserted.1 = .ok 1 := by rfl
example : inserted.2.allocationCursor = 7 := by rfl
example : inserted.2.representatives = some [caller, cell] := by rfl
example : repeated.1 = .error .outOfMemory := by rfl
example : repeated.2 = { inserted.2 with allocationCursor := 8 } := by rfl
example : rollback = (.error .outOfMemory, { before with allocationCursor := 7 }) := by rfl

def failure (site : Fin 5) := observedInsertWith cell key true (allocation site.val) callerHeap
theorem each_failure_restores (site : Fin 5) :
    failure site = (.error .outOfMemory, { callerHeap with allocationCursor := site.val + 1 }) := by
  refine Fin.cases (by rfl) (fun site => ?_) site
  refine Fin.cases (by rfl) (fun site => ?_) site
  refine Fin.cases (by rfl) (fun site => ?_) site
  refine Fin.cases (by rfl) (fun site => ?_) site
  exact Fin.cases (by rfl) (fun site => Fin.elim0 site) site

def publicationKey := { key with sequence := 100 }
def publicationFailure := publishWith (attempt 7) publicationKey 1 inserted.2
theorem publication_safe : Safe model (publishWith (attempt 7) publicationKey 1) inserted.2 (fun _ _ => True) :=
  publish_with_safe model (attempt 7) publicationKey 1 inserted.2 cell.value inserted_safe.1 rfl rfl
example : publicationFailure = (.error .outOfMemory, { inserted.2 with allocationCursor := 8 }) := by rfl
example : publicationFailure.2.table publicationKey = none := by rfl
example : publicationFailure.2.table key = some 1 := by rfl
example : observedInsertWith cell key true (allocation 0) ObservedTests.unrepresented =
    (.error .safetyFault, ObservedTests.unrepresented) := by rfl

def takeOwned (failAt : Nat) (ids : List NodeId) : Local Unit := fun cursor =>
  if ids.isEmpty then (.ok (), cursor) else
  let (ok, cursor) := attempt failAt cursor
  (if ok then .ok () else .error .outOfMemory, cursor)
def insert (failAt : Nat) (key : Key) (deterministic : Bool) : Action NodeId := fun before =>
  observedInsertWith (FrameTests.cellFor key before) key deterministic (allocation failAt) before
def primitives (failAt : Nat) : Primitives := {
  FrameTests.primitives true true with
  takeOwned := takeOwned failAt,
  insert := insert failAt, publish := publishWith (attempt failAt)
}
theorem primitive_frames (failAt : Nat) : PrimitiveFrames (primitives failAt) where
  insert := fun key deterministic before => Frames.insertWith (FrameTests.cellFor key before)
    key deterministic (allocation failAt) before
  publish := Frames.publishWith (attempt failAt)
theorem all_depths (failAt depth : Nat) :
    FindFrames (unfold (primitives failAt) representativeReads 64 depth) :=
  unfold_frames _ (primitive_frames failAt) _ _ depth

def recursive (failAt depth : Nat) :=
  unfold (primitives failAt) representativeReads 64 depth FrameTests.request FrameTests.initial
def success := recursive 99 2
def parentFailure := recursive 6 2
def childFailure := recursive 5 2
def cached := unfold (primitives 7) representativeReads 64 1 FrameTests.request success.2

theorem recursive_retains (failAt depth : Nat) : Extends FrameTests.initial (recursive failAt depth).2 :=
  all_depths failAt depth FrameTests.request FrameTests.initial

example : success.1 = .ok 3 := by rfl
example : success.2.allocationCursor = 7 := by rfl
example : cached = (.ok 3, success.2) := by rfl
example : parentFailure.1 = .error .outOfMemory := by rfl
example : parentFailure.2.allocationCursor = 7 := by rfl
example : parentFailure.2.representatives = some (FrameTests.cells ++ [FrameTests.newCell]) := by rfl
example : parentFailure.2.table ⟨1, 1, 0, [1, 2], 77⟩ = none := by rfl
example : parentFailure.2.table ⟨2, 0, 42, [], 0⟩ = some 3 := by rfl
example : childFailure = (.error .outOfMemory, { FrameTests.initial with allocationCursor := 6 }) := by rfl
example : recursive 0 2 = (.error .outOfMemory, { FrameTests.initial with allocationCursor := 1 }) := by rfl
example : recursive 99 1 = (.error .unsupported, { FrameTests.initial with allocationCursor := 1 }) := by rfl

end Compiler.Extraction.Interner.InsertEffectTests
