/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ScopedRecursiveSemantics
import Compiler.Extraction.ScopedFrameTests

namespace Compiler.Extraction.Interner.Scoped.SemanticTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open Compiler.Extraction.Recursive.Tests (model env base pushes)
set_option maxRecDepth 8192

/-- Fixture denotations are ghost values, never native constant reads. This
reuses the source-bound insertion transaction, and rejects a cell/key mismatch
instead of assuming that any supplied representative is coherent. -/
def cellFor (key : Key) (before : Heap) (value : Word) : Storage.Cell :=
  { Recursive.FrameTests.cellFor key before with otherValue := value }

def insert (failAt : Nat) (key : Key) (deterministic : Bool) : Interner.Action NodeId := fun before =>
  match key.eval model before.read with
  | none => (.error .unsupported, before)
  | some value =>
    let cell := cellFor key before value
    if keyCode.run cell.item cell.arguments cell.sequence = some key ∧ cell.value = value then
      observedInsertWith cell key deterministic (InsertEffectTests.allocation failAt) before
    else (.error .unsupported, before)

theorem insert_safe (failAt : Nat) (key : Key) (deterministic : Bool) (before : Heap) (value : Word)
    (valid : Invariant model before) (evaluated : key.eval model before.read = some value) :
    Interner.Safe model (insert failAt key deterministic) before (fun id after => after.read id = some value) := by
  let cell := cellFor key before value
  by_cases admitted : keyCode.run cell.item cell.arguments cell.sequence = some key ∧ cell.value = value
  · dsimp only [cell] at admitted
    have checked := observed_insert_with_safe model cell key deterministic (InsertEffectTests.allocation failAt)
      before valid admitted.1 (by rw [admitted.2]; exact evaluated)
    have cellValue : cell.value = value := admitted.2
    intro result after ran
    simp only [insert, evaluated, admitted] at ran
    simpa only [cellValue] using checked result after ran
  · dsimp only [cell] at admitted
    intro result after ran
    simp only [insert, evaluated, admitted, ↓reduceIte] at ran
    cases ran
    exact ⟨valid, fun _ _ found => found, trivial⟩

theorem insert_frames (failAt : Nat) (key : Key) (deterministic : Bool) :
    Interner.Frames (insert failAt key deterministic) := by
  intro before
  unfold insert
  cases evaluated : key.eval model before.read with
  | none => exact Extends.refl before
  | some value =>
    simp only []
    split
    · exact Interner.Frames.insertWith (cellFor key before value) key deterministic (InsertEffectTests.allocation failAt) before
    · exact Extends.refl before

def primitives (failAt : Nat) : Primitives := { InsertEffectTests.primitives failAt with insert := insert failAt }

theorem graph_contracts (failAt : Nat) : GraphContracts model (primitives failAt) where
  insert := insert_safe failAt
  publish := publish_with_safe model (InsertEffectTests.attempt failAt)

theorem graph_frames (failAt : Nat) : Recursive.PrimitiveFrames (primitives failAt) where
  insert := insert_frames failAt
  publish := Interner.Frames.publishWith (InsertEffectTests.attempt failAt)

theorem sort_permutation (failAt : Nat) (ids : List NodeId) : ((Tests.resources failAt).sort ids).Perm ids :=
  List.reverse_perm ids

theorem initial_valid : Invariant model Recursive.FrameTests.initial := by
  apply observed_invariant model _ _ (by intro key id found; cases found)
  intro cell member
  simp only [Recursive.FrameTests.cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same <;> subst cell <;> rfl

def result (failAt depth : Nat) := ScopedRecursive.detailed (Tests.resources failAt) (primitives failAt)
  representativeReads 64 depth Recursive.FrameTests.request Recursive.FrameTests.initial

theorem all_depths_verified (failAt depth : Nat) :
    Invariant model (result failAt depth).2.heap ∧ Stable Recursive.FrameTests.initial (result failAt depth).2.heap ∧
      Extends Recursive.FrameTests.initial (result failAt depth).2.heap ∧ Closed (result failAt depth).2.scope ∧
      match (result failAt depth).1 with | .error _ => True | .ok id => (result failAt depth).2.heap.read id = some 42 :=
  ScopedRecursive.detailed_verified env base pushes (Tests.resources failAt) (sort_permutation failAt)
    (primitives failAt) (graph_contracts failAt) (graph_frames failAt) 64 depth
    Recursive.FrameTests.request Recursive.FrameTests.initial 42 initial_valid rfl

theorem success : (result 99 2).1 = .ok 3 ∧ (result 99 2).2.heap.read 3 = some 42 ∧
    Invariant model (result 99 2).2.heap ∧ Closed (result 99 2).2.scope :=
  ⟨rfl, (all_depths_verified 99 2).2.2.2.2, (all_depths_verified 99 2).1, (all_depths_verified 99 2).2.2.2.1⟩

theorem failed_parent_retains_semantics : (result 6 2).1 = .error .outOfMemory ∧
    (result 6 2).2.heap.read 3 = some 42 ∧ (result 6 2).2.heap.allocationCursor = 8 ∧
    Invariant model (result 6 2).2.heap ∧ Closed (result 6 2).2.scope :=
  ⟨rfl, rfl, rfl, (all_depths_verified 6 2).1, (all_depths_verified 6 2).2.2.2.1⟩

def next := ScopedRecursive.detailed (Tests.resources 8) (primitives 8) representativeReads 64 2
  Tests.nextRequest (result 6 2).2.heap

theorem repeated_failure_preserves : next.1 = .error .outOfMemory ∧ next.2.heap.allocationCursor = 9 ∧
    Invariant model next.2.heap ∧ Stable (result 6 2).2.heap next.2.heap ∧ Closed next.2.scope := by
  have checked := ScopedRecursive.detailed_verified env base pushes (Tests.resources 8) (sort_permutation 8)
    (primitives 8) (graph_contracts 8) (graph_frames 8) 64 2 Tests.nextRequest (result 6 2).2.heap
    42 (all_depths_verified 6 2).1 rfl
  exact ⟨rfl, rfl, checked.1, checked.2.1, checked.2.2.2.1⟩

theorem cutoff_preserves : (result 99 1).1 = .error .unsupported ∧
    Invariant model (result 99 1).2.heap ∧ Closed (result 99 1).2.scope :=
  ⟨rfl, (all_depths_verified 99 1).1, (all_depths_verified 99 1).2.2.2.1⟩

theorem completed : ScopedRecursive.Executes (Tests.resources 99) (primitives 99) representativeReads 64
    Recursive.FrameTests.request Recursive.FrameTests.initial (.ok 3) (result 99 2).2.heap :=
  ⟨2, rfl, by intro impossible; cases impossible⟩

theorem cutoff_not_completed : ¬ScopedRecursive.Executes (Tests.resources 99) (primitives 99) representativeReads 64
    Recursive.FrameTests.request Recursive.FrameTests.initial (.error .unsupported) (result 99 1).2.heap :=
  ScopedRecursive.unsupported_not_execution _ _ _ _ _ _ _

theorem force_equal_safe (failAt : Nat) :
    Interner.Safe model (force (Tests.resources failAt) (primitives failAt) (fun _ _ => .ok ())
      1 ⟨2, none, 10⟩ []) Recursive.FrameTests.initial (fun _ _ => True) :=
  force_safe (Dispatch.wordBaseMeaning env base) (Tests.resources failAt) (sort_permutation failAt)
    (primitives failAt) (graph_contracts failAt).publish (fun _ _ => .ok ()) 1 ⟨2, none, 10⟩ []
    Recursive.FrameTests.initial 10 initial_valid rfl rfl

def rejectedKey : Key := ⟨2, 1, 9, [], 0⟩
theorem unbound_fixture_key_rejected : insert 99 rejectedKey true Recursive.FrameTests.initial =
    (.error .unsupported, Recursive.FrameTests.initial) := rfl

-- Negative witnesses isolate the remaining primitive premises. Ownership and
-- graph preservation alone do not prove normalization or returned word values.
def badSort : Resources := { Tests.resources 99 with sort := fun _ => [1, 1] }
def changed := ScopedRecursive.detailed badSort (primitives 99) representativeReads 64 2
  Recursive.FrameTests.request Recursive.FrameTests.initial

theorem bad_sort_changes_value : changed.1 = .ok 3 ∧ changed.2.heap.read 3 = some 20 ∧ Closed changed.2.scope :=
  ⟨rfl, rfl, ScopedRecursive.all_scopes_closed _ _ _ _ _ _ _⟩

theorem bad_sort_not_permutation : ¬(badSort.sort [2, 1]).Perm [2, 1] := by decide

def wrongForce := forceDetailed (Tests.resources 99) (primitives 99) (fun _ _ => .ok ())
  1 Recursive.FrameTests.request.item Recursive.FrameTests.request.arguments Recursive.FrameTests.initial

theorem wrong_force_closed : wrongForce.1 = .ok () ∧ Closed wrongForce.2.scope :=
  ⟨rfl, force_closed _ _ _ _ _ _ _⟩

theorem wrong_force_invalid : ¬Invariant model wrongForce.2.heap := by
  intro valid
  obtain ⟨value, denotation, actual⟩ := valid.cache ⟨1, 1, 0, [1, 2], 0⟩ 1 rfl
  have same : value = 42 := Option.some.inj denotation.symm
  subst value
  have impossible : (10 : Word) = 42 := Option.some.inj actual
  exact (by decide : (10 : Word) ≠ 42) impossible

end Compiler.Extraction.Interner.Scoped.SemanticTests
