/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerPublicationInput
import Compiler.Extraction.NormalizationMemoryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.OriginTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

inductive Case where
  | temporary | scratch | offsetBorrow | empty | replacement | emptyAlias
  deriving DecidableEq, Repr

def source : Case → View
  | .temporary => ⟨0, 0, 3⟩
  | .scratch => ⟨0, 0, 2⟩
  | .offsetBorrow => ⟨0, 1, 2⟩
  | .replacement => ⟨0, 0, 1⟩
  | _ => ⟨900, 90, 0⟩
def values : Case → List NodeId
  | .temporary => [3, 1, 2]
  | .scratch => [3, 1]
  | .offsetBorrow => [1, 2]
  | .replacement => [99]
  | _ => []
def sorted : Case → List NodeId
  | .temporary => [1, 2, 3]
  | .scratch => [1, 3]
  | other => values other
def request (case : Case) := Interner.constructorCode.operationRequest (if case = .offsetBorrow then 3 else 1) (values case)
def key (case : Case) := (Interner.makeKey (request case) (sorted case)).toOption.getD ⟨0, 0, 0, [], 0⟩
def keys (case : Case) : OwnedKeys.Table :=
  if case = .replacement then OwnedKeys.store (fun _ => none) (key case) ⟨2, 8⟩
  else if case = .emptyAlias then OwnedKeys.store (fun _ => none) (key case) ⟨4, 9⟩ else fun _ => none
def native (case : Case) : Compiler.ZigAir.Memory.State :=
  if case = .replacement then
    { Normalization.Tests.original.memory with heap := [(0, ⟨16, .array 3 word,
      [(0, number 99), (4, number 1), (8, number 2)], true, false⟩), (2, PreparationTests.otherCell)] }
  else Normalization.Tests.original.memory
def before (case : Case) : World (Effects Nat) :=
  ⟨Interner.observedHeap [] (OwnedKeys.view (keys case)),
    ⟨Normalization.Tests.original.heap, native case, ⟨keys case, 5⟩⟩⟩
def stack (case : Case) : Compiler.ZigAir.Memory.State :=
  { native case with heap := (3, Normalization.Tests.scratchCell) :: (native case).heap, nextId := 4, nextAddress := 60 }
def initialized (case : Case) := Caller.initLookup (external Normalization.Tests.success) 160 11 (source case) ⟨3, 0, 2⟩ (request case)
  ⟨{ before case with memory := { (before case).memory with memory := stack case } }, { lookup := none }⟩
def taken (case : Case) := take (external Normalization.Tests.success) 11 (initialized case).2
def slice (case : Case) : ArgumentSlice := ⟨if case = .scratch then 5 else 4, sorted case⟩
def remaining (case : Case) : Handle :=
  ⟨match case with
    | .temporary => ⟨4, 0, 3⟩
    | .scratch => ⟨3, 0, 2⟩
    | _ => source case, sorted case, none⟩

theorem initial_good (case : Case) : Good (source case) (request case).arguments (before case) := by
  have two : ∀ id block, Normalization.Tests.original.heap id = some block → id = 2 := by
    intro id block stored
    by_cases address : id = 2
    · exact address
    · by_cases one : id = 1 <;>
        simp [Normalization.Tests.original, Allocation.Tests.logical, PreparationTests.logical, write, address, one] at stored
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · cases case <;> decide +kernel
  · intro allocator id items nonempty stored
    have address := two id _ stored
    subst id
    have old := Normalization.Tests.original_valid.related allocator 2 items nonempty stored
    cases case <;> exact old
  · intro id block stored
    have address := two id block stored
    subst id
    cases case <;> exact ⟨PreparationTests.otherCell, by rfl', rfl⟩
  · cases case <;> refine ⟨rfl, ?_⟩ <;> intro index inside
    all_goals simp only [request, Interner.ConstructorCode.operationRequest, values, List.length_cons, List.length_nil] at inside
    all_goals have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    all_goals rcases cases with rfl | rfl | rfl <;> first | (exfalso; omega) | rfl'

theorem prefix_results (case : Case) :
    Compiler.ZigAir.Memory.allocate (before case).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨3, 0⟩, stack case) ∧
    (initialized case).1 = .ok (sorted case) ∧ (taken case).1 = .ok () ∧
    (taken case).2.scope = ⟨some (remaining case), some (slice case), false⟩ ∧
    Interner.makeKey (request case) (sorted case) = .ok (key case) := by
  cases case <;> exact ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem initial_keys (case : Case) :
    (∀ old, (before case).memory.effects.keys (key case) = some old →
      SliceValid 11 (before case).memory.heap (OwnedKeys.slice (key case) old)) ∧
    (∀ old, (before case).memory.effects.keys (key case) = some old → (key case).arguments ≠ [] →
      (source case).length ≠ 0 → (source case).allocation ≠ old.address) := by
  cases case <;> constructor <;> intro old found
  all_goals simp [before, keys, OwnedKeys.store] at found
  all_goals first | contradiction | subst old
  · exact Or.inr (by rfl')
  · intro _ _; decide
  · exact Or.inl rfl
  · intro nonempty; exact False.elim (nonempty rfl)

/-- All ownership and local admission facts come from the production caller
theorem, including a live replaced key and an empty key aliasing the incoming
sentinel. The exact reached prefix is independently evaluated above. -/
theorem derived_input (case : Case) :
    Caller.Origin 11 (source case) (request case) (sorted case) (before case) (taken case).2 (slice case) (remaining case) ∧
    Input 11 (source case) (key case) (slice case) (taken case).2.world := by
  have ran := prefix_results case
  have initRan : initialized case = (.ok (sorted case), (initialized case).2) := Prod.ext ran.2.1 rfl
  obtain ⟨owned, handle, origin, _, input⟩ := caller_input Normalization.Tests.success 160 11 (source case)
    (request case) (before case) (stack case) _ (sorted case) (initialized case).2 (taken case).2 (key case)
    (initial_good case) (Normalization.Tests.external_admitted _) ran.1
    (by simpa only [show (before case).memory.memory.nextId = 3 by cases case <;> rfl] using initRan)
    (Prod.ext ran.2.2.1 rfl) ran.2.2.2.2 (initial_keys case).1 (initial_keys case).2
  have scopes := origin.scope.symm.trans ran.2.2.2.1
  have same := Local.mk.inj scopes
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact ⟨origin, input⟩

theorem reached_observations (case : Case) :
    ((taken case).2.world.memory.effects.allocator, (taken case).2.world.memory.memory.nextId) =
      (match case with
        | .temporary => (17, 7)
        | .scratch => (13, 6)
        | .offsetBorrow => (13, 5)
        | .replacement => (9, 5)
        | _ => (5, 4)) := by
  cases case <;> rfl'

theorem outer_deinit (case : Case) (reached : World (Effects Nat)) (handedOff : Bool) :
    deinit (external Normalization.Tests.success) 11 ⟨reached, { (taken case).2.scope with handedOff }⟩ =
      (.ok (), ⟨reached, { (taken case).2.scope with lookup := none, handedOff }⟩) :=
  (derived_input case).1.deinit (external Normalization.Tests.success) 11 (source case) (request case)
    (sorted case) (before case) (taken case).2 (slice case) (remaining case) reached handedOff

def failed := take (external (Normalization.Tests.external (fun _ => true))) 11 (initialized .replacement).2

theorem duplicate_oom : failed.1 = .error (.language .outOfMemory) ∧
    failed.2.world.memory.effects.allocator = 9 ∧
    failed.2.world.memory.effects.keys (key .replacement) = some ⟨2, 8⟩ ∧
    failed.2.world.memory.heap 2 = some ⟨11, .arguments [99]⟩ ∧
    failed.2.scope.slice = none := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def incompleteResult := Caller.initLookup (external Normalization.Tests.success) 0 11 (source .temporary) ⟨3, 0, 2⟩ (request .temporary)
  ⟨{ before .replacement with memory := { (before .replacement).memory with memory := stack .temporary } }, { lookup := none }⟩

theorem incomplete_initialization : incompleteResult.1 = .error (.memory (.preparation .incomplete)) ∧
    incompleteResult.2.world.memory.effects.allocator = 17 ∧
    incompleteResult.2.world.memory.effects.keys (key .replacement) = some ⟨2, 8⟩ ∧
    incompleteResult.2.world.memory.heap 4 = some ⟨11, .arguments [3, 1, 2]⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.OriginTests
