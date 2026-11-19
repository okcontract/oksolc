/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerPublicationCompletion
import Compiler.Extraction.InternerCallerOriginTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.CompletionTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open OriginTests (Case source values sorted request key stack slice remaining)

/-- An unrelated live key survives both outcomes. In the replacement case it
is empty and deliberately aliases the replaced allocation instead. -/
def foreignKey (case : Case) : Key := ⟨1, 3, 0, if case = .replacement then [] else [99], 0⟩
def keys (case : Case) := OwnedKeys.store (OriginTests.keys case) (foreignKey case) ⟨2, 12⟩
def before (case : Case) : World (Effects Nat) :=
  { OriginTests.before case with
    graph := Interner.observedHeap [] (OwnedKeys.view (keys case))
    memory := { (OriginTests.before case).memory with effects := ⟨keys case, 5⟩ } }
def host := Normalization.Tests.success
def probe (accepted : Bool) : OwnedKeys.Physical.Probe Nat := fun _ memory => (accepted, memory.effects * 10 + 1)
def seed : Primitives (Effects Nat) where
  simplify := fun _ _ state => (.error (.language .unsupported), state)
  publish := fun _ _ _ state => (.error (.language .unsupported), state)
  insert := fun _ _ _ state => (.error (.language .unsupported), state)
def initialized (case : Case) := Caller.initLookup (external host) 160 11 (source case) ⟨3, 0, 2⟩ (request case)
  ⟨{ before case with memory := { (before case).memory with memory := stack case } }, { lookup := none }⟩
def taken (case : Case) := take (external host) 11 (initialized case).2
def execute (case : Case) (accepted : Bool) :=
  let (result, reached) := Interner.forceCode.controlOwned
    (OwnedCall.execution (external host) 11 (callbacks (probe accepted) host 11 (source case) seed))
    (request case) (sorted case) 42 (initialized case).2
  finish (external host) 11 result reached

theorem initial_good (case : Case) : Good (source case) (request case).arguments (before case) := by
  have good := OriginTests.initial_good case
  exact ⟨⟨good.1.memory, good.1.related, good.1.injected⟩, good.2⟩

theorem foreign_different (case : Case) : key case ≠ foreignKey case := by
  cases case <;> decide +kernel

theorem initial_keys (case : Case) : OwnedKeys.Live 11 ⟨(before case).memory.effects.keys, (before case).memory.heap⟩ ∧
    OwnedKeys.Unique (before case).memory.effects.keys ∧
    (∀ old, (before case).memory.effects.keys (key case) = some old → (key case).arguments ≠ [] →
      (source case).length ≠ 0 → (source case).allocation ≠ old.address) := by
  have baseLive : OwnedKeys.Live 11 ⟨OriginTests.keys case, (OriginTests.before case).memory.heap⟩ := by
    intro query entry found
    change OriginTests.keys case query = some entry at found
    by_cases same : query = key case
    · subst query; exact (OriginTests.initial_keys case).1 entry found
    · have absent : OriginTests.keys case query = none := by
        cases case <;> simp [OriginTests.keys, OwnedKeys.store, same]
      rw [absent] at found; cases found
  have emptyUnique : OwnedKeys.Unique (fun _ => none) := by intro _ _ _ _ impossible; cases impossible
  have emptyFresh (key : Key) (entry : OwnedKeys.Entry) : OwnedKeys.Fresh (fun _ => none) key entry := by
    intro _ _ impossible; cases impossible
  have baseUnique : OwnedKeys.Unique (OriginTests.keys case) := by
    cases case <;> first
    | exact emptyUnique
    | exact OwnedKeys.store_unique _ _ _ emptyUnique (emptyFresh _ _)
  have fresh : OwnedKeys.Fresh (OriginTests.keys case) (foreignKey case) ⟨2, 12⟩ := by
    intro old entry found nonempty oldNonempty
    by_cases same : old = key case
    · subst old
      cases case <;> first
      | exact False.elim (nonempty rfl)
      | exact False.elim (oldNonempty rfl)
      | cases found
    · have absent : OriginTests.keys case old = none := by
        cases case <;> simp [OriginTests.keys, OwnedKeys.store, same]
      rw [absent] at found; cases found
  refine ⟨?_, OwnedKeys.store_unique _ _ _ baseUnique fresh, ?_⟩
  · intro query entry found
    change OwnedKeys.store (OriginTests.keys case) (foreignKey case) ⟨2, 12⟩ query = some entry at found
    by_cases same : query = foreignKey case
    · subst query
      simp only [OwnedKeys.store, ↓reduceIte, Option.some.injEq] at found
      subst entry
      cases case <;> first | exact Or.inl rfl | exact Or.inr (by rfl')
    · simp only [OwnedKeys.store, if_neg same] at found
      exact baseLive query entry found
  · intro old found
    change OwnedKeys.store (OriginTests.keys case) (foreignKey case) ⟨2, 12⟩ (key case) = some old at found
    simp only [OwnedKeys.store, if_neg (foreign_different case)] at found
    exact (OriginTests.initial_keys case).2 old found

theorem prefix_results (case : Case) :
    Compiler.ZigAir.Memory.allocate (before case).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨3, 0⟩, stack case) ∧
    (initialized case).1 = .ok (sorted case) ∧ (taken case).1 = .ok () ∧
    (taken case).2.scope = ⟨some (remaining case), some (slice case), false⟩ := by
  cases case <;> exact ⟨by rfl', by rfl', by rfl', by rfl'⟩

/-- Exercise the composed theorem, rather than supplying final liveness,
cleanup or table-correspondence premises. Cache routing and recursive calls
are intentionally outside this owned-continuation fixture. -/
theorem derived_completion (case : Case) (accepted : Bool) :
    (execute case accepted).1 = (if accepted then .ok () else .error (.language .outOfMemory)) ∧
    Completion host 11 (source case) (request case) (key case) (slice case) 42 (before case) (taken case).2.world
      accepted ((taken case).2.world.memory.effects.allocator * 10 + 1) (execute case accepted).2 ∧
    (execute case accepted).2.world.graph.table = OwnedKeys.view (execute case accepted).2.world.memory.effects.keys := by
  have calls := prefix_results case
  have initializedCall : initialized case = (.ok (sorted case), (initialized case).2) := Prod.ext calls.2.1 rfl
  obtain ⟨owned, handle, after, origin, ran, completed, linked⟩ := caller_owned_publication (probe accepted) host 160 11 (source case) seed
    (request case) (before case) (stack case) _ (sorted case) (initialized case).2 (taken case).2 (key case) 42 accepted
    ((taken case).2.world.memory.effects.allocator * 10 + 1)
    (initial_good case) (Normalization.Tests.external_admitted _) calls.1
    (by simpa only [show (before case).memory.memory.nextId = 3 by cases case <;> rfl] using initializedCall)
    (Prod.ext calls.2.2.1 rfl) (OriginTests.prefix_results case).2.2.2.2
    (initial_keys case).1 (initial_keys case).2.1 (initial_keys case).2.2 rfl
  have scope := Local.mk.inj (origin.scope.symm.trans calls.2.2.2)
  cases Option.some.inj scope.1
  cases Option.some.inj scope.2.1
  have same : execute case accepted = (if accepted then .ok () else .error (.language .outOfMemory), after) := ran
  rw [same]
  exact ⟨rfl, completed, linked rfl⟩

def observation (case : Case) (accepted : Bool) :=
  let state := (execute case accepted).2
  (state.world.memory.effects.allocator, state.world.memory.memory.nextId, state.scope,
    (state.world.memory.heap 2).isSome, (state.world.memory.memory.heap.lookup 2).isSome,
    (state.world.memory.heap (slice case).address).isSome, (state.world.memory.memory.heap.lookup 0).isSome,
    state.world.memory.effects.keys (key case), state.world.memory.effects.keys (foreignKey case))

theorem reached_observations (case : Case) (accepted : Bool) : observation case accepted =
    (if accepted then (match case with | .temporary => 171 | .scratch | .offsetBorrow => 131 | .replacement => 192 | _ => 51)
      else (match case with | .temporary => 274 | .scratch | .offsetBorrow => 233 | .replacement => 192 | _ => 51),
     match case with | .temporary => 7 | .scratch => 6 | .offsetBorrow | .replacement => 5 | _ => 4,
     if accepted then ⟨none, some (slice case), true⟩ else ⟨none, none, false⟩,
     !(accepted && case == .replacement), !(accepted && case == .replacement),
     accepted && !(slice case).items.isEmpty, true,
     if accepted then some ⟨(slice case).address, 42⟩ else OriginTests.keys case (key case), some ⟨2, 12⟩) := by
  cases case <;> cases accepted <;> rfl'

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.CompletionTests
