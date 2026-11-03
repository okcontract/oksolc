/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolInitializedMiss
import Compiler.Extraction.InternerMissInitializedTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.TakenTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Interner.InvocationTrace
open Insertion.Native CallerSpareSuccessTests
open CallerInputTests (request key values)

/-- Reuse the populated spare fixture's actual allocation, initialization and
take in both native layouts and argument shapes. The body reaches the same
recorded miss for either source guard whenever that guard selects a miss. -/
theorem spare_prefix (safety empty deterministic : Bool)
    (p : Primitives (Publication.Effects Nat)) (q : Queries)
    (observations : GraphObservations (Publication.Effects Nat))
    (leading suffix : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (room : q.atCapacity (before safety empty).graph = false)
    (classified : q.deterministic (request empty).item = .ok deterministic)
    (absent : deterministic = true → (before safety empty).graph.table (key empty) = none) :
    let external := Publication.external ops.arguments
    let buffer : View := ⟨(before safety empty).memory.memory.nextId, 0, 2⟩
    let start := { before safety empty with memory := { (before safety empty).memory with memory := Publication.GraphTests.stack safety empty } }
    let init := Initialization.capture external 160 7 false (argumentView empty) buffer (request empty).arguments start.memory
    ∃ lookupToken, init.1 = .ok (some lookupToken) ∧
      let transfer := Take.capture external 7 lookupToken.origin init.2.effects.handle (prepared safety empty).2.world.memory
      let missLeading := leading ++ init.2.events.map Event.normalization ++ transfer.2.events.map Event.normalization
      let entry : Recorded (Publication.Effects Nat) := ⟨(taken safety empty).2,
        { lookup := some transfer.1.2, items := (lookup empty).values, phase := .cleanup }, missLeading⟩
      let r := resources (missLeading ++ suffix) (.preparation .incomplete)
      let initialScope := Interner.Scoped.initScope r (request empty)
        ⟨{}, { (before safety empty).graph with allocationCursor := leading.length }⟩
      transfer.1.2.owned = false ∧ transfer.1.2.owner = .caller ∧
      initialScope.1 = .ok (values empty) ∧ Interner.Scoped.take r initialScope.2 = (.ok (), scopeView entry) ∧
      findBody external 160 7 p q observations (argumentView empty) buffer (request empty)
        ⟨⟨start, { lookup := none }⟩, {}, leading⟩ =
        missBody external 160 7 p q observations (argumentView empty) buffer (request empty) (key empty) deterministic entry := by
  intro external buffer start init
  have calls := Publication.GraphTests.prefix_results safety empty
  have good := (CallerFirstSuccessTests.native_borrow_good safety empty).2
  obtain ⟨lookupToken, captured, composed⟩ := initialized_taken_recorded external 160 7 false (argumentView empty)
    (request empty) (before safety empty) (Publication.GraphTests.stack safety empty) _ (values empty)
    (prepared safety empty).2 (taken safety empty).2 leading other read sequence good.1 good.2 calls.1
    (by cases empty <;> rfl) (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (Prod.ext calls.2.1 rfl) (Prod.ext calls.2.2.1 rfl)
  refine ⟨lookupToken, captured, ?_⟩
  intro transfer missLeading entry r initialScope
  obtain ⟨slice, remaining, locals, _, _, unowned, caller, _, normalizedResult, takenRecord, prefixProof⟩ := composed
  have same := locals.symm.trans calls.2.2.2
  have sameHandle := Option.some.inj (congrArg Local.lookup same)
  subst remaining
  obtain ⟨initialResult, takeResult, takeState⟩ := prefixProof suffix
  refine ⟨unowned, caller, initialResult, Prod.ext takeResult takeState, ?_⟩
  exact findBody_taken external 160 7 p q observations (argumentView empty) buffer (request empty) (key empty) deterministic
    (values empty) _ _ entry room (Prod.ext normalizedResult rfl) classified
    (CallerInputTests.prefix_results safety empty).2.2.2.2 absent takenRecord

/-- A nondeterministic caller takes ownership even when its original graph
contains the same key. This is a source-routing regression: the classifier is
selected explicitly, while all memory and ownership are the existing fixture. -/
theorem nondeterministic_spare (safety empty : Bool)
    (p : Primitives (Publication.Effects Nat)) (observations : GraphObservations (Publication.Effects Nat))
    (leading suffix : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let q : Queries := { Interner.Queries.queries with atCapacity := fun _ => false, deterministic := fun _ => .ok false }
    let external := Publication.external ops.arguments
    let buffer : View := ⟨(before safety empty).memory.memory.nextId, 0, 2⟩
    let start := { before safety empty with memory := { (before safety empty).memory with memory := Publication.GraphTests.stack safety empty } }
    (before safety empty).graph.table (key empty) = some 0 ∧
    ∃ entry : Recorded (Publication.Effects Nat), entry.native = (taken safety empty).2 ∧
      entry.tokens.phase = .cleanup ∧ entry.tokens.incomplete = false ∧
      findBody external 160 7 p q observations (argumentView empty) buffer (request empty)
        ⟨⟨start, { lookup := none }⟩, {}, leading⟩ =
        missBody external 160 7 p q observations (argumentView empty) buffer (request empty) (key empty) false entry := by
  intro q external buffer start
  refine ⟨?_, ?_⟩
  · cases safety <;> cases empty <;> insertion_kernel_rfl
  obtain ⟨lookupToken, _, composed⟩ := spare_prefix safety empty false p q observations leading suffix other read sequence rfl rfl
    (by intro impossible; cases impossible)
  exact ⟨_, rfl, rfl, rfl, composed.2.2.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.TakenTests
