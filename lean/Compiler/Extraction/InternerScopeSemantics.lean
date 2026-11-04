/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerScopeFrames

namespace Compiler.Extraction.Interner.Scoped
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Semantic preservation observes the actual heap reached by scoped execution,
including its allocator cursor. Cleanup is not erased from subsequent calls. -/
def Safe (meaning : Meaning) (action : Action α) (before : Session) (post : α → Heap → Prop) : Prop :=
  ∀ result after, action before = (result, after) →
    Invariant meaning after.heap ∧ Stable before.heap after.heap ∧
      match result with | .error _ => True | .ok value => post value after.heap

theorem Safe.pure (meaning : Meaning) (before : Session) (value : α) (post : α → Heap → Prop)
    (valid : Invariant meaning before.heap) (fact : post value before.heap) :
    Safe meaning (pure value) before post := by
  intro result after ran
  cases ran
  exact ⟨valid, fun _ _ h => h, fact⟩

theorem Safe.graph (meaning : Meaning) (action : Interner.Action α) (before : Session)
    (post : α → Heap → Prop) (safe : Interner.Safe meaning action before.heap post) :
    Safe meaning (liftGraph action) before post := by
  intro result after ran
  cases step : action before.heap with
  | mk outcome heap =>
    simp only [liftGraph, step] at ran
    cases ran
    exact safe result heap step

theorem Safe.bind (meaning : Meaning) (before : Session) (first : Action α) (next : α → Action β)
    (middle : α → Heap → Prop) (post : β → Heap → Prop)
    (safeFirst : Safe meaning first before middle)
    (safeNext : ∀ value after, Invariant meaning after.heap → Stable before.heap after.heap → middle value after.heap →
      Safe meaning (next value) after post) : Safe meaning (first >>= next) before post := by
  intro result after ran
  change Effect.bind first next before = (result, after) at ran
  cases step : first before with
  | mk outcome current =>
    obtain ⟨valid, stable, fact⟩ := safeFirst outcome current step
    cases outcome with
    | error error =>
      simp only [Effect.bind, step] at ran
      cases ran
      exact ⟨valid, stable, trivial⟩
    | ok value =>
      have final := safeNext value current valid stable fact result after
        (by simpa only [Effect.bind, step] using ran)
      exact ⟨final.1, stable.trans final.2.1, final.2.2⟩

theorem Safe.local (meaning : Meaning) (action : Action α) (before : Session)
    (localEffect : LocalEffect action) (valid : Invariant meaning before.heap) :
    Safe meaning action before (fun _ _ => True) := by
  intro result after ran
  have frame := localEffect before
  rw [ran] at frame
  have afterValid : Invariant meaning after.heap := by rw [frame]; exact valid.with_cursor _
  refine ⟨afterValid, ?_, ?_⟩
  · intro id value found
    rw [show after.heap.read = before.heap.read by rw [frame]]
    exact found
  · cases result <;> trivial

theorem local_bind_safe (meaning : Meaning) (action : Action α) (next : α → Action β)
    (before : Session) (post : β → Heap → Prop) (localEffect : LocalEffect action)
    (valid : Invariant meaning before.heap)
    (continuation : ∀ value after, action before = (.ok value, after) → Invariant meaning after.heap →
      after.heap = { before.heap with allocationCursor := after.heap.allocationCursor } →
      Safe meaning (next value) after post) : Safe meaning (action >>= next) before post := by
  intro result after ran
  change Effect.bind action next before = (result, after) at ran
  cases step : action before with
  | mk outcome current =>
    have frame := localEffect before
    rw [step] at frame
    have safe := Safe.local meaning action before localEffect valid outcome current step
    cases outcome with
    | error error =>
      simp only [Effect.bind, step] at ran
      cases ran
      exact ⟨safe.1, safe.2.1, trivial⟩
    | ok value =>
      have final := continuation value current step safe.1 frame result after
        (by simpa only [Effect.bind, step] using ran)
      exact ⟨final.1, safe.2.1.trans final.2.1, final.2.2⟩

theorem lift_bind_safe (meaning : Meaning) (result : Except Error α) (next : α → Action β)
    (before : Session) (post : β → Heap → Prop) (valid : Invariant meaning before.heap)
    (continuation : ∀ value, result = .ok value → Safe meaning (next value) before post) :
    Safe meaning (liftGraph (Interner.lift result) >>= next) before post := by
  cases result with
  | error error =>
    intro outcome after ran
    change (Except.error error, before) = (outcome, after) at ran
    cases ran
    exact ⟨valid, fun _ _ h => h, trivial⟩
  | ok value => exact continuation value rfl

theorem get_bind_safe (meaning : Meaning) (next : Heap → Action α) (before : Session)
    (post : α → Heap → Prop) (safe : Safe meaning (next before.heap) before post) :
    Safe meaning (liftGraph Interner.get >>= next) before post := safe

/-- Only graph primitives remain abstract. Normalization and ownership transfer
are executed by the scoped model; they have no opaque callback premise. -/
structure GraphContracts (meaning : Meaning) (p : Primitives) : Prop where
  insert : ∀ key deterministic before value, Invariant meaning before → key.eval meaning before.read = some value →
    Interner.Safe meaning (p.insert key deterministic) before (fun id after => after.read id = some value)
  publish : Publishes meaning p

/-- The source calls simplification only on operation keys. The key-kind link
is proved at the actual makeKey site, avoiding an extra interpreter guard. -/
structure Contracts (meaning : Meaning) (p : Primitives) : Prop extends GraphContracts meaning p where
  simplify : ∀ key, key.kind = 1 → ∀ before value, Invariant meaning before → key.eval meaning before.read = some value →
    Interner.Safe meaning (p.simplify key) before (fun result after => ∀ id, result = some id → after.read id = some value)

/-- An entry only needs graph laws for keys produced by that entry. The
predicate restricts inputs, never outcomes or reached heaps. -/
structure GraphContractsFor (meaning : Meaning) (p : Primitives) (allowed : Key → Prop) : Prop where
  insert : ∀ key, allowed key → ∀ deterministic before value,
    Invariant meaning before → key.eval meaning before.read = some value →
    Interner.Safe meaning (p.insert key deterministic) before (fun id after => after.read id = some value)
  publish : Publishes meaning p

structure ContractsFor (meaning : Meaning) (p : Primitives) (allowed : Key → Prop) : Prop
    extends GraphContractsFor meaning p allowed where
  simplify : ∀ key, allowed key → key.kind = 1 → ∀ before value,
    Invariant meaning before → key.eval meaning before.read = some value →
    Interner.Safe meaning (p.simplify key) before (fun result after => ∀ id, result = some id → after.read id = some value)

theorem GraphContracts.restrict (meaning : Meaning) (p : Primitives) (allowed : Key → Prop)
    (contracts : GraphContracts meaning p) : GraphContractsFor meaning p allowed :=
  ⟨fun key _ => contracts.insert key, contracts.publish⟩

theorem Contracts.restrict (meaning : Meaning) (p : Primitives) (allowed : Key → Prop)
    (contracts : Contracts meaning p) : ContractsFor meaning p allowed :=
  ⟨contracts.toGraphContracts.restrict meaning p allowed, fun key _ => contracts.simplify key⟩

theorem handoff_insert_safe_for (meaning : Meaning) (p : Primitives) (allowed : Key → Prop) (contracts : GraphContractsFor meaning p allowed)
    (key : Key) (admissible : allowed key) (deterministic : Bool) (before : Session) (value : Word)
    (valid : Invariant meaning before.heap) (denotation : key.eval meaning before.heap.read = some value) :
    Safe meaning (handoff >>= fun _ => liftGraph (p.insert key deterministic)) before
      (fun id after => after.read id = some value) := by
  apply local_bind_safe meaning _ _ before _ handoff_local valid
  intro ignored after _ validAfter frame
  exact Safe.graph meaning _ after _ (contracts.insert key admissible deterministic after.heap value validAfter
    (by rw [show after.heap.read = before.heap.read by rw [frame]]; exact denotation))

theorem miss_safe_for (meaning : Meaning) (r : Resources) (p : Primitives) (allowed : Key → Prop) (contracts : ContractsFor meaning p allowed)
    (request : Request) (key : Key) (admissible : allowed key) (deterministic : Bool) (before : Session) (value : Word)
    (kind : key.kind = request.item.kind) (valid : Invariant meaning before.heap)
    (denotation : key.eval meaning before.heap.read = some value) :
    Safe meaning (findCode.controlMiss (execution r p) request key deterministic) before
      (fun id after => after.read id = some value) := by
  unfold FindCode.controlMiss
  simp only [execution]
  by_cases branch : (deterministic && (request.item.kind == 1)) = true
  · simp only [branch, ↓reduceIte]
    have operation : key.kind = 1 := by
      rw [kind]
      simpa using (Bool.and_eq_true_iff.mp branch).2
    apply Safe.bind meaning before _ _ (fun result after => ∀ id, result = some id → after.read id = some value) _
      (Safe.graph meaning _ before _ (contracts.simplify key admissible operation before.heap value valid denotation))
    intro result middle validMiddle stable fact
    have keyMiddle := key_stable meaning before.heap.read middle.heap.read stable key value denotation
    cases result with
    | none => exact handoff_insert_safe_for meaning p allowed contracts.toGraphContractsFor key admissible deterministic middle value validMiddle keyMiddle
    | some id =>
      have actual := fact id rfl
      apply Safe.bind meaning middle _ _ (fun _ _ => True) _
        (Safe.graph meaning _ middle _ (contracts.publish key id middle.heap value validMiddle keyMiddle actual))
      intro ignored after validAfter stableAfter _
      apply local_bind_safe meaning _ _ after _ handoff_local validAfter
      intro ignored final _ validFinal frame
      exact Safe.pure meaning final id _ validFinal (by
        rw [show final.heap.read = after.heap.read by rw [frame]]
        exact stableAfter id value actual)
  · simp only [branch]
    exact handoff_insert_safe_for meaning p allowed contracts.toGraphContractsFor key admissible deterministic before value valid denotation

theorem owned_safe_for (meaning : Meaning) (r : Resources) (p : Primitives) (allowed : Key → Prop) (contracts : ContractsFor meaning p allowed)
    (request : Request) (admissible : ∀ args key, makeKey request args = .ok key → allowed key)
    (args : List NodeId) (deterministic : Bool) (before : Session) (value : Word)
    (valid : Invariant meaning before.heap)
    (denotation : request.item.eval meaning before.heap.read args request.sequence = some value) :
    Safe meaning (findCode.controlOwned (execution r p) request args deterministic) before
      (fun id after => after.read id = some value) := by
  unfold FindCode.controlOwned
  simp only [execution]
  apply local_bind_safe meaning _ _ before _ (take_local r) valid
  intro ignored after _ validAfter frame
  apply lift_bind_safe meaning _ _ after _ validAfter
  intro key made
  exact miss_safe_for meaning r p allowed contracts request key (admissible args key made) deterministic after value
    (Recursive.make_key_kind request args key made) validAfter
    (Interner.makeKey_sound meaning after.heap request args value key
      (by rw [show after.heap.read = before.heap.read by rw [frame]]; exact denotation) made)

theorem handoff_insert_safe (meaning : Meaning) (p : Primitives) (contracts : GraphContracts meaning p)
    (key : Key) (deterministic : Bool) (before : Session) (value : Word)
    (valid : Invariant meaning before.heap) (denotation : key.eval meaning before.heap.read = some value) :
    Safe meaning (handoff >>= fun _ => liftGraph (p.insert key deterministic)) before
      (fun id after => after.read id = some value) :=
  handoff_insert_safe_for meaning p (fun _ => True) (contracts.restrict meaning p _) key trivial deterministic before value valid denotation

theorem miss_safe (meaning : Meaning) (r : Resources) (p : Primitives) (contracts : Contracts meaning p)
    (request : Request) (key : Key) (deterministic : Bool) (before : Session) (value : Word)
    (kind : key.kind = request.item.kind) (valid : Invariant meaning before.heap)
    (denotation : key.eval meaning before.heap.read = some value) :
    Safe meaning (findCode.controlMiss (execution r p) request key deterministic) before
      (fun id after => after.read id = some value) :=
  miss_safe_for meaning r p (fun _ => True) (contracts.restrict meaning p _) request key trivial deterministic before value kind valid denotation

theorem owned_safe (meaning : Meaning) (r : Resources) (p : Primitives) (contracts : Contracts meaning p)
    (request : Request) (args : List NodeId) (deterministic : Bool) (before : Session) (value : Word)
    (valid : Invariant meaning before.heap)
    (denotation : request.item.eval meaning before.heap.read args request.sequence = some value) :
    Safe meaning (findCode.controlOwned (execution r p) request args deterministic) before
      (fun id after => after.read id = some value) :=
  owned_safe_for meaning r p (fun _ => True) (contracts.restrict meaning p _) request (fun _ _ _ => trivial) args deterministic before value valid denotation

end Compiler.Extraction.Interner.Scoped
