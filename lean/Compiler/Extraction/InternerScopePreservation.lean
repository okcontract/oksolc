/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerScopeSemantics

namespace Compiler.Extraction.Interner.Scoped
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

theorem control_find_safe_for (other : Meaning) (r : Resources)
    (permutation : ∀ ids, (r.sort ids).Perm ids) (p : Primitives)
    (allowed : Key → Prop) (contracts : ContractsFor (Folding.wordMeaning other) p allowed)
    (request : Request) (admissible : ∀ args key, makeKey request args = .ok key → allowed key) (before : Session)
    (value : Word) (valid : Invariant (Folding.wordMeaning other) before.heap)
    (denotation : request.item.eval (Folding.wordMeaning other) before.heap.read request.arguments request.sequence = some value) :
    Safe (Folding.wordMeaning other) (findCode.controlRun (execution r p) request) before
      (fun id after => after.read id = some value) := by
  let meaning := Folding.wordMeaning other
  unfold FindCode.controlRun
  simp only [execution]
  apply get_bind_safe meaning _ before
  by_cases capacity : p.atCapacity before.heap = true
  · simp only [capacity, ↓reduceIte]
    exact Safe.graph meaning _ before _ (Interner.Safe.fail meaning before.heap .capacity _ valid)
  · simp only [capacity]
    apply local_bind_safe meaning _ _ before _ (initialize_local r request) valid
    intro args current normalized validCurrent frame
    have argsBefore : request.item.eval meaning before.heap.read args request.sequence = some value :=
      (normalize_word other r.sort permutation request.item request.arguments args before.heap.read request.sequence
        (initialize_projection r request before current args normalized)).trans denotation
    have argsCurrent : request.item.eval meaning current.heap.read args request.sequence = some value := by
      rw [show current.heap.read = before.heap.read by rw [frame]]
      exact argsBefore
    apply lift_bind_safe meaning _ _ current _ validCurrent
    intro deterministic _
    cases deterministic with
    | false => exact owned_safe_for meaning r p allowed contracts request admissible args false current value validCurrent argsCurrent
    | true =>
      apply lift_bind_safe meaning _ _ current _ validCurrent
      intro key made
      have keyValue := Interner.makeKey_sound meaning before.heap request args value key argsBefore made
      cases found : before.heap.table key with
      | none =>
        simpa only [found] using owned_safe_for meaning r p allowed contracts request admissible args true current value validCurrent argsCurrent
      | some id =>
        obtain ⟨cachedValue, cachedKey, cachedId⟩ := valid.cache key id found
        have same : cachedValue = value := by rw [keyValue] at cachedKey; exact Option.some.inj cachedKey.symm
        subst cachedValue
        simpa only [found, findCode, ResultId.run] using
          Safe.pure meaning current id _ validCurrent (by rw [show current.heap.read = before.heap.read by rw [frame]]; exact cachedId)

theorem control_find_safe (other : Meaning) (r : Resources)
    (permutation : ∀ ids, (r.sort ids).Perm ids) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (request : Request) (before : Session)
    (value : Word) (valid : Invariant (Folding.wordMeaning other) before.heap)
    (denotation : request.item.eval (Folding.wordMeaning other) before.heap.read request.arguments request.sequence = some value) :
    Safe (Folding.wordMeaning other) (findCode.controlRun (execution r p) request) before
      (fun id after => after.read id = some value) :=
  control_find_safe_for other r permutation p (fun _ => True) (contracts.restrict _ p _)
    request (fun _ _ _ => trivial) before value valid denotation

theorem control_force_safe (other : Meaning) (r : Resources)
    (permutation : ∀ ids, (r.sort ids).Perm ids) (p : Primitives)
    (publishes : Publishes (Folding.wordMeaning other) p)
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId) (item : Item) (arguments : List NodeId)
    (before : Session) (value : Word) (valid : Invariant (Folding.wordMeaning other) before.heap)
    (denotation : item.eval (Folding.wordMeaning other) before.heap.read arguments 0 = some value)
    (equalValue : before.heap.read id = some value) :
    Safe (Folding.wordMeaning other) (forceCode.controlRun (execution r p) validate id item arguments) before
      (fun _ _ => True) := by
  let meaning := Folding.wordMeaning other
  unfold ForceCode.controlRun ForceCode.controlOwned
  simp only [execution]
  apply get_bind_safe meaning _ before
  apply lift_bind_safe meaning _ _ before _ valid
  intro ignored _
  apply local_bind_safe meaning _ _ before _ (initialize_local r _) valid
  intro args current normalized validCurrent frame
  have argsBefore : item.eval meaning before.heap.read args 0 = some value :=
    (normalize_word other r.sort permutation item arguments args before.heap.read 0
      (initialize_projection r ⟨item, arguments, 0⟩ before current args normalized)).trans denotation
  apply lift_bind_safe meaning _ _ current _ validCurrent
  intro key _
  cases found : before.heap.table key with
  | some cached =>
    simpa only [found] using Safe.pure meaning current () (fun _ _ => True) validCurrent trivial
  | none =>
    apply local_bind_safe meaning _ _ current _ (take_local r) validCurrent
    intro ignored owned _ validOwned ownedFrame
    apply lift_bind_safe meaning _ _ owned _ validOwned
    intro ownedKey made
    apply Safe.bind meaning owned _ _ (fun _ _ => True) _
      (Safe.graph meaning _ owned _ (publishes ownedKey id owned.heap value validOwned
        (Interner.makeKey_sound meaning owned.heap ⟨item, arguments, 0⟩ args value ownedKey
          (by rw [show owned.heap.read = before.heap.read by rw [ownedFrame, frame]]; exact argsBefore) made)
        (by rw [show owned.heap.read = before.heap.read by rw [ownedFrame, frame]]; exact equalValue)))
    intro ignored after validAfter _ _
    exact Safe.local meaning _ after handoff_local validAfter

/-- Closing the scope preserves graph semantics while retaining the reached
allocator state. The result postcondition must itself ignore only that cursor. -/
theorem finish_safe (meaning : Meaning) (r : Resources) (action : Action α) (before : Heap)
    (post : α → Heap → Prop) (safe : Safe meaning action ⟨{}, before⟩ post)
    (postCursor : ∀ value heap cursor, post value heap → post value { heap with allocationCursor := cursor }) :
    Interner.Safe meaning (fun heap => let (result, after) := finish r action heap; (result, after.heap)) before post := by
  intro result after ran
  cases step : action ⟨{}, before⟩ with
  | mk outcome current =>
    have checked := safe outcome current step
    simp only [finish, step] at ran
    cases ran
    refine ⟨?_, ?_, ?_⟩
    · rw [close_heap]
      exact checked.1.with_cursor _
    · intro id value found
      rw [(close_frame r current).1]
      exact checked.2.1 id value found
    · cases result with
      | error error => trivial
      | ok value =>
        rw [close_heap]
        exact postCursor value current.heap _ checked.2.2

/-- Every outcome preserves the semantic invariant and all old IDs. Success
returns the requested word, with real normalization and local cleanup effects. -/
theorem find_safe_for (other : Meaning) (r : Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (allowed : Key → Prop) (contracts : ContractsFor (Folding.wordMeaning other) p allowed)
    (request : Request) (admissible : ∀ args key, makeKey request args = .ok key → allowed key)
    (before : Heap) (value : Word) (valid : Invariant (Folding.wordMeaning other) before)
    (denotation : request.item.eval (Folding.wordMeaning other) before.read request.arguments request.sequence = some value) :
    Interner.Safe (Folding.wordMeaning other) (find r p request) before (fun id after => after.read id = some value) :=
  finish_safe _ r _ before _ (control_find_safe_for other r permutation p allowed contracts request admissible ⟨{}, before⟩ value valid denotation)
    (fun _ _ _ actual => actual)

theorem find_safe (other : Meaning) (r : Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (contracts : Contracts (Folding.wordMeaning other) p)
    (request : Request) (before : Heap) (value : Word) (valid : Invariant (Folding.wordMeaning other) before)
    (denotation : request.item.eval (Folding.wordMeaning other) before.read request.arguments request.sequence = some value) :
    Interner.Safe (Folding.wordMeaning other) (find r p request) before (fun id after => after.read id = some value) :=
  find_safe_for other r permutation p (fun _ => True) (contracts.restrict _ p _) request
    (fun _ _ _ => trivial) before value valid denotation

/-- `forceEqual` still requires the caller's semantic equality proof. Scoped
cleanup cannot turn an arbitrary representative into a correct cache value. -/
theorem force_safe (other : Meaning) (r : Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (publishes : Publishes (Folding.wordMeaning other) p)
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId) (item : Item) (arguments : List NodeId)
    (before : Heap) (value : Word) (valid : Invariant (Folding.wordMeaning other) before)
    (denotation : item.eval (Folding.wordMeaning other) before.read arguments 0 = some value)
    (equalValue : before.read id = some value) :
    Interner.Safe (Folding.wordMeaning other) (force r p validate id item arguments) before (fun _ _ => True) :=
  finish_safe _ r _ before _
    (control_force_safe other r permutation p publishes validate id item arguments ⟨{}, before⟩ value valid denotation equalValue)
    (fun _ _ _ actual => actual)

end Compiler.Extraction.Interner.Scoped
