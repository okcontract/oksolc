/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerProgram

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Contract.Yul Compiler.Extraction.Cache
set_option linter.unusedSimpArgs false

private theorem lift_bind_safe (meaning : Meaning) (before : Heap) (result : Except Error α)
    (next : α → Action β) (post : β → Heap → Prop) (valid : Invariant meaning before)
    (continuation : ∀ value, result = .ok value → Safe meaning (next value) before post) :
    Safe meaning (lift result >>= next) before post := by
  cases result with
  | error error =>
    intro outcome after run
    change (Except.error error, before) = (outcome, after) at run
    cases run
    exact ⟨valid, fun _ _ h => h, trivial⟩
  | ok value => exact continuation value rfl

private theorem local_bind_safe (meaning : Meaning) (before : Heap) (action : Local α)
    (next : α → Action β) (post : β → Heap → Prop) (valid : Invariant meaning before)
    (continuation : ∀ value cursor, action before.allocationCursor = (.ok value, cursor) →
      Safe meaning (next value) { before with allocationCursor := cursor } post) :
    Safe meaning (liftLocal action >>= next) before post := by
  cases step : action before.allocationCursor with
  | mk result cursor =>
    cases result with
    | error error =>
      intro outcome after ran
      change Effect.bind (liftLocal action) next before = (outcome, after) at ran
      simp only [Effect.bind, liftLocal, step] at ran
      cases ran
      exact ⟨valid.with_cursor cursor, fun _ _ found => found, trivial⟩
    | ok value =>
      intro outcome after ran
      have checked := continuation value cursor step outcome after
        (by simpa only [bind, Effect.bind, liftLocal, step] using ran)
      exact checked

theorem makeKey_sound (meaning : Meaning) (before : Heap) (request : Request)
    (args : List NodeId) (value : Word) (key : Key)
    (denotation : request.item.eval meaning before.read args request.sequence = some value)
    (made : makeKey request args = .ok key) : key.eval meaning before.read = some value := by
  unfold makeKey at made
  cases actual : keyCode.run request.item args request.sequence with
  | none => simp [actual] at made
  | some produced =>
    simp [actual] at made
    subst produced
    rw [Cache.key_sound meaning before.read request.item args request.sequence key actual]
    exact denotation

/-- Only the source simplification branch can reach publication. Direct
insertion needs neither simplifier nor publication semantics. -/
theorem miss_safe_branches (meaning : Meaning) (p : Primitives)
    (request : Request) (key : Key) (deterministic : Bool) (before : Heap) (value : Word)
    (valid : Invariant meaning before) (denotation : key.eval meaning before.read = some value)
    (simplify : (deterministic && (request.item.kind == 1)) = true →
      Safe meaning (p.simplify key) before (fun found after => ∀ id, found = some id → after.read id = some value))
    (insert : ∀ reached, Invariant meaning reached → key.eval meaning reached.read = some value →
      Safe meaning (p.insert key deterministic) reached (fun id after => after.read id = some value))
    (publish : (deterministic && (request.item.kind == 1)) = true →
      ∀ id reached, Invariant meaning reached → key.eval meaning reached.read = some value →
      reached.read id = some value → Safe meaning (p.publish key id) reached (fun _ _ => True)) :
    Safe meaning (findCode.miss p request key deterministic) before (fun id after => after.read id = some value) := by
  unfold FindCode.miss
  by_cases branch : (deterministic && (request.item.kind == 1)) = true
  · simp only [branch, ↓reduceIte]
    apply Safe.bind meaning before (p.simplify key) _
      (fun result after => ∀ id, result = some id → after.read id = some value) _
      (simplify branch)
    intro result middle validMiddle stable fact
    have keyMiddle := key_stable meaning before.read middle.read stable key value denotation
    cases result with
    | none => exact insert middle validMiddle keyMiddle
    | some id =>
      have actual := fact id rfl
      apply Safe.bind meaning middle (p.publish key id) _ (fun _ _ => True) _
        (publish branch id middle validMiddle keyMiddle actual)
      intro ignored after validAfter stableAfter _
      exact Safe.pure meaning after id _ validAfter (stableAfter id value actual)
  · have branch' : (deterministic && (request.item.kind == 1)) = false := by
      cases h : deterministic && (request.item.kind == 1) <;> simp_all
    simp only [branch', Bool.false_eq_true, ↓reduceIte]
    exact insert before valid denotation

/-- The original local interface specializes the guarded branch proof. Prefix
normalization remains independent of this step. -/
theorem miss_safe_at (meaning : Meaning) (p : Primitives)
    (request : Request) (key : Key) (deterministic : Bool) (before : Heap) (value : Word)
    (valid : Invariant meaning before) (denotation : key.eval meaning before.read = some value)
    (simplify : (deterministic && (request.item.kind == 1)) = true →
      Safe meaning (p.simplify key) before (fun found after => ∀ id, found = some id → after.read id = some value))
    (insert : ∀ reached, Invariant meaning reached → key.eval meaning reached.read = some value →
      Safe meaning (p.insert key deterministic) reached (fun id after => after.read id = some value))
    (publish : ∀ id reached, Invariant meaning reached → key.eval meaning reached.read = some value →
      reached.read id = some value → Safe meaning (p.publish key id) reached (fun _ _ => True)) :
    Safe meaning (findCode.miss p request key deterministic) before (fun id after => after.read id = some value) :=
  miss_safe_branches meaning p request key deterministic before value valid denotation simplify insert (fun _ => publish)

/-- The original callback-contract interface specializes the local step proof. -/
theorem miss_safe (meaning : Meaning) (p : Primitives) (contracts : Contracts meaning p)
    (request : Request) (key : Key) (deterministic : Bool) (before : Heap) (value : Word)
    (valid : Invariant meaning before) (denotation : key.eval meaning before.read = some value) :
    Safe meaning (findCode.miss p request key deterministic) before (fun id after => after.read id = some value) :=
  miss_safe_at meaning p request key deterministic before value valid denotation
    (fun _ => contracts.simplify key before value valid denotation)
    (fun reached => contracts.insert key deterministic reached value)
    (fun id reached => contracts.publish key id reached value)

theorem owned_safe (meaning : Meaning) (p : Primitives) (contracts : Contracts meaning p)
    (request : Request) (args : List NodeId) (deterministic : Bool) (before : Heap) (value : Word)
    (valid : Invariant meaning before)
    (denotation : request.item.eval meaning before.read args request.sequence = some value) :
    Safe meaning (findCode.owned p request args deterministic) before (fun id after => after.read id = some value) := by
  unfold FindCode.owned
  apply local_bind_safe meaning before _ _ _ valid
  intro _ cursor _
  apply lift_bind_safe meaning { before with allocationCursor := cursor } _ _ _ (valid.with_cursor cursor)
  intro key made
  exact miss_safe meaning p contracts request key deterministic { before with allocationCursor := cursor } value (valid.with_cursor cursor)
    (makeKey_sound meaning before request args value key denotation made)

/-- Every admitted execution outcome preserves the semantic heap invariant and
all previous IDs. Errors after recursive work retain that work; rollback is not
invented. Success returns the original requested expression's value. -/
theorem find_safe (meaning : Meaning) (p : Primitives) (contracts : Contracts meaning p)
    (request : Request) (before : Heap) (value : Word) (valid : Invariant meaning before)
    (denotation : request.item.eval meaning before.read request.arguments request.sequence = some value) :
    Safe meaning (findCode.run p request) before (fun id after => after.read id = some value) := by
  unfold FindCode.run
  change Safe meaning (if p.atCapacity before then fail .capacity else _) before _
  by_cases capacity : p.atCapacity before = true
  · simp only [capacity, ↓reduceIte]
    exact Safe.fail meaning before .capacity _ valid
  · have room : p.atCapacity before = false := by cases h : p.atCapacity before <;> simp_all
    simp only [room, Bool.false_eq_true, ↓reduceIte]
    apply local_bind_safe meaning before _ _ _ valid
    intro args cursor normalized
    have argsValue : request.item.eval meaning before.read args request.sequence = some value :=
      (contracts.normalize request args before.read before.allocationCursor cursor normalized).trans denotation
    apply lift_bind_safe meaning { before with allocationCursor := cursor } _ _ _ (valid.with_cursor cursor)
    intro deterministic _
    cases deterministic with
    | false => exact owned_safe meaning p contracts request args false { before with allocationCursor := cursor } value (valid.with_cursor cursor) argsValue
    | true =>
      apply lift_bind_safe meaning { before with allocationCursor := cursor } _ _ _ (valid.with_cursor cursor)
      intro key made
      have keyValue := makeKey_sound meaning before request args value key argsValue made
      cases found : before.table key with
      | none =>
        simpa only [found] using owned_safe meaning p contracts request args true { before with allocationCursor := cursor } value (valid.with_cursor cursor) argsValue
      | some id =>
        obtain ⟨cachedValue, cachedKey, cachedId⟩ := valid.cache key id found
        have same : cachedValue = value := by rw [keyValue] at cachedKey; exact Option.some.inj cachedKey.symm
        subst cachedValue
        simpa only [found, findCode, ResultId.run] using
          Safe.pure meaning { before with allocationCursor := cursor } id _ (valid.with_cursor cursor) cachedId

/-- This discharges the successful-result shape required by the earlier
construction proof, from the smaller primitive contracts and a valid heap. -/
theorem find_ensures (meaning : Meaning) (p : Primitives) (contracts : Contracts meaning p)
    (request : Request) (before : Heap) (value : Word) (valid : Invariant meaning before)
    (denotation : request.item.eval meaning before.read request.arguments request.sequence = some value) :
    Ensures Heap.read (findCode.run p request) before value := by
  intro id after run
  have result := find_safe meaning p contracts request before value valid denotation (.ok id) after run
  exact ⟨result.2.1, result.2.2⟩

/-- `forceEqual` is sound only when the caller establishes semantic equality.
It neither discovers equality nor makes an arbitrary ID a correct representative.
No recursive-optimizer or insertion contract is needed for this path. -/
theorem force_safe (meaning : Meaning) (p : Primitives)
    (normalizes : Normalizes meaning p) (publishes : Publishes meaning p)
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId) (item : Item)
    (arguments : List NodeId) (before : Heap) (value : Word) (valid : Invariant meaning before)
    (denotation : item.eval meaning before.read arguments 0 = some value)
    (equalValue : before.read id = some value) :
    Safe meaning (forceCode.run p validate id item arguments) before (fun _ _ => True) := by
  unfold ForceCode.run
  change Safe meaning (lift (validate id before) >>= _) before _
  apply lift_bind_safe meaning before _ _ _ valid
  intro _ _
  apply local_bind_safe meaning before _ _ _ valid
  intro args cursor normalized
  have argsValue : item.eval meaning before.read args 0 = some value :=
    (normalizes ⟨item, arguments, 0⟩ args before.read before.allocationCursor cursor normalized).trans denotation
  apply lift_bind_safe meaning { before with allocationCursor := cursor } _ _ _ (valid.with_cursor cursor)
  intro key made
  cases found : before.table key with
  | some cached =>
    simpa only [found] using Safe.pure meaning { before with allocationCursor := cursor } () (fun _ _ => True) (valid.with_cursor cursor) trivial
  | none =>
    simp only [found]
    change Safe meaning (liftLocal (p.takeOwned args) >>= _) { before with allocationCursor := cursor } _
    apply local_bind_safe meaning { before with allocationCursor := cursor } _ _ _ (valid.with_cursor cursor)
    intro _ ownedCursor _
    apply lift_bind_safe meaning { before with allocationCursor := ownedCursor } _ _ _ (valid.with_cursor ownedCursor)
    intro ownedKey ownedMade
    exact publishes ownedKey id { before with allocationCursor := ownedCursor } value (valid.with_cursor ownedCursor)
      (makeKey_sound meaning before ⟨item, arguments, 0⟩ args value ownedKey argsValue ownedMade) equalValue

end Compiler.Extraction.Interner
