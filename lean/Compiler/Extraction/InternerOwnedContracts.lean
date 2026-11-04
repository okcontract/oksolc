/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

def Good (source : View) (values : List NodeId) (state : World σ) : Prop :=
  Valid state.memory ∧ Represents state.memory.memory source values

/-- An initialized nonempty view has a live native region, including offset
views and unregistered stack arrays. Empty sentinels need no backing. -/
theorem Good.backed {source : View} {values : List NodeId} {state : World σ}
    (good : Good source values state) (nonempty : source.length ≠ 0) :
    ∃ cell, state.memory.memory.heap.lookup source.allocation = some cell := by
  have inside : 0 < values.length := by have size := good.2.1; omega
  have read := good.2.2 0 inside
  cases accessed : Compiler.ZigAir.Memory.access state.memory.memory (source.address 0) ⟨4, 4⟩ false with
  | error fault =>
    simp [Compiler.ZigAir.Memory.load, View.pointer, word, Compiler.ZigAir.Memory.Ty.layout,
      accessed, bind, Except.bind] at read
  | ok cell =>
    exact ⟨cell, (Compiler.ZigAir.Memory.access_success_region _ _ _ false cell accessed).1⟩

def Held (allocator : Nat) (source : View) (values : List NodeId) (slice : ArgumentSlice) (state : World σ) : Prop :=
  Good source values state ∧ SliceValid allocator state.memory.heap slice ∧
    (values ≠ [] → source.allocation ≠ slice.address)

/-- These are obligations of graph implementations, not additional native
allocator assumptions. Publication keeps the caller's slice on ordinary
failure; insertion has already received ownership on every outcome. Their graph
meaning and ultimate storage ownership remain separate. -/
structure GraphContracts (allocator : Nat) (source : View) (values : List NodeId) (p : Primitives σ) : Prop where
  publish : ∀ key slice id before, key.arguments = slice.items → Held allocator source values slice before →
    let (result, after) := p.publish key slice id before
    ordinary result = true → Good source values after ∧
      (∀ fault, result = .error fault → SliceValid allocator after.memory.heap slice)
  insert : ∀ key slice deterministic before, key.arguments = slice.items → Held allocator source values slice before →
    let (result, after) := p.insert key slice deterministic before
    ordinary result = true → Good source values after

/-- Separate recursive simplification from graph ownership so that callers can
construct this field from the actual dispatcher proof. -/
structure Contracts (allocator : Nat) (source : View) (values : List NodeId) (p : Primitives σ) : Prop
    extends GraphContracts allocator source values p where
  simplify : ∀ key slice before, key.arguments = slice.items → Held allocator source values slice before →
    let (result, after) := p.simplify key slice before
    ordinary result = true → Held allocator source values slice after

/-- Private descriptors survive graph calls. A transferred slice can already
be consumed by the callee, so detached lookup destruction needs no readable
alias to it. Only a still-owned slice needs the release precondition. -/
def Post (allocator : Nat) (source : View) (values : List NodeId) (slice : ArgumentSlice) (remaining : Handle)
    (execution : Except Fault α × State σ) : Prop :=
  execution.2.scope.lookup = some remaining ∧ execution.2.scope.slice = some slice ∧
    (ordinary execution.1 = true → Good source values execution.2.world ∧
      (execution.2.scope.handedOff = false → SliceValid allocator execution.2.world.memory.heap slice))

theorem graph_preserves_local (action : ArgumentSlice → GraphAction σ α) (before : State σ) :
    (graph action before).2.scope = before.scope := by
  cases present : before.scope.slice <;> simp [graph, present]

/-- Insertion has already received ownership. Its actual ordinary result
only needs to preserve the source; no live normalized owner is required. -/
theorem insert_post_at (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (key : Key) (slice : ArgumentSlice) (remaining : Handle) (deterministic : Bool) (before : World σ)
    (preserves : ordinary (p.insert key slice deterministic before).1 = true →
      Good source values (p.insert key slice deterministic before).2) :
    Post allocator source values slice remaining
      ((do let _ ← handoff; graph (fun slice => p.insert key slice deterministic) : Action σ NodeId)
        ⟨before, ⟨some remaining, some slice, false⟩⟩) := by
  change Post allocator source values slice remaining
    ((graph (fun slice => p.insert key slice deterministic)) ⟨before, ⟨some remaining, some slice, true⟩⟩)
  cases called : p.insert key slice deterministic before with
  | mk result after =>
    simp only [graph, called, Post]
    refine ⟨trivial, trivial, ?_⟩
    intro completed
    have good := preserves
    rw [called] at good
    exact ⟨good completed, by intro impossible; cases impossible⟩

theorem insert_post (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (contracts : Contracts allocator source values p) (key : Key) (slice : ArgumentSlice) (remaining : Handle)
    (deterministic : Bool) (before : World σ) (aligned : key.arguments = slice.items) (held : Held allocator source values slice before) :
    Post allocator source values slice remaining
      ((do let _ ← handoff; graph (fun slice => p.insert key slice deterministic) : Action σ NodeId)
        ⟨before, ⟨some remaining, some slice, false⟩⟩) :=
  insert_post_at allocator p source values key slice remaining deterministic before
    (contracts.insert key slice deterministic before aligned held)

/-- Local lifetime composition for the actual first dispatch and reached
publication/insertion calls. The extra native invariant is needed only before
those graph calls; release/transfer need not preserve the dispatch input frame. -/
theorem miss_post_at (external : External σ) (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (remaining : Handle)
    (deterministic : Bool) (before : World σ) (predicate : World σ → Prop)
    (initial : predicate before) (held : Held allocator source values slice before)
    (simplifies : ordinary (p.simplify key slice before).1 = true →
      predicate (p.simplify key slice before).2 ∧ Held allocator source values slice (p.simplify key slice before).2)
    (publishes : ∀ id world, predicate world → Held allocator source values slice world →
      ordinary (p.publish key slice id world).1 = true → Good source values (p.publish key slice id world).2 ∧
        (∀ fault, (p.publish key slice id world).1 = .error fault → SliceValid allocator (p.publish key slice id world).2.memory.heap slice))
    (inserts : ∀ world, predicate world → Held allocator source values slice world →
      ordinary (p.insert key slice deterministic world).1 = true → Good source values (p.insert key slice deterministic world).2) :
    Post allocator source values slice remaining
      (Interner.findCode.controlMiss (execution external allocator p) request key deterministic
        ⟨before, ⟨some remaining, some slice, false⟩⟩) := by
  unfold Interner.FindCode.controlMiss
  simp only [execution]
  by_cases branch : (deterministic && (request.item.kind == 1)) = true
  · simp only [branch, ↓reduceIte]
    cases simplified : p.simplify key slice before with
    | mk result middle =>
      have contract := simplifies
      rw [simplified] at contract
      cases result with
      | error fault =>
        simp only [bind, Effect.bind, graph, simplified, Post]
        exact ⟨trivial, trivial, fun completed => ⟨(contract completed).2.1, fun _ => (contract completed).2.2.1⟩⟩
      | ok result =>
        have middlePredicate := (contract rfl).1
        have middleHeld := (contract rfl).2
        cases result with
        | none =>
          simpa only [bind, Effect.bind, graph, simplified, pure, Effect.pure] using
            insert_post_at allocator p source values key slice remaining deterministic middle (inserts middle middlePredicate middleHeld)
        | some id =>
          cases published : p.publish key slice (Interner.findCode.published.run id) middle with
          | mk result after =>
            have publication := publishes (Interner.findCode.published.run id) middle middlePredicate middleHeld
            rw [published] at publication
            cases result with
            | error fault =>
              simp only [bind, Effect.bind, graph, simplified, published, Post]
              exact ⟨trivial, trivial, fun completed => ⟨(publication completed).1, fun _ => (publication completed).2 fault rfl⟩⟩
            | ok returned =>
              cases returned
              simp only [bind, Effect.bind, graph, simplified, published, handoff, pure, Effect.pure, Post]
              exact ⟨trivial, trivial, fun _ => ⟨(publication rfl).1, by intro impossible; cases impossible⟩⟩
  · simpa only [branch, Bool.false_eq_true, ↓reduceIte, pure, Effect.pure, bind, Effect.bind] using
      insert_post_at allocator p source values key slice remaining deterministic before (inserts before initial held)

theorem miss_post (external : External σ) (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (contracts : Contracts allocator source values p) (request : Interner.Request) (key : Key)
    (slice : ArgumentSlice) (remaining : Handle) (deterministic : Bool) (before : World σ)
    (aligned : key.arguments = slice.items) (held : Held allocator source values slice before) :
    Post allocator source values slice remaining
      (Interner.findCode.controlMiss (execution external allocator p) request key deterministic
        ⟨before, ⟨some remaining, some slice, false⟩⟩) :=
  miss_post_at external allocator p source values request key slice remaining deterministic before (fun _ => True) trivial held
    (fun completed => ⟨trivial, contracts.simplify key slice before aligned held completed⟩)
    (fun id world _ live => contracts.publish key slice id world aligned live)
    (fun world _ live => contracts.insert key slice deterministic world aligned live)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
