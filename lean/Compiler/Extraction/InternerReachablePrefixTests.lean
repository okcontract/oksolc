/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerReachablePrefixFirstTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ReachablePrefixTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] invoke run before

structure Prefix (safety : Bool) (n : Nat) : Prop where
  result : (run safety n).1 = .ok (BitVec.ofNat 32 n)
  facts : GraphFacts safety backing 5 (before safety n) (cells safety n)
  count : (cells safety n).length = n + 1
  frame : ∀ id native, (CallerInputTests.world safety).memory.memory.heap.lookup id = some native →
    id ≠ 6 → id ≠ backing → (before safety n).memory.memory.heap.lookup id = some native

theorem first (safety : Bool) : Prefix safety 0 := by
  obtain ⟨after, inserted, facts, itemReads, frame⟩ := first_publication safety
  obtain ⟨item, entry⟩ := first_entry safety
  have room : Interner.Queries.queries.atCapacity (call safety 0).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _
      ((congrArg Interner.Heap.representatives item.graph).trans (initial safety).projected)]
    decide
  have returned := (call safety 0).publication_return allocate none safety backing 5 10 backing [] (operands 0)
    (primitives safety) after entry inserted facts itemReads (initial safety).valid
    (fun id native found apart _ _ => frame id native found apart)
    (by cases safety <;> decide +kernel) (by simp only [List.nil_append, List.length_singleton]; decide)
    (routed safety 0 (by decide) item entry room)
  have reached : run safety 0 = ((call safety 0).invoked (primitives safety)).map id (fun state => state.world) := by
    unfold run sequence
    simpa only [invoke, prior] using invoked safety 0
  refine ⟨?_, ?_, count safety 0, ?_⟩
  · rw [reached]; exact returned.1
  · rw [before, cells, reached]; exact returned.2.1
  · intro id native found ownerApart backingApart
    rw [before, reached]
    exact returned.2.2.2.2 id native found ownerApart backingApart
      (by intro old selected nonempty; exact False.elim (nonempty rfl))

theorem next (safety : Bool) (n : Nat) (bounded : n < 3) (previous : Prefix safety n) : Prefix safety (n + 1) := by
  have observed := observed safety (n + 1) (by omega)
  have good : Good (call safety (n + 1)).source [] (call safety (n + 1)).before :=
    ⟨previous.facts.valid, rfl, by intro index impossible; cases impossible⟩
  have domain : ((call safety (n + 1)).request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues := by
    change (1 : Int) ∈ AssemblyItem.itemTagValues; decide
  have established := (call safety (n + 1)).establish safety backing 5 (cells safety n) previous.facts
    (by rw [previous.count]; omega) good domain observed.1
  have room : Interner.Queries.queries.atCapacity (call safety (n + 1)).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, previous.count]
    simp only [decide_eq_false_iff_not]; omega
  have complete := (call safety (n + 1)).spare_publication allocate none safety backing 5 (object (n + 1))
    (cells safety n) (operands (n + 1)) (call safety (n + 1)).duplicate.2 (call safety (n + 1)).create.2
    (call safety (n + 1)).clone.2 (primitives safety) previous.facts good domain observed.1
    (by rw [previous.count]; omega) (by rw [previous.count]; omega)
    (Prod.ext observed.2.1 rfl) (Prod.ext observed.2.2.1 rfl) (Prod.ext observed.2.2.2 rfl)
    (routed safety (n + 1) (by omega) established.item established.entry room)
  have reached : run safety (n + 1) =
      ((call safety (n + 1)).invoked (primitives safety)).map id (fun state => state.world) := by
    have priorRun : run safety n = (.ok (BitVec.ofNat 32 n), before safety n) :=
      Prod.ext previous.result (by rw [before])
    rw [run] at priorRun
    simp only [run, sequence, bind, Effect.bind, priorRun]
    simpa only [invoke, prior] using invoked safety (n + 1)
  refine ⟨?_, ?_, count safety (n + 1), ?_⟩
  · rw [reached]
    simpa only [Storage.idFor, previous.count] using complete.1
  · rw [before, cells, reached]; exact complete.2.1
  · intro id native found ownerApart backingApart
    have kept := previous.frame id native found ownerApart backingApart
    rw [before, reached]
    exact complete.2.2.2.2.1 id native kept ownerApart backingApart
      (by intro old selected nonempty; exact False.elim (nonempty rfl))

/-- Four complete constructor calls start at the actual native initializer.
Cache lookup, dispatch, ownership handoff, publication and local returns are
part of every step; no selected insertion continuation supplies these rows. -/
theorem initialized_prefix (safety : Bool) (n : Nat) (bounded : n < 4) : Prefix safety n := by
  induction n with
  | zero => exact first safety
  | succ n ih => exact next safety n (by omega) (ih (by omega))

/-- The same actual prefix supplies each constructor's entry and capacity guard. -/
theorem entered (safety : Bool) (n : Nat) (bounded : n < 4) :
    Prepared (call safety n).request.item debug (call safety n).before (call safety n).constructed ∧
    CallerInput 7 (call safety n).source (call safety n).address (call safety n).request []
      (call safety n).native (call safety n).key (call safety n).constructed (call safety n).taken.2
      (call safety n).normalized (call safety n).lookup ∧
    Interner.Queries.queries.atCapacity (call safety n).constructed.graph = false := by
  cases n with
  | zero =>
    obtain ⟨item, entry⟩ := first_entry safety
    refine ⟨item, entry, ?_⟩
    rw [Interner.Queries.capacity_exact _ _
      ((congrArg Interner.Heap.representatives item.graph).trans (initial safety).projected)]
    decide
  | succ n =>
    have previous := initialized_prefix safety n (by omega)
    have facts := (call safety (n + 1)).establish safety backing 5 (cells safety n) previous.facts
      (by rw [previous.count]; omega)
      ⟨previous.facts.valid, rfl, by intro index impossible; cases impossible⟩
      (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (observed safety (n + 1) bounded).1
    refine ⟨facts.item, facts.entry, ?_⟩
    rw [Interner.Queries.capacity_exact _ _ facts.constructed.projected, previous.count]
    simp only [decide_eq_false_iff_not]; omega

theorem step_result (safety : Bool) (n : Nat) (bounded : n < 4) :
    invoke safety n (prior safety n) = (.ok (BitVec.ofNat 32 n), before safety n) := by
  have result : run safety n = (.ok (BitVec.ofNat 32 n), before safety n) :=
    Prod.ext (initialized_prefix safety n bounded).result (by rw [before])
  cases n with
  | zero => simpa only [run, sequence, invoke, prior] using result
  | succ n =>
    have previous : run safety n = (.ok (BitVec.ofNat 32 n), before safety n) :=
      Prod.ext (initialized_prefix safety n (by omega)).result (by rw [before])
    rw [run] at previous
    simpa only [run, sequence, bind, Effect.bind, previous, invoke, prior] using result

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ReachablePrefixTests
