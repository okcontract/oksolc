/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerReachablePrefixSetupTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ReachablePrefixTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] invoke run before

/-- Empty operands take the dispatch miss before any query or recursive call.
This holds for arbitrary proper children, not just the exhausted observation. -/
theorem simplified (safety : Bool) (n : Nat) (children : NativeRecursion.Constructors (Publication.Effects Nat))
    (context : PairInput.Context (Publication.Effects Nat) := base safety) :
    ((NativeRecursion.context context 6 64 children debug).primitives
      (call safety n).source (call safety n).address (call safety n).native).simplify
      (call safety n).key (call safety n).normalized (call safety n).taken.2.world =
        (.ok none, (call safety n).taken.2.world) := by
  rw [NativeRecursion.dispatcher_snapshot]
  rfl

theorem routed (safety : Bool) (n : Nat) (bounded : n < 4)
    (item : Prepared (call safety n).request.item debug (call safety n).before (call safety n).constructed)
    (entry : CallerInput 7 (call safety n).source (call safety n).address (call safety n).request []
      (call safety n).native (call safety n).key (call safety n).constructed (call safety n).taken.2
      (call safety n).normalized (call safety n).lookup)
    (room : Interner.Queries.queries.atCapacity (call safety n).constructed.graph = false) :
    (call safety n).invoked (primitives safety) =
      (let done := finishInsertion ops allocate safety 7 6 (call safety n).source (call safety n).address
        Insertion.Tests.model (call safety n).native (call safety n).key true (call safety n).taken.2 none
       if ordinary done.1 then (done.1, (call safety n).returned done.2) else done) := by
  have result := (call safety n).route (primitives safety) (observed safety n bounded).1 item.graph room (classified n)
  have continued : (call safety n).continuation ((primitives safety) (call safety n).address (call safety n).native) =
      (do handoff; graph (fun slice => Native.insert ops allocate safety 7 6 (call safety n).source
        (call safety n).address Insertion.Tests.model (call safety n).native (call safety n).key slice true none) :
          Action (Publication.Effects Nat) NodeId) (call safety n).taken.2 := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (call safety n).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      graph, entry.origin.scope, show ((primitives safety) (call safety n).address (call safety n).native).simplify
        (call safety n).key (call safety n).normalized (call safety n).taken.2.world =
          (.ok none, (call safety n).taken.2.world) from simplified safety n NativeRecursion.exhausted,
      bind, Effect.bind]
    rw [← entry.origin.scope]; rfl
  rw [continued] at result
  exact result

theorem invoked (safety : Bool) (n : Nat) : invoke safety n (prior safety n) =
    ((call safety n).invoked (primitives safety)).map id (fun state => state.world) := by
  unfold invoke
  rfl

theorem first_entry (safety : Bool) :
    Prepared (call safety 0).request.item debug (call safety 0).before (call safety 0).constructed ∧
    CallerInput 7 (call safety 0).source (call safety 0).address (call safety 0).request []
      (call safety 0).native (call safety 0).key (call safety 0).constructed (call safety 0).taken.2
      (call safety 0).normalized (call safety 0).lookup :=
  (call safety 0).entry ⟨(initial safety).valid, rfl, by intro index impossible; cases impossible⟩
    (initial safety).linked (initial safety).live (initial safety).unique (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (observed safety 0 (by decide)).1

def firstInstalled (safety : Bool) := (call safety 0).installed 10 (call safety 0).clone.2

theorem first_allocation (safety : Bool) :
    AssemblyClone.NativeFields.install (call safety 0).native 10 (call safety 0).clone.2 = .ok (firstInstalled safety) ∧
    (call safety 0).clone.2.memory.nextId = backing ∧
    Compiler.ZigAir.Memory.RegionAllocation.Fits (firstInstalled safety).memory ⟨160, 8⟩ 4096 := by
  refine ⟨?_, ?_, by decide, by decide, by decide, ?_⟩
  · cases safety <;> insertion_kernel_rfl
  · cases safety <;> insertion_kernel_rfl
  · have bound : (firstInstalled safety).memory.heap.all (fun entry =>
        decide (entry.2.base + (entry.2.type.layout.getD ⟨0, 1⟩).bytes ≤ 4096)) = true := by
      cases safety <;> decide +kernel
    intro entry present layout shaped
    have checked := (List.all_eq_true.mp bound) entry present
    simp only [shaped, Option.getD_some, decide_eq_true_eq] at checked
    exact Or.inr checked

/-- The first full constructor derives its published native graph from the
actual initializer, item/caller prefix, first backing allocation and publication. -/
theorem first_publication (safety : Bool) : ∃ after,
    Native.insert ops allocate safety 7 6 (call safety 0).source (call safety 0).address Insertion.Tests.model
      (call safety 0).native (call safety 0).key (call safety 0).normalized true none (call safety 0).taken.2.world =
        (.ok 0, (call safety 0).publicationWorld [] 10 (operands 0) (call safety 0).taken.2.world after) ∧
    GraphFacts safety backing 5 ((call safety 0).publicationWorld [] 10 (operands 0) (call safety 0).taken.2.world after)
      [row safety 0] ∧
    AssemblyClone.NativeFields.Represents
      ((call safety 0).publicationWorld [] 10 (operands 0) (call safety 0).taken.2.world after).memory.memory ⟨10, 0⟩ (call safety 0).native ∧
    (∀ id native, (call safety 0).before.memory.memory.heap.lookup id = some native → id ≠ 6 →
      (memory after).memory.heap.lookup id = some native) := by
  obtain ⟨post, entry⟩ := first_entry safety
  have initialFacts := initial safety
  have constructed := initialFacts.frame post.valid
    ((congrArg Interner.Heap.representatives post.graph).trans initialFacts.projected)
    (congrArg Interner.Heap.table post.graph) (congrArg Publication.Effects.keys post.effects)
    (fun id cell found _ => post.memory id cell found) (by intro id block found; rw [post.heap]; exact found)
  obtain ⟨owner, found, typed, writable⟩ := constructed.ownerLive
  have observations := observed safety 0 (by decide)
  have assigned := first_allocation safety
  let effects := (memory (append safety allocate 7 6 [] (call safety 0).native (call safety 0).key (call safety 0).normalized
    (((call safety 0).key.eval Insertion.Tests.model (call safety 0).taken.2.world.graph.read).getD 0) preparationOwnership
    (preparedFrame 10 (call safety 0).native (operands 0) (firstInstalled safety))).2).effects.allocator * 10 + 8
  obtain ⟨after, finalOwner, ran, valid, ownerFound, ownerTyped, ownerWritable, vector, owned, header, descriptors, _,
      resident, itemOwned, itemReads, _, _, _, live, unique, keys, _, _, _, frame, accepted, apart, candidate⟩ :=
    entry.first_success ops allocate safety 7 6 10 4096 owner CallerInputTests.sentinel
      (call safety 0).source (call safety 0).address Insertion.Tests.model (call safety 0).request []
      (call safety 0).native (call safety 0).native (call safety 0).key (call safety 0).normalized (operands 0)
      (call safety 0).lookup ⟨view (call safety 0).normalized, [], none⟩ (call safety 0).constructed (call safety 0).taken.2
      (call safety 0).duplicate.2 (call safety 0).create.2 (call safety 0).clone.2
      (Normalization.Tests.external_admitted _) (by rw [post.effects]; exact CallerFirstSuccessTests.initial_key_table safety)
      found typed writable (readHeader_items _ _ _ _ constructed.header)
      (Append.readHeader_parts _ _ _ _ constructed.header).2
      (Prod.ext observations.2.1 rfl) (Prod.ext observations.2.2.1 rfl) (Prod.ext observations.2.2.2 rfl)
      ((firstInstalled safety).effects.allocator * 10 + 7) (by
        intro installed called
        have same := Except.ok.inj (called.symm.trans assigned.1)
        rw [same]; exact ⟨rfl, assigned.2.2⟩) effects (by
        intro installed called
        have same := Except.ok.inj (called.symm.trans assigned.1)
        rw [same]; rfl) (by
        have original := CallerInputTests.initialized_owner safety
        exact (Owner.NativeLock.checkHeader_eq_of_lookup safety _ _ 6 (CallerInputTests.owner safety)
          post.valid.memory original.1 original.2.1 ((post.memory _ _ original.1).trans original.1.symm)).trans
          (CallerInputTests.initialized_lock safety))
  rw [assigned.2.1] at vector owned header descriptors
  have checked := entry.checked_execution ops allocate safety 7 6 (call safety 0).source (call safety 0).address
    Insertion.Tests.model (call safety 0).request [] (call safety 0).native (call safety 0).key
    (call safety 0).normalized (call safety 0).lookup (call safety 0).constructed (call safety 0).taken.2 true [] none
    owner CallerInputTests.sentinel found (readHeader_items _ _ _ _ constructed.header)
  rw [ran] at checked
  have projected : (call safety 0).taken.2.world.graph.representatives = some [] :=
    (congrArg Interner.Heap.representatives entry.origin.graph).trans constructed.projected
  refine ⟨after, ?_, ?_, itemReads, fun id native found apart => frame id native (post.memory id native found) apart⟩
  · simp only [Native.insert, projected, Native.body, checked, candidate, Interner.insertionOutcome, Except.mapError]
    rfl
  · obtain ⟨inputCell, inputFound⟩ := (CallerInputTests.source_inputs safety true).2.live
    have inputTyped : inputCell.type = AssemblyItem.viewType := by
      have read : ((CallerInputTests.world safety).memory.memory.heap.lookup
          AssemblyItem.Creation.NativeFields.Tests.source.allocation).map (fun cell => cell.type) = some AssemblyItem.viewType := by
        cases safety <;> insertion_kernel_rfl
      rw [inputFound] at read
      exact Option.some.inj read
    have kept := frame _ inputCell (post.memory _ _ inputFound) (by decide)
    refine ⟨rfl, ?_, valid, ⟨finalOwner, ownerFound, ownerTyped, ownerWritable⟩, owned, vector, header, descriptors,
      resident, ?_, ⟨inputCell, kept, inputTyped, (CallerInputTests.source_inputs safety true).2.frame (kept.trans inputFound.symm)⟩,
      live, unique, ?_, accepted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide), ?_⟩
    · change Cache.put equalityFields (call safety 0).taken.2.world.graph.table (call safety 0).key 0 = OwnedKeys.view (memory after).effects.keys
      rw [keys, OwnedKeys.view_store, entry.origin.graph, constructed.linked]
    · intro logical member
      have same := List.mem_singleton.mp member
      subst logical
      obtain ⟨native, located, itemTyped, _⟩ := itemOwned.2
      refine ⟨native, located, itemTyped, ?_⟩
      apply AssemblyItem.Query.of_members _ _ native valid.memory located itemTyped (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
      · simpa only [row, Call.publicationRow, (AssemblyClone.NativeFields.key_fields (call safety 0).native).1] using itemReads .kind
      · simpa only [row, Call.publicationRow, (AssemblyClone.NativeFields.key_fields (call safety 0).native).2.1] using itemReads .instruction
    · intro key old stored nonempty owned
      obtain ⟨logical, member, nonempty, _⟩ := owned
      have same := List.mem_singleton.mp member
      subst logical
      exact False.elim (nonempty rfl)
    · intro logical member push
      have same := List.mem_singleton.mp member
      subst logical
      change (1 : BitVec 32) = 2 at push
      contradiction

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ReachablePrefixTests
