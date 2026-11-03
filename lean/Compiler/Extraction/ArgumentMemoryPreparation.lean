/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryProofs
import Compiler.Extraction.InsertionSortStorage

namespace Compiler.Extraction.Memory.Arguments
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.InsertionSort

theorem owned_retained (before after : Compiler.ZigAir.Memory.State) (id length : Nat)
    (owned : Owned before id length) (retained : before.heap.RetainsShape after.heap) : Owned after id length := by
  obtain ⟨cell, found, typed, writable, stack⟩ := owned
  obtain ⟨updated, lookup, shape⟩ := retained id cell found
  exact ⟨updated, lookup, shape.2.1.trans typed, shape.2.2.1.trans writable, shape.2.2.2.trans stack⟩

theorem copied_owned (budget : Nat) (state : Compiler.ZigAir.Memory.State) (source target : View)
    (id length : Nat) (valid : state.valid = true) (owned : Owned state id length) :
    Owned (Copied.run budget state source target).2 id length :=
  owned_retained state _ id length owned (Copied.run_storage budget state source target valid).2

/-- Only this existing allocation's payload changes. Its allocator and extent
remain those registered before preparation; this is a logical projection, not
a new allocator operation or permission to adopt arbitrary native storage. -/
def Updated (before after : Heap) (id : Nat) (values : List NodeId) : Prop :=
  ∃ allocator previous, before id = some ⟨allocator, .arguments previous⟩ ∧
    previous.length = values.length ∧ after = write before id (some ⟨allocator, .arguments values⟩)

theorem updated_owner (before after : Heap) (id allocator : Nat) (previous values : List NodeId)
    (updated : Updated before after id values) (registered : before id = some ⟨allocator, .arguments previous⟩) :
    after id = some ⟨allocator, .arguments values⟩ := by
  obtain ⟨owner, old, stored, _, rfl⟩ := updated
  have same : owner = allocator ∧ old = previous := by simpa using stored.symm.trans registered
  rw [same.1]
  exact write_same before id (some ⟨allocator, .arguments values⟩)

theorem updated_length (before after : Heap) (id allocator : Nat) (previous values : List NodeId)
    (updated : Updated before after id values) (registered : before id = some ⟨allocator, .arguments previous⟩) :
    previous.length = values.length := by
  obtain ⟨owner, old, stored, length, _⟩ := updated
  have same : owner = allocator ∧ old = previous := by simpa using stored.symm.trans registered
  simpa only [same.2] using length

/-- During private initialization the destination's old payload is unobserved:
the existing Related predicate is applied with that one logical entry removed.
No initialized contents are claimed there until the actual copy/sort supplies
them. The frame carries other allocations' full relation to the result. -/
theorem related_publish (heap : Heap) (before after : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (target : View) (values : List NodeId) (others : Related (write heap target.allocation none) before)
    (framed : HeapFrame target before after) (owned : Owned after target.allocation values.length)
    (first : target.first = 0) (represented : Represents after target values) :
    Related (write heap target.allocation (some ⟨allocator, .arguments values⟩)) after := by
  intro owner id items nonempty stored
  by_cases selected : id = target.allocation
  · subst id
    have same : allocator = owner ∧ values = items := by simpa [write] using stored
    rcases same with ⟨rfl, rfl⟩
    refine ⟨owned, ?_⟩
    have sameView : view ⟨target.allocation, values⟩ = target := by
      cases target
      simp only [view, View.mk.injEq, true_and]
      exact ⟨first.symm, represented.1⟩
    rw [sameView]
    exact represented
  · have original : write heap target.allocation none id = some ⟨owner, .arguments items⟩ := by
      simpa [write, selected] using stored
    obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ := others owner id items nonempty original
    refine ⟨⟨cell, (framed.allocations id selected).trans found, typed, writable, stack⟩, represented.1, ?_⟩
    intro index inside
    exact (Compiler.ZigAir.Memory.load_eq_of_lookup before after true false word _
      (framed.allocations id selected)).trans (represented.2 index inside)

/-- Preparation establishes a full logical/typed relation from an uninitialized
owned destination. It derives the terminal result and budget, preserves the
registered allocator/extent, and retains exact source/frame observations.
OOM remains a semantic preparation fault; this theorem performs no cleanup. -/
theorem copied_refines (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (destination : ArgumentSlice) (items : List NodeId)
    (valid : state.valid = true) (owned : Owned state destination.address destination.items.length)
    (registered : heap destination.address = some ⟨allocator, .arguments destination.items⟩)
    (others : Related (write heap destination.address none) state)
    (represented : Represents state source items) (length : source.length = destination.items.length)
    (separate : Compiler.ZigAir.Memory.WordCopy.disjoint source (view destination) = true) :
    ∃ result after values projected, Captured.Settles (fun budget => Copied.run budget state source (view destination)) (result, after) ∧
      Updated heap projected destination.address values ∧ Related projected after ∧
      after.valid = true ∧ values.Perm items ∧ Represents after source items ∧ HeapFrame (view destination) state after ∧
      SliceValid allocator projected ⟨destination.address, values⟩ ∧
      ((result = .ok () ∧ values = sortIds items) ∨ result = .error (.memory .outOfMemory)) := by
  obtain ⟨result, after, values, settled, connected, permutation, preserved, frame, effect⟩ :=
    Copied.run_refines state source (view destination) items valid
      (owned_writable state destination.address destination.items.length owned) represented length separate
  have counts : values.length = destination.items.length := connected.values.1
  obtain ⟨budget, adequate⟩ := settled
  dsimp only at adequate
  have retained := copied_owned budget state source (view destination) destination.address destination.items.length valid owned
  rw [adequate budget (Nat.le_refl budget)] at retained
  have cap : Owned after destination.address values.length := by simpa only [counts] using retained
  refine ⟨result, after, values, write heap destination.address (some ⟨allocator, .arguments values⟩),
    ⟨budget, adequate⟩, ⟨allocator, destination.items, registered, counts.symm, rfl⟩,
    related_publish heap state after allocator (view destination) values others frame cap rfl connected.values,
    connected.valid, permutation, preserved, frame, Or.inr ?_, effect⟩
  exact write_same heap destination.address (some ⟨allocator, .arguments values⟩)

/-- Every observed run is covered. Suspension retains its actual partially
written heap and owned allocation, but does not publish an initialized payload.
Every terminal observation admits the same allocator-preserving projection. -/
theorem copied_result (budget : Nat) (heap : Heap) (state after : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (destination : ArgumentSlice) (items : List NodeId) (result : Except InsertionSort.Heap.Fault Unit)
    (valid : state.valid = true) (owned : Owned state destination.address destination.items.length)
    (registered : heap destination.address = some ⟨allocator, .arguments destination.items⟩)
    (others : Related (write heap destination.address none) state)
    (represented : Represents state source items) (length : source.length = destination.items.length)
    (separate : Compiler.ZigAir.Memory.WordCopy.disjoint source (view destination) = true)
    (done : Copied.run budget state source (view destination) = (result, after)) :
    result = .error .incomplete ∨ ∃ values projected,
      Updated heap projected destination.address values ∧ Related projected after ∧
      after.valid = true ∧ values.Perm items ∧ Represents after source items ∧ HeapFrame (view destination) state after ∧
      SliceValid allocator projected ⟨destination.address, values⟩ ∧
      ((result = .ok () ∧ values = sortIds items) ∨ result = .error (.memory .outOfMemory)) := by
  rcases Copied.run_result budget state after source (view destination) items result valid
      (owned_writable state destination.address destination.items.length owned) represented length separate done with
    incomplete | ⟨values, connected, permutation, preserved, frame, effect⟩
  · exact Or.inl incomplete
  · have counts : values.length = destination.items.length := connected.values.1
    have retained := copied_owned budget state source (view destination) destination.address destination.items.length valid owned
    rw [done] at retained
    have cap : Owned after destination.address values.length := by simpa only [counts] using retained
    refine Or.inr ⟨values, write heap destination.address (some ⟨allocator, .arguments values⟩),
      ⟨allocator, destination.items, registered, counts.symm, rfl⟩,
      related_publish heap state after allocator (view destination) values others frame cap rfl connected.values,
      connected.valid, permutation, preserved, frame, Or.inr ?_, effect⟩
    exact write_same heap destination.address (some ⟨allocator, .arguments values⟩)

end Compiler.Extraction.Memory.Arguments
