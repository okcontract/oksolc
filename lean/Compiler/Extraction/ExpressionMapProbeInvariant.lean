/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbePublication

namespace Compiler.Extraction.ExpressionMap.Probe
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Buckets Insertion
open Compiler.Extraction.Cache (Key)

/-- Original native table admission, maintained by initialization and each
new-slot publication. The hash function remains arbitrary; its native producer
and growth/rehash transport are separate obligations. -/
structure Invariant (hashes : Key → BitVec 64) (place : Initialization.Placement) (safety : Bool)
    (receiver bucket : Nat) (capacity : BitVec 32) (available : BitVec 32) (state : State) (table : OwnedKeys.Table) : Prop where
  binding : Table.Binding place safety receiver bucket capacity state table
  power : Power capacity
  canonical : Canonical state capacity bucket
  routing : Routing hashes state capacity bucket table
  availableRead : load state (Counter.field place safety receiver .available) = .ok (number available)
  budget : Table.count capacity bucket state + available.toNat = (Local.Availability.word capacity).toNat

variable {hashes : Key → BitVec 64} {place : Initialization.Placement} {safety : Bool}
    {receiver bucket index : Nat} {capacity available size : BitVec 32} {state after : State} {table : OwnedKeys.Table}

theorem Invariant.room (inv : Invariant hashes place safety receiver bucket capacity available state table)
    (positive : 0 < available.toNat) : Table.count capacity bucket state < capacity.toNat := by
  have bound := (Local.Availability.word_exact capacity).2.2
  have budget := inv.budget
  omega

theorem Invariant.of_ready (hashes : Key → BitVec 64) (ready : Local.EmptyReady safety receiver bucket capacity base state)
    (power : Power capacity) :
    Invariant hashes .localMap safety receiver bucket capacity (Local.Availability.word capacity) state (fun _ => none) := by
  have zero : Table.count capacity bucket state = 0 := by
    apply List.countP_eq_zero.mpr
    intro i member
    simp [Table.occupied, ready.slots i (List.mem_range.mp member)]
  exact ⟨Table.Binding.of_ready ready, power, Canonical.of_ready ready, Routing.empty hashes state capacity bucket,
    by simpa only [Counter.field, Initialization.Placement.offset, Nat.zero_add, Local.field, Local.Availability.value, number]
      using ready.available, by rw [zero]; omega⟩

theorem Invariant.published (inv : Invariant hashes place safety receiver bucket capacity available state table)
    (key : Key) (incoming : OwnedKeys.Entry)
    (post : Published place safety receiver bucket index capacity (fingerprint (hashes key)) available
      (BitVec.ofNat 32 (Table.count capacity bucket state)) key ⟨incoming.address, 0⟩ incoming.id state after)
    (inside : index < capacity.toNat) (vacant : ¬Table.Used state bucket index) (absent : table key = none)
    (route : RouteTo state capacity bucket (hashes key) index) (view : Table.EntryView capacity bucket index after key incoming) :
    Invariant hashes place safety receiver bucket capacity (available - 1#32) after (OwnedKeys.store table key incoming) := by
  refine ⟨inv.binding.after_new_slot incoming post inside vacant absent view, inv.power,
    inv.canonical.published post inv.binding.layout inside,
    inv.routing.published inv.power inv.binding incoming post inside vacant route view, post.availableRead, ?_⟩
  have changed := Table.publication_count incoming inv.binding post inside vacant
  have exactDecrement := post.availableExact
  have budget := inv.budget
  omega

end Compiler.Extraction.ExpressionMap.Probe
