/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapTablePublication
import Compiler.Extraction.ExpressionMapNewTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapTableTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets ExpressionMap
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)

def prepared (safety : Bool) : World (Publication.Effects Nat) :=
  (prepareGrowth .embedded safety 3 1 (MapAllocationTests.host (some 1024)) (owned safety)).2

def firstKey : Key := ⟨0, 0, 0, [], 0⟩
def secondKey : Key := ⟨0, 1, 0, [], 0⟩

theorem empty_custody (world : World (Publication.Effects σ)) :
    Caller.GraphCustody 7 ⟨0, []⟩ [] world.memory := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [Memory.SliceValid]
  · intro key entry found nonempty impossible; exact impossible.1 rfl
  · simp

/-- Two insertions consume the general theorem on the existing initialized
owner fixture. The allocated map is still the local pre-rehash receiver; this
does not claim installation into the owner's embedded map or probe selection. -/
theorem repeated_from_initialized_owner (safety : Bool) (meaning : Meaning) :
    ∃ first second,
      publishSelectedNew .localMap safety 4 8 5 2 93 firstKey ⟨0, []⟩ 37 (prepared safety) = (.ok (), first) ∧
      publishSelectedNew .localMap safety 4 8 5 3 17 secondKey ⟨0, []⟩ 53 first = (.ok (), second) ∧
      Facts safety 7 3 sentinel 0 second [] ∧
      Table.Binding .localMap safety 4 5 8 second.memory.memory second.memory.effects.keys ∧
      second.memory.effects.keys firstKey = some ⟨0, 37⟩ ∧
      second.memory.effects.keys secondKey = some ⟨0, 53⟩ ∧
      Table.count 8 5 second.memory.memory = 2 := by
  obtain ⟨world, ran, facts, ready, _, _, _⟩ := MapCapacityTests.from_initialized_owner safety meaning
  have same : prepared safety = world := congrArg Prod.snd ran
  rw [← same] at facts ready
  have keys : (prepared safety).memory.effects.keys = fun _ => none := by
    exact prepareGrowth_keys .embedded safety 3 1 _ (owned safety)
  have binding : Table.Binding .localMap safety 4 5 8 (prepared safety).memory.memory (prepared safety).memory.effects.keys := by
    rw [keys]; exact Table.Binding.of_ready ready
  have available : Compiler.ZigAir.Memory.load (prepared safety).memory.memory (Counter.field .localMap safety 4 .available) = .ok (number 6) := by
    simpa only [Counter.field, Initialization.Placement.offset, Nat.zero_add, Local.field] using ready.available
  have unused (i : Nat) (inside : i < 8) : ¬Table.Used (prepared safety).memory.memory 5 i := by
    simp [Table.Used, ready.slots i inside]
  obtain ⟨first, ranFirst, firstFacts, firstBinding, firstKeys, _, firstPost⟩ := facts.publish_selected_new
    .localMap 4 8 5 2 (by intro impossible; cases impossible) binding 93 6 (by decide) available (by decide)
    (unused 2 (by decide)) firstKey ⟨0, []⟩ 37 rfl (by rw [keys]) (empty_custody _)
  have vacant : ¬Table.Used first.memory.memory 5 3 := by
    rw [Table.used_frame (firstPost.metadata_other binding.layout 3 (by decide) (by decide))]
    exact unused 3 (by decide)
  have absent : first.memory.effects.keys secondKey = none := by rw [firstKeys, keys]; decide +kernel
  obtain ⟨second, ranSecond, secondFacts, secondBinding, secondKeys, _, secondPost⟩ := firstFacts.publish_selected_new
    .localMap 4 8 5 3 (by intro impossible; cases impossible) firstBinding 17 5 (by decide) firstPost.availableRead (by decide)
    vacant secondKey ⟨0, []⟩ 53 rfl absent (empty_custody _)
  refine ⟨first, second, ranFirst, ranSecond, secondFacts, secondBinding, ?_, ?_, ?_⟩
  · rw [secondKeys, firstKeys, keys]; decide +kernel
  · rw [secondKeys]; simp [OwnedKeys.store]
  · rw [Table.publication_count ⟨0, 53⟩ firstBinding secondPost (by decide) vacant,
      Table.publication_count ⟨0, 37⟩ binding firstPost (by decide) (unused 2 (by decide))]
    have zero : Table.count 8 5 (prepared safety).memory.memory = 0 := by cases safety <;> decide +kernel
    omega

open Compiler.ZigAir.Memory

/-- Native argument words are an actual live allocation. The earlier key-field
fixture intentionally used an arbitrary pointer and cannot supply this relation. -/
def arguments : Compiler.ZigAir.Memory.Allocation :=
  ⟨9000, .array 3 word, [(0, number 5), (4, number 17), (8, number 4294967295)], true, false⟩
def withArguments : Compiler.ZigAir.Memory.State :=
  { MapNewTests.initialized with
    heap := (3, arguments) :: MapNewTests.initialized.heap
    nextId := 4
    nextAddress := 9012 }
def native : Compiler.ZigAir.Memory.State :=
  (Insertion.publish .localMap true 2 8 1 2 93 MapKeyTests.sample ⟨3, 0⟩ 37 withArguments).2

theorem argument_view : Table.EntryView 8 1 2 native MapKeyTests.sample ⟨3, 37⟩ := by
  refine ⟨⟨?_, ?_⟩, ⟨rfl, ?_⟩, ?_⟩
  · intro slot; cases slot <;> decide +kernel
  · decide +kernel
  · intro i inside
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at inside; omega
    rcases cases with rfl | rfl | rfl
    · change load native (.pointer (.pointer true false word) ⟨3, 0⟩) = .ok (number 5); decide +kernel
    · change load native (.pointer (.pointer true false word) ⟨3, 4⟩) = .ok (number 17); decide +kernel
    · change load native (.pointer (.pointer true false word) ⟨3, 8⟩) = .ok (number 4294967295); decide +kernel
  · intro _; exact ⟨arguments, by decide +kernel, rfl, rfl, rfl⟩

theorem wrong_arguments_rejected :
    ¬Table.EntryView 8 1 2 native { MapKeyTests.sample with arguments := [5, 18, 4294967295] } ⟨3, 37⟩ := by
  intro view
  have equal := (view.unique argument_view).1
  have different : ({ MapKeyTests.sample with arguments := [5, 18, 4294967295] } : Key) ≠ MapKeyTests.sample := by decide +kernel
  exact different equal

theorem phantom_entry_rejected (binding : Table.Binding place safety receiver bucket capacity state (fun _ => none))
    (inside : index < capacity.toNat) : ¬Table.Used state bucket index := by
  intro used
  obtain ⟨_, _, impossible, _⟩ := binding.slots index inside used
  cases impossible

theorem uninitialized_metadata_rejected
    (missing : Metadata.readByte state bucket index = .error .uninitialized) (inside : index < capacity.toNat) :
    ¬Table.Binding place safety receiver bucket capacity state table := by
  intro binding
  obtain ⟨bits, read⟩ := binding.metadata index inside
  rw [missing] at read
  cases read

theorem ghost_only_entry_rejected : ¬Table.Binding .localMap true 2 1 8 MapNewTests.initialized
    (OwnedKeys.store (fun _ => none) MapKeyTests.sample ⟨3, 37⟩) := by
  intro binding
  obtain ⟨i, inside, used, _⟩ := binding.entries MapKeyTests.sample ⟨3, 37⟩ (by simp [OwnedKeys.store])
  have free : Metadata.observe MapNewTests.initialized 1 i = .ok (true, false) := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by change i < 8 at inside; omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  rw [Table.Used, free] at used
  cases used

def wrongSize : Compiler.ZigAir.Memory.State :=
  (Counter.write .localMap true native 2 .size (number 0)).toOption.getD native

theorem wrong_size_rejected : ¬Table.Binding .localMap true 2 1 8 wrongSize table := by
  intro binding
  have wrong : load wrongSize (Counter.field .localMap true 2 .size) ≠
      .ok (number (BitVec.ofNat 32 (Table.count 8 1 wrongSize))) := by decide +kernel
  exact wrong binding.size

theorem wrong_slot_rejected : ¬Table.EntryView 8 1 3 native MapKeyTests.sample ⟨3, 37⟩ := by
  intro view
  have missing : Values.read native 8 1 3 ≠ .ok (number 37) := by decide +kernel
  exact missing view.stored.value

def readonlyArguments : Compiler.ZigAir.Memory.State :=
  { native with heap := native.heap.replace 3 { arguments with writable := false } }

theorem unowned_arguments_rejected : ¬Table.EntryView 8 1 2 readonlyArguments MapKeyTests.sample ⟨3, 37⟩ := by
  intro view
  obtain ⟨cell, found, _, writable, _⟩ := view.owned (by decide)
  have actual : readonlyArguments.heap.lookup 3 = some { arguments with writable := false } := by decide +kernel
  rw [actual] at found
  cases Option.some.inj found
  cases writable

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapTableTests
