/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingRegistryFrame
import Compiler.Extraction.RepresentativeBackingReleaseTests

namespace Compiler.Extraction.RepresentativeArray.Backing.Registry.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

abbrev Effects := Release.Tests.Effects
def before : Session Effects := Release.Tests.before
def request (response : Option Nat := some 800) : Allocate Effects :=
  fun allocator bytes alignment effects => (response, effects ++ [(allocator, 0, bytes, alignment)])
def ready : Session Effects :=
  ⟨Compiler.Extraction.Memory.write before.heap 4 (some ⟨7, .representatives []⟩),
    RegionAllocation.extend before.memory (Backing.type 7) 224 800, before.effects ++ [(7, 0, 224, 8)]⟩

theorem initial_valid : Valid before := Release.Tests.initial_valid

theorem fits : RegionAllocation.Fits before.memory ⟨224, 8⟩ 800 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  simp only [before, Release.Tests.before, Release.Tests.memory, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl <;> cases shaped <;> decide

theorem actual_reservation : run request 7 7 before = (.ok (some ⟨4, 0⟩), ready) := rfl

theorem without_final_premises : ∃ after, run request 7 7 before = (.ok (some ⟨4, 0⟩), after) ∧
    Valid after ∧ Release.Owned 7 ⟨4, 0⟩ 7 after ∧
    after.memory = RegionAllocation.extend before.memory (Backing.type 7) 224 800 ∧
    after.heap = Compiler.Extraction.Memory.write before.heap 4 (some ⟨7, .representatives []⟩) ∧
    after.effects = before.effects ++ [(7, 0, 224, 8)] :=
  verified request 7 7 800 before _ initial_valid (by decide) (by decide) rfl fits

theorem ready_owned : Valid ready ∧ Release.Owned 7 ⟨4, 0⟩ 7 ready := by
  obtain ⟨after, executed, valid, owned, _⟩ := without_final_premises
  rw [actual_reservation] at executed
  rw [← (Prod.mk.inj executed).2] at valid owned
  exact ⟨valid, owned⟩

theorem uninitialized_is_not_published : ready.memory.heap.lookup 4 = some ⟨800, Backing.type 7, [], true, false⟩ ∧
    Expression.readFields ready.memory false ⟨4, 32⟩ = .error .uninitialized ∧
    readHeader ready.memory ⟨3, 0⟩ = readHeader before.memory ⟨3, 0⟩ := by decide

theorem actual_release : (Release.run Release.Tests.external 7 ⟨4, 0⟩ 7 ready).1 = .ok () ∧
    (Release.run Release.Tests.external 7 ⟨4, 0⟩ 7 ready).2.heap 4 = none ∧
    (Release.run Release.Tests.external 7 ⟨4, 0⟩ 7 ready).2.memory.heap.lookup 4 = none ∧
    (Release.run Release.Tests.external 7 ⟨4, 0⟩ 7 ready).2.effects = before.effects ++ [(7, 0, 224, 8), (7, 800, 224, 8)] := by decide

theorem release_without_owned_premise : ∃ allocated after,
    run request 7 7 before = (.ok (some ⟨4, 0⟩), allocated) ∧
    Release.run Release.Tests.external 7 ⟨4, 0⟩ 7 allocated = (.ok (), after) ∧
    Release.Post 4 allocated after ∧ after.heap = before.heap ∧
    (∀ query, after.memory.heap.lookup query = before.memory.heap.lookup query) ∧
    after.memory.nextId = 5 ∧ after.memory.nextAddress = 1024 ∧
    after.effects = before.effects ++ [(7, 0, 224, 8), (7, 800, 224, 8)] :=
  release_derived request Release.Tests.external 7 7 800 before _ initial_valid (by decide) (by decide) rfl fits

theorem oom_keeps_effects : run (request none) 7 7 before =
    (.ok none, { before with effects := before.effects ++ [(7, 0, 224, 8)] }) := rfl

theorem wrong_region_keeps_effects : run (request (some 801)) 7 7 before =
    (.error (.memory .memoryValidity), { before with effects := before.effects ++ [(7, 0, 224, 8)] }) := rfl

theorem overlap_keeps_old_backing : run (request (some 512)) 7 7 before =
    (.error (.memory .memoryValidity), { before with effects := before.effects ++ [(7, 0, 224, 8)] }) := rfl

theorem null_region_rejects : run (request (some 0)) 7 7 before =
    (.error (.memory .memoryValidity), { before with effects := before.effects ++ [(7, 0, 224, 8)] }) := rfl

theorem extent_overflow_is_oom : run request 7 (addressLimit / 32) before = (.ok none, before) := rfl
theorem capacity_width_rejects : run request 7 addressLimit before = (.error (.memory .malformed), before) := rfl

def collision : Session Effects :=
  { before with heap := Compiler.Extraction.Memory.write before.heap 4 (some ⟨8, .bytes 8⟩) }

theorem collision_keeps_allocation : (run request 7 7 collision).1 = .error (.registry .notFresh) ∧
    (run request 7 7 collision).2.heap 4 = some ⟨8, .bytes 8⟩ ∧
    (run request 7 7 collision).2.memory = ready.memory ∧
    (run request 7 7 collision).2.effects = ready.effects := ⟨rfl, rfl, rfl, rfl⟩

def invalid : Session Effects := { collision with memory := { before.memory with nextId := 0 } }
theorem empty_does_not_register : run request 9 0 invalid = (.ok (some ⟨0, 0⟩), invalid) := rfl
theorem invalid_state_skips_allocator : run request 7 7 invalid = (.error (.memory .malformed), invalid) := rfl

theorem all_outcomes_preserve_parent (allocator capacity : Nat) (response : Option Nat) :
    WordArray.Represents (run (request response) allocator capacity before).2.memory Release.Tests.parent [99, 1] :=
  (parent_borrow (request response) allocator capacity before initial_valid Release.Tests.parent [99, 1]
    Expression.Tests.argumentsAllocation rfl Release.Tests.parent_contents).2.1

theorem old_vector_and_arguments_survive : ready.heap 2 = before.heap 2 ∧
    ready.memory.heap.lookup 2 = before.memory.heap.lookup 2 ∧ ready.memory.heap.lookup 1 = before.memory.heap.lookup 1 ∧
    ready.memory.nextId = 5 ∧ ready.memory.nextAddress = 1024 := ⟨rfl, rfl, rfl, rfl, rfl⟩

def reused : Session Effects :=
  ⟨Compiler.Extraction.Memory.write before.heap 2 none, erase before.memory 2, before.effects⟩
theorem dead_address_has_new_lifetime : (run (request (some 512)) 7 5 reused).1 = .ok (some ⟨4, 0⟩) ∧
    (run (request (some 512)) 7 5 reused).2.memory.heap.lookup 2 = none ∧
    (run (request (some 512)) 7 5 reused).2.memory.heap.lookup 4 = some ⟨512, Backing.type 5, [], true, false⟩ ∧
    (run (request (some 512)) 7 5 reused).2.memory.nextId = 5 ∧
    (run (request (some 512)) 7 5 reused).2.memory.nextAddress = 728 := by decide

theorem selected_allocator_brand : (run request 19 7 before).2.heap 4 = some ⟨19, .representatives []⟩ ∧
    (run request 19 7 before).2.effects = before.effects ++ [(19, 0, 224, 8)] := ⟨rfl, rfl⟩

end Compiler.Extraction.RepresentativeArray.Backing.Registry.Tests
