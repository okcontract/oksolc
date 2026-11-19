/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapAllocation
import Compiler.Extraction.ExpressionMapBucketStorageTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapAllocationTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ExpressionMap.Buckets
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)

/-- A declared local stack receiver beside the existing source-initialized
compiler owner. This fixture does not prove grow's local-declaration lowering. -/
def localCell (safety writable : Bool) : Compiler.ZigAir.Memory.Allocation :=
  ⟨256, ExpressionMap.allocationType safety,
    ([ExpressionMap.Initialization.Slot.metadata, .size, .available] ++ (if safety then [ExpressionMap.Initialization.Slot.lock] else [])).map
      (fun (slot : ExpressionMap.Initialization.Slot) => (slot.offset safety, slot.value)), writable, true⟩

def seed (safety writable : Bool) : World (Publication.Effects Nat) :=
  { owned safety with memory := { (owned safety).memory with memory :=
    ⟨(4, localCell safety writable) :: (owned safety).memory.memory.heap, 5, 512⟩ } }

theorem seed_valid (safety writable : Bool) : (seed safety writable).memory.memory.valid = true := by
  cases safety <;> cases writable <;> decide +kernel

theorem seed_frame (safety writable : Bool) (id : Nat) (apart : id ≠ 4) :
    (seed safety writable).memory.memory.heap.lookup id = (owned safety).memory.memory.heap.lookup id := by
  change (((4, localCell safety writable) :: (owned safety).memory.memory.heap).find? _).map _ = _
  simp [Compiler.ZigAir.Memory.Heap.lookup, Ne.symm apart]

theorem seed_facts (safety : Bool) (meaning : Meaning) : Facts safety 7 3 sentinel 0 (seed safety true) [] := by
  have initial := Tests.initialized_from_execution safety meaning
  have older (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
      (found : (owned safety).memory.memory.heap.lookup id = some cell) : id ≠ 4 := by
    have bounded := (Compiler.ZigAir.Memory.valid_lookup _ _ _ initial.valid.memory found).1
    have cursor : (owned safety).memory.memory.nextId = 4 := by cases safety <;> rfl
    rw [cursor] at bounded
    omega
  have shape : (owned safety).memory.memory.heap.RetainsShape (seed safety true).memory.memory.heap := by
    intro id cell found
    exact ⟨cell, (seed_frame safety true id (older id cell found)).trans found,
      Compiler.ZigAir.Memory.Allocation.SameShape.refl _⟩
  have valid := initial.valid.private_memory_frame (owned safety).memory (seed safety true).memory.memory 4
    (by cases safety <;> rfl) (seed_valid safety true) shape (seed_frame safety true)
  exact initial.frame (after := seed safety true) valid initial.projected rfl rfl
    (fun id cell found _ => (seed_frame safety true id (older id cell found)).trans found) (fun _ _ found => found)

def host (base : Option Nat) : Compiler.ZigAir.Memory.RegionAllocation.Allocator Nat :=
  fun bytes alignment effects => (base, effects + bytes + alignment)

def execute (safety writable : Bool) (base : Option Nat) :=
  allocateBuckets safety 8 4 (host base) (seed safety writable)

/-- The general consumer runs from the existing compiler initializer and keeps
all native queries while publishing the distinct stack receiver's pointer. -/
theorem from_initialized_owner (safety : Bool) (meaning : Meaning) :
    ∃ after, execute safety true (some 1024) = (.ok (some ⟨5, 0⟩), after) ∧
      Facts safety 7 3 sentinel 0 after [] ∧
      ExpressionMap.Receiver.read safety after.memory.memory ⟨4, 0⟩ = .ok (ExpressionMap.Receiver.value 5) := by
  obtain ⟨after, ran, facts, read, _⟩ := (seed_facts safety meaning).allocate_buckets 4 (localCell safety true)
    (by rfl) rfl rfl 8 (by decide) 1024 (host (some 1024)) 597
    (by cases safety <;> decide +kernel)
    (Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ (seed_valid safety true)
      (by decide) (by decide) (by decide) (by change 512 ≤ 1024; decide))
  exact ⟨after, ran, facts, read⟩

theorem captured_publication (safety : Bool) :
    (execute safety true (some 1024)).1 = .ok (some ⟨5, 0⟩) ∧
    ExpressionMap.Receiver.read safety (execute safety true (some 1024)).2.memory.memory ⟨4, 0⟩ =
      .ok (.optionalObject ExpressionMap.metadataPointerType ⟨8, 8⟩
        (some (.leaf (.pointer ExpressionMap.metadataPointerType ⟨5, 24⟩)))) ∧
    Compiler.ZigAir.Memory.load (execute safety true (some 1024)).2.memory.memory (Header.Slot.capacity.pointer 8 5) =
      .ok (.scalar (.int false 32 8)) ∧
    (execute safety true (some 1024)).2.memory.memory.nextId = 6 ∧
    (execute safety true (some 1024)).2.memory.effects.allocator = 597 := by
  cases safety <;> decide +kernel

theorem receiver_fields_retained (safety : Bool) :
    (∀ slot : ExpressionMap.Initialization.Slot, slot.Active safety → slot ≠ .metadata →
      Compiler.ZigAir.Memory.load (execute safety true (some 1024)).2.memory.memory
        (.pointer (.pointer false false slot.value.type) ⟨4, slot.offset safety⟩) = .ok slot.value) ∧
    ExpressionMap.Initialization.observeEmpty safety (execute safety true (some 1024)).2.memory.memory ⟨3, 0⟩ = .ok () := by
  constructor
  · intro slot active different
    cases slot <;> cases safety <;> simp_all [ExpressionMap.Initialization.Slot.Active]
    all_goals decide +kernel
  · cases safety <;> decide +kernel

theorem oom_retains_receiver (safety : Bool) : execute safety true none =
    (.ok none, { seed safety true with memory := { (seed safety true).memory with
      effects := { (seed safety true).memory.effects with allocator := 597 } } }) := by
  exact allocateBuckets_oom safety (seed safety true) 4 8 (by decide) (host none) 597
    (seed_valid safety true) (by cases safety <;> rfl)

theorem readonly_retains_header (safety : Bool) :
    (execute safety false (some 1024)).1 = .error .readOnly ∧
    (execute safety false (some 1024)).2.memory.memory.nextId = 6 ∧
    (execute safety false (some 1024)).2.memory.effects.allocator = 597 ∧
    ExpressionMap.Receiver.read safety (execute safety false (some 1024)).2.memory.memory ⟨4, 0⟩ =
      .ok ExpressionMap.Initialization.Slot.metadata.value ∧
    Compiler.ZigAir.Memory.load (execute safety false (some 1024)).2.memory.memory (Header.Slot.capacity.pointer 8 5) =
      .ok (.scalar (.int false 32 8)) := by
  let headed := (reserveHeader 8 (host (some 1024)) (seed safety false)).2
  have reserved : reserveHeader 8 (host (some 1024)) (seed safety false) = (.ok (some ⟨5, 0⟩), headed) := by
    apply Prod.ext
    · cases safety <;> decide +kernel
    · rfl
  have rejected : ExpressionMap.Receiver.publish safety 8 ⟨4, 0⟩ 5 headed.memory.memory = .error .readOnly := by
    cases safety <;> decide +kernel
  have ran := allocateBuckets_rejected safety 8 4 (host (some 1024)) (seed safety false) headed ⟨5, 0⟩ .readOnly reserved rejected
  simp only [execute, ran]
  cases safety <;> decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapAllocationTests
