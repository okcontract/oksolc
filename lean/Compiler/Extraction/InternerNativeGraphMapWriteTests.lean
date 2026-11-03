/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphMapWrites
import Compiler.Extraction.InternerNativeGraphTests
import Compiler.Extraction.InternerPublicationMemoryBoundaryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapWriteTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ExpressionMap.Initialization
open ConstructorItem
open NativeRecursion.Tests (program)
open RecursiveBorrowedTests (rows)

attribute [local irreducible] program

/-- Reuse the completed recursive execution with its nonempty backing, live
keys and operands. Every representative query survives an admitted map-field
write. This does not assert that an arbitrary new field value describes a valid
native hash map; bucket/key correspondence remains a separate obligation. -/
theorem recursive_fields (safety : Bool) (depth : Nat) (slot : Slot) (value : Compiler.ZigAir.Memory.Value)
    (typed : value.type = slot.value.type) (valid : value.valid = true) (active : slot.Active safety) :
    ∃ memory, writeValue safety (program safety (depth + 2)).2.memory.memory ⟨6, 0⟩ slot value = .ok memory ∧
      WrittenValue safety (program safety (depth + 2)).2.memory.memory memory 6 slot value ∧
      Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
        { (program safety (depth + 2)).2 with memory := { (program safety (depth + 2)).2.memory with memory } } (rows safety) ∧
      (∀ id opcode, Operation.run memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
        Operation.run (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode) ∧
      (∀ id, Constant.value memory (Owner.headerAddress ⟨6, 0⟩) id =
        Constant.value (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id) := by
  have facts := Tests.recursive_after safety depth
  obtain ⟨memory, ran, post, after⟩ := facts.write_map slot value typed valid active
  refine ⟨memory, ran, post, after, ?_, ?_⟩
  · intro id opcode
    exact (after.operations id opcode).trans (facts.operations id opcode).symm
  · intro id
    exact (after.constants id).trans (facts.constants id).symm

/-- All 32-bit counts use the same store/frame proof; zero initialization is
only one specialization. The theorem does not supply a hash-map size invariant. -/
theorem recursive_count (safety : Bool) (depth : Nat) (count : BitVec 32) :
    ∃ memory, writeValue safety (program safety (depth + 2)).2.memory.memory ⟨6, 0⟩ .size (number count) = .ok memory ∧
      ExpressionMap.readSize safety memory ⟨6, 0⟩ = .ok (number count) ∧
      (∀ id opcode, Operation.run memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
        Operation.run (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode) := by
  obtain ⟨memory, ran, post, _, queries, _⟩ := recursive_fields safety depth .size (number count) rfl
    (number_valid count) (by simp [Slot.Active])
  exact ⟨memory, ran, (size_read safety memory ⟨6, 0⟩).symm.trans post.value, queries⟩

/-- Nonnull metadata is retained as a pointer value. No pointee allocation or
bucket contents are inferred from this field-write theorem. -/
theorem recursive_metadata (safety : Bool) (depth : Nat) (address : Compiler.ZigAir.Memory.Address) :
    let value : Compiler.ZigAir.Memory.Value :=
      .optionalObject ExpressionMap.metadataPointerType ⟨8, 8⟩ (some (.leaf (.pointer ExpressionMap.metadataPointerType address)))
    ∃ memory, writeValue safety (program safety (depth + 2)).2.memory.memory ⟨6, 0⟩ .metadata value = .ok memory ∧
      read safety memory ⟨6, 0⟩ .metadata = .ok value ∧
      (∀ id, Constant.value memory (Owner.headerAddress ⟨6, 0⟩) id =
        Constant.value (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id) := by
  intro value
  have valid : value.valid = true := by
    change (decide (ExpressionMap.metadataPointerType = ExpressionMap.metadataPointerType) && true) = true
    simp only [decide_true, Bool.true_and]
  obtain ⟨memory, ran, post, _, _, queries⟩ := recursive_fields safety depth .metadata value rfl valid (by simp [Slot.Active])
  exact ⟨memory, ran, post.value, queries⟩

open GraphInit.OwnerMemory.Tests (before)

theorem inactive_lock_rejected :
    (writeValue false (before false true).memory ⟨3, 0⟩ .lock (.scalar (.int false 64 0))).map (fun _ => ()) =
      .error .unsupported := by decide +kernel

theorem wrong_type_rejected :
    (writeValue true (before true true).memory ⟨3, 0⟩ .size (.scalar (.bool true))).map (fun _ => ()) =
      .error .malformed := by decide +kernel

theorem out_of_range_rejected :
    (writeValue true (before true true).memory ⟨3, 0⟩ .size (.scalar (.int false 32 4294967296))).map (fun _ => ()) =
      .error .malformed := by decide +kernel

theorem readonly_rejected :
    (writeValue true (before true false).memory ⟨3, 0⟩ .size (.scalar (.int false 32 1))).map (fun _ => ()) =
      .error .readOnly := by decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapWriteTests
