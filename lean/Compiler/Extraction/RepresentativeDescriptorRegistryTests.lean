/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorRegistry
import Compiler.Extraction.RepresentativeDescriptorAppendTests

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation.RegistryTests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

def before (runtimeSafety : Bool) : Session (List (Nat × Nat)) := {
  memory := (Tests.before runtimeSafety).memory
  effects := []
  heap := Compiler.Extraction.Memory.write (Tests.before runtimeSafety).heap 2 (some ⟨7, .representatives Tests.nodes⟩) }

theorem initial_valid (runtimeSafety : Bool) : Valid (before runtimeSafety) := by
  have valid := Backing.Registry.vector_write_valid (Tests.before runtimeSafety) 7 2 (Tests.backing Tests.allCells) Tests.nodes
    (Tests.initial_valid runtimeSafety) (by cases runtimeSafety <;> rfl) rfl
  exact ⟨valid.memory, valid.related, valid.injected⟩

theorem registered_spare (runtimeSafety : Bool) : ∃ after : Session (List (Nat × Nat)),
    AppendTests.attempt runtimeSafety = ((.ok (some ()), after.memory), after.effects) ∧ Valid after ∧
    Compiler.Extraction.Memory.Vector 7 after.heap 2 AppendTests.cells ∧ Prefix after.memory 2 AppendTests.cells ∧
    (∀ id, representativeFields after.memory ⟨3, 16⟩ id =
      .ok ((Storage.representativeProgram.run AppendTests.cells id).map (values id.toNat))) := by
  obtain ⟨after, executed, _, _, valid, vector, _, represented, queries, _⟩ :=
    spare_registered runtimeSafety (before runtimeSafety) 7 3 2 3 (Backing.Relocation.Tests.owner runtimeSafety)
      (Tests.backing Tests.allCells) Tests.nodes AppendTests.third (AppendTests.request none) (initial_valid runtimeSafety)
      (by cases runtimeSafety <;> rfl) rfl rfl (by cases runtimeSafety <;> rfl) rfl rfl
      (by cases runtimeSafety <;> rfl) (by cases runtimeSafety <;> rfl) rfl
      (Tests.prefix_from_initialization runtimeSafety) (by decide) (by decide) (by decide)
  exact ⟨after, executed, valid, vector, represented, queries⟩

theorem every_outcome_valid (runtimeSafety : Bool) (argumentsLength : Nat) (id sequence : Int) :
    let outcome := AppendTests.attempt runtimeSafety argumentsLength id sequence
    Valid ({before runtimeSafety with memory := outcome.1.2, effects := outcome.2} : Session (List (Nat × Nat))) :=
  spare_session runtimeSafety (before runtimeSafety) 3 2 3 (Backing.Relocation.Tests.owner runtimeSafety) Tests.nodes
    ⟨0, 0⟩ ⟨1, 0⟩ argumentsLength id sequence (AppendTests.request none) (initial_valid runtimeSafety)
    (by cases runtimeSafety <;> rfl) rfl (by cases runtimeSafety <;> rfl) (by cases runtimeSafety <;> rfl) (by decide) (by decide)

/-- The partial native row can coexist with the old logical vector only at an
intermediate failure point. It cannot satisfy the extended descriptor relation. -/
theorem partial_keeps_old_vector (runtimeSafety : Bool) :
    let after : Session (List (Nat × Nat)) := {before runtimeSafety with memory := AppendTests.after runtimeSafety AppendTests.itemOnly}
    Valid after ∧ Compiler.Extraction.Memory.Vector 7 after.heap 2 Tests.nodes ∧
      Prefix after.memory 2 Tests.nodes ∧ ¬Prefix after.memory 2 AppendTests.cells := by
  have valid := every_outcome_valid runtimeSafety addressLimit 2 31
  rw [AppendTests.malformed_arguments_keep_length_and_item] at valid
  have rows := AppendTests.partial_row_is_not_published runtimeSafety
  exact ⟨valid, rfl, rows.1, rows.2.1⟩

theorem wrong_allocator_rejects (runtimeSafety : Bool) :
    ¬Compiler.Extraction.Memory.Vector 8 (before runtimeSafety).heap 2 Tests.nodes := by
  simp [Compiler.Extraction.Memory.Vector, before, Compiler.Extraction.Memory.write]

theorem missing_row_rejects (runtimeSafety : Bool) :
    ¬Compiler.Extraction.Memory.Vector 7 (before runtimeSafety).heap 2 [Tests.first] := by
  simp [Compiler.Extraction.Memory.Vector, before, Compiler.Extraction.Memory.write, Tests.nodes]

theorem native_prefix_is_not_registration (runtimeSafety : Bool) :
    Prefix (Tests.before runtimeSafety).memory 2 Tests.nodes ∧
      ¬Compiler.Extraction.Memory.Vector 7 (Tests.before runtimeSafety).heap 2 Tests.nodes := by
  refine ⟨Tests.prefix_from_initialization runtimeSafety, ?_⟩
  change ¬(some ⟨7, .representatives []⟩ : Option Compiler.Extraction.Memory.Allocation) = some ⟨7, .representatives Tests.nodes⟩
  simp [Tests.nodes]

end Compiler.Extraction.RepresentativeArray.DescriptorRelation.RegistryTests
