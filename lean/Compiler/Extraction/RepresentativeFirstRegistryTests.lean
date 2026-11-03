/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeFirstRegistry
import Compiler.Extraction.RepresentativeDescriptorRegistryTests

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation.FirstRegistryTests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

def registry : Compiler.Extraction.Memory.Heap :=
  Compiler.Extraction.Memory.write (fun _ => none) 1 (some ⟨7, .arguments [777, 99, 1, 5]⟩)
def before (runtimeSafety stack : Bool) : Session (List (Nat × Nat)) :=
  ⟨registry, AppendTests.emptyState runtimeSafety stack, []⟩
def owner (runtimeSafety stack : Bool) : Allocation := AppendTests.emptyOwner runtimeSafety stack
def request := AppendTests.request
def registeredRequest (response : Option Nat) : Backing.Registry.Allocate (List (Nat × Nat)) :=
  fun allocator => request (if allocator = 7 then response else none)

theorem initial_valid (runtimeSafety stack : Bool) : Valid (before runtimeSafety stack) := by
  refine ⟨Growth.Tests.initial_valid runtimeSafety stack, ?_, ?_⟩
  · intro allocator id values nonempty stored
    by_cases same : id = 1
    · subst id
      have same : (⟨7, .arguments [777, 99, 1, 5]⟩ : Compiler.Extraction.Memory.Allocation) = ⟨allocator, .arguments values⟩ :=
        Option.some.inj (by simpa only [before, registry, Compiler.Extraction.Memory.write, ↓reduceIte] using stored)
      cases same
      obtain ⟨_, represented⟩ := Backing.RegisteredCopy.Tests.initial_valid.related 7 1 [777, 99, 1, 5] (by decide) rfl
      have frame : (before runtimeSafety stack).memory.heap.lookup 1 = Backing.RegisteredCopy.Tests.before.memory.heap.lookup 1 := by
        cases runtimeSafety <;> cases stack <;> rfl
      exact ⟨⟨Expression.Tests.argumentsAllocation, by cases runtimeSafety <;> cases stack <;> rfl, rfl, rfl, rfl⟩,
        represented_frame _ _ represented frame⟩
    · simp [before, registry, Compiler.Extraction.Memory.write, same] at stored
  · intro id block stored
    by_cases same : id = 1
    · subst id; exact ⟨Expression.Tests.argumentsAllocation, by cases runtimeSafety <;> cases stack <;> rfl, rfl⟩
    · simp [before, registry, Compiler.Extraction.Memory.write, same] at stored

theorem registered_first (runtimeSafety stack : Bool) : ∃ after : Session (List (Nat × Nat)),
    Append.Execution.ownerRun runtimeSafety (before runtimeSafety stack).memory ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩ 4 0 23
      (request (some 800)) [] = ((.ok (some ()), after.memory), after.effects) ∧
    Valid after ∧ Compiler.Extraction.Memory.Vector 7 after.heap 4 [Tests.first] ∧
    Backing.Release.Owned 7 ⟨4, 0⟩ 5 after ∧ Prefix after.memory 4 [Tests.first] ∧
    after.memory.nextId = 5 ∧ after.effects = [(160, 8)] ∧
    (∀ id, representativeFields after.memory ⟨3, 16⟩ id =
      .ok ((Storage.representativeProgram.run [Tests.first] id).map (values id.toNat))) := by
  obtain ⟨after, executed, _, effects, valid, vector, owned, _, represented, nextId, _, queries, _⟩ :=
    first_registered runtimeSafety (before runtimeSafety stack) 7 3 (owner runtimeSafety stack) Growth.Tests.sentinel Tests.first
      800 (registeredRequest (some 800)) [(160, 8)] (initial_valid runtimeSafety stack) rfl rfl rfl
      (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl)
      (by decide) rfl (Capacity.Tests.fits runtimeSafety stack) (Growth.Tests.empty_unlocked runtimeSafety true stack)
  exact ⟨after, executed, valid, vector, owned, represented, nextId, effects, queries⟩

theorem actual_queries (runtimeSafety stack : Bool) :
    Prefix (AppendTests.firstAfter runtimeSafety stack) 4 [Tests.first] ∧
      ∀ id, representativeFields (AppendTests.firstAfter runtimeSafety stack) ⟨3, 16⟩ id =
        .ok ((Storage.representativeProgram.run [Tests.first] id).map (values id.toNat)) := by
  obtain ⟨after, executed, _, _, _, represented, _, _, queries⟩ := registered_first runtimeSafety stack
  have same : after.memory = AppendTests.firstAfter runtimeSafety stack :=
    congrArg (fun outcome => outcome.1.2) (executed.symm.trans (AppendTests.actual_first runtimeSafety stack))
  exact same ▸ ⟨represented, queries⟩

theorem every_outcome_valid (runtimeSafety stack : Bool) (length : Nat) (id sequence : Int) :
    let outcome := Append.Execution.ownerRun runtimeSafety (before runtimeSafety stack).memory ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩
      length id sequence (request (some 800)) []
    Valid ({before runtimeSafety stack with memory := outcome.1.2, effects := outcome.2} : Session (List (Nat × Nat))) :=
  first_session runtimeSafety (before runtimeSafety stack) 3 (owner runtimeSafety stack) Growth.Tests.sentinel ⟨0, 0⟩ ⟨1, 4⟩
    length id sequence 800 (request (some 800)) [(160, 8)] (initial_valid runtimeSafety stack) rfl rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl) rfl (Capacity.Tests.fits runtimeSafety stack) (Growth.Tests.empty_unlocked runtimeSafety true stack)

theorem every_outcome_releasable (runtimeSafety stack : Bool) (length : Nat) (id sequence : Int) :
    let outcome := Append.Execution.ownerRun runtimeSafety (before runtimeSafety stack).memory ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩
      length id sequence (request (some 800)) []
    let after : Session (List (Nat × Nat)) := { before runtimeSafety stack with
      memory := outcome.1.2
      effects := outcome.2
      heap := Compiler.Extraction.Memory.write registry 4 (some ⟨7, .representatives []⟩) }
    Valid after ∧ Compiler.Extraction.Memory.Vector 7 after.heap 4 [] ∧ Backing.Release.Owned 7 ⟨4, 0⟩ 5 after :=
  first_reserved runtimeSafety (before runtimeSafety stack) 7 3 (owner runtimeSafety stack) Growth.Tests.sentinel ⟨0, 0⟩ ⟨1, 4⟩
    length id sequence 800 (registeredRequest (some 800)) [(160, 8)] (initial_valid runtimeSafety stack) rfl rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl) rfl (Capacity.Tests.fits runtimeSafety stack) (Growth.Tests.empty_unlocked runtimeSafety true stack)

theorem oom_keeps_registry (runtimeSafety stack : Bool) :
    Append.Execution.ownerRun runtimeSafety (before runtimeSafety stack).memory ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ addressLimit (-1) (-1)
      (request none) [] = ((.ok none, (before runtimeSafety stack).memory), [(160, 8)]) ∧
    Valid ({before runtimeSafety stack with effects := [(160, 8)]} : Session (List (Nat × Nat))) ∧ registry 4 = none :=
  first_registry_oom runtimeSafety (before runtimeSafety stack) 3 (owner runtimeSafety stack) Growth.Tests.sentinel ⟨0, 0⟩ ⟨1, 4⟩
    addressLimit (-1) (-1) (request none) [(160, 8)] (initial_valid runtimeSafety stack) rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl) rfl
    (Growth.Tests.empty_unlocked runtimeSafety true stack)

theorem partial_execution (runtimeSafety stack : Bool) :
    Append.Execution.ownerRun runtimeSafety (before runtimeSafety stack).memory ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ addressLimit 0 29
      (request (some 800)) [] = ((.error .malformed, Append.Execution.Tests.after runtimeSafety stack Append.Execution.Tests.withItem), [(160, 8)]) := by
  have selected := Owner.root_header_pointer runtimeSafety (before runtimeSafety stack).memory 3 (owner runtimeSafety stack)
    true (initial_valid runtimeSafety stack).memory rfl rfl
  simpa only [Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected, Append.Execution.run] using Append.Execution.Tests.malformed_arguments_keep_length_and_item runtimeSafety stack

theorem partial_is_owned_not_complete (runtimeSafety stack : Bool) :
    let after : Session (List (Nat × Nat)) := {
      heap := Compiler.Extraction.Memory.write registry 4 (some ⟨7, .representatives []⟩)
      memory := Append.Execution.Tests.after runtimeSafety stack Append.Execution.Tests.withItem
      effects := [(160, 8)] }
    Valid after ∧ Compiler.Extraction.Memory.Vector 7 after.heap 4 [] ∧ Backing.Release.Owned 7 ⟨4, 0⟩ 5 after ∧
      ¬Prefix after.memory 4 [Tests.first] ∧ representativeFields after.memory ⟨3, 16⟩ 0 = .error .uninitialized := by
  have retained := every_outcome_releasable runtimeSafety stack addressLimit 0 29
  rw [partial_execution] at retained
  refine ⟨retained.1, retained.2.1, retained.2.2, ?_, (Append.Execution.Tests.partial_descriptor_is_not_complete runtimeSafety stack).2⟩
  intro represented
  have row := represented 0 Tests.first rfl
  have rejected : ¬Row (Append.Execution.Tests.after runtimeSafety stack Append.Execution.Tests.withItem) 4 0 Tests.first := by
    simp only [Row]; cases runtimeSafety <;> cases stack <;> decide
  exact rejected row

theorem empty_arguments_registered (runtimeSafety stack : Bool) :
    let cell := {Tests.first with arguments := [], argumentsAddress := 97}
    ∃ after : Session (List (Nat × Nat)),
      Append.Execution.ownerRun runtimeSafety (before runtimeSafety stack).memory ⟨3, 0⟩ ⟨0, 0⟩ ⟨97, 0⟩ 0 0 23
        (request (some 800)) [] = ((.ok (some ()), after.memory), after.effects) ∧
      Valid after ∧ Compiler.Extraction.Memory.Vector 7 after.heap 4 [cell] ∧ Prefix after.memory 4 [cell] := by
  obtain ⟨after, executed, _, _, valid, vector, _, _, represented, _⟩ :=
    first_registered runtimeSafety (before runtimeSafety stack) 7 3 (owner runtimeSafety stack) Growth.Tests.sentinel
      {Tests.first with arguments := [], argumentsAddress := 97} 800 (registeredRequest (some 800)) [(160, 8)]
      (initial_valid runtimeSafety stack) rfl rfl rfl (by cases runtimeSafety <;> cases stack <;> rfl)
      (by cases runtimeSafety <;> cases stack <;> rfl) (by decide) rfl (Capacity.Tests.fits runtimeSafety stack) (Growth.Tests.empty_unlocked runtimeSafety true stack)
  exact ⟨after, executed, valid, vector, represented⟩

theorem alias_registry_is_invalid (runtimeSafety stack : Bool) :
    ¬Valid ({before runtimeSafety stack with
      heap := Compiler.Extraction.Memory.write registry 4 (some ⟨7, .representatives []⟩)} : Session (List (Nat × Nat))) := by
  intro valid
  obtain ⟨backing, found, _⟩ := valid.injected 4 ⟨7, .representatives []⟩ rfl
  have absent : (before runtimeSafety stack).memory.heap.lookup 4 = none := by cases runtimeSafety <;> cases stack <;> rfl
  rw [absent] at found
  contradiction

theorem registered_parent_offset (runtimeSafety stack : Bool) : ∃ after : Session (List (Nat × Nat)),
    Append.Execution.ownerRun runtimeSafety (before runtimeSafety stack).memory ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩ 4 0 23
      (request (some 800)) [] = ((.ok (some ()), after.memory), after.effects) ∧
    Compiler.Extraction.Memory.Vector 7 after.heap 4 [Tests.first] ∧
    WordArray.Represents after.memory ⟨1, 1, 2⟩ [99, 1] := by
  obtain ⟨after, executed, _, vector, _⟩ := registered_first runtimeSafety stack
  have retained := Append.Execution.owner_parent_borrow runtimeSafety (before runtimeSafety stack).memory 3 (owner runtimeSafety stack)
    ⟨0, 0⟩ ⟨1, 0⟩ 4 0 23 (request (some 800)) [] ⟨1, 1, 2⟩ [99, 1] 4 Expression.Tests.argumentsAllocation
    (initial_valid runtimeSafety stack).memory rfl rfl (by cases runtimeSafety <;> cases stack <;> rfl) rfl
    (Growth.Tests.parent_contents runtimeSafety stack)
  rw [executed] at retained
  exact ⟨after, executed, vector, retained.2.2.1⟩

theorem different_callback_oom (runtimeSafety stack : Bool) :
    Append.Execution.ownerRun runtimeSafety (before runtimeSafety stack).memory ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ addressLimit (-1) (-1)
      (registeredRequest (some 800) 8) [] = ((.ok none, (before runtimeSafety stack).memory), [(160, 8)]) ∧
    Valid ({before runtimeSafety stack with effects := [(160, 8)]} : Session (List (Nat × Nat))) ∧ registry 4 = none :=
  first_registry_oom runtimeSafety (before runtimeSafety stack) 3 (owner runtimeSafety stack) Growth.Tests.sentinel ⟨0, 0⟩ ⟨1, 4⟩
    addressLimit (-1) (-1) (registeredRequest (some 800) 8) [(160, 8)] (initial_valid runtimeSafety stack) rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl) rfl

    (Growth.Tests.empty_unlocked runtimeSafety true stack)

end Compiler.Extraction.RepresentativeArray.DescriptorRelation.FirstRegistryTests
