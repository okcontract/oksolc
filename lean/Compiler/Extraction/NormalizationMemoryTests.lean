/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryCaller
import Compiler.Extraction.ArgumentMemoryDuplicationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

/-- A computable witness of the external contract, not a verified native
allocator: allocate above the current high-water mark or return ordinary OOM.
Private effects expose request/free ordering and are retained on OOM. -/
def external (fail : NormalizationOwnership.Allocation → Bool) : External Nat := {
  allocate := fun site state bytes effects =>
    let base := (state.memory.nextAddress / 4 + 1) * 4
    (if fail site || decide (addressLimit < base + bytes) then none else some base, effects + bytes)
  free := fun slice state => state.effects + 100 + slice.items.length }

theorem external_admitted (fail : NormalizationOwnership.Allocation → Bool) : Admitted (external fail) := by
  intro site state values base effects valid _ response
  dsimp only [external] at response
  split at response
  · simp at response
  · have same := (Prod.mk.inj response).1
    cases same
    rename_i allowed
    have bound : (state.memory.nextAddress / 4 + 1) * 4 + values.length * 4 ≤ addressLimit := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at allowed
      omega
    refine ⟨by omega, by dsimp; omega, bound, ?_⟩
    intro entry present layout shaped
    simp only [Compiler.ZigAir.Memory.State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
    have checked := valid.1.2 entry present
    simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact Or.inr (by omega)

def original : Session Nat := ⟨Allocation.Tests.logical, Allocation.Tests.before, 5⟩
def scratchCell : Compiler.ZigAir.Memory.Allocation := ⟨52, .array 2 word, [], true, true⟩
def before : Session Nat := { original with memory := ⟨(3, scratchCell) :: original.memory.heap, 4, 60⟩ }
def source : View := ⟨0, 0, 3⟩
def buffer : View := ⟨3, 0, 2⟩
def items : List NodeId := [3, 1, 2]
def success := external (fun _ => false)
def observed (commutative : Bool) (source : View) (items : List NodeId) (exit : NormalizationOwnership.Exit) :=
  run normalizationOwnershipCode success 160 7 commutative source buffer items exit before
def prepared := (init normalizationOwnershipCode success 160 7 true source buffer items before).2
def scratchPrepared := (init normalizationOwnershipCode success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] before).2

theorem original_valid : Valid original := by
  refine ⟨Allocation.Tests.valid, Allocation.Tests.related, ?_⟩
  intro id block stored
  by_cases other : id = 2
  · subst id; exact ⟨PreparationTests.otherCell, by rfl', rfl⟩
  · by_cases old : id = 1 <;> simp [original, Allocation.Tests.logical, PreparationTests.logical, write, other, old] at stored

theorem actual_caller_allocation : Compiler.ZigAir.Memory.allocate original.memory (.array 2 word) =
    .ok (.pointer (.pointer true false (.array 2 word)) ⟨3, 0⟩, before.memory) := by rfl'

theorem ready_caller : Valid before ∧ Represents before.memory source items ∧
    (∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before) := by
  have contract := caller_buffer original before.memory _ source items original_valid Allocation.Tests.represented actual_caller_allocation
  exact ⟨contract.1, contract.2.1, contract.2.2.1⟩

theorem allocated_transfer : (observed true source items .transfer).1 = .ok (.transferred ⟨4, [1, 2, 3]⟩) ∧
    (observed true source items .transfer).2.effects = 17 := ⟨by rfl', by rfl'⟩
theorem allocated_lookup_cleanup : (observed true source items .lookup).1 = .ok .lookup ∧
    (observed true source items .lookup).2.effects = 120 ∧
    (observed true source items .lookup).2.memory.heap.lookup 4 = none := ⟨by rfl', by rfl', by rfl'⟩
theorem allocated_caller_cleanup : (observed true source items .cleanup).1 = .ok .cleaned ∧
    (observed true source items .cleanup).2.effects = 120 ∧
    (observed true source items .cleanup).2.heap 4 = none := ⟨by rfl', by rfl', by rfl'⟩
theorem transferred_buffer_live :
    load (observed true source items .transfer).2.memory ((⟨4, 0, 3⟩ : View).pointer 1) = .ok (number 2) ∧
    (observed true source items .transfer).2.memory.nextId = 7 := ⟨by rfl', by rfl'⟩

theorem noncommutative_borrows : observed false source items .lookup = (.ok .lookup, before) := by rfl'
theorem noncommutative_duplicate_exact : (observed false source items .transfer).1 = .ok (.transferred ⟨4, items⟩) ∧
    (observed false source items .transfer).2.memory.nextId = 5 := ⟨by rfl', by rfl'⟩
theorem singleton_borrows : observed true ⟨0, 0, 1⟩ [3] .lookup = (.ok .lookup, before) := by rfl'
theorem exact_fit_scratch_lookup : (observed true ⟨0, 0, 2⟩ [3, 1] .lookup).1 = .ok .lookup ∧
    (observed true ⟨0, 0, 2⟩ [3, 1] .lookup).2.effects = 5 ∧
    load (observed true ⟨0, 0, 2⟩ [3, 1] .lookup).2.memory (buffer.pointer 0) = .ok (number 1) := ⟨by rfl', by rfl', by rfl'⟩
theorem scratch_duplicate_after_sort : (observed true ⟨0, 0, 2⟩ [3, 1] .transfer).1 = .ok (.transferred ⟨5, [1, 3]⟩) ∧
    (observed true ⟨0, 0, 2⟩ [3, 1] .transfer).2.effects = 13 := ⟨by rfl', by rfl'⟩
theorem scratch_caller_retains_buffer : (observed true ⟨0, 0, 2⟩ [3, 1] .cleanup).2.effects = 115 ∧
    (observed true ⟨0, 0, 2⟩ [3, 1] .cleanup).2.memory.heap.lookup 5 = none ∧
    load (observed true ⟨0, 0, 2⟩ [3, 1] .cleanup).2.memory (buffer.pointer 1) = .ok (number 3) := ⟨by rfl', by rfl', by rfl'⟩
theorem empty_dead_sentinel : observed true ⟨900, 90, 0⟩ [] .transfer = (.ok (.transferred ⟨4, []⟩), before) ∧
    observed true ⟨900, 90, 0⟩ [] .cleanup = (.ok .cleaned, before) := ⟨by rfl', by rfl'⟩

theorem temporary_oom_retains_effects :
    run normalizationOwnershipCode (external (fun _ => true)) 160 7 true source buffer items .transfer before =
      (.error .outOfMemory, { before with effects := 17 }) := by rfl'
theorem duplicate_oom_after_scratch :
    run normalizationOwnershipCode (external (fun _ => true)) 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .cleanup before =
      (.error .outOfMemory, { scratchPrepared with effects := 13 }) := by rfl'
theorem suspension_retains_allocation :
    let result := run normalizationOwnershipCode success 0 7 true source buffer items .cleanup before
    result.1 = .error (.preparation .incomplete) ∧ result.2.effects = 17 ∧
      result.2.heap 4 = some ⟨7, .arguments items⟩ ∧
      load result.2.memory ((⟨4, 0, 3⟩ : View).pointer 0) = .ok (number 3) := ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem semantic_stack_exhaustion_is_not_oom :
    let result := run normalizationOwnershipCode success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .cleanup
      { before with memory := { before.memory with nextAddress := addressLimit - 8 } }
    result.1 = .error (.preparation (.memory .outOfMemory)) ∧ result.2.effects = 5 := ⟨by rfl', by rfl'⟩

theorem full_contract (exit : NormalizationOwnership.Exit) (budget : Nat) :
    let result := run normalizationOwnershipCode success budget 7 true source buffer items exit before
    Post success budget 7 true source buffer items exit before result.1 result.2 ∧
      (result.1 = .error (.preparation .incomplete) ∨ result.1 = .error (.preparation (.memory .outOfMemory)) ∨ Frame before buffer result.2) :=
  run_verified success budget 7 true source buffer items exit before _ _ ready_caller.1 ready_caller.2.1
    (ready_caller.2.2 true) (external_admitted _) rfl

theorem complete_frame : Frame before buffer (observed true source items .transfer).2 := by
  rcases (full_contract .transfer 160).2 with impossible | impossible | frame
  · change (observed true source items .transfer).1 = _ at impossible
    rw [allocated_transfer.1] at impossible; contradiction
  · change (observed true source items .transfer).1 = _ at impossible
    rw [allocated_transfer.1] at impossible; contradiction
  · exact frame

theorem original_and_other_preserved :
    load (observed true source items .transfer).2.memory (source.pointer 0) = .ok (number 3) ∧
      load (observed true source items .transfer).2.memory ((⟨2, 0, 1⟩ : View).pointer 0) = .ok (number 99) := ⟨by rfl', by rfl'⟩

/-- Instantiate the production theorem at a binary ADD, with an inhabited
allocator contract and the actual caller allocation. -/
theorem production_add (other : Meaning) (read : Read) (sequence : BitVec 32)
    (after : Session Nat)
    (executed : run normalizationOwnershipCode success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .transfer before =
      (.ok (.transferred ⟨5, [1, 3]⟩), after)) :
    (⟨1, some 1, 0⟩ : Item).eval (Folding.wordMeaning other) read [1, 3] sequence =
      (⟨1, some 1, 0⟩ : Item).eval (Folding.wordMeaning other) read [3, 1] sequence := by
  have represented : Represents original.memory ⟨0, 0, 2⟩ [3, 1] := by
    refine ⟨rfl, ?_⟩
    intro index inside
    have cases : index = 0 ∨ index = 1 := by simp at inside; omega
    rcases cases with rfl | rfl <;> rfl'
  have contract := production_verified success 160 7 true ⟨0, 0, 2⟩ [3, 1] .transfer original
    after before.memory _
    (.ok (.transferred ⟨5, [1, 3]⟩)) ⟨1, some 1, 0⟩ other read sequence
    original_valid represented actual_caller_allocation (by rfl') (external_admitted _) executed
  exact contract.2.2 ⟨5, [1, 3]⟩ rfl

theorem production_add_observed (other : Meaning) (read : Read) (sequence : BitVec 32) :
    (⟨1, some 1, 0⟩ : Item).eval (Folding.wordMeaning other) read [1, 3] sequence =
      (⟨1, some 1, 0⟩ : Item).eval (Folding.wordMeaning other) read [3, 1] sequence := by
  have selected := scratch_duplicate_after_sort.1
  generalize observation : observed true ⟨0, 0, 2⟩ [3, 1] .transfer = result at selected
  rcases result with ⟨outcome, after⟩
  dsimp only at selected
  rw [selected] at observation
  exact production_add other read sequence after observation

theorem all_exits_settle (exit : NormalizationOwnership.Exit) :
    ∃ result after budget, (∀ fuel, budget ≤ fuel →
      run normalizationOwnershipCode success fuel 7 true source buffer items exit before = (result, after) ∧
      Post success fuel 7 true source buffer items exit before result after) ∧ result ≠ .error (.preparation .incomplete) :=
  run_settles success 7 true source buffer items exit before ready_caller.1 ready_caller.2.1 (ready_caller.2.2 true) (external_admitted _)

end Compiler.Extraction.Memory.Arguments.Normalization.Tests
