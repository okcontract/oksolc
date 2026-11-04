/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ObservedStorage
import Compiler.Extraction.ObservedHeapTests

namespace Compiler.Extraction.Interner.ObservedStorageTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open ObservedTests (model caller callerHeap caller_valid)
set_option maxRecDepth 4096

def cell : Storage.Cell := {
  item := ⟨1, some 0x19, 0⟩, otherValue := ~~~(3 : Word), itemAddress := 30,
  arguments := [0], sequence := 99, argumentsAddress := 40
}
def key : Key := ⟨1, 0x19, 0, [0], 99⟩
def succeeds : Storage.Allocation → Bool := fun _ => true
def result := observedInsertTransaction [caller] (fun _ => none) cell key true succeeds

theorem binding : keyCode.run cell.item cell.arguments cell.sequence = some key := rfl
theorem denotation : key.eval model (Storage.readValue [caller]) = some cell.value := rfl

theorem preserved : Invariant model result.2 ∧ Stable callerHeap result.2 ∧ result.2.read 1 = some cell.value := by
  exact observed_insert_transaction_safe model [caller] (fun _ => none) cell key true succeeds
    caller_valid binding denotation

theorem action_preserved : Safe model (observedInsert cell key true succeeds) callerHeap
    (fun id after => after.read id = some cell.value) :=
  observed_insert_safe model cell key true succeeds callerHeap caller_valid binding denotation

example : observedInsert cell key true succeeds callerHeap = result := by rfl
example : (observedInsert cell key true succeeds ObservedTests.unrepresented).1 = .error .safetyFault := by rfl
example : (observedInsert cell key true succeeds ObservedTests.unrepresented).2 = ObservedTests.unrepresented := by rfl

example : result.1 = .ok 1 := by rfl
example : result.2.representatives = some [caller, cell] := by rfl
example : result.2.read 0 = some 3 := by rfl
example : result.2.read 1 = some (~~~(3 : Word)) := by rfl
example : result.2.table key = some 1 := by rfl
example : result.2.table { key with sequence := 0 } = none := by rfl
example : (representativeReads result.2).operation 1 0x19 = .ok (some ⟨40, [0]⟩) := by rfl
example : (representativeReads result.2).operation 0 0x33 = .ok (some ⟨0, []⟩) := by rfl
example : (representativeReads result.2).constant 0 = .ok none := by rfl
example : (representativeReads result.2).constant 1 = .ok none := by rfl

def failAt (site : Storage.Allocation) : Storage.Allocation → Bool := fun actual => actual != site
def failure (site : Storage.Allocation) := observedInsertTransaction [caller] (fun _ => none) cell key true (failAt site)

theorem each_failure_restores (site : Storage.Allocation) :
    (failure site).1 = .error .outOfMemory ∧ (failure site).2 = callerHeap := by
  cases site <;> exact ⟨rfl, rfl⟩
example : (failure .publish).2.read 1 = none := by rfl
example : (failure .publish).2.table key = none := by rfl
example : (representativeReads (failure .publish).2).operation 1 0x19 = .ok none := by rfl

-- The non-deterministic path transfers its normalized buffer into the graph;
-- it skips duplication and cache publication, which may independently fail.
def uncached := observedInsertTransaction [caller] (fun _ => none) cell key false
  (Storage.allocationPolicy false true true true false)
example : uncached.1 = .ok 1 := by rfl
example : uncached.2.representatives = some [caller, cell] := by rfl
example : uncached.2.table key = none := by rfl

theorem uncached_preserved : Invariant model uncached.2 ∧ Stable callerHeap uncached.2 ∧
    uncached.2.read 1 = some cell.value := by
  exact observed_insert_transaction_safe model [caller] (fun _ => none) cell key false
    (Storage.allocationPolicy false true true true false) caller_valid binding denotation

-- Word/cache agreement by itself cannot justify a clone with different
-- operands. The bad cell retains the requested word but does not denote it.
def wrongCell := { cell with arguments := [1] }
def wrongResult := observedInsertTransaction [caller] (fun _ => none) wrongCell key true succeeds
example : wrongResult.2.read 1 = some cell.value := by rfl
example : wrongResult.2.table key = some 1 := by rfl

theorem wrong_binding_rejected : keyCode.run wrongCell.item wrongCell.arguments wrongCell.sequence ≠ some key := by decide

theorem wrong_cell_rejected : ¬Invariant model wrongResult.2 := by
  intro valid
  have coherent : Storage.Coherent model [caller, wrongCell] := valid.representation.2
  have impossible := coherent wrongCell (by simp)
  change (some (3 : Word)) = some (~~~(3 : Word)) at impossible
  exact (by decide : (some (3 : Word)) ≠ some (~~~(3 : Word))) impossible

end Compiler.Extraction.Interner.ObservedStorageTests
