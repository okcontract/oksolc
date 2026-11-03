/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NormalizationTests

namespace Compiler.Extraction.Interner.ObservedTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Nested Contract.Yul

def model := Recursive.Tests.model
def constant : Storage.Cell := { item := ⟨2, none, 3⟩, otherValue := 0, itemAddress := 10 }
def caller : Storage.Cell := { item := ⟨1, some 0x33, 0⟩, otherValue := 3, itemAddress := 20 }
def constantHeap := observedHeap [constant] (fun _ => none)
def callerHeap := observedHeap [caller] (fun _ => none)

theorem constant_coherent : Storage.Coherent model [constant] := by
  intro cell member
  have same : cell = constant := by simpa using member
  subst cell
  rfl

theorem caller_coherent : Storage.Coherent model [caller] := by
  intro cell member
  have same : cell = caller := by simpa using member
  subst cell
  rfl

theorem constant_valid : Invariant model constantHeap :=
  observed_invariant model _ _ (by intro key id found; cases found) constant_coherent

theorem caller_valid : Invariant model callerHeap :=
  observed_invariant model _ _ (by intro key id found; cases found) caller_coherent

/-- Equal values and cache entries do not determine native structural reads. -/
theorem same_values : constantHeap.read = callerHeap.read := by
  funext id
  cases index : id.toNat with
  | zero => simp [constantHeap, callerHeap, observedHeap, Storage.readValue, index,
      constant, caller, Storage.Cell.value, Storage.Cell.isPush, Storage.Cell.dataValue]
  | succ index => simp [constantHeap, callerHeap, observedHeap, Storage.readValue, index]
example : constantHeap.table = callerHeap.table := rfl
example : (representativeReads constantHeap).constant 0 = .ok (some 3) := by rfl
example : (representativeReads callerHeap).constant 0 = .ok none := by rfl
example : (representativeReads callerHeap).operation 0 0x33 = .ok (some ⟨0, []⟩) := by rfl
example : (representativeReads constantHeap).operation 0 0x33 = .ok none := by rfl
example : (representativeReads callerHeap).constant 1 = .ok none := by rfl

def unrepresented := { constantHeap with representatives := none }
example : (representativeReads unrepresented).constant 0 = .error .safetyFault := by rfl
example : (representativeReads unrepresented).operation 0 0x33 = .error .safetyFault := by rfl

def forgedRead := { callerHeap with read := fun _ => some 42 }
theorem forged_read_rejected : ¬Invariant model forgedRead := by
  intro valid
  have impossible := congrFun valid.representation.1 (0 : NodeId)
  change (some (42 : Word)) = some 3 at impossible
  exact (by decide : (some (42 : Word)) ≠ some 3) impossible

def forgedCaller := { caller with otherValue := 4 }
def forgedStructure := observedHeap [forgedCaller] (fun _ => none)
theorem forged_structure_rejected : ¬Invariant model forgedStructure := by
  intro valid
  have impossible := valid.representation.2 forgedCaller (by simp)
  change (some (3 : Word)) = some 4 at impossible
  exact (by decide : (some (3 : Word)) ≠ some 4) impossible

-- A concrete witness for recursive preservation with source-bound structural
-- reads. Insertion deliberately fails; the idempotence rule needs no allocation.
def primitives : Primitives := { NormalizationTests.primitives with insert := fun _ _ => fail .outOfMemory }
theorem contracts : Recursive.PrimitiveContracts model primitives where
  normalize := NormalizationTests.normalizes
  insert := by intro key deterministic before value valid evaluated; exact Safe.fail _ _ _ _ valid
  publish := publish_safe model true

def request : Request := ⟨⟨1, some 0x16, 0⟩, [0, 0], 99⟩
def result := Recursive.unfold primitives representativeReads 64 1 request callerHeap
example : result.1 = .ok 0 := by rfl
example : result.2.read 0 = some 3 := by rfl
example : result.2.representatives = some [caller] := by rfl
example : result.2.table ⟨1, 0x16, 0, [0, 0], 99⟩ = some 0 := by rfl

theorem preserved : Invariant model result.2 ∧ Stable callerHeap result.2 ∧ result.2.read 0 = some 3 :=
  Recursive.unfold_representatives_safe Recursive.Tests.env Recursive.Tests.base Recursive.Tests.pushes
    primitives contracts 64 1 request callerHeap 3 caller_valid rfl (.ok 0) result.2 rfl

def publicationFailure := Recursive.unfold { primitives with publish := publish false } representativeReads 64 1 request callerHeap
example : publicationFailure.1 = .error .outOfMemory := by rfl
example : publicationFailure.2.representatives = some [caller] := by rfl
example : publicationFailure.2.table ⟨1, 0x16, 0, [0, 0], 99⟩ = none := by rfl

def recursiveFailure := Recursive.unfold primitives representativeReads 64 2 ⟨⟨1, some 1, 0⟩, [0, 0], 99⟩ callerHeap
example : recursiveFailure.1 = .error .outOfMemory := by rfl
example : recursiveFailure.2.representatives = some [caller] := by rfl

end Compiler.Extraction.Interner.ObservedTests
