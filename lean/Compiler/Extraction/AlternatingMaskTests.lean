/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AlternatingMaskProofs
import Compiler.Extraction.NestedConstructionTests

namespace Compiler.Extraction.AlternatingMask.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Nested.Tests (literal operation corrupt)
open Compiler.Extraction.Nested.ConstructionTests (callKey)

-- Both alternatives are ANDs with two literals: all inner choices can match.
-- The native loop order must still select the first AND's right-hand constant.
def graph := [literal 7, literal 3, literal 13, literal 5,
  operation 22 [0, 1] 3, operation 22 [2, 3] 5, operation 23 [4, 5] 7, literal 6]
def reads := storageReads graph
def empty : Heap := ⟨fun _ => none, fun _ => none, none, 0⟩

theorem coherent : Coherent (Folding.wordMeaning Compiler.Extraction.Nested.Tests.fallback) graph := by
  intro cell member
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

-- This trace adapter deliberately makes no ConstructorSound claim. Slot zero
-- counts callbacks; fresh result slots record their opcodes; the table records
-- exact arguments and debug data. Failure retains the failing call's writes.
def record (failAt : Nat) (opcode : Opcode) (ids : List NodeId) (debug : NodeId) : Action NodeId := fun heap =>
  let step := (heap.read 0).getD 0 |>.toNat
  let id : NodeId := BitVec.ofNat 32 (10 + step)
  let after := { heap with
    read := fun index => if index == 0 then some (BitVec.ofNat 256 (step + 1))
      else if index == id then some (opcode.setWidth 256) else heap.read index,
    table := fun key => if key == callKey opcode ids then some debug else heap.table key }
  (if failAt == step + 1 then .error .outOfMemory else .ok id, after)

def constructors (failAt : Nat) : Constructors NodeId where
  operation := record failAt
  constant := fun value => record failAt 0 [value.setWidth 32]
  materialize := fun id value => record failAt 254 [id, value.setWidth 32]

def run (failAt : Nat) := distributeAlternatingMask reads (constructors failAt) 6 7 42 empty

example : matchCandidate reads ⟨false, false, false⟩ 6 7 = .ok (some ⟨0, 5, 7, 3, 6, ⟨0, [0, 1]⟩, ⟨0, [4, 5]⟩, 0, 1⟩) := by rfl
example : matchCandidate reads ⟨false, false, true⟩ 7 6 = .ok (some ⟨0, 5, 7, 3, 6, ⟨0, [0, 1]⟩, ⟨0, [4, 5]⟩, 0, 1⟩) := by rfl
example : matchCandidate reads ⟨false, true, false⟩ 6 7 = .ok (some ⟨2, 4, 7, 5, 6, ⟨0, [2, 3]⟩, ⟨0, [4, 5]⟩, 0, 0⟩) := by rfl
example : matchCandidate reads ⟨false, true, true⟩ 7 6 = .ok (some ⟨2, 4, 7, 5, 6, ⟨0, [2, 3]⟩, ⟨0, [4, 5]⟩, 0, 0⟩) := by rfl
example : matchCandidate reads ⟨true, false, false⟩ 6 7 = .ok (some ⟨1, 5, 7, 7, 6, ⟨0, [0, 1]⟩, ⟨0, [4, 5]⟩, 1, 1⟩) := by rfl
example : matchCandidate reads ⟨true, false, true⟩ 7 6 = .ok (some ⟨1, 5, 7, 7, 6, ⟨0, [0, 1]⟩, ⟨0, [4, 5]⟩, 1, 1⟩) := by rfl
example : matchCandidate reads ⟨true, true, false⟩ 6 7 = .ok (some ⟨3, 4, 7, 13, 6, ⟨0, [2, 3]⟩, ⟨0, [4, 5]⟩, 1, 0⟩) := by rfl
example : matchCandidate reads ⟨true, true, true⟩ 7 6 = .ok (some ⟨3, 4, 7, 13, 6, ⟨0, [2, 3]⟩, ⟨0, [4, 5]⟩, 1, 0⟩) := by rfl

example : (run 0).1 = .ok (some 14) := by rfl
example : (run 0).2.table (callKey 0 [2]) = some 42 := by rfl
example : (run 0).2.table (callKey 22 [0, 10]) = some 42 := by rfl
example : (run 0).2.table (callKey 254 [7, 6]) = some 42 := by rfl
example : (run 0).2.table (callKey 22 [5, 12]) = some 42 := by rfl
example : (run 0).2.table (callKey 23 [11, 13]) = some 42 := by rfl
example : (distributeAlternatingMask reads (constructors 0) 7 6 42 empty).1 = .ok (some 14) := by rfl

example : (run 1).1 = .error .outOfMemory ∧ (run 1).2.read 0 = some 1 ∧ (run 1).2.read 11 = none := by exact ⟨rfl, rfl, rfl⟩
example : (run 2).1 = .error .outOfMemory ∧ (run 2).2.read 0 = some 2 ∧ (run 2).2.read 12 = none := by exact ⟨rfl, rfl, rfl⟩
example : (run 3).1 = .error .outOfMemory ∧ (run 3).2.read 0 = some 3 ∧ (run 3).2.read 13 = none := by exact ⟨rfl, rfl, rfl⟩
example : (run 4).1 = .error .outOfMemory ∧ (run 4).2.read 0 = some 4 ∧ (run 4).2.read 14 = none := by exact ⟨rfl, rfl, rfl⟩
example : (run 5).1 = .error .outOfMemory ∧ (run 5).2.read 0 = some 5 ∧ (run 5).2.read 14 = some 23 := by exact ⟨rfl, rfl, rfl⟩
example : (run 2).2.table (callKey 22 [0, 10]) = some 42 := by rfl

example : (distributeAlternatingMask reads (constructors 0) 99 7 42 empty).1 = .ok none := by rfl
example : (distributeAlternatingMask reads (constructors 0) 6 99 42 empty).2.read 0 = none := by rfl
example : matchCandidate (storageReads [literal 6, operation 23 [0] 6]) ⟨false, false, false⟩ 1 0 = .ok none := by rfl
example : matchCandidate (storageReads [literal 6, operation 22 [0] 6, operation 23 [1, 0] 6])
    ⟨false, false, false⟩ 2 0 = .ok none := by rfl
example : (distributeAlternatingMask (storageReads (literal 6 :: corrupt)) (constructors 0) 1 0 42 empty).1 = .error .invalidOptional := by rfl
example : (distributeAlternatingMask { reads with constant := fun _ => .error .safetyFault }
    (constructors 0) 6 7 42 empty).2.read 0 = none := by rfl

-- Reaching the last candidate exercises every ordered miss, without adapting
-- reads to the requested choice. Only left constants and the second OR arm fit.
def lastGraph := [literal 6, operation 99 [] 7, literal 3,
  operation 22 [2, 1] 3, operation 23 [1, 3] 7]
example : (distributeAlternatingMask (storageReads lastGraph) (constructors 0) 0 4 42 empty).2.table
    (callKey 22 [1, 10]) = some 42 := by rfl
example : (distributeAlternatingMask (storageReads lastGraph) (constructors 0) 0 4 42 empty).2.table
    (callKey 254 [0, 6]) = some 42 := by rfl

end Compiler.Extraction.AlternatingMask.Tests
