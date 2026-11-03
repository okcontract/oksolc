/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ShiftMasksProofs
import Compiler.Extraction.NestedConstructionTests

namespace Compiler.Extraction.ShiftMasks.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner Compiler.Extraction.Storage
open Compiler.Extraction.Nested Compiler.Extraction.Nested.Tests
open Compiler.Extraction.Nested.ConstructionTests Contract.Yul

def graph (amount mask : Word) := [literal amount, literal 1, operation 99 [] 7,
  operation 27 [0, 1] (Folding.Op.shl.value amount 1 0), literal mask,
  operation 28 [0, 2] (Folding.Op.shr.value amount 7 0)]
def initial (amount mask : Word) : Heap := ⟨readValue (graph amount mask), fun _ => none, none, 0⟩
def reads (amount mask : Word) := storageReads (graph amount mask)

example : shiftedCoverage 0 = .ok (BitVec.allOnes 256) := by rfl
example : shiftedCoverage 255 = .ok 1 := by rfl
example : shiftedCoverage 256 = .ok 0 := by rfl
example : shiftedCoverage 257 = .error .safetyFault := by rfl
example : shiftedCoverage (BitVec.allOnes 256) = .error .safetyFault := by rfl
example : (powerOfTwoShiftProduct (reads 0 0) recording 2 3 42 (initial 0 0)).1 = .ok (some 8) := by rfl
example : (powerOfTwoShiftProduct (reads 255 0) recording 2 3 42 (initial 255 0)).2.table (callKey 27 [0, 2]) = some 42 := by rfl
example : (powerOfTwoShiftProduct (reads 256 0) recording 2 3 42 (initial 256 0)).1 = .ok (some 8) := by rfl
example : (powerOfTwoShiftProduct (reads 257 0) recording 2 3 42 (initial 257 0)).1 = .ok (some 8) := by rfl
example : (powerOfTwoShiftProduct (storageReads [literal 2, operation 27 [0, 0] 8]) failing 0 1 42 (initial 0 0)).1 = .ok none := by rfl
example : (powerOfTwoShiftProduct (storageReads [operation 27 [0] 0]) failing 0 0 42 (initial 0 0)).1 = .ok none := by rfl
example : (powerOfTwoShiftProduct (storageReads corrupt) failing 0 0 42 (initial 0 0)).1 = .error .invalidOptional := by rfl
example : (powerOfTwoShiftProduct (reads 256 0) failing 2 3 42 (initial 256 0)).1 = .error .outOfMemory := by rfl
/-- Only operation construction is observed by this helper fixture. -/
def maskConstructors (build : OperationBuilder Debug) : Associative.Constructors Debug where
  operation := build
  constant := fun _ _ => pure 0
  materialize := fun _ _ _ => pure 0

example : ((removeCoveredShiftMask (reads 0 (BitVec.allOnes 256)) (maskConstructors recording) 4 5 42) (initial 0 (BitVec.allOnes 256))).1 = .ok (some 8) := by rfl
example : ((removeCoveredShiftMask (reads 255 1) (maskConstructors recording) 4 5 42) (initial 255 1)).2.table (callKey 28 [0, 2]) = some 42 := by rfl
example : ((removeCoveredShiftMask (reads 255 0) (maskConstructors failing) 4 5 42) (initial 255 0)).1 = .ok none := by rfl
example : ((removeCoveredShiftMask (reads 256 0) (maskConstructors recording) 4 5 42) (initial 256 0)).1 = .ok (some 8) := by rfl
example : ((removeCoveredShiftMask (reads 257 0) (maskConstructors failing) 4 5 42) (initial 257 0)).1 = .ok none := by rfl
example : ((removeCoveredShiftMask (reads (BitVec.allOnes 256) 0) (maskConstructors failing) 4 5 42) (initial (BitVec.allOnes 256) 0)).1 = .ok none := by rfl
example : ((removeCoveredShiftMask (reads 1 0) (maskConstructors failing) 99 5 42) (initial 1 0)).1 = .ok none := by rfl
example : let result := (removeCoveredShiftMask (reads 256 0) (maskConstructors failing) 4 5 42) (initial 256 0)
    result.1 = .error .outOfMemory ∧ result.2.read 8 = some 28 := by exact ⟨rfl, rfl⟩
example : let p := { Fixtures.primitives with publish := publish false }
    let result := (removeCoveredShiftMask (reads 256 0) (maskConstructors (internerBuilder p)) 4 5 ()) (initial 256 0)
    result.1 = .error .outOfMemory ∧ result.2.read 7 = some 42 := by exact ⟨rfl, rfl⟩

end Compiler.Extraction.ShiftMasks.Tests
