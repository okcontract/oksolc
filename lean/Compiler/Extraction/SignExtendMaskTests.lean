/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.SignExtendMaskProofs
import Compiler.Extraction.AssociativeTests

namespace Compiler.Extraction.SignExtendMask.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative
open Compiler.Extraction.Nested.Tests (literal operation corrupt)
open Compiler.Extraction.Associative.Tests (constructors)
open Compiler.Extraction.Nested.ConstructionTests (callKey failing)
open Contract.Yul

def graph (index mask : Word) := [literal mask, literal index, operation 99 [] 384,
  operation 11 [1, 2] (Folding.Op.signextend.value index 384 0)]
def reads (index mask : Word) := storageReads (graph index mask)
def initial : Heap := ⟨readValue (graph 0 255), fun _ => none, none, 0⟩

example : nativeLowMask 0 = .ok 255 := by rfl
example : nativeLowMask 30 = .ok (lowBits 248) := by rfl
example : nativeLowMask 31 = .error .invalidCast := by rfl
example : nativeLowMask (BitVec.allOnes 256) = .error .integerOverflow := by rfl
example : nativeLowMask (BitVec.twoPow 256 255) = .error .integerOverflow := by rfl
example : lowMaskRead 31 = .error .safetyFault := by rfl
example : 255#256 &&& Folding.Op.signextend.value 0 384 0 = 128 := by rfl
example : 256#256 &&& Folding.Op.signextend.value 0 128 0 ≠ 256#256 &&& 128 := by decide

-- Trace callbacks observe order/captures/debug data, not semantic constructors.
example : (stripRedundantSignExtendMask (reads 0 255) constructors 0 3 42 initial).1 = .ok (some 9) := by rfl
example : (stripRedundantSignExtendMask (reads 0 255) constructors 0 3 42 initial).2.table (callKey 254 [0, 255]) = some 42 := by rfl
example : (stripRedundantSignExtendMask (reads 0 255) constructors 0 3 42 initial).2.table (callKey 22 [8, 2]) = some 42 := by rfl
example : (stripRedundantSignExtendMask (reads 0 0) constructors 0 3 42 initial).1 = .ok (some 9) := by rfl
example : (stripRedundantSignExtendMask (reads 30 (lowBits 248)) constructors 0 3 42 initial).1 = .ok (some 9) := by rfl
example : (stripRedundantSignExtendMask (reads 0 256) constructors 0 3 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (reads 30 (BitVec.twoPow 256 248)) constructors 0 3 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (reads 31 255) constructors 0 3 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (reads (BitVec.allOnes 256) 255) constructors 0 3 42 initial).2.read 8 = none := by rfl
example : (stripRedundantSignExtendMask (reads 0 255) constructors 99 3 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (reads 0 255) constructors 0 99 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (reads 0 255) constructors 0 2 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (storageReads [literal 255, operation 11 [] 0]) constructors 0 1 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (storageReads [literal 255, operation 11 [0] 0]) constructors 0 1 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (storageReads [literal 255, operation 11 [0, 0, 0] 0]) constructors 0 1 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (storageReads [literal 255, operation 11 [99, 0] 0]) constructors 0 1 42 initial).1 = .ok none := by rfl
example : (stripRedundantSignExtendMask (storageReads (literal 255 :: corrupt)) constructors 0 1 42 initial).1 = .error .invalidOptional := by rfl
example : (stripRedundantSignExtendMask (storageReads corrupt) constructors 0 0 42 initial).1 = .ok none := by rfl
example : let changed := { constructors with materialize := fun original value => failing 254 [original, value.setWidth 32] }
    let result := stripRedundantSignExtendMask (reads 0 255) changed 0 3 42 initial
    result.1 = .error .outOfMemory ∧ result.2.read 8 = some 254 ∧
      result.2.table (callKey 22 [8, 2]) = none := by exact ⟨rfl, rfl, rfl⟩
example : let result := stripRedundantSignExtendMask (reads 0 255) { constructors with operation := failing } 0 3 42 initial
    result.1 = .error .outOfMemory ∧ result.2.read 8 = some 254 ∧ result.2.read 9 = some 22 := by exact ⟨rfl, rfl, rfl⟩
example : let p := { Fixtures.primitives with publish := publish false }
    let result := stripRedundantSignExtendMask (reads 0 255) (implementedConstructors p) 0 3 () initial
    result.1 = .error .outOfMemory ∧ result.2.read 7 = some 42 := by exact ⟨rfl, rfl⟩

end Compiler.Extraction.SignExtendMask.Tests
