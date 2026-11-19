/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssociativeProofs
import Compiler.Extraction.NestedConstructionTests

namespace Compiler.Extraction.Associative.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner Compiler.Extraction.Storage
open Compiler.Extraction.Nested Compiler.Extraction.Nested.Tests
open Compiler.Extraction.Nested.ConstructionTests Contract.Yul

-- An opaque operand, a literal, and both source operand orders. These fixtures
-- observe constructor order/debug data; semantic preservation uses the proofs.
def graph := [operation 99 [] 7, literal 2, operation 1 [0, 1] 9,
  operation 1 [1, 0] 9, literal 3, operation 99 [] 4]
def initial : Heap := ⟨readValue graph, fun _ => none, none, 0⟩
def reads := storageReads graph
def constant : Word → NodeId → Action NodeId := fun value => recording 0 [value.setWidth 32]
def materialize : NodeId → Word → NodeId → Action NodeId := fun original value =>
  recording 254 [original, value.setWidth 32]
def constructors : Constructors NodeId where
  operation := recording
  constant := constant
  materialize := materialize

example : isAssociative 1 = true := by rfl
example : isAssociative 2 = true := by rfl
example : isAssociative 22 = true := by rfl
example : isAssociative 23 = true := by rfl
example : isAssociative 24 = true := by rfl
example : isAssociative 3 = false := by rfl
example : combineConstants 1 (BitVec.allOnes 256) 1 = .ok 0 := by rfl
example : combineConstants 2 (BitVec.allOnes 256) 2 = .ok (BitVec.allOnes 256 - 1) := by rfl
example : combineConstants 22 7 2 = .ok 2 := by rfl
example : combineConstants 23 7 2 = .ok 7 := by rfl
example : combineConstants 24 7 2 = .ok 5 := by rfl
example : combineConstants 3 7 2 = .error .safetyFault := by rfl

example : ((reassociate reads constructors 1 2 4 false 42) initial).1 = .ok (some 9) := by rfl
example : ((reassociate reads constructors 1 2 4 false 42) initial).2.table (callKey 0 [5]) = some 42 := by rfl
example : ((reassociate reads constructors 1 2 4 true 42) initial).2.table (callKey 1 [0, 8]) = some 42 := by rfl
example : ((reassociate reads constructors 1 3 4 false 42) initial).2.table (callKey 1 [0, 8]) = some 42 := by rfl
example : ((reassociate reads constructors 1 2 5 false 42) initial).2.table (callKey 1 [0, 5]) = some 42 := by rfl
example : ((reassociate reads constructors 1 2 5 true 42) initial).2.table (callKey 1 [5, 0]) = some 42 := by rfl
example : ((reassociate reads constructors 1 2 5 true 42) initial).2.table (callKey 254 [1, 2]) = some 42 := by rfl
example : ((reassociate reads constructors 1 2 5 true 42) initial).2.table (callKey 1 [8, 9]) = some 42 := by rfl
example : ((reassociate reads constructors 1 99 5 true 42) initial).1 = .ok none := by rfl
example : ((reassociate reads constructors 99 0 5 true 42) initial).1 = .ok none := by rfl
example : ((reassociate (storageReads corrupt) constructors 1 0 5 true 42) initial).1 = .error .invalidOptional := by rfl
example : let changed := { constructors with materialize := fun original value => failing 254 [original, value.setWidth 32] }
    let result := (reassociate reads changed 1 2 5 false 42) initial
    result.1 = .error .outOfMemory ∧ result.2.read 8 = some 1 ∧ result.2.read 9 = some 254 := by exact ⟨rfl, rfl, rfl⟩
example : ((reassociate reads { constructors with constant := fun value => failing 0 [value.setWidth 32] }
    1 2 4 false 42) initial).2.table (callKey 1 [0, 8]) = none := by rfl
example : (materializeConstant constant 99 5 42 initial).2.table (callKey 0 [5]) = some 42 := by rfl
example : let p := { Fixtures.primitives with publish := publish false }
    let result := (reassociate reads (implementedConstructors p) 1 2 4 false ()) initial
    result.1 = .error .outOfMemory ∧ result.2.read 7 = some 42 := by exact ⟨rfl, rfl⟩

end Compiler.Extraction.Associative.Tests
