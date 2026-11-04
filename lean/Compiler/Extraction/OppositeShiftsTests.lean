/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.OppositeShiftsProofs
import Compiler.Extraction.AssociativeTests

namespace Compiler.Extraction.OppositeShifts.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Associative
open Compiler.Extraction.Associative.Tests (constructors)
open Compiler.Extraction.Nested.ConstructionTests (callKey failing initial)
open Contract.Yul

example : nativeMask 28 0 0 = .ok (BitVec.allOnes 256) := by rfl
example : nativeMask 27 255 255 = .ok (BitVec.twoPow 256 255) := by rfl
example : nativeMask 28 255 255 = .ok 1 := by rfl
example : nativeMask 27 256 0 = .error .safetyFault := by rfl
example : nativeMask 28 0 256 = .error .safetyFault := by rfl
example : checkedDifference 255 0 = .ok 255 := by rfl
example : checkedDifference 0 0 = .ok 0 := by rfl
example : checkedDifference 0 1 = .error .safetyFault := by rfl

-- Both directions, both strict orders, and the equal-count path. These trace
-- callbacks record operands/debug tokens and have no semantic correctness claim.
example : (combineOppositeShifts constructors 28 1 3 0 42 initial).2.table (callKey 0 [2]) = some 42 := by rfl
example : (combineOppositeShifts constructors 28 1 3 0 42 initial).2.table (callKey 27 [8, 0]) = some 42 := by rfl
example : (combineOppositeShifts constructors 28 3 1 0 42 initial).2.table (callKey 28 [8, 0]) = some 42 := by rfl
example : (combineOppositeShifts constructors 27 1 3 0 42 initial).2.table (callKey 28 [8, 0]) = some 42 := by rfl
example : (combineOppositeShifts constructors 27 3 1 0 42 initial).2.table (callKey 27 [8, 0]) = some 42 := by rfl
example : (combineOppositeShifts constructors 28 3 3 0 42 initial).2.table (callKey 22 [0, 8]) = some 42 := by rfl
example : (combineOppositeShifts constructors 27 3 3 0 42 initial).2.table (callKey 22 [0, 8]) = some 42 := by rfl
example : (combineOppositeShifts constructors 28 3 3 0 42 initial).2.table (callKey 0 [4294967295]) = some 42 := by rfl
example : (combineOppositeShifts constructors 28 256 0 0 42 initial).1 = .error .safetyFault := by rfl
example : (combineOppositeShifts constructors 27 0 256 0 42 initial).2.read 8 = none := by rfl
example : let changed := { constructors with constant := fun value => failing 0 [value.setWidth 32] }
    let result := combineOppositeShifts changed 28 1 3 0 42 initial
    result.1 = .error .outOfMemory ∧ result.2.table (callKey 27 [8, 0]) = none := by exact ⟨rfl, rfl⟩
example : let changed := { constructors with operation := failing }
    let result := combineOppositeShifts changed 28 1 3 0 42 initial
    result.1 = .error .outOfMemory ∧ result.2.read 8 = some 0 ∧ result.2.read 9 = some 27 := by exact ⟨rfl, rfl, rfl⟩
example : let changed := { constructors with operation := failing }
    let result := combineOppositeShifts changed 28 3 3 0 42 initial
    result.1 = .error .outOfMemory ∧ result.2.table (callKey 22 [0, 8]) = some 42 := by exact ⟨rfl, rfl⟩
example : let p := { Fixtures.primitives with publish := publish false }
    let result := combineOppositeShifts (implementedConstructors p) 28 1 3 0 () initial
    result.1 = .error .outOfMemory ∧ result.2.read 7 = some 42 := by exact ⟨rfl, rfl⟩

end Compiler.Extraction.OppositeShifts.Tests
