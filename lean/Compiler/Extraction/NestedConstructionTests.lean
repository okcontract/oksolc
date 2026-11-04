/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NestedConstructionProofs
import Compiler.Extraction.NestedTests
import Compiler.Extraction.InternerFixtures

namespace Compiler.Extraction.Nested.ConstructionTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Contract.Yul Nested.Tests

def initial : Heap := ⟨readValue cells, fun _ => none, none, 0⟩
def callKey (opcode : Opcode) (ids : List NodeId) : Key := ⟨1, opcode, 0, ids, 0⟩

/-- Observable callback traces, deliberately not claimed to satisfy Constructs.
The table records the operands and debug token at each construction call. -/
def record (opcode : Opcode) (ids : List NodeId) (debug : NodeId) (heap : Heap) : NodeId × Heap :=
  let id := if (heap.read 8).isNone then 8 else 9
  (id, ⟨fun key => if key == id then some (BitVec.ofNat 256 opcode.toNat) else heap.read key,
    (fun key => if key == callKey opcode ids then some debug else heap.table key), none, heap.allocationCursor⟩)

def recording : OperationBuilder NodeId := fun opcode ids debug heap =>
  let (id, after) := record opcode ids debug heap
  (.ok id, after)
def failing : OperationBuilder NodeId := fun opcode ids debug heap =>
  (.error .outOfMemory, (record opcode ids debug heap).2)
def failSecond : OperationBuilder NodeId := fun opcode ids debug heap =>
  if (heap.read 8).isSome then failing opcode ids debug heap else recording opcode ids debug heap

example : (dropRepeatedNested (storageReads cells) recording 22 3 0 false 42 initial).1 = .ok (some 8) := by rfl
example : (dropRepeatedNested (storageReads cells) recording 22 3 0 false 42 initial).2.table (callKey 22 [0, 1]) = some 42 := by rfl
example : (dropRepeatedNested indiscriminate recording 22 3 6 true 42 initial).2.table (callKey 22 [0, 6]) = some 42 := by rfl
example : (dropRepeatedNested indiscriminate recording 22 3 6 false 42 initial).2.table (callKey 22 [0, 1]) = some 42 := by rfl
example : repeatedOperands (storageReads cells) 0 1 0 true = some [0, 1] := by rfl
example : repeatedOperands (storageReads cells) 0 1 1 true = some [0, 1] := by rfl
example : (dropRepeatedNested (storageReads cells) failing 22 3 6 true 42 initial).1 = .ok none := by rfl
example : (dropRepeatedNested (storageReads cells) failing 22 3 6 true 42 initial).2.read 8 = none := by rfl
example : (dropRepeatedNested (storageReads cells) failing 22 99 0 true 42 initial).1 = .ok none := by rfl
example : (dropRepeatedNested (storageReads [operation 22 [0] 0]) failing 22 0 0 false 42 initial).1 = .ok none := by rfl
example : (dropRepeatedNested (storageReads corrupt) recording 22 0 0 true 42 initial).1 = .error .invalidOptional := by rfl
example : (readAction (m := Action) (.error .safetyFault : Except ReadError Unit) initial).1 = .error .safetyFault := by rfl
example : let result := dropRepeatedNested (storageReads cells) failing 22 3 0 false 42 initial
    result.1 = .error .outOfMemory ∧ result.2.read 8 = some 22 := by exact ⟨rfl, rfl⟩

example : (doubleIsZero recording 0 42 initial).1 = .ok 9 := by rfl
example : (doubleIsZero recording 0 42 initial).2.table (callKey 21 [0]) = some 42 := by rfl
example : (doubleIsZero recording 0 42 initial).2.table (callKey 21 [8]) = some 42 := by rfl
example : let result := doubleIsZero failing 0 42 initial
    result.1 = .error .outOfMemory ∧ result.2.read 8 = some 21 ∧ result.2.read 9 = none := by exact ⟨rfl, rfl, rfl⟩
example : let result := doubleIsZero failSecond 0 42 initial
    result.1 = .error .outOfMemory ∧ result.2.read 8 = some 21 ∧ result.2.read 9 = some 21 := by exact ⟨rfl, rfl, rfl⟩

-- Compose the generated helper with the actual extracted constructor/interner.
example : (dropRepeatedNested (storageReads cells) (internerBuilder Fixtures.primitives)
    22 3 0 false () initial).1 = .ok (some 7) := by rfl
example : let p := { Fixtures.primitives with publish := publish false }
    let result := dropRepeatedNested (storageReads cells) (internerBuilder p) 22 3 0 false () initial
    result.1 = .error .outOfMemory ∧ result.2.read 7 = some 42 := by exact ⟨rfl, rfl⟩

end Compiler.Extraction.Nested.ConstructionTests
