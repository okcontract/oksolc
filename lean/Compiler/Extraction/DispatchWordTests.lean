/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchWordProofs
import Compiler.Extraction.DispatchTests
import Compiler.Extraction.AddressMaskTests

namespace Compiler.Extraction.Dispatch.WordTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024

def env := AddressMask.Tests.env
def epochMeaning : Meaning where
  operation := fun _ sequence _ => some (sequence.setWidth 256)
  atom := fun _ data sequence _ => some (data + sequence.setWidth 256)
def model := wordDispatchMeaning env epochMeaning

-- The unified model preserves each extension and the unmodeled epoch boundary.
example : model.operation 48 77 [] = some 5 := by rfl
example : model.operation 51 77 [] = some 3 := by rfl
example : model.operation 50 77 [] = some 7 := by rfl
example : model.operation 65 77 [] = some 9 := by rfl
example : model.operation 48 77 [1] = none := by rfl
example : model.operation 29 77 [1, BitVec.ofInt 256 (-3)] = some (BitVec.ofInt 256 (-2)) := by rfl
example : model.operation 29 77 [256, BitVec.ofInt 256 (-3)] = some (BitVec.allOnes 256) := by rfl
example : model.operation 29 77 [256, 3] = some 0 := by rfl
example : model.operation 29 77 [1] = none := by rfl
example : model.operation 49 77 [5] = some 77 := by rfl
example : model.operation 49 78 [5] = some 78 := by rfl
example : model.atom 2 11 77 [] = some 88 := by rfl
example : Folding.decodeWord 29 = none := by rfl
example : Folding.decodeWord 49 = none := by rfl

def samples : List (Folding.Op × Word) := [
  (.add, 10), (.mul, 21), (.sub, 4), (.div, 2), (.sdiv, 2), (.mod, 1), (.smod, 1),
  (.exp, 343), (.not, BitVec.allOnes 256 - 7), (.lt, 0), (.gt, 1), (.slt, 0), (.sgt, 1),
  (.eq, 0), (.iszero, 0), (.and, 3), (.or, 7), (.xor, 4), (.byte, 0), (.addmod, 0),
  (.mulmod, 1), (.signextend, 3), (.shl, 384), (.shr, 0)]
def sampleValues (op : Folding.Op) : List Word := [7, 3, 5].take op.arity
example : samples.map Prod.fst = Folding.wordOperations := by rfl
example : samples.all (fun (op, expected) => model.operation op.opcode 77 (sampleValues op) == some expected) = true := by
  decide +kernel
example : Folding.wordOperations.all (fun op => model.operation op.opcode 77 [] == none) = true := by rfl
example : Folding.wordOperations.all (fun op => model.operation op.opcode 77 [7, 3, 5, 1] == none) = true := by rfl

def folded (op : Folding.Op) (failAt : Nat := 0) :=
  run [⟨some 7, none, []⟩, ⟨some 3, none, []⟩, ⟨some 5, none, []⟩]
    op.opcode ([0, 1, 2].take op.arity) {} failAt
example : samples.all (fun (op, expected) => traceMatches (folded op)
    (.ok (some 1024)) [(2, 0, expected, [], 42)]) = true := by rfl
example : samples.all (fun (op, expected) => traceMatches (folded op 1)
    (.error .outOfMemory) [(2, 0, expected, [], 42)]) = true := by rfl

end Compiler.Extraction.Dispatch.WordTests
