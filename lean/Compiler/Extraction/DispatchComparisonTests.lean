/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchComparisonProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.ComparisonTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests

def zeroLeft : List Probe := [⟨some 0, none, []⟩, ⟨none, none, []⟩]
def unknown : List Probe := [⟨none, none, []⟩]

example : traceMatches (run zeroLeft 16 [0, 1]) (.ok (some 1025))
    [(1, 21, 0, [1], 42), (1, 21, 0, [1024], 42)] = true := by rfl
example : traceMatches (run zeroLeft 16 [0, 1] {} 2) (.error .outOfMemory)
    [(1, 21, 0, [1], 42), (1, 21, 0, [1024], 42)] = true := by rfl
example : (run zeroLeft 16 [0, 1] {} 2).2.read 0 = some 2 := by rfl
example : (run zeroLeft 18 [0, 1]).1 = .ok none := by rfl

example : traceMatches (run unknown 20 [0, 0]) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl
example : traceMatches (run unknown 18 [0, 0]) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (run unknown 19 [0, 0] ⟨true, some .osaka⟩) (.ok (some 1024))
    [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (run [⟨some 0, none, []⟩] 20 [0, 0]) (.ok (some 1024))
    [(2, 0, 1, [], 42)] = true := by rfl

-- The negative signed word is greater as an unsigned word and less as signed.
example : Folding.Op.lt.eval [BitVec.allOnes 256, 0] = some 0 ∧
    Folding.Op.slt.eval [BitVec.allOnes 256, 0] = some 1 := by exact ⟨rfl, rfl⟩
example : traceMatches (run [⟨some (BitVec.allOnes 256), none, []⟩, ⟨some 0, none, []⟩] 18 [0, 1])
    (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl

def orderedFaults : Reads where
  constant := fun id => if id == 0 then .error .invalidOptional else .error .safetyFault
  operation := fun _ _ => .error .invalidId

example : (binaryStage orderedFaults (constructors 0) 64 opLT 0 1 42 {} empty).1 = .error .invalidOptional := by rfl
example : (binaryStage orderedFaults (constructors 0) 64 opLT 1 0 42 {} empty).1 = .error .safetyFault := by rfl
example : (simplifyWithOptions orderedFaults (constructors 0) 64 opLT [0, 1] 42 {} empty).2 = empty := by rfl
example (op : Folding.Op) (comparison : BooleanOperation op) (version : Version) :
    evmStage orderedFaults (constructors 0) 64 op.opcode [0, 1] 42 version = pure none :=
  comparison_evm_stage orderedFaults (constructors 0) op comparison [0, 1] 42 version 64

end Compiler.Extraction.Dispatch.ComparisonTests
