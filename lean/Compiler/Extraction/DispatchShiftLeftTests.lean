/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchShiftLeftProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.ShiftLeftTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Calls := List (Kind × Opcode × Word × List NodeId × NodeId)
def extendTrial (amount index : Word) (failAt : Nat := 0) :=
  run [⟨some amount, none, []⟩, ⟨some index, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opSIGNEXTEND, [1, 2]⟩] opSHL [0, 3] ⟨true, some .homestead⟩ failAt
def extendCalls (index : Word) : Calls :=
  [(1, 27, 0, [0, 2], 42), (2, 0, index, [], 42), (1, 11, 0, [1025, 1024], 42)]
example : traceMatches (extendTrial 8 2) (.ok (some 1026)) (extendCalls 3) = true := by rfl
example : [1, 2, 3].all (fun failAt => traceMatches (extendTrial 8 2 failAt)
    (.error .outOfMemory) ((extendCalls 3).take failAt)) = true := by rfl
example : (extendTrial 8 2 3).2.read 0 = some 3 := by rfl
example : [0, 30, 31, 32].all (fun index => traceMatches (extendTrial 8 index)
    (.ok (some 1026)) (extendCalls (index + 1))) = true := by rfl
example : traceMatches (extendTrial 248 0) (.ok (some 1026)) (extendCalls 31) = true := by rfl
example : traceMatches (extendTrial 16 30) (.ok (some 1026)) (extendCalls 32) = true := by rfl
example : traceMatches (extendTrial 0 (BitVec.allOnes 256)) (.ok (some 3)) [] = true := by rfl
example : [1, 7, 9, 255].all (fun amount => traceMatches (extendTrial amount 0) (.ok none) []) = true := by rfl
example : [33, BitVec.allOnes 256].all (fun index => traceMatches (extendTrial 8 index) (.ok none) []) = true := by rfl
example : [256, 264, BitVec.allOnes 256].all (fun amount => traceMatches (extendTrial amount 0)
    (.ok (some 1024)) [(2, 0, 0, [], 42)]) = true := by rfl

example : Folding.Op.shl.value 8 (Folding.Op.signextend.value 0 0x80 0) 0 =
    Folding.Op.signextend.value 1 0x8000 0 := by decide
example : Folding.Op.shl.value 8 (Folding.Op.signextend.value 0 0x7f 0) 0 = 0x7f00 := by decide
-- Removing byte alignment makes the proposed sign-bit position incorrect.
example : Folding.Op.shl.value 1 (Folding.Op.signextend.value 0 0x40 0) 0 ≠
    Folding.Op.signextend.value 0 (Folding.Op.shl.value 1 0x40 0) 0 := by decide

def shiftTrial (outer inner : Word) (opcode : Opcode := opSHL) (failAt : Nat := 0) :=
  run [⟨some outer, none, []⟩, ⟨some inner, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opcode, [1, 2]⟩] opSHL [0, 3] {} failAt
example : traceMatches (shiftTrial 7 9) (.ok (some 1025))
    [(2, 0, 16, [], 42), (1, 27, 0, [1024, 2], 42)] = true := by rfl
example : traceMatches (shiftTrial 1 255) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (shiftTrial 2 7 opSHR) (.ok (some 1027))
    [(2, 0, 5, [], 42), (1, 28, 0, [1024, 2], 42),
     (2, 0, (BitVec.allOnes 256 >>> 7) <<< 2, [], 42), (1, 22, 0, [1025, 1026], 42)] = true := by rfl
example : traceMatches (shiftTrial 8 8 opSHR) (.ok (some 1025))
    [(2, 0, (BitVec.allOnes 256 >>> 8) <<< 8, [], 42), (1, 22, 0, [2, 1024], 42)] = true := by rfl
example : traceMatches (shiftTrial 1 256 opSHR) (.ok none) [] = true := by rfl
example : traceMatches (shiftTrial 8 255 opAND) (.ok (some 1026))
    [(1, 27, 0, [0, 2], 42), (2, 0, 0xff00, [], 42), (1, 22, 0, [1024, 1025], 42)] = true := by rfl

-- Callback probes expose read order independently of graph coherence.
def firstReads (selected : Opcode) : Reads where
  constant := fun id => .ok (if id == 0 then some 8 else if id == 1 then some 2 else none)
  operation := fun id op => if op == opSIGNEXTEND then .error .invalidOptional
    else .ok (if id == 3 && op == selected then some ⟨0, [1, 2]⟩ else none)
def firstTrial (selected : Opcode) (failAt : Nat := 0) :=
  simplifyWithOptions (firstReads selected) (constructors failAt) 64 opSHL [0, 3] 42 {} empty
example : outcomeEqual (firstTrial opSHL).1 (.ok (some 1025)) = true := by rfl
example : outcomeEqual (firstTrial opSHR).1 (.ok (some 1027)) = true := by rfl
example : outcomeEqual (firstTrial opAND).1 (.ok (some 1026)) = true := by rfl
example : outcomeEqual (firstTrial opAND 3).1 (.error .outOfMemory) = true := by rfl
example : outcomeEqual (firstTrial 0).1 (.error .invalidOptional) = true := by rfl

def constantFaultReads : Reads where
  constant := fun id => if id == 1 then .error .invalidOptional else .ok (if id == 0 then some 8 else none)
  operation := fun id op => .ok (if id == 3 && op == opSIGNEXTEND then some ⟨0, [1, 2]⟩ else none)
example : outcomeEqual (simplifyWithOptions constantFaultReads (constructors 0) 64 opSHL [0, 3] 42 {} empty).1
    (.error .invalidOptional) = true := by rfl
example : traceMatches (run [⟨none, none, []⟩, ⟨none, some opSIGNEXTEND, [2, 3]⟩] opSHL [0, 1])
    (.ok none) [] = true := by rfl
example : traceMatches (run [⟨some 8, none, []⟩, ⟨none, some opSIGNEXTEND, [2]⟩] opSHL [0, 1])
    (.ok none) [] = true := by rfl
example : traceMatches (run [⟨some 0, none, []⟩, ⟨some 7, none, []⟩] opSHL [0, 1])
    (.ok (some 1024)) [(2, 0, 7, [], 42)] = true := by rfl

end Compiler.Extraction.Dispatch.ShiftLeftTests
