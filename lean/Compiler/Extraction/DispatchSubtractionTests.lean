/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchSubtractionProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.SubtractionTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def nestedTrial (instruction : Opcode) (onRight constantFirst : Bool) (failAt : Nat := 0) :=
  run [⟨none, none, []⟩, ⟨some 7, none, []⟩,
    ⟨none, some instruction, if constantFirst then [1, 0] else [0, 1]⟩, ⟨none, none, []⟩]
    opSUB (if onRight then [3, 2] else [2, 3]) ⟨true, some .osaka⟩ failAt

abbrev Calls := List (Kind × Opcode × Word × List NodeId × NodeId)
def leftAddCalls : Calls := [(1, 3, 0, [0, 3], 42), (3, 0, 7, [1], 42), (1, 1, 0, [1024, 1025], 42)]
def rightAddCalls : Calls := [(1, 3, 0, [3, 0], 42), (2, 0, 0 - 7, [], 42), (1, 1, 0, [1024, 1025], 42)]
def leftSubRightCalls : Calls := [(1, 3, 0, [0, 3], 42), (3, 0, 7, [1], 42), (1, 3, 0, [1024, 1025], 42)]
def leftSubLeftCalls : Calls := [(1, 1, 0, [0, 3], 42), (3, 0, 7, [1], 42), (1, 3, 0, [1025, 1024], 42)]
def rightSubRightCalls : Calls := [(1, 3, 0, [3, 0], 42), (2, 0, 7, [], 42), (1, 1, 0, [1024, 1025], 42)]
def rightSubLeftCalls : Calls := [(1, 1, 0, [3, 0], 42), (2, 0, 0 - 7, [], 42), (1, 1, 0, [1024, 1025], 42)]
def nestedCases : List (Opcode × Bool × Bool × Calls) :=
  [(opADD, false, false, leftAddCalls), (opADD, false, true, leftAddCalls),
   (opADD, true, false, rightAddCalls), (opADD, true, true, rightAddCalls),
   (opSUB, false, false, leftSubRightCalls), (opSUB, false, true, leftSubLeftCalls),
   (opSUB, true, false, rightSubRightCalls), (opSUB, true, true, rightSubLeftCalls)]

example : nestedCases.all (fun (op, right, first, calls) =>
    traceMatches (nestedTrial op right first) (.ok (some 1026)) calls) = true := by rfl
example : nestedCases.all (fun (op, right, first, calls) => [1, 2, 3].all (fun failAt =>
    traceMatches (nestedTrial op right first failAt) (.error .outOfMemory) (calls.take failAt))) = true := by rfl
example : (nestedTrial opSUB false true 3).2.read 0 = some 3 := by rfl

def constantTrial (value : Word) (failAt : Nat := 0) :=
  run [⟨none, none, []⟩, ⟨some value, none, []⟩] opSUB [0, 1] {} failAt
example : traceMatches (constantTrial 7) (.ok (some 1025))
    [(2, 0, 0 - 7, [], 42), (1, 1, 0, [0, 1024], 42)] = true := by rfl
example : traceMatches (constantTrial (BitVec.allOnes 256)) (.ok (some 1025))
    [(2, 0, 1, [], 42), (1, 1, 0, [0, 1024], 42)] = true := by rfl
example : traceMatches (constantTrial 0) (.ok (some 0)) [] = true := by rfl
example : traceMatches (constantTrial 7 2) (.error .outOfMemory)
    [(2, 0, 0 - 7, [], 42), (1, 1, 0, [0, 1024], 42)] = true := by rfl
example : traceMatches (run [⟨some 0, none, []⟩, ⟨some 1, none, []⟩] opSUB [0, 1])
    (.ok (some 1024)) [(2, 0, BitVec.allOnes 256, [], 42)] = true := by rfl
example : traceMatches (run [] opSUB [0, 0]) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl

-- Competing matches and faults are callback probes, with no coherence claim.
-- A successful earlier rule and its failures must both stop the search.
def orderedReads : Reads where
  constant := fun id => .ok (if id == 1 then some 7 else none)
  operation := fun id op =>
    if id == 2 && op == opADD then .ok (some ⟨0, [0, 1]⟩) else .error .invalidOptional
def orderedTrial (failAt : Nat) :=
  simplifyWithOptions orderedReads (constructors failAt) 64 opSUB [2, 3] 42 {} empty
example : traceMatches (orderedTrial 0) (.ok (some 1026)) leftAddCalls = true := by rfl
example : traceMatches (orderedTrial 2) (.error .outOfMemory) (leftAddCalls.take 2) = true := by rfl

def faultyReads : Reads where
  constant := fun _ => .ok none
  operation := fun _ _ => .error .invalidOptional
def faultyTrial := simplifyWithOptions faultyReads (constructors 0) 64 opSUB [0, 1] 42 {} empty
example : traceMatches faultyTrial (.error .invalidOptional) [] = true := by rfl

-- When both nested operands are known, the right constant wins before the
-- left constant. The outer node deliberately does not claim to be constant.
def bothConstants (onRight : Bool) :=
  run [⟨some 7, none, []⟩, ⟨some 9, none, []⟩, ⟨none, some opSUB, [0, 1]⟩]
    opSUB (if onRight then [3, 2] else [2, 3])
example : traceMatches (bothConstants false) (.ok (some 1026))
    [(1, 3, 0, [0, 3], 42), (3, 0, 9, [1], 42), (1, 3, 0, [1024, 1025], 42)] = true := by rfl
example : traceMatches (bothConstants true) (.ok (some 1026))
    [(1, 3, 0, [3, 0], 42), (2, 0, 9, [], 42), (1, 1, 0, [1024, 1025], 42)] = true := by rfl

example : traceMatches (run [⟨none, some opADD, [1]⟩, ⟨some 7, none, []⟩] opSUB [0, 2])
    (.ok none) [] = true := by rfl
example : traceMatches (run [⟨none, some opSUB, [1, 2, 3]⟩, ⟨some 7, none, []⟩] opSUB [4, 0])
    (.ok none) [] = true := by rfl

end Compiler.Extraction.Dispatch.SubtractionTests
