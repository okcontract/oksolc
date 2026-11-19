/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchShiftRightProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.ShiftRightTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Calls := List (Kind × Opcode × Word × List NodeId × NodeId)
def shiftTrial (outer inner : Word) (opcode : Opcode := opSHR) (failAt : Nat := 0) :=
  run [⟨some outer, none, []⟩, ⟨some inner, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opcode, [1, 2]⟩] opSHR [0, 3] ⟨true, some .homestead⟩ failAt
def sumCalls : Calls := [(2, 0, 16, [], 42), (1, 28, 0, [1024, 2], 42)]
example : traceMatches (shiftTrial 7 9) (.ok (some 1025)) sumCalls = true := by rfl
example : traceMatches (shiftTrial 7 9 opSHR 1) (.error .outOfMemory) (sumCalls.take 1) = true := by rfl
example : traceMatches (shiftTrial 7 9 opSHR 2) (.error .outOfMemory) sumCalls = true := by rfl
example : traceMatches (shiftTrial 1 254) (.ok (some 1025))
    [(2, 0, 255, [], 42), (1, 28, 0, [1024, 2], 42)] = true := by rfl
example : traceMatches (shiftTrial 1 255) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (shiftTrial 1 (BitVec.allOnes 256)) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (shiftTrial 0 (BitVec.allOnes 256)) (.ok (some 3)) [] = true := by rfl
example : traceMatches (shiftTrial 256 1) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl

def oppositeCalls : Calls := [(2, 0, 5, [], 42), (1, 28, 0, [1024, 2], 42),
  (2, 0, (BitVec.allOnes 256 <<< 2) >>> 7, [], 42), (1, 22, 0, [1025, 1026], 42)]
example : traceMatches (shiftTrial 7 2 opSHL) (.ok (some 1027)) oppositeCalls = true := by rfl
example : [1, 2, 3, 4].all (fun failAt => traceMatches (shiftTrial 7 2 opSHL failAt)
    (.error .outOfMemory) (oppositeCalls.take failAt)) = true := by rfl
example : (shiftTrial 7 2 opSHL 4).2.read 0 = some 4 := by rfl
example : traceMatches (shiftTrial 2 7 opSHL) (.ok (some 1027))
    [(2, 0, 5, [], 42), (1, 27, 0, [1024, 2], 42),
     (2, 0, (BitVec.allOnes 256 <<< 7) >>> 2, [], 42), (1, 22, 0, [1025, 1026], 42)] = true := by rfl
example : traceMatches (shiftTrial 8 8 opSHL) (.ok (some 1025))
    [(2, 0, (BitVec.allOnes 256 <<< 8) >>> 8, [], 42), (1, 22, 0, [2, 1024], 42)] = true := by rfl
example : traceMatches (shiftTrial 1 256 opSHL) (.ok none) [] = true := by rfl

def maskTrial (constantFirst : Bool) (failAt : Nat := 0) :=
  run [⟨some 8, none, []⟩, ⟨some 0xff00, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opAND, if constantFirst then [1, 2] else [2, 1]⟩] opSHR [0, 3] {} failAt
def maskCalls : Calls := [(1, 28, 0, [0, 2], 42), (2, 0, 255, [], 42), (1, 22, 0, [1024, 1025], 42)]
example : traceMatches (maskTrial false) (.ok (some 1026)) maskCalls = true := by rfl
example : traceMatches (maskTrial true) (.ok (some 1026)) maskCalls = true := by rfl
example : [1, 2, 3].all (fun failAt => traceMatches (maskTrial false failAt)
    (.error .outOfMemory) (maskCalls.take failAt)) = true := by rfl

def folded (amount value : Word) := run [⟨some amount, none, []⟩, ⟨some value, none, []⟩] opSHR [0, 1]
example : traceMatches (folded 255 (BitVec.allOnes 256)) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl
example : traceMatches (folded 0 7) (.ok (some 1024)) [(2, 0, 7, [], 42)] = true := by rfl

-- These callback probes check order and explicit failure without asserting a
-- coherent graph. Earlier constructors must stop before the invalid lookup.
def firstReads (badConstant : Bool) : Reads where
  constant := fun id => if id == 1 && badConstant then .error .invalidOptional
    else .ok (if id == 0 then some 7 else if id == 1 then some 9 else none)
  operation := fun id op => if id == 3 && op == opSHR then .ok (some ⟨0, [1, 2]⟩) else .error .invalidOptional
def firstTrial (badConstant : Bool) (failAt : Nat := 0) :=
  simplifyWithOptions (firstReads badConstant) (constructors failAt) 64 opSHR [0, 3] 42 {} empty
example : traceMatches (firstTrial false) (.ok (some 1025)) sumCalls = true := by rfl
example : traceMatches (firstTrial false 2) (.error .outOfMemory) sumCalls = true := by rfl
example : traceMatches (firstTrial true) (.error .invalidOptional) [] = true := by rfl

def faultReads (amount : Option Word) : Reads where
  constant := fun id => .ok (if id == 0 then amount else none)
  operation := fun _ _ => .error .invalidOptional
def faultTrial (amount : Option Word) :=
  simplifyWithOptions (faultReads amount) (constructors 0) 64 opSHR [0, 3] 42 {} empty
example : traceMatches (faultTrial none) (.ok none) [] = true := by rfl
example : traceMatches (faultTrial (some 0)) (.ok (some 3)) [] = true := by rfl
example : traceMatches (faultTrial (some 7)) (.error .invalidOptional) [] = true := by rfl
example : traceMatches (faultTrial (some 256)) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl

example : traceMatches (run [⟨some 7, none, []⟩, ⟨none, some opSHR, [2]⟩] opSHR [0, 1]) (.ok none) [] = true := by rfl
example : traceMatches (run [⟨some 7, none, []⟩, ⟨none, some opAND, [2, 3, 4]⟩] opSHR [0, 1]) (.ok none) [] = true := by rfl

end Compiler.Extraction.Dispatch.ShiftRightTests
