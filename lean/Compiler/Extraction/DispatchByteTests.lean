/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchByteProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.ByteTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def shiftTrial (index : Word) (opcode : Opcode) (amount : Word) (failAt : Nat := 0) :=
  run [⟨some index, none, []⟩, ⟨some amount, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opcode, [1, 2]⟩] opBYTE [0, 3] ⟨true, some .homestead⟩ failAt
def byteCalls (index : Word) : List (Kind × Opcode × Word × List NodeId × NodeId) :=
  [(2, 0, index, [], 42), (1, 26, 0, [1024, 2], 42)]
def maskCalls : List (Kind × Opcode × Word × List NodeId × NodeId) :=
  [(2, 0, 255, [], 42), (1, 22, 0, [3, 1024], 42)]

example : traceMatches (shiftTrial 2 opSHL 8) (.ok (some 1025)) (byteCalls 3) = true := by rfl
example : traceMatches (shiftTrial 30 opSHL 16) (.ok (some 1025)) (byteCalls 32) = true := by rfl
example : traceMatches (shiftTrial 0 opSHL 256) (.ok (some 1025)) (byteCalls 32) = true := by rfl
example : traceMatches (shiftTrial 2 opSHR 8) (.ok (some 1025)) (byteCalls 1) = true := by rfl
example : traceMatches (shiftTrial 1 opSHR 9) (.ok none) [] = true := by rfl
example : traceMatches (shiftTrial 0 opSHR 9) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (shiftTrial 30 opSHR (BitVec.allOnes 256))
    (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (shiftTrial 2 opSHL 9) (.ok none) [] = true := by rfl
example : traceMatches (shiftTrial 0 opSHL 264) (.ok none) [] = true := by rfl
example : traceMatches (shiftTrial 31 opSHR 256) (.ok (some 1025)) maskCalls = true := by rfl
example : traceMatches (shiftTrial 32 opSHL 8) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (shiftTrial 2 opSHL 8 1) (.error .outOfMemory) ((byteCalls 3).take 1) = true := by rfl
example : traceMatches (shiftTrial 2 opSHL 8 2) (.error .outOfMemory) (byteCalls 3) = true := by rfl
example : traceMatches (shiftTrial 2 opSHR 8 2) (.error .outOfMemory) (byteCalls 1) = true := by rfl
example : (shiftTrial 2 opSHR 8 2).2.read 0 = some 2 := by rfl
example : traceMatches (shiftTrial 0 opSHR 9 1) (.error .outOfMemory) [(2, 0, 0, [], 42)] = true := by rfl

def folded (index value : Word) := run [⟨some index, none, []⟩, ⟨some value, none, []⟩] opBYTE [0, 1]
example : traceMatches (folded 0 (BitVec.allOnes 256)) (.ok (some 1024)) [(2, 0, 255, [], 42)] = true := by rfl
example : traceMatches (folded 31 0x1234) (.ok (some 1024)) [(2, 0, 0x34, [], 42)] = true := by rfl
example : traceMatches (folded 32 (BitVec.allOnes 256)) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl

-- Probe callback order without claiming coherent graph semantics. An earlier
-- match or failure must stop before the deliberately failing later lookup.
def firstReads : Reads where
  constant := fun id => .ok (if id == 0 then some 2 else if id == 1 then some 8 else none)
  operation := fun id op =>
    if id == 3 && op == opSHL then .ok (some ⟨0, [1, 2]⟩) else .error .invalidOptional
def firstTrial (failAt : Nat) :=
  simplifyWithOptions firstReads (constructors failAt) 64 opBYTE [0, 3] 42 {} empty
example : traceMatches (firstTrial 0) (.ok (some 1025)) (byteCalls 3) = true := by rfl
example : traceMatches (firstTrial 2) (.error .outOfMemory) (byteCalls 3) = true := by rfl

def faultReads (index : Option Word) : Reads where
  constant := fun id => .ok (if id == 0 then index else none)
  operation := fun _ _ => .error .invalidOptional
def faultTrial (index : Option Word) :=
  simplifyWithOptions (faultReads index) (constructors 0) 64 opBYTE [0, 3] 42 {} empty
example : traceMatches (faultTrial none) (.ok none) [] = true := by rfl
example : traceMatches (faultTrial (some 0)) (.error .invalidOptional) [] = true := by rfl
example : traceMatches (faultTrial (some 31)) (.ok (some 1025)) maskCalls = true := by rfl
example : traceMatches (faultTrial (some 32)) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl

example : traceMatches (run [⟨some 0, none, []⟩, ⟨none, some opSHL, [2]⟩] opBYTE [0, 1])
    (.ok none) [] = true := by rfl
example : traceMatches (run [⟨some 0, none, []⟩, ⟨none, some opSHR, [2, 3, 4]⟩] opBYTE [0, 1])
    (.ok none) [] = true := by rfl

end Compiler.Extraction.Dispatch.ByteTests
