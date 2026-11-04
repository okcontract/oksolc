/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchSignExtendProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.SignExtendTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Calls := List (Kind × Opcode × Word × List NodeId × NodeId)
def nestedTrial (outer inner : Word) (failAt : Nat := 0) :=
  run [⟨some outer, none, []⟩, ⟨some inner, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opSIGNEXTEND, [1, 2]⟩] opSIGNEXTEND [0, 3] {} failAt
def nestedCalls (index : Word) : Calls := [(2, 0, index, [], 42), (1, 11, 0, [1024, 2], 42)]
example : traceMatches (nestedTrial 7 2) (.ok (some 1025)) (nestedCalls 2) = true := by rfl
example : traceMatches (nestedTrial 2 7) (.ok (some 1025)) (nestedCalls 2) = true := by rfl
example : traceMatches (nestedTrial 2 2) (.ok (some 1025)) (nestedCalls 2) = true := by rfl
example : [31, 32, BitVec.allOnes 256].all (fun outer => traceMatches (nestedTrial outer 0)
    (.ok (some 1025)) (nestedCalls 0)) = true := by rfl
example : traceMatches (nestedTrial 1 (BitVec.allOnes 256)) (.ok (some 1025)) (nestedCalls 1) = true := by rfl
example : [1, 2].all (fun failAt => traceMatches (nestedTrial 7 2 failAt)
    (.error .outOfMemory) ((nestedCalls 2).take failAt)) = true := by rfl
example : (nestedTrial 7 2 2).2.read 0 = some 2 := by rfl

def repeatTrial (index : Option Word) (failAt : Nat := 0) :=
  run [⟨index, none, []⟩, ⟨none, none, []⟩, ⟨none, some opSIGNEXTEND, [0, 1]⟩]
    opSIGNEXTEND [0, 2] {} failAt
example : traceMatches (repeatTrial none) (.ok (some 1024)) [(1, 11, 0, [0, 1], 42)] = true := by rfl
example : traceMatches (repeatTrial (some 31)) (.ok (some 1024)) [(1, 11, 0, [0, 1], 42)] = true := by rfl
example : traceMatches (repeatTrial none 1) (.error .outOfMemory) [(1, 11, 0, [0, 1], 42)] = true := by rfl

def shiftTrial (index amount : Word) (failAt : Nat := 0) :=
  run [⟨some index, none, []⟩, ⟨some amount, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opSHR, [1, 2]⟩] opSIGNEXTEND [0, 3] ⟨true, some .homestead⟩ failAt
def sarCalls : Calls := [(1, 29, 0, [1, 2], 42)]
example : traceMatches (shiftTrial 2 232) (.ok (some 1024)) sarCalls = true := by rfl
example : traceMatches (shiftTrial 2 232 1) (.error .outOfMemory) sarCalls = true := by rfl
example : (shiftTrial 2 232 1).2.read 0 = some 1 := by rfl
example : traceMatches (shiftTrial 0 248) (.ok (some 1024)) sarCalls = true := by rfl
example : traceMatches (shiftTrial 30 8) (.ok (some 1024)) sarCalls = true := by rfl
example : [0, 1, 7, 8, 231, 233, 240, 255, 256, 264, BitVec.allOnes 256].all
    (fun amount => traceMatches (shiftTrial 2 amount) (.ok none) []) = true := by rfl
example : [31, 32, 256, BitVec.allOnes 256].all
    (fun index => traceMatches (shiftTrial index 0) (.ok (some 3)) []) = true := by rfl

example : ArithmeticShift.value 1 (BitVec.allOnes 256) = BitVec.allOnes 256 := by decide
example : ArithmeticShift.value 1 1 = 0 := by decide
example : ArithmeticShift.value 255 (1 <<< 255) = BitVec.allOnes 256 := by decide
example : ArithmeticShift.value 256 ((1 <<< 255) - 1) = 0 := by decide
example : ArithmeticShift.value (BitVec.allOnes 256) (1 <<< 255) = BitVec.allOnes 256 := by decide
example : ArithmeticShift.eval [1] = none := by rfl
example : ArithmeticShift.eval [1, 2, 3] = none := by rfl
example : Folding.Op.signextend.value 0 (Folding.Op.shr.value 248 (1 <<< 255) 0) 0 =
    ArithmeticShift.value 248 (1 <<< 255) := by decide
example : Folding.Op.signextend.value 0 (Folding.Op.shr.value 248 ((1 <<< 255) - 1) 0) 0 = 127 := by decide
example : Folding.Op.signextend.value 0 (Folding.Op.shr.value 247 (1 <<< 255) 0) 0 ≠
    ArithmeticShift.value 247 (1 <<< 255) := by decide

-- These probes expose callback order without asserting graph coherence.
def firstReads (equal badConstant : Bool) : Reads where
  constant := fun id => if id == 1 && badConstant then .error .invalidOptional
    else .ok (if id == 0 then some 31 else if id == 1 then some 2 else none)
  operation := fun id op => if id == 3 && op == opSIGNEXTEND then .ok (some ⟨0, [1, 2]⟩)
    else .error .invalidOptional
  overrideEquality := some (fun a b => equal && a == 0 && b == 1)
def firstTrial (equal badConstant : Bool) (failAt : Nat := 0) :=
  simplifyWithOptions (firstReads equal badConstant) (constructors failAt) 64 opSIGNEXTEND [0, 3] 42 {} empty
example : traceMatches (firstTrial false false) (.ok (some 1025)) (nestedCalls 2) = true := by rfl
example : traceMatches (firstTrial false false 2) (.error .outOfMemory) (nestedCalls 2) = true := by rfl
example : traceMatches (firstTrial false true) (.error .invalidOptional) [] = true := by rfl
example : traceMatches (firstTrial true true) (.ok (some 1024)) [(1, 11, 0, [0, 2], 42)] = true := by rfl

def faultReads (index : Option Word) (nestedFault : Bool) : Reads where
  constant := fun id => .ok (if id == 0 then index else none)
  operation := fun _ op => if nestedFault || op == opSHR then .error .invalidOptional else .ok none
def faultTrial (index : Option Word) (nestedFault : Bool) :=
  simplifyWithOptions (faultReads index nestedFault) (constructors 0) 64 opSIGNEXTEND [0, 3] 42 {} empty
example : traceMatches (faultTrial (some 31) true) (.error .invalidOptional) [] = true := by rfl
example : traceMatches (faultTrial (some 31) false) (.ok (some 3)) [] = true := by rfl
example : traceMatches (faultTrial none false) (.ok none) [] = true := by rfl
example : traceMatches (faultTrial (some 2) false) (.error .invalidOptional) [] = true := by rfl
example : traceMatches (run [⟨some 31, none, []⟩, ⟨some 128, none, []⟩] opSIGNEXTEND [0, 1])
    (.ok (some 1024)) [(2, 0, 128, [], 42)] = true := by rfl
example : traceMatches (run [⟨some 2, none, []⟩, ⟨none, some opSIGNEXTEND, [2]⟩] opSIGNEXTEND [0, 1])
    (.ok none) [] = true := by rfl

end Compiler.Extraction.Dispatch.SignExtendTests
