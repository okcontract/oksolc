/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchModuloProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.ModuloTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 4096
set_option exponentiation.threshold 512

def nestedTrial (instruction : Opcode) (forYul : Bool) (failAt : Nat := 0)
    (arguments : List NodeId := [0, 1]) :=
  run [⟨none, none, []⟩, ⟨none, none, []⟩, ⟨none, some instruction, arguments⟩, ⟨some 8, none, []⟩]
    opMOD [2, 3] ⟨forYul, some .osaka⟩ failAt

def maskCalls : List (Kind × Opcode × Word × List NodeId × NodeId) :=
  [(2, 0, 7, [], 42), (1, 22, 0, [2, 1024], 42)]

example : traceMatches (nestedTrial opMUL true) (.ok (some 1024)) [(1, 9, 0, [0, 1, 3], 42)] = true := by rfl
example : traceMatches (nestedTrial opADD true) (.ok (some 1024)) [(1, 8, 0, [0, 1, 3], 42)] = true := by rfl
example : traceMatches (nestedTrial opMUL false) (.ok (some 1025)) maskCalls = true := by rfl
example : traceMatches (nestedTrial opMUL false 1) (.error .outOfMemory) (maskCalls.take 1) = true := by rfl
example : traceMatches (nestedTrial opMUL false 2) (.error .outOfMemory) maskCalls = true := by rfl
example : (nestedTrial opMUL false 2).2.read 0 = some 2 := by rfl
example : traceMatches (nestedTrial opMUL true 0 [0]) (.ok (some 1025)) maskCalls = true := by rfl

-- A successful product candidate stops before a deliberately faulty ADD read.
def firstProduct : Reads where
  constant := fun id => .ok (if id == 1 then some 8 else none)
  operation := fun _ op => if op == opMUL then .ok (some ⟨0, [2, 3]⟩) else .error .invalidOptional
def firstTrial (failAt : Nat) :=
  simplifyWithOptions firstProduct (constructors failAt) 64 opMOD [0, 1] 42 ⟨true, some .osaka⟩ empty
example : traceMatches (firstTrial 0) (.ok (some 1024)) [(1, 9, 0, [2, 3, 1], 42)] = true := by rfl
example : traceMatches (firstTrial 1) (.error .outOfMemory) [(1, 9, 0, [2, 3, 1], 42)] = true := by rfl

def faultyNested (modulus : Word) : Reads where
  constant := fun id => .ok (if id == 1 then some modulus else none)
  operation := fun _ _ => .error .invalidOptional
def faultyTrial (modulus : Word) :=
  simplifyWithOptions (faultyNested modulus) (constructors 0) 64 opMOD [0, 1] 42 ⟨true, some .osaka⟩ empty
example : traceMatches (faultyTrial 7) (.ok none) [] = true := by rfl
example : traceMatches (faultyTrial 8) (.error .invalidOptional) [] = true := by rfl

def highTrial (forYul : Bool) (width : Nat) :=
  run [⟨none, none, []⟩, ⟨some (BitVec.ofNat 256 (2^255)), none, []⟩] opMOD [0, 1] ⟨forYul, some .osaka⟩ 0 width
example : traceMatches (highTrial false 64) (.ok (some 1025))
    [(2, 0, BitVec.ofNat 256 (2^255 - 1), [], 42), (1, 22, 0, [0, 1024], 42)] = true := by rfl
example : traceMatches (highTrial false 7) (.error .safetyFault) [] = true := by rfl
example : traceMatches (highTrial true 7) (.error .safetyFault) [] = true := by rfl

example : traceMatches (run [⟨none, none, []⟩, ⟨some 0, none, []⟩] opMOD [0, 1] ⟨true, some .osaka⟩)
    (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (run [⟨none, none, []⟩] opMOD [0, 0] ⟨true, some .osaka⟩)
    (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl

-- A nonpower modulus is a concrete counterexample to dropping the guard.
example : Folding.Op.mod.value (Folding.Op.add.value (BitVec.allOnes 256) 2 0) 3 0 = 1 := by rfl
example : Folding.Op.addmod.value (BitVec.allOnes 256) 2 3 = 2 := by rfl
example : Folding.Op.mod.value (Folding.Op.mul.value (BitVec.allOnes 256) 2 0) 3 0 = 2 := by rfl
example : Folding.Op.mulmod.value (BitVec.allOnes 256) 2 3 = 0 := by rfl

end Compiler.Extraction.Dispatch.ModuloTests
