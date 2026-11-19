/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchArityProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.ArityTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option exponentiation.threshold 512

def modularTrial (instruction : Opcode) (failAt : Nat := 0) :=
  run [⟨some (BitVec.allOnes 256), none, []⟩, ⟨some 2, none, []⟩, ⟨some 3, none, []⟩]
    instruction [0, 1, 2] ⟨true, some .osaka⟩ failAt

example : traceMatches (modularTrial opADDMOD) (.ok (some 1024)) [(2, 0, 2, [], 42)] = true := by rfl
example : traceMatches (modularTrial opMULMOD) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (modularTrial opADDMOD 1) (.error .outOfMemory) [(2, 0, 2, [], 42)] = true := by rfl
example : (modularTrial opADDMOD 1).2.read 0 = some 1 := by rfl
example : traceMatches (modularTrial opADD) (.ok none) [] = true := by rfl
example : traceMatches (modularTrial opISZERO) (.ok none) [] = true := by rfl

def missingThenFault : Reads where
  constant := fun id => if id == 0 then .ok none else .error .invalidOptional
  operation := fun _ _ => .error .safetyFault

def missingTrial (arguments : List NodeId) :=
  simplifyWithOptions missingThenFault (constructors 0) 64 opADDMOD arguments 42 ⟨true, some .osaka⟩ empty

example : traceMatches (missingTrial [0, 1, 2]) (.ok none) [] = true := by rfl
example : traceMatches (missingTrial [1, 0, 2]) (.error .invalidOptional) [] = true := by rfl
example : traceMatches (missingTrial []) (.ok none) [] = true := by rfl
example : traceMatches (missingTrial [1, 2, 3, 4]) (.ok none) [] = true := by rfl
example : traceMatches (missingTrial (List.replicate 17 1)) (.ok none) [] = true := by rfl

def zeroModulus (instruction : Opcode) :=
  run [⟨some 7, none, []⟩, ⟨some 9, none, []⟩, ⟨some 0, none, []⟩] instruction [0, 1, 2]
example : traceMatches (zeroModulus opADDMOD) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (zeroModulus opMULMOD) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl

end Compiler.Extraction.Dispatch.ArityTests
