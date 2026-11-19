/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchExponentProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.ExponentTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def minusTrial (failAt : Nat) :=
  run [⟨some (BitVec.allOnes 256), none, []⟩, ⟨none, none, []⟩] opEXP [0, 1] ⟨true, some .osaka⟩ failAt
def minusCalls : List (Kind × Opcode × Word × List NodeId × NodeId) :=
  [(2, 0, 1, [], 42), (1, 22, 0, [1, 1024], 42),
   (1, 21, 0, [1025], 42), (1, 3, 0, [1026, 1025], 42)]

example : traceMatches (minusTrial 0) (.ok (some 1027)) minusCalls = true := by rfl
example : traceMatches (minusTrial 1) (.error .outOfMemory) (minusCalls.take 1) = true := by rfl
example : traceMatches (minusTrial 2) (.error .outOfMemory) (minusCalls.take 2) = true := by rfl
example : traceMatches (minusTrial 3) (.error .outOfMemory) (minusCalls.take 3) = true := by rfl
example : traceMatches (minusTrial 4) (.error .outOfMemory) minusCalls = true := by rfl
example : (minusTrial 4).2.read 0 = some 4 := by rfl

def baseTrial (base : Word) (version : Option Version) (failAt : Nat := 0) :=
  run [⟨some base, none, []⟩, ⟨none, none, []⟩] opEXP [0, 1] ⟨false, version⟩ failAt
def shiftCalls : List (Kind × Opcode × Word × List NodeId × NodeId) :=
  [(2, 0, 1, [], 42), (1, 27, 0, [1, 1024], 42)]
example : traceMatches (baseTrial 0 (some .homestead)) (.ok (some 1024)) [(1, 21, 0, [1], 42)] = true := by rfl
example : traceMatches (baseTrial 1 (some .homestead)) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl
example : traceMatches (baseTrial 2 (some .constantinople)) (.ok (some 1025)) shiftCalls = true := by rfl
example : traceMatches (baseTrial 2 (some .constantinople) 2) (.error .outOfMemory) shiftCalls = true := by rfl
example : traceMatches (baseTrial 2 (some .byzantium)) (.ok none) [] = true := by rfl
example : traceMatches (baseTrial 1 none) (.ok none) [] = true := by rfl
example : traceMatches (baseTrial 3 (some .osaka)) (.ok none) [] = true := by rfl

def folded (base exponent : Word) (failAt : Nat := 0) :=
  run [⟨some base, none, []⟩, ⟨some exponent, none, []⟩] opEXP [0, 1] ⟨true, some .osaka⟩ failAt
example : traceMatches (folded 0 0) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl
example : traceMatches (folded 2 256) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (folded (BitVec.allOnes 256) 2) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl
example : traceMatches (folded (BitVec.allOnes 256) 3 1) (.error .outOfMemory)
    [(2, 0, BitVec.allOnes 256, [], 42)] = true := by rfl

-- The revision stage reads only the base. These callbacks assert no coherence.
def onlyBase : Reads where
  constant := fun id => if id == 0 then .ok (some 1) else .error .invalidOptional
  operation := fun _ _ => .error .safetyFault
example : traceMatches (evmStage onlyBase (constructors 0) 64 opEXP [0, 1] 42 .osaka empty)
    (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl
example : traceMatches (evmStage onlyBase (constructors 0) 64 opEXP [1, 0] 42 .osaka empty)
    (.error .invalidOptional) [] = true := by rfl

end Compiler.Extraction.Dispatch.ExponentTests
