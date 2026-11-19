/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchMultiplicationProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.MultiplicationTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 4096

/-- Test the revision stage in isolation: its first candidate must stop before
a later failing read. These callbacks do not assert graph coherence. -/
def firstPower : Reads where
  constant := fun id => if id == 0 then .ok (some 8) else .error .invalidOptional
  operation := fun _ _ => .error .safetyFault

def revisionTrial (failAt : Nat) :=
  evmStage firstPower (constructors failAt) 64 opMUL [0, 1] 42 .osaka empty

def revisionCalls : List (Kind × Opcode × Word × List NodeId × NodeId) :=
  [(2, 0, 3, [], 42), (1, 27, 0, [1024, 1], 42)]

example : traceMatches (revisionTrial 0) (.ok (some 1025)) revisionCalls = true := by rfl
example : traceMatches (revisionTrial 1) (.error .outOfMemory) (revisionCalls.take 1) = true := by rfl
example : traceMatches (revisionTrial 2) (.error .outOfMemory) revisionCalls = true := by rfl
example : (revisionTrial 2).2.read 0 = some 2 := by rfl
example : (evmStage firstPower (constructors 0) 64 opMUL [0, 1] 42 .byzantium empty).1 = .ok none := by rfl

def highPower : List Probe := [⟨some (BitVec.ofNat 256 (2^255)), none, []⟩, ⟨none, none, []⟩]
def highTrial (width : Nat) (version : Version) := run highPower opMUL [0, 1] ⟨false, some version⟩ 0 width

example : traceMatches (highTrial 64 .osaka) (.ok (some 1025))
    [(2, 0, 255, [], 42), (1, 27, 0, [1024, 1], 42)] = true := by rfl
example : traceMatches (highTrial 7 .osaka) (.error .safetyFault) [] = true := by rfl
example : traceMatches (highTrial 7 .byzantium) (.ok none) [] = true := by rfl
example : BinaryLogarithm.binaryLogarithm 0 1 = .ok (some 0) := by rfl
example : BinaryLogarithm.binaryLogarithm 0 2 = .error .invalidCast := by rfl

example : traceMatches (run [⟨some 3, none, []⟩, ⟨none, none, []⟩] opMUL [0, 1] ⟨true, some .osaka⟩)
    (.ok none) [] = true := by rfl
example : traceMatches (run [⟨some 8, none, []⟩, ⟨some 3, none, []⟩] opMUL [0, 1] ⟨true, some .osaka⟩)
    (.ok (some 1024)) [(2, 0, 24, [], 42)] = true := by rfl

-- Reassociation precedes the also-eligible shift-product candidate.
def competing : List Probe := [⟨none, none, []⟩, ⟨some 7, none, []⟩, ⟨none, some 2, [0, 1]⟩,
  ⟨none, none, []⟩, ⟨some 1, none, []⟩, ⟨none, some 27, [3, 4]⟩]
example : traceMatches (run competing opMUL [2, 5] ⟨true, some .osaka⟩) (.ok (some 1026))
    [(1, 2, 0, [0, 5], 42), (3, 0, 7, [1], 42), (1, 2, 0, [1024, 1025], 42)] = true := by rfl

end Compiler.Extraction.Dispatch.MultiplicationTests
