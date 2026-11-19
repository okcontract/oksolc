/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchDivisionProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.DivisionTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 4096

-- Callback probes test order and failures without asserting graph coherence.
def divisorPower : Reads where
  constant := fun id => if id == 1 then .ok (some 8) else .error .invalidOptional
  operation := fun _ _ => .error .safetyFault

def revisionTrial (failAt : Nat) :=
  evmStage divisorPower (constructors failAt) 64 opDIV [0, 1] 42 .osaka empty

def revisionCalls : List (Kind × Opcode × Word × List NodeId × NodeId) :=
  [(2, 0, 3, [], 42), (1, 28, 0, [1024, 0], 42)]

example : traceMatches (revisionTrial 0) (.ok (some 1025)) revisionCalls = true := by rfl
example : traceMatches (revisionTrial 1) (.error .outOfMemory) (revisionCalls.take 1) = true := by rfl
example : traceMatches (revisionTrial 2) (.error .outOfMemory) revisionCalls = true := by rfl
example : (revisionTrial 2).2.read 0 = some 2 := by rfl
example : (evmStage divisorPower (constructors 0) 64 opDIV [0, 1] 42 .byzantium empty).1 = .ok none := by rfl

def highTrial (width : Nat) (version : Version) :=
  run [⟨none, none, []⟩, ⟨some (BitVec.ofNat 256 (2^255)), none, []⟩]
    opDIV [0, 1] ⟨false, some version⟩ 0 width

example : traceMatches (highTrial 64 .osaka) (.ok (some 1025))
    [(2, 0, 255, [], 42), (1, 28, 0, [1024, 0], 42)] = true := by rfl
example : traceMatches (highTrial 7 .osaka) (.error .safetyFault) [] = true := by rfl
example : traceMatches (highTrial 7 .byzantium) (.ok none) [] = true := by rfl

def shifted (amount base : Word) (args : List NodeId := [1, 2]) : List Probe :=
  [⟨none, none, []⟩, ⟨some amount, none, []⟩, ⟨some base, none, []⟩, ⟨none, some opSHL, args⟩]
def shiftTrial (amount base : Word) (failAt : Nat := 0) :=
  run (shifted amount base) opDIV [0, 3] ⟨false, some .byzantium⟩ failAt

example : traceMatches (shiftTrial 256 1) (.ok (some 1024)) [(1, 28, 0, [1, 0], 42)] = true := by rfl
example : traceMatches (shiftTrial 256 1 1) (.error .outOfMemory) [(1, 28, 0, [1, 0], 42)] = true := by rfl
example : traceMatches (shiftTrial 7 2) (.ok none) [] = true := by rfl
example : traceMatches (run (shifted 7 1 [1]) opDIV [0, 3]) (.ok none) [] = true := by rfl
example : traceMatches (run [⟨none, none, []⟩, ⟨some 3, none, []⟩] opDIV [0, 1] ⟨true, some .osaka⟩)
    (.ok none) [] = true := by rfl
example : traceMatches (run [⟨some 17, none, []⟩, ⟨some 8, none, []⟩] opDIV [0, 1] ⟨true, some .osaka⟩)
    (.ok (some 1024)) [(2, 0, 2, [], 42)] = true := by rfl
example : traceMatches (run [⟨some 17, none, []⟩, ⟨some 0, none, []⟩] opDIV [0, 1])
    (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (run [⟨none, none, []⟩] opDIV [0, 0] ⟨true, some .osaka⟩)
    (.ok none) [] = true := by rfl

end Compiler.Extraction.Dispatch.DivisionTests
