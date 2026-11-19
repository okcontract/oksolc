/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchDefaultProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.DefaultTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def nonwords : List Opcode := (List.range 256).map (BitVec.ofNat 8) |>.filter
  (fun op => (Folding.decodeWord op).isNone)
example : nonwords.length = 232 := by rfl
example : nonwords.all (fun op => [0, 1, 2, 3, 4].all (fun arity =>
    traceMatches (run [⟨some 7, none, []⟩, ⟨some 3, none, []⟩, ⟨some 5, none, []⟩, ⟨some 9, none, []⟩]
      op ([0, 1, 2, 3].take arity)) (.ok none) [])) = true := by rfl

-- Reads can fail; only a successful miss leaves later stages reachable.
def faultReads (leftFault : Bool) : Reads where
  constant := fun id => if id == 0 then
    if leftFault then .error .invalidId else .ok none
    else .error .invalidOptional
  operation := fun _ _ => .error .safetyFault
def faults (op : Opcode) (args : List NodeId) (leftFault : Bool) (options : Options := {}) :=
  simplifyWithOptions (faultReads leftFault) (constructors 0) 64 op args 42 options empty
example : outcomeEqual (faults 0 [0, 1] true).1 (.error .invalidId) = true := by rfl
example : outcomeEqual (faults 0 [0, 1] false).1 (.error .invalidOptional) = true := by rfl
example : outcomeEqual (faults 29 [0, 1] false).1 (.error .invalidOptional) = true := by rfl
example : outcomeEqual (faults 0 [0] false).1 (.ok none) = true := by rfl
example : outcomeEqual (faults 0 [0, 1, 2] false).1 (.ok none) = true := by rfl
example : outcomeEqual (faults 0 [] true).1 (.ok none) = true := by rfl
example : outcomeEqual (faults 0 [0, 1, 2, 3] true).1 (.ok none) = true := by rfl
example : outcomeEqual (faults 49 [0] false).1 (.ok none) = true := by rfl
example : outcomeEqual (faults 49 [0] false ⟨false, some .osaka⟩).1 (.error .safetyFault) = true := by rfl

def selfBalance (version : Option Version := none) (args : List NodeId := [0]) (failAt : Nat := 0) :=
  run [⟨none, some opADDRESS, []⟩] opBALANCE args ⟨false, version⟩ failAt
example : traceMatches (selfBalance none) (.ok none) [] = true := by rfl
example : traceMatches (selfBalance (some .petersburg)) (.ok none) [] = true := by rfl
example : traceMatches (selfBalance (some .istanbul)) (.ok (some 1024)) [(1, 71, 0, [], 42)] = true := by rfl
example : traceMatches (selfBalance (some .osaka) [0] 1) (.error .outOfMemory) [(1, 71, 0, [], 42)] = true := by rfl
example : traceMatches (selfBalance (some .osaka) [0, 0]) (.ok none) [] = true := by rfl

end Compiler.Extraction.Dispatch.DefaultTests
