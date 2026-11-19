/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAssociativeProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.AssociativeTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests

/-- A later candidate traps if entered. This callback fixture checks order and
failure propagation; it does not assert graph coherence. -/
def leftReassociation : Reads where
  constant := fun id => .ok (if id == 4 then some 7 else none)
  operation := fun id opcode =>
    if id == 2 && opcode == opADD then .ok (some ⟨0, [0, 4]⟩)
    else if id == 3 then .error .invalidOptional else .ok none

def trapped (failAt : Nat) :=
  simplifyWithOptions leftReassociation (constructors failAt) 64 opADD [2, 3] 42 {} empty

def calls : List (Kind × Opcode × Word × List NodeId × NodeId) :=
  [(1, 1, 0, [0, 3], 42), (3, 0, 7, [4], 42), (1, 1, 0, [1024, 1025], 42)]

example : traceMatches (trapped 0) (.ok (some 1026)) calls = true := by rfl
example : traceMatches (trapped 1) (.error .outOfMemory) (calls.take 1) = true := by rfl
example : traceMatches (trapped 2) (.error .outOfMemory) (calls.take 2) = true := by rfl
example : traceMatches (trapped 3) (.error .outOfMemory) calls = true := by rfl
example : (trapped 2).2.read 0 = some 2 := by rfl

def absorption : List Probe := [⟨none, none, []⟩, ⟨none, none, []⟩, ⟨none, some 22, [0, 1]⟩]
def cancellation : List Probe := [⟨none, none, []⟩, ⟨none, none, []⟩, ⟨none, some 24, [0, 1]⟩]

example : traceMatches (run absorption 23 [0, 2]) (.ok (some 0)) [] = true := by rfl
example : traceMatches (run absorption 23 [2, 0]) (.ok (some 0)) [] = true := by rfl
example : traceMatches (run cancellation 24 [0, 2]) (.ok (some 1)) [] = true := by rfl
example : traceMatches (run cancellation 24 [2, 0]) (.ok (some 1)) [] = true := by rfl
example : traceMatches (run [⟨some (BitVec.allOnes 256), none, []⟩, ⟨some 1, none, []⟩] 1 [0, 1])
    (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl

-- General stage composition must retain a mutating miss. Only a separate
-- exact-state proof licenses reuse of a stage's starting heap.
def growingMiss : Action (Option NodeId) := do
  let _ ← record 0 2 0 7 [] 42
  return none

example : (orNext growingMiss (pure none) empty).1 = .ok none := by rfl
example : (orNext growingMiss (pure none) empty).2.read 0 = some 1 := by rfl

end Compiler.Extraction.Dispatch.AssociativeTests
