/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAndProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.AndTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Calls := List (Kind × Opcode × Word × List NodeId × NodeId)
def byteTrial (mask : Word) (reverse : Bool := false) (args : List NodeId := [2, 3]) (failAt : Nat := 0) :=
  run [⟨none, some opBYTE, args⟩, ⟨some mask, none, []⟩] opAND (if reverse then [1, 0] else [0, 1]) {} failAt
example : traceMatches (byteTrial 255) (.ok (some 1024)) [(1, 26, 0, [2, 3], 42)] = true := by rfl
example : traceMatches (byteTrial 255 false [2]) (.ok (some 1024)) [(1, 26, 0, [2], 42)] = true := by rfl
example : traceMatches (byteTrial 255 true) (.ok none) [] = true := by rfl
example : traceMatches (byteTrial 256) (.ok none) [] = true := by rfl
example : traceMatches (byteTrial (BitVec.allOnes 256)) (.ok (some 0)) [] = true := by rfl
example : traceMatches (byteTrial 0) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (byteTrial 255 false [2, 3] 1) (.error .outOfMemory) [(1, 26, 0, [2, 3], 42)] = true := by rfl

def stripTrial (mask index : Word) (reverse : Bool := false) (failAt : Nat := 0) :=
  run [⟨some mask, none, []⟩, ⟨some index, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opSIGNEXTEND, [1, 2]⟩] opAND (if reverse then [3, 0] else [0, 3]) {} failAt
def stripCalls : Calls := [(3, 0, 255, [0], 42), (1, 22, 0, [1024, 2], 42)]
example : [false, true].all (fun reverse => traceMatches (stripTrial 255 0 reverse) (.ok (some 1025)) stripCalls) = true := by rfl
example : [1, 2].all (fun failAt => traceMatches (stripTrial 255 0 false failAt)
    (.error .outOfMemory) (stripCalls.take failAt)) = true := by rfl
example : traceMatches (stripTrial 256 0) (.ok none) [] = true := by rfl
example : traceMatches (stripTrial 255 31) (.ok none) [] = true := by rfl

def addressTrial (op : Opcode) (reverse : Bool := false) (mask : Word := AddressMask.mask) (failAt : Nat := 0) :=
  run [⟨some mask, none, []⟩, ⟨none, some op, []⟩] opAND (if reverse then [1, 0] else [0, 1]) {} failAt
example : [48, 51, 50, 65].all (fun op => [false, true].all (fun reverse =>
    traceMatches (addressTrial op reverse) (.ok (some 1024)) [(1, op, 0, [], 42)])) = true := by rfl
example : traceMatches (addressTrial 48 false (AddressMask.mask - 1)) (.ok none) [] = true := by rfl
example : traceMatches (addressTrial 48 false AddressMask.mask 1) (.error .outOfMemory) [(1, 48, 0, [], 42)] = true := by rfl

def reassociateTrial (reverse : Bool := false) (failAt : Nat := 0) :=
  run [⟨none, none, []⟩, ⟨some 7, none, []⟩, ⟨none, some opAND, [0, 1]⟩, ⟨none, none, []⟩]
    opAND (if reverse then [3, 2] else [2, 3]) {} failAt
def reassociateCalls (reverse : Bool := false) : Calls :=
  [(1, 22, 0, if reverse then [3, 0] else [0, 3], 42), (3, 0, 7, [1], 42), (1, 22, 0, [1024, 1025], 42)]
example : [false, true].all (fun reverse => traceMatches (reassociateTrial reverse)
    (.ok (some 1026)) (reassociateCalls reverse)) = true := by rfl
example : [1, 2, 3].all (fun failAt => traceMatches (reassociateTrial false failAt)
    (.error .outOfMemory) ((reassociateCalls false).take failAt)) = true := by rfl

def alternatingTrial (reverse : Bool := false) (failAt : Nat := 0) :=
  run [⟨some 6, none, []⟩, ⟨some 3, none, []⟩, ⟨none, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opAND, [2, 1]⟩, ⟨none, some opOR, [4, 3]⟩]
    opAND (if reverse then [0, 5] else [5, 0]) {} failAt
def alternatingCalls : Calls := [(2, 0, 2, [], 42), (1, 22, 0, [2, 1024], 42),
  (3, 0, 6, [0], 42), (1, 22, 0, [3, 1026], 42), (1, 23, 0, [1025, 1027], 42)]
example : [false, true].all (fun reverse => traceMatches (alternatingTrial reverse)
    (.ok (some 1028)) alternatingCalls) = true := by rfl
example : [1, 2, 3, 4, 5].all (fun failAt => traceMatches (alternatingTrial false failAt)
    (.error .outOfMemory) (alternatingCalls.take failAt)) = true := by rfl
example : (alternatingTrial false 5).2.read 0 = some 5 := by rfl

def coveredTrial (amount mask : Word) (reverse : Bool := false) (failAt : Nat := 0) :=
  run [⟨some mask, none, []⟩, ⟨some amount, none, []⟩, ⟨none, none, []⟩, ⟨none, some opSHR, [1, 2]⟩]
    opAND (if reverse then [3, 0] else [0, 3]) {} failAt
example : [false, true].all (fun reverse => traceMatches (coveredTrial 7 (BitVec.allOnes 256 >>> 7) reverse)
    (.ok (some 1024)) [(1, 28, 0, [1, 2], 42)]) = true := by rfl
example : traceMatches (coveredTrial 256 1) (.ok (some 1024)) [(1, 28, 0, [1, 2], 42)] = true := by rfl
example : traceMatches (coveredTrial 257 1) (.ok none) [] = true := by rfl
example : traceMatches (coveredTrial 7 1) (.ok none) [] = true := by rfl
example : traceMatches (coveredTrial 7 (BitVec.allOnes 256)) (.ok (some 3)) [] = true := by rfl

def mergedTrial (amount : Option Word) (failAt : Nat := 0) :=
  run [⟨amount, none, []⟩, ⟨none, none, []⟩, ⟨none, none, []⟩,
    ⟨none, some opSHL, [0, 1]⟩, ⟨none, some opSHL, [0, 2]⟩] opAND [3, 4] {} failAt
def mergedCalls : Calls := [(1, 22, 0, [1, 2], 42), (1, 27, 0, [0, 1024], 42)]
example : [none, some 0, some 255, some 256, some (BitVec.allOnes 256)].all
    (fun amount => traceMatches (mergedTrial amount) (.ok (some 1025)) mergedCalls) = true := by rfl
example : [1, 2].all (fun failAt => traceMatches (mergedTrial none failAt)
    (.error .outOfMemory) (mergedCalls.take failAt)) = true := by rfl

example : traceMatches (run [⟨none, none, []⟩, ⟨none, none, []⟩, ⟨none, some opOR, [1, 0]⟩] opAND [0, 2])
    (.ok (some 0)) [] = true := by rfl
example : traceMatches (run [⟨none, none, []⟩, ⟨none, some opNOT, [0]⟩] opAND [0, 1])
    (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (run [⟨none, none, []⟩, ⟨none, none, []⟩, ⟨none, some opAND, [0, 1]⟩] opAND [2, 0])
    (.ok (some 1024)) [(1, 22, 0, [0, 1], 42)] = true := by rfl
example : traceMatches (run [⟨some 7, none, []⟩, ⟨some 3, none, []⟩] opAND [0, 1])
    (.ok (some 1024)) [(2, 0, 3, [], 42)] = true := by rfl

-- Callback probes retain early success and the final candidate's read order.
def byteReads : Reads where
  constant := fun id => .ok (if id == 1 then some 255 else none)
  operation := fun id op => if id == 0 && op == opBYTE then .ok (some ⟨0, [2, 3]⟩) else .error .invalidOptional
def byteFirst (failAt : Nat := 0) := simplifyWithOptions byteReads (constructors failAt) 64 opAND [0, 1] 42 {} empty
example : traceMatches (byteFirst 0) (.ok (some 1024)) [(1, 26, 0, [2, 3], 42)] = true := by rfl
example : traceMatches (byteFirst 1) (.error .outOfMemory) [(1, 26, 0, [2, 3], 42)] = true := by rfl
def mergedFaultReads : Reads where
  constant := fun _ => .ok none
  operation := fun id op => if op == opSHL then
    if id == 0 then .ok (some ⟨0, [2]⟩) else .error .invalidOptional else .ok none
def mergedFault := simplifyWithOptions mergedFaultReads (constructors 0) 64 opAND [0, 1] 42 {} empty
example : traceMatches mergedFault (.error .invalidOptional) [] = true := by rfl

end Compiler.Extraction.Dispatch.AndTests
