/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AddressMaskProofs
import Compiler.Extraction.NestedConstructionTests

namespace Compiler.Extraction.AddressMask.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul
open Compiler.Extraction.Nested.Tests (literal operation corrupt fallback)

def env : Environment := ⟨⟨3, 5⟩, 7, 9⟩
def graph := [literal nativeMask, operation 48 [] 5, operation 51 [] 3,
  operation 50 [] 7, operation 65 [] 9]
def reads := storageReads graph
def initial : Heap := ⟨readValue graph, fun _ => none, none, 0⟩

theorem coherent : Coherent (meaning env fallback) graph := by
  simp [Coherent, graph, literal, operation, Item.eval, readArguments,
    Cell.value, Cell.isPush, Cell.dataValue, meaning, Folding.wordMeaning, Folding.decodeWord,
    Folding.wordOperations, Folding.Op.opcode, addressMeaning, decode,
    Kind.opcode, Kind.eval, Kind.value, Kind.addressValue, env, fallback]

example : nativeMask = mask := by rfl
example : addressInstruction reads 1 0 = .ok (some 48) := by rfl
example : addressInstruction reads 2 0 = .ok (some 51) := by rfl
example : addressInstruction reads 3 0 = .ok (some 50) := by rfl
example : addressInstruction reads 4 0 = .ok (some 65) := by rfl
example : addressInstruction reads 0 1 = .ok none := by rfl
example : addressInstruction reads 99 0 = .ok none := by rfl
example : addressInstruction reads 1 99 = .ok none := by rfl
example : addressInstruction (storageReads [literal nativeMask, operation 48 [0] 5]) 1 0 = .ok none := by rfl
example : addressInstruction (storageReads [literal (nativeMask - 1), operation 48 [] 5]) 1 0 = .ok none := by rfl
example : addressInstruction (storageReads [literal (BitVec.twoPow 256 160), operation 48 [] 5]) 1 0 = .ok none := by rfl
example : addressInstruction (storageReads (literal nativeMask :: corrupt)) 1 0 = .error .invalidOptional := by rfl
example : addressInstruction (storageReads (literal 0 :: corrupt)) 1 0 = .ok none := by rfl

-- Deliberately polymorphic probes expose first-match order and early faults;
-- they have no native graph coherence claim.
def everyMatch : Reads := ⟨fun _ => .ok (some nativeMask), fun _ _ => .ok (some ⟨0, []⟩), none⟩
example : addressInstruction everyMatch 1 0 = .ok (some 48) := by rfl
example : addressInstruction { everyMatch with operation := fun _ opcode =>
    if opcode == 48 then (.ok none) else (.ok (some ⟨0, []⟩)) } 1 0 = .ok (some 51) := by rfl
example : addressInstruction { everyMatch with operation := fun _ opcode =>
    if opcode == 48 then (.ok (some ⟨0, [1]⟩)) else (.ok (some ⟨0, []⟩)) } 1 0 = .ok (some 51) := by rfl
example : addressInstruction { everyMatch with operation := fun _ opcode =>
    if opcode == 48 then (.ok (some ⟨0, []⟩)) else (.error .safetyFault) } 1 0 = .ok (some 48) := by rfl
example : addressInstruction { everyMatch with operation := fun _ opcode =>
    if opcode == 48 then (.error .safetyFault) else (.ok (some ⟨0, []⟩)) } 1 0 = .error .safetyFault := by rfl
example : addressInstruction { everyMatch with constant := fun _ => .error .invalidId } 1 0 = .error .invalidId := by rfl

example : Kind.address.value env = 5 ∧ Kind.caller.value env = 3 ∧
    Kind.origin.value env = 7 ∧ Kind.coinbase.value env = 9 := by exact ⟨rfl, rfl, rfl, rfl⟩
example : (meaning env fallback).operation 48 77 [] = some 5 := by rfl
example : (meaning env fallback).operation 48 77 [1] = none := by rfl
example : (meaning env fallback).operation 50 77 [] = some 7 := by rfl
example : (meaning env fallback).operation 65 77 [] = some 9 := by rfl
example : ((BitVec.allOnes 160).setWidth 256 &&& mask) = mask := by rfl
example : 0#256 &&& mask = 0 := by rfl
example : BitVec.twoPow 256 160 &&& mask ≠ BitVec.twoPow 256 160 := by decide
example : let p := { Fixtures.primitives with publish := publish false }
    let result := internerBuilder p 48 [] () initial
    result.1 = .error .outOfMemory ∧ result.2.read 7 = some 42 := by exact ⟨rfl, rfl⟩

end Compiler.Extraction.AddressMask.Tests
