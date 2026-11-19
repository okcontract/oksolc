/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchUnaryProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.UnaryTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests

def tripleZero : List Probe := [⟨none, none, []⟩, ⟨none, some 21, [0]⟩, ⟨none, some 21, [1]⟩]

example : traceMatches (run tripleZero 21 [2]) (.ok (some 1024)) [(1, 21, 0, [0], 42)] = true := by rfl
example : traceMatches (run tripleZero 21 [2] {} 1) (.error .outOfMemory) [(1, 21, 0, [0], 42)] = true := by rfl
example : (run tripleZero 21 [2] {} 1).2.read 0 = some 1 := by rfl

def faultReads (error : Storage.ReadError) : Reads where
  constant := fun _ => .error error
  operation := fun _ _ => .error error

example (error : Storage.ReadError) : (unaryStage (faultReads error) (constructors 0) opNOT 0 42 empty).1 =
    .error (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault) := by
  cases error <;> rfl
example (error : Storage.ReadError) : (unaryStage (faultReads error) (constructors 0) opNOT 0 42 empty).2 = empty := by
  cases error <;> rfl
example : (unaryStage (faultReads .invalidId) (constructors 0) opADD 0 42 empty).1 = .ok none := by rfl

/-- The first successful comparison lookup must terminate. Later probes fail,
so this also detects accidental fallthrough after a successful construction.
These callback fixtures do not claim graph coherence. -/
def firstComparison : Reads where
  constant := fun _ => .ok none
  operation := fun id opcode =>
    if id == 2 && opcode == opISZERO then .ok (some ⟨0, [1]⟩)
    else if id == 1 && opcode == opISZERO then .ok none
    else if id == 1 && opcode == opEQ then .ok (some ⟨0, [0, 0]⟩)
    else .error .safetyFault

example : traceMatches (unaryStage firstComparison (constructors 0) opISZERO 2 42 empty)
    (.ok (some 1024)) [(1, 20, 0, [0, 0], 42)] = true := by rfl
example : traceMatches (unaryStage firstComparison (constructors 1) opISZERO 2 42 empty)
    (.error .outOfMemory) [(1, 20, 0, [0, 0], 42)] = true := by rfl

example : Unary.iszero.eval (Unary.iszero.eval (2 : Word)) = 1 := by rfl
example : Folding.Op.eq.eval [0, BitVec.allOnes 256] = some 0 ∧
    Unary.iszero.eval (0 - BitVec.allOnes 256) = 0 := by exact ⟨rfl, rfl⟩

/-- Constant folding must stop before any nested-operation probe. These read
callbacks test order independently of a storage-coherence premise. -/
def constantFirst : Reads where
  constant := fun _ => .ok (some 7)
  operation := fun _ _ => .error .invalidOptional

def fullConstant (instruction : Opcode) (failAt : Nat) :=
  simplifyWithOptions constantFirst (constructors failAt) 64 instruction [0] 42 ⟨true, some .osaka⟩ empty

example : traceMatches (fullConstant opNOT 0) (.ok (some 1024))
    [(2, 0, BitVec.ofInt 256 (-8), [], 42)] = true := by rfl
example : traceMatches (fullConstant opISZERO 0) (.ok (some 1024))
    [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (fullConstant opNOT 1) (.error .outOfMemory)
    [(2, 0, BitVec.ofInt 256 (-8), [], 42)] = true := by rfl
example : (fullConstant opNOT 1).2.read 0 = some 1 := by rfl
example : (simplifyWithOptions (faultReads .invalidId) (constructors 0) 64 opNOT [0] 42 {} empty).1 =
    .error .invalidId := by rfl
example (version : Version) :
    evmStage (faultReads .invalidId) (constructors 0) 64 opISZERO [0] 42 version = pure none :=
  word_unary_evm_stage (faultReads .invalidId) (constructors 0) .iszero (Or.inr rfl) [0] 42 version 64

end Compiler.Extraction.Dispatch.UnaryTests
