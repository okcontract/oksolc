/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchSignedProofs
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Dispatch.SignedTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.Dispatch.Tests

def signedPair (a b : Int) : List Probe :=
  [⟨some (BitVec.ofInt 256 a), none, []⟩, ⟨some (BitVec.ofInt 256 b), none, []⟩]

def zeroRight : List Probe := [⟨none, none, []⟩, ⟨some 0, none, []⟩]
def oneRight : List Probe := [⟨none, none, []⟩, ⟨some 1, none, []⟩]

example : traceMatches (run (signedPair (-7) 2) 5 [0, 1]) (.ok (some 1024))
    [(2, 0, BitVec.ofInt 256 (-3), [], 42)] = true := by rfl
example : traceMatches (run (signedPair (-7) 2) 7 [0, 1]) (.ok (some 1024))
    [(2, 0, BitVec.ofInt 256 (-1), [], 42)] = true := by rfl
example : traceMatches (run (signedPair 7 (-2)) 7 [0, 1]) (.ok (some 1024))
    [(2, 0, 1, [], 42)] = true := by rfl
example : traceMatches (run (signedPair (-(2^255)) (-1)) 5 [0, 1]) (.ok (some 1024))
    [(2, 0, BitVec.ofNat 256 (2^255), [], 42)] = true := by rfl
example : traceMatches (run (signedPair (-(2^255)) (-1)) 7 [0, 1]) (.ok (some 1024))
    [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (run zeroRight 5 [0, 1]) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl
example : traceMatches (run zeroRight 5 [0, 1] {} 1) (.error .outOfMemory)
    [(2, 0, 0, [], 42)] = true := by rfl
example : (run zeroRight 5 [0, 1] {} 1).2.read 0 = some 1 := by rfl
example : traceMatches (run oneRight 5 [0, 1]) (.ok (some 0)) [] = true := by rfl
-- Constant folding keeps priority over the division-by-one identity.
example : traceMatches (run (signedPair 7 1) 5 [0, 1]) (.ok (some 1024))
    [(2, 0, 7, [], 42)] = true := by rfl
-- SMOD has no zero/one-divisor inline rule in this source, despite the word laws.
example : traceMatches (run zeroRight 7 [0, 1]) (.ok none) [] = true := by rfl
example : traceMatches (run oneRight 7 [0, 1]) (.ok none) [] = true := by rfl
example : traceMatches (run [] 7 [0, 0] ⟨true, some .osaka⟩) (.ok none) [] = true := by rfl

def readFailure : Reads where
  constant := fun id => if id == 0 then .ok (some 0) else .error .invalidId
  operation := fun _ _ => .error .invalidOptional

example : (simplifyWithOptions readFailure (constructors 0) 64 opSDIV [0, 1] 42 {} empty).1 =
    .error .invalidId := by rfl
example : (simplifyWithOptions readFailure (constructors 0) 64 opSDIV [0, 1] 42 {} empty).2 = empty := by rfl
example (version : Version) :
    evmStage readFailure (constructors 0) 64 opSDIV [0, 1] 42 version = pure none :=
  signed_evm_stage readFailure (constructors 0) .sdiv (Or.inl rfl) [0, 1] 42 version 64

end Compiler.Extraction.Dispatch.SignedTests
