/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchProofs

namespace Compiler.Extraction.Dispatch.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

/-- Read-only probes for differential testing of the callback boundary. These
can represent malformed arities; they carry no graph-coherence assertion. -/
structure Probe where
  constant : Option Word := none
  instruction : Option Opcode := none
  arguments : List NodeId := []

def reads (nodes : List Probe) : Reads where
  constant := fun id => .ok ((nodes[id.toNat]?).bind (·.constant))
  operation := fun id opcode => .ok (do
    let node ← nodes[id.toNat]?
    if node.instruction == some opcode then some ⟨0, node.arguments⟩ else none)

def empty : Heap := ⟨fun _ => none, fun _ => none, none, 0⟩

-- Calls occupy distinct sequence slots, so equal repeated calls cannot erase
-- evidence of their order. Full 256-bit constants and debug IDs are retained.
def record (failAt : Nat) (kind : Kind) (opcode : Opcode) (value : Word)
    (arguments : List NodeId) (debug : NodeId) : Action NodeId := fun heap =>
  let step := ((heap.read 0).getD 0).toNat
  if step ≥ 16 ∨ arguments.length > 4 then (.error .capacity, heap) else
  let key : Key := ⟨kind, opcode, value, arguments, BitVec.ofNat 32 step⟩
  let after := { heap with
    read := fun id => if id == 0 then some (BitVec.ofNat 256 (step + 1)) else heap.read id,
    table := fun other => if other == key then some debug else heap.table other }
  (if failAt == step + 1 then .error .outOfMemory else .ok (BitVec.ofNat 32 (1024 + step)), after)

def constructors (failAt : Nat) : Constructors NodeId :=
  { operation := fun opcode args => record failAt 1 opcode 0 args
    constant := fun value => record failAt 2 0 value []
    materialize := fun original value => record failAt 3 0 value [original] }

def run (nodes : List Probe) (instruction : Opcode) (arguments : List NodeId)
    (options : Options := {}) (failAt : Nat := 0) (usizeBits : Nat := 64) :=
  simplifyWithOptions (reads nodes) (constructors failAt) usizeBits instruction arguments 42 options empty

def outcomeEqual : Except Error (Option NodeId) → Except Error (Option NodeId) → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => decide (left = right)
  | _, _ => false

def traceMatches (actual : Except Error (Option NodeId) × Heap) (result : Except Error (Option NodeId))
    (calls : List (Kind × Opcode × Word × List NodeId × NodeId)) : Bool :=
  outcomeEqual actual.1 result && (actual.2.read 0).getD 0 == BitVec.ofNat 256 calls.length &&
    (calls.zipIdx.all fun ((kind, opcode, value, arguments, debug), index) =>
      actual.2.table ⟨kind, opcode, value, arguments, BitVec.ofNat 32 index⟩ == some debug)

example : (run [⟨some 7, none, []⟩, ⟨some 3, none, []⟩] 1 [0, 1]).1 = .ok (some 1024) := by rfl
example : traceMatches (run [⟨some 7, none, []⟩, ⟨some 3, none, []⟩] 1 [0, 1])
    (.ok (some 1024)) [(2, 0, 10, [], 42)] = true := by rfl
example : traceMatches (run [⟨some 7, none, []⟩, ⟨some 3, none, []⟩] 1 [0, 1] {} 1)
    (.error .outOfMemory) [(2, 0, 10, [], 42)] = true := by rfl
example : hasBitwiseShifting .byzantium = false ∧ hasBitwiseShifting .constantinople = true := by exact ⟨rfl, rfl⟩
example : hasSelfBalance .petersburg = false ∧ hasSelfBalance .istanbul = true := by exact ⟨rfl, rfl⟩
example : (run [] 1 []).1 = .ok none := by rfl
example : (run [] 1 [0, 1, 2, 3]).1 = .ok none := by rfl

end Compiler.Extraction.Dispatch.Tests
