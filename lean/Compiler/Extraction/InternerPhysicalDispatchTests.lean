/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatch
import Compiler.Extraction.InternerPhysicalTests
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def traceWorld : World (List Interner.Request) :=
  ⟨Dispatch.Tests.empty, ⟨fun _ => none, ⟨[], 0, 4⟩, []⟩⟩

def recording (failAt : Nat) (fault : Fault) : Find (List Interner.Request) := fun request before =>
  let index := before.memory.effects.length
  let after := { before with
    memory := { before.memory with effects := before.memory.effects ++ [request] }
    graph := { before.graph with allocationCursor := before.graph.allocationCursor + 1 } }
  (if failAt = index + 1 then .error fault else .ok (BitVec.ofNat 32 (1024 + index)), after)

def trace (nodes : List Dispatch.Tests.Probe) (opcode : Opcode) (args : List NodeId)
    (options : Dispatch.Options := {}) (failAt : Nat := 0) (fault : Fault := .language .outOfMemory) :=
  Dispatch.simplifyWithOptions (Dispatch.Tests.reads nodes) (constructors (recording failAt fault)) 64 opcode args () options traceWorld

theorem constant_trace : (trace [⟨some 10, none, []⟩, ⟨some 32, none, []⟩] 1 [0, 1]).1 = .ok (some 1024) ∧
    (trace [⟨some 10, none, []⟩, ⟨some 32, none, []⟩] 1 [0, 1]).2.memory.effects =
      [Interner.constructorCode.constantRequest 42] := ⟨rfl, rfl⟩

def boolean := trace [⟨none, none, []⟩, ⟨some 0, none, []⟩] 17 [0, 1]

theorem sequential_constructor_state : boolean.1 = .ok (some 1025) ∧ boolean.2.graph.allocationCursor = 2 ∧
    boolean.2.memory.effects = [Interner.constructorCode.operationRequest 21 [0], Interner.constructorCode.operationRequest 21 [1024]] :=
  ⟨rfl, rfl, rfl⟩

theorem first_failure_stops_second :
    let ran := trace [⟨none, none, []⟩, ⟨some 0, none, []⟩] 17 [0, 1] {} 1
    ran.1 = .error (.language .outOfMemory) ∧ ran.2.memory.effects = [Interner.constructorCode.operationRequest 21 [0]] := ⟨rfl, rfl⟩

theorem second_failure_retains_first :
    let ran := trace [⟨none, none, []⟩, ⟨some 0, none, []⟩] 17 [0, 1] {} 2
    ran.1 = .error (.language .outOfMemory) ∧ ran.2.graph.allocationCursor = 2 ∧ ran.2.memory.effects = boolean.2.memory.effects := ⟨rfl, rfl, rfl⟩

theorem semantic_failure_retains_effects :
    let ran := trace [⟨none, none, []⟩, ⟨some 0, none, []⟩] 17 [0, 1] {} 2 (.memory (.preparation .incomplete))
    ordinary ran.1 = false ∧ ran.2.graph.allocationCursor = 2 ∧ ran.2.memory.effects = boolean.2.memory.effects := ⟨rfl, rfl, rfl⟩

theorem materialization_encoding :
    let ran := (constructors (recording 0 (.language .outOfMemory))).materialize 9 42 () traceWorld
    ran.1 = .ok 1024 ∧ ran.2.memory.effects = [Interner.constructorCode.constantRequest 42] := ⟨rfl, rfl⟩

theorem unary_dispatch :
    let ran := trace [⟨none, some 24, [1, 2]⟩, {}, {}] 21 [0]
    ran.1 = .ok (some 1024) ∧ ran.2.memory.effects = [Interner.constructorCode.operationRequest 20 [1, 2]] := ⟨rfl, rfl⟩

theorem revision_dispatch :
    let nodes : List Dispatch.Tests.Probe := [⟨none, some 48, []⟩]
    (trace nodes 49 [0] { evmVersion := some .petersburg }).1 = .ok none ∧
    (trace nodes 49 [0] { evmVersion := some .istanbul }).2.memory.effects = [Interner.constructorCode.operationRequest 71 []] := ⟨rfl, rfl⟩

/-- This concrete recursive fixture actually invokes the complete physical
caller for a folded constant. Its zero-argument constructor needs no readable
argument buffer; its private scratch is allocated and cleaned under host.stack.
It is not the missing universal recursive or native argument-preparation proof. -/
def seed (fail : Bool) : Primitives Nat :=
  { Semantic.Tests.callbacks Semantic.Tests.meaning 42 with
    insert := fun key slice _ before =>
      let (result, after) := OwnedCall.Tests.releaseSlice success 7 slice before
      (match result with
        | .error fault => .error fault
        | .ok () => if fail || key.kind != 2 || key.data != 42 then .error (.language .outOfMemory) else .ok 42, after) }

def constantChild (fail : Bool) : Find Nat := fun request before =>
  if request.arguments ≠ [] then (.error (.language .unsupported), before) else
  let mark := before.memory.memory.nextId
  match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok (_, memory) =>
    let (result, reached) := Caller.find success 160 7 (seed fail) Caller.Tests.queries ⟨0, 0, 0⟩ ⟨mark, 0, 2⟩ request
      { before with memory := { before.memory with memory } }
    let world := reached.world
    (result, if ordinary result then { world with memory := { world.memory with memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } } else world)

def wordReads (heap : Interner.Heap) : Nested.Reads where
  constant := fun id => .ok (heap.read id)
  operation := fun _ _ => .ok none

def nestedCaller (fail : Bool) := Caller.find success 160 7 (callbacks (seed fail) wordReads 64 (constantChild fail)) Caller.Tests.queries
  Semantic.Tests.source Semantic.Tests.buffer Semantic.Tests.request Semantic.Tests.world

theorem complete_nested_success : (nestedCaller false).1 = .ok 42 ∧
    (nestedCaller false).2.world.graph.read 42 = some 42 ∧ (nestedCaller false).2.world.memory.effects = 115 ∧
    (nestedCaller false).2.scope.lookup = none ∧ (nestedCaller false).2.scope.handedOff = true ∧
    (nestedCaller false).2.world.memory.memory.heap.map Prod.fst = Semantic.Tests.world.memory.memory.heap.map Prod.fst :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem complete_nested_failure : (nestedCaller true).1 = .error (.language .outOfMemory) ∧
    (nestedCaller true).2.world.memory.effects = 115 ∧ (nestedCaller true).2.scope = ⟨none, none, false⟩ ∧
    (nestedCaller true).2.world.memory.memory.heap.map Prod.fst = Semantic.Tests.world.memory.memory.heap.map Prod.fst :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Tests
