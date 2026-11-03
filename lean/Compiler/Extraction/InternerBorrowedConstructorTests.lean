/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerBorrowedConstructor
import Compiler.Extraction.InternerConstructorFrameTests
import Compiler.Extraction.DispatchTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.BorrowedConstructor.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def temporary : Find σ := fun _ before => (.error (.language .unsupported), before)

def addressed (address : Nat) (nodes : List Dispatch.Tests.Probe) : Nested.Reads :=
  { Dispatch.Tests.reads nodes with operation := fun id opcode =>
    (Dispatch.Tests.reads nodes).operation id opcode |>.map (fun found => found.map (fun slice => ⟨address, slice.items⟩)) }

def traceWorld : World (List (View × Interner.Request)) :=
  ⟨Dispatch.Tests.empty, ⟨fun _ => none, ⟨[], 0, 4⟩, []⟩⟩

def record : Borrowed (List (View × Interner.Request)) := fun source request before =>
  (.ok 42, { before with memory := { before.memory with effects := before.memory.effects ++ [(source, request)] } })

def trace (address : Nat) (nodes : List Dispatch.Tests.Probe) (opcode : Opcode) (values : List NodeId) :=
  Dispatch.simplify (addressed address nodes) (constructors temporary record) 64 opcode values () traceWorld

def forwarded (ran : Except Fault (Option NodeId) × World (List (View × Interner.Request)))
    (address : Nat) (opcode : Opcode) (values : List NodeId) : Prop :=
  ran.1 = .ok (some 42) ∧ ran.2.memory.effects = [(⟨address, 0, values.length⟩, Interner.constructorCode.operationRequest opcode values)]

theorem byte_borrow (address : Nat) :
    forwarded (trace address [⟨none, some 26, [2, 3]⟩, ⟨some 255, none, []⟩, {}, {}] 22 [0, 1]) address 26 [2, 3] :=
  ⟨by rfl', by rfl'⟩

theorem comparison_borrows (address : Nat) :
    forwarded (trace address [⟨none, some 21, [1]⟩, ⟨none, some 20, [2, 3]⟩, {}, {}] 21 [0]) address 20 [2, 3] ∧
    forwarded (trace address [⟨none, some 21, [1]⟩, ⟨none, some 16, [2, 3]⟩, {}, {}] 21 [0]) address 16 [2, 3] ∧
    forwarded (trace address [⟨none, some 21, [1]⟩, ⟨none, some 18, [2, 3]⟩, {}, {}] 21 [0]) address 18 [2, 3] ∧
    forwarded (trace address [⟨none, some 21, [1]⟩, ⟨none, some 17, [2, 3]⟩, {}, {}] 21 [0]) address 17 [2, 3] ∧
    forwarded (trace address [⟨none, some 21, [1]⟩, ⟨none, some 19, [2, 3]⟩, {}, {}] 21 [0]) address 19 [2, 3] :=
  ⟨⟨by rfl', by rfl'⟩, ⟨by rfl', by rfl'⟩, ⟨by rfl', by rfl'⟩, ⟨by rfl', by rfl'⟩, ⟨by rfl', by rfl'⟩⟩

theorem arithmetic_borrows (address : Nat) :
    forwarded (trace address [⟨none, some 24, [1, 2]⟩, {}, {}] 21 [0]) address 20 [1, 2] ∧
    forwarded (trace address [⟨none, some 3, [1, 2]⟩, {}, {}] 21 [0]) address 20 [1, 2] :=
  ⟨⟨by rfl', by rfl'⟩, ⟨by rfl', by rfl'⟩⟩

theorem shift_mask_borrow (address : Nat) :
    forwarded (trace address [⟨some 1, none, []⟩, ⟨none, some 28, [2, 3]⟩, ⟨some 255, none, []⟩, {}] 22 [0, 1]) address 28 [2, 3] :=
  ⟨by rfl', by rfl'⟩

def world : World Nat := { Semantic.Tests.caller with graph := { Semantic.Tests.wordGraph with
  read := fun id => if id = 42 then some 0 else if id = 0 then some 42 else Semantic.Tests.wordGraph.read id } }

def child (known : NodeId) (budget : Nat) : GraphAction Nat NodeId :=
  (constructors temporary (caller success budget 7 (Semantic.Tests.callbacks Semantic.Tests.meaning known) Caller.Tests.queries)).borrowedOperation
    0 20 [3, 1] ()

def run (known : NodeId) (budget : Nat := 160) :=
  Dispatch.simplify (addressed 0 [⟨none, some 24, [3, 1]⟩])
    (constructors temporary (caller success budget 7 (Semantic.Tests.callbacks Semantic.Tests.meaning known) Caller.Tests.queries))
    64 21 [0] () world

theorem dispatch_reaches_child (known : NodeId) (budget : Nat) :
    run known budget = let ran := child known budget world; (ran.1.map some, ran.2) := by
  change (Dispatch.orNext (pure none) <| Dispatch.orNext (pure none) <|
    Dispatch.orNext (do let id ← child known budget; pure (some id)) (pure none)) world = _
  cases executed : child known budget world with
  | mk result after =>
    cases result <;> simp only [Dispatch.orNext, bind, Effect.bind, pure, Effect.pure, executed, Except.map]

theorem production_success : (run 42).1 = .ok (some 42) ∧ (run 42).2.graph.read 42 = some 0 ∧
    (run 42).2.memory.effects = 225 ∧ (run 42).2.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem production_failure : (run 1).1 = .error (.language .outOfMemory) ∧
    (run 1).2.memory.effects = 225 ∧ (run 1).2.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem production_semantic_fault : (run 42 0).1 = .error (.memory (.preparation .incomplete)) ∧
    ((run 42 0).2.memory.memory.heap.lookup 3).isSome = true := ⟨by rfl', by rfl'⟩

theorem contract (known : NodeId) (budget : Nat) :
    let ran := child known budget world
    ordinary ran.1 = true → Good ⟨0, 0, 2⟩ [3, 1] ran.2 ∧
      Closed (ConstructorFrame.operation success budget 7 (Semantic.Tests.callbacks Semantic.Tests.meaning known) Caller.Tests.queries
        ⟨0, 0, 2⟩ 20 [3, 1] world).2.scope ∧
      Semantic.Ensures Semantic.Tests.meaning world.graph ran.1 ran.2.graph (fun id after => after.read id = some 0) :=
  operation_verified temporary success budget 7 (Semantic.Tests.callbacks Semantic.Tests.meaning known) Caller.Tests.queries
    0 20 [3, 1] () world Compiler.Extraction.Recursive.Tests.base 0
    ⟨original_valid, Semantic.Tests.source_represented⟩ (external_admitted _)
    (Semantic.Tests.ownership _ _ _ _) (Semantic.Tests.semantics _ _ _ _)
    ⟨(by intro _ _ impossible; cases impossible), trivial⟩ (by rfl')

theorem dispatcher_restores_good (known : NodeId) (budget : Nat) :
    ordinary (run known budget).1 = true → Good ⟨0, 0, 2⟩ [3, 1] (run known budget).2 := by
  rw [dispatch_reaches_child]
  have checked := contract known budget
  cases executed : child known budget world with
  | mk result after =>
    rw [executed] at checked
    cases result <;> exact fun completed => (checked completed).1

theorem success_restores_good : Good ⟨0, 0, 2⟩ [3, 1] (run 42).2 :=
  dispatcher_restores_good 42 160 (by rw [production_success.1]; rfl)

theorem failure_restores_good : Good ⟨0, 0, 2⟩ [3, 1] (run 1).2 :=
  dispatcher_restores_good 1 160 (by rw [production_failure.1]; rfl)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.BorrowedConstructor.Tests
