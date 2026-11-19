/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Read-only queries are kept explicit. The memory theorem covers every
returned observation; their semantic/native refinement remains a compiler
obligation, rather than a new host assumption. -/
structure Queries where
  atCapacity : Interner.Heap → Bool
  deterministic : Item → Except Interner.Error Bool
  validate : NodeId → Interner.Heap → Except Interner.Error Unit

def initLookup (external : External σ) (budget allocator : Nat) (source buffer : View)
    (request : Interner.Request) : Action σ (List NodeId) := fun before =>
  match Interner.Scoped.commutative request.item with
  | .error error => (.error (.language error), before)
  | .ok commutative =>
    let (result, memory) := init normalizationOwnershipCode external budget allocator commutative source buffer request.arguments before.world.memory
    let world := { before.world with memory }
    match result with
    | .error failure => (.error (memoryFault failure), { before with world })
    | .ok handle => (.ok handle.values, ⟨world, { lookup := some handle }⟩)

def execution (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (source buffer : View) : Interner.Execution (Action σ) :=
  { OwnedCall.execution external allocator p with
    normalize := initLookup external budget allocator source buffer
    atCapacity := q.atCapacity
    deterministic := q.deterministic }

def findBody (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (source buffer : View) (request : Interner.Request) : Action σ NodeId :=
  Interner.findCode.controlRun (execution external budget allocator p q source buffer) request

def forceBody (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (source buffer : View) (id : NodeId) (item : Item) (values : List NodeId) : Action σ Unit :=
  Interner.forceCode.controlRun (execution external budget allocator p q source buffer) q.validate id item values

/-- Both complete callers share exactly the same physical defer interpreter.
On semantic faults it retains the body state, including unfinished ownership. -/
def invoke (external : External σ) (allocator : Nat) (action : Action σ α) (before : World σ) : Except Fault α × State σ :=
  let (result, reached) := action ⟨before, { lookup := none }⟩
  finish external allocator result reached

def find (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (source buffer : View) (request : Interner.Request) (before : World σ) :=
  invoke external allocator (findBody external budget allocator p q source buffer request) before

def force (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (source buffer : View) (id : NodeId) (item : Item) (values : List NodeId) (before : World σ) :=
  invoke external allocator (forceBody external budget allocator p q source buffer id item values) before

theorem owned_execution (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (source buffer : View) (request : Interner.Request) (values : List NodeId) (deterministic : Bool) :
    Interner.findCode.controlOwned (execution external budget allocator p q source buffer) request values deterministic =
      body external allocator p request values deterministic := rfl

theorem force_owned_execution (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (source buffer : View) (request : Interner.Request) (values : List NodeId) (id : NodeId) :
    Interner.forceCode.controlOwned (execution external budget allocator p q source buffer) request values id =
      Interner.forceCode.controlOwned (OwnedCall.execution external allocator p) request values id := rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
