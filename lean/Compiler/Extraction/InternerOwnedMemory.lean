/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryLifetime
import Compiler.Extraction.InternerProgram

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache

/-- Graph callbacks borrow only shared state. The caller's normalization handle
and deferred-cleanup flag never become a recursive callee's local variables. -/
structure World (σ : Type) where
  graph : Interner.Heap
  memory : Session σ

inductive Fault where
  | language (error : Interner.Error)
  | memory (failure : Failure)
  | missingHandle
  | outsideOwnedContinuation
  deriving DecidableEq, Repr

def Fault.recoverable : Fault → Bool
  | .language .outOfMemory | .language .capacity | .language .invalidId | .language .assemblyException => true
  | _ => false

def ordinary : Except Fault α → Bool
  | .ok _ => true
  | .error fault => fault.recoverable

def memoryFault : Failure → Fault
  | .outOfMemory => .language .outOfMemory
  | failure => .memory failure

structure Local where
  lookup : Option Handle
  slice : Option ArgumentSlice := none
  handedOff : Bool := false
  deriving DecidableEq, Repr

structure State (σ : Type) where
  world : World σ
  scope : Local

abbrev Action (σ α : Type) := Effect (State σ) Fault α
abbrev GraphAction (σ α : Type) := Effect (World σ) Fault α

structure Primitives (σ : Type) where
  simplify : Key → ArgumentSlice → GraphAction σ (Option NodeId)
  publish : Key → ArgumentSlice → NodeId → GraphAction σ Unit
  insert : Key → ArgumentSlice → Bool → GraphAction σ NodeId

/-- The exact physical slice is available to its borrower/consumer. Every
callback sees the memory and allocator effects left by its predecessor. -/
def graph (action : ArgumentSlice → GraphAction σ α) : Action σ α := fun before =>
  match before.scope.slice with
  | none => (.error .missingHandle, before)
  | some slice =>
    let (result, world) := action slice before.world
    (result, { before with world })

def take (external : External σ) (allocator : Nat) : Action σ Unit := fun before =>
  match before.scope.lookup with
  | none => (.error .missingHandle, before)
  | some handle =>
    let (result, memory) := takeOwned normalizationOwnershipCode external allocator handle before.world.memory
    let world := { before.world with memory }
    match result with
    | .error failure => (.error (memoryFault failure), { before with world })
    | .ok (slice, remaining) =>
      (.ok (), ⟨world, ⟨some remaining, some slice, false⟩⟩)

def handoff : Action σ Unit := fun before =>
  (.ok (), { before with scope := { before.scope with handedOff := true } })

/-- The source-bound owned continuation uses only take, lift, graph calls and
handoff. Other entry points explicitly reject; initialization is supplied by
the already verified normalization operation before entering this continuation. -/
def execution (external : External σ) (allocator : Nat) (p : Primitives σ) : Interner.Execution (Action σ) where
  get := fun before => (.ok before.world.graph, before)
  lift := fun result before => (result.mapError Fault.language, before)
  atCapacity := fun _ => false
  normalize := fun _ before => (.error .outsideOwnedContinuation, before)
  deterministic := fun _ => .error .unsupported
  takeOwned := fun _ => take external allocator
  handoff := OwnedCall.handoff
  simplify := fun key => graph (p.simplify key)
  publish := fun key id => graph (fun slice => p.publish key slice id)
  insert := fun key deterministic => graph (fun slice => p.insert key slice deterministic)

def deinit (external : External σ) (allocator : Nat) : Action σ Unit := fun before =>
  match before.scope.lookup with
  | none => (.ok (), before)
  | some handle =>
    let (result, memory) := deinitialize normalizationOwnershipCode external allocator handle before.world.memory
    let reached := { before with world := { before.world with memory } }
    match result with
    | .error failure => (.error (memoryFault failure), reached)
    | .ok () => (.ok (), { reached with scope := { reached.scope with lookup := none } })

def cleanup (external : External σ) (allocator : Nat) : Action σ Unit := fun before =>
  if before.scope.handedOff then deinit external allocator before else
  match before.scope.slice with
  | none => deinit external allocator before
  | some slice =>
    let (result, memory) := free external allocator slice before.world.memory
    let reached := { before with world := { before.world with memory } }
    match result with
    | .error failure => (.error (memoryFault failure), reached)
    | .ok () => deinit external allocator { reached with scope := { reached.scope with slice := none } }

/-- Native defers run only for successful or recoverable outcomes, at the
callback's reached world. A semantic fault keeps that world and the local
descriptors, without inventing cleanup or rollback. -/
def finish (external : External σ) (allocator : Nat) (result : Except Fault α) (before : State σ) :
    Except Fault α × State σ :=
  if ordinary result then
    let (closed, after) := cleanup external allocator before
    match closed with
    | .error fault => (.error fault, after)
    | .ok () => (result, after)
  else (result, before)

def body (external : External σ) (allocator : Nat) (p : Primitives σ)
    (request : Interner.Request) (values : List NodeId) (deterministic : Bool) : Action σ NodeId :=
  Interner.findCode.controlOwned (execution external allocator p) request values deterministic

def run (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (deterministic : Bool) (handle : Handle) (before : World σ) : Except Fault NodeId × State σ :=
  let (result, after) := body external allocator p request handle.values deterministic ⟨before, { lookup := some handle }⟩
  finish external allocator result after

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
