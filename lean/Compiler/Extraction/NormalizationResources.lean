/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemory
import Compiler.Extraction.NormalizationPrepared

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

inductive Rejection where
  | memory (failure : Failure)
  | missingSlice
  deriving DecidableEq, Repr

/-- Invocation-local descriptors around the existing memory session. The
ownership interpreter supplies the logical token; a remembered owned slice
remains available after its effect-free transfer. This is no additional heap. -/
structure State (σ : Type) where
  session : Session σ
  handle : Handle
  transferred : Option ArgumentSlice := none
  rejected : Option Rejection := none

def initial (source : View) (values : List NodeId) (before : Session σ) : State σ :=
  ⟨before, ⟨source, values, none⟩, none, none⟩

def outputSlice (before : State σ) : Option ArgumentSlice :=
  match before.transferred with
  | some slice => some slice
  | none => before.handle.owned

/-- Ordinary OOM is the ownership interpreter's false result. Semantic
failures remain a separate, absorbing rejection with their reached state. -/
def failed (failure : Failure) (memory : Session σ) (before : State σ) : Bool × State σ :=
  (false, { before with session := memory, rejected := if failure = .outOfMemory then none else some (.memory failure) })

def allocate (external : External σ) (allocator : Nat) (values : List NodeId)
    (site : NormalizationOwnership.Allocation) (before : State σ) : Bool × State σ :=
  if before.rejected.isSome then (false, before) else
  match site with
  | .temporary =>
    let (result, memory) := Normalization.reserve external allocator values before.session
    match result with
    | .error failure => failed failure memory before
    | .ok slice => (true, { before with session := memory, handle := ⟨view slice, values, some slice⟩ })
  | .duplicate =>
    let (result, memory) := Normalization.takeOwned normalizationOwnershipCode external allocator before.handle before.session
    match result with
    | .error failure => failed failure memory before
    | .ok (slice, remaining) => (true, { before with session := memory, handle := remaining, transferred := some slice })

def prepare (budget allocator : Nat) (source buffer : View) (values : List NodeId)
    (lookup : NormalizationOwnership.State) (before : State σ) : Except Failure Unit × State σ :=
  let target := if lookup.origin = .scratch then bufferPrefix buffer source.length else before.handle.items
  let (result, memory) := Normalization.prepare normalizationOwnershipCode budget allocator buffer.length source target values
    (lookup.origin == .allocation) before.session
  match result with
  | .error failure => (.error failure, { before with session := memory })
  | .ok handle => (.ok (), { before with session := memory, handle := handle })

/-- The callback observes the owner before its move/invalidation. Remembered
descriptors are never freed twice: dispatch is controlled by the source-bound
ownership interpreter, and a semantic failure stops further memory effects. -/
def release (external : External σ) (allocator : Nat) (lookup : NormalizationOwnership.State)
    (before : State σ) : State σ :=
  if before.rejected.isSome then before else
  let slice := if lookup.owner = .lookup then before.handle.owned else
    if lookup.owner = .caller then outputSlice before else none
  match slice with
  | none => { before with rejected := some .missingSlice }
  | some slice =>
    let (result, memory) := Normalization.free external allocator slice before.session
    { before with session := memory, rejected := match result with
      | .ok () => none
      | .error failure => some (.memory failure) }

def primitives (external : External σ) (budget allocator : Nat) (source buffer : View) (values : List NodeId) :
    NormalizationOwnership.PreparedPrimitives (State σ) Failure := {
  allocate := allocate external allocator values
  release := release external allocator
  prepare := prepare budget allocator source buffer values }

/-- A missing descriptor rejects the adapter; it cannot manufacture an OOM or
successful artifact. Native semantic failures keep their exact classification.
The equality theorem below will exclude missing descriptors for full runs. -/
def observe (result : NormalizationOwnership.PreparedResult Failure) (after : State σ) : Option (Except Failure Outcome) :=
  match after.rejected with
  | some (.memory failure) => some (.error failure)
  | some .missingSlice => none
  | none =>
    match result with
    | .error (failure, _) => some (.error failure)
    | .ok (.allocationFailure, _) => some (.error .outOfMemory)
    | .ok (.lookup, _) => some (.ok .lookup)
    | .ok (.cleaned, _) => some (.ok .cleaned)
    | .ok (.transferred, _) => (outputSlice after).map (fun slice => .ok (.transferred slice))

def run (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ) : Option (Except Failure Outcome) × Session σ :=
  let (result, after) := normalizationOwnershipCode.runPrepared commutative source.length buffer.length
    (primitives external budget allocator source buffer values) exit (initial source values before)
  (observe result after, after.session)

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
