/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.CacheProgram
import Compiler.Extraction.ArgumentMemoryDuplication
import Compiler.Extraction.InsertionSortCopied

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

/-- The existing logical registry, typed heap and external allocator state.
No heap is reconstructed from a successful result or discarded on failure. -/
structure Session (σ : Type) where
  heap : Memory.Heap
  memory : Compiler.ZigAir.Memory.State
  effects : σ

/-- `values` is the logical descriptor used by the existing argument-memory
relation. The other fields model the production items/owned slices. -/
structure Handle where
  items : View
  values : List NodeId
  owned : Option ArgumentSlice
  deriving DecidableEq, Repr

/-- External operations can inspect the actual reached state. Free effects run
only after the checked whole-allocation release is admitted; empty free skips
the callback, as does an owned transfer. Native implementations are trusted
under the versioned contracts, not assumed to verify normalization itself. -/
structure External (σ : Type) where
  allocate : NormalizationOwnership.Allocation → Session σ → Compiler.ZigAir.Memory.WordAllocation.Allocator σ
  free : ArgumentSlice → Session σ → σ

inductive Failure where
  | outOfMemory
  | allocation (fault : Allocation.Fault)
  | preparation (fault : InsertionSort.Heap.Fault)
  | release (fault : ReleaseFault)
  deriving DecidableEq, Repr

abbrev Step (σ α : Type) := Except Failure α × Session σ

def bufferPrefix (buffer : View) (length : Nat) : View := { buffer with length := length }

def reserve (external : External σ) (allocator : Nat) (values : List NodeId) (before : Session σ) : Step σ ArgumentSlice :=
  let ((result, heap, memory), effects) := Allocation.reserve before.heap before.memory allocator values
    (external.allocate .temporary before) before.effects
  let after := { before with heap := heap, memory := memory, effects := effects }
  match result with
  | .error fault => (.error (.allocation fault), after)
  | .ok none => (.error .outOfMemory, after)
  | .ok (some slice) => (.ok slice, after)

/-- Preparation uses the exact existing typed copy/captured sort. Registry
publication is a ghost update for an allocated destination, performed only on
success. A suspended or faulting preparation retains its provisional registry
and actual partial writes, without inventing native cleanup. -/
def prepare (code : NormalizationOwnership.Code) (budget allocator bufferLength : Nat) (source target : View)
    (values : List NodeId) (allocated : Bool) (before : Session σ) : Step σ Handle :=
  let (result, memory) := Copied.run budget before.memory source target
  let reached := { before with memory := memory }
  match result with
  | .error fault => (.error (.preparation fault), reached)
  | .ok () =>
    let sorted := sortIds values
    let slice : ArgumentSlice := ⟨target.allocation, sorted⟩
    let after := if allocated then { reached with heap := write before.heap target.allocation (some ⟨allocator, .arguments sorted⟩) } else reached
    (.ok ⟨target, sorted, if code.ownTemporary.test source.length bufferLength then some slice else none⟩, after)

def init (code : NormalizationOwnership.Code) (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (values : List NodeId) (before : Session σ) : Step σ Handle :=
  if !commutative || decide (source.length < code.threshold) then
    (.ok ⟨source, values, none⟩, before)
  else if code.useScratch.test source.length buffer.length then
    prepare code budget allocator buffer.length source (bufferPrefix buffer source.length) values false before
  else
    let (result, allocated) := reserve external allocator values before
    match result with
    | .error fault => (.error fault, allocated)
    | .ok slice => prepare code budget allocator buffer.length source (view slice) values true allocated

def takeOwned (code : NormalizationOwnership.Code) (external : External σ) (allocator : Nat)
    (handle : Handle) (before : Session σ) : Step σ (ArgumentSlice × Handle) :=
  match handle.owned with
  | some owned => (.ok (owned, { handle with owned := if code.clearOnTake then none else handle.owned }), before)
  | none =>
    let ((result, heap, memory), effects) := Duplication.run before.heap before.memory allocator handle.items handle.values
      (external.allocate .duplicate before) before.effects
    let after := { before with heap := heap, memory := memory, effects := effects }
    match result with
    | .error fault => (.error (.allocation fault), after)
    | .ok none => (.error .outOfMemory, after)
    | .ok (some slice) => (.ok (slice, handle), after)

def free (external : External σ) (allocator : Nat) (slice : ArgumentSlice) (before : Session σ) : Step σ Unit :=
  match Arguments.release before.heap before.memory allocator slice with
  | .error fault => (.error (.release fault), before)
  | .ok (heap, memory) =>
    (.ok (), ⟨heap, memory, if slice.items.isEmpty then before.effects else external.free slice before⟩)

theorem free_empty (external : External σ) (allocator : Nat) (slice : ArgumentSlice) (before : Session σ)
    (empty : slice.items = []) : free external allocator slice before = (.ok (), before) := by
  cases slice with
  | mk address items => cases empty; rfl

/-- There is no live returned handle after deinit. Reusing a native handle
after `self.* = undefined` is outside the admitted calling discipline. -/
def deinitialize (code : NormalizationOwnership.Code) (external : External σ) (allocator : Nat)
    (handle : Handle) (before : Session σ) : Step σ Unit :=
  match handle.owned with
  | some owned => if code.freeOnDeinit then free external allocator owned before else (.ok (), before)
  | none => (.ok (), before)

inductive Outcome where
  | lookup
  | transferred (slice : ArgumentSlice)
  | cleaned
  deriving DecidableEq, Repr

def close (code : NormalizationOwnership.Code) (external : External σ) (allocator : Nat) (handle : Handle)
    (result : Except Failure Outcome) (before : Session σ) : Step σ Outcome :=
  let (closed, after) := deinitialize code external allocator handle before
  match closed with
  | .error fault => (.error fault, after)
  | .ok () => (result, after)

/-- Native deferred cleanup runs on ordinary OOM and normal exits. A semantic
contract fault or incomplete observation stops at its exact reached state;
it is not a recoverable Zig error and authorizes no invented rollback. -/
def continueWith (code : NormalizationOwnership.Code) (external : External σ) (allocator : Nat)
    (exit : NormalizationOwnership.Exit) (handle : Handle) (before : Session σ) : Step σ Outcome :=
  match exit with
  | .lookup => close code external allocator handle (.ok .lookup) before
  | .transfer | .cleanup =>
    let (taken, reached) := takeOwned code external allocator handle before
    match taken with
    | .error .outOfMemory => close code external allocator handle (.error .outOfMemory) reached
    | .error fault => (.error fault, reached)
    | .ok (slice, remaining) =>
      match exit with
      | .cleanup =>
        let (released, after) := free external allocator slice reached
        match released with
        | .error fault => (.error fault, after)
        | .ok () => close code external allocator remaining (.ok .cleaned) after
      | _ => close code external allocator remaining (.ok (.transferred slice)) reached

/-- Full normalization lifecycle using the source-bound Code, existing checked
memory operations and actual reached external effects. -/
def run (code : NormalizationOwnership.Code) (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ) : Step σ Outcome :=
  let (initialized, prepared) := init code external budget allocator commutative source buffer values before
  match initialized with
  | .error fault => (.error fault, prepared)
  | .ok handle => continueWith code external allocator exit handle prepared

end Compiler.Extraction.Memory.Arguments.Normalization
