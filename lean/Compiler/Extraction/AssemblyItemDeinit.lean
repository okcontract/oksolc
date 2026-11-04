/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryContracts

namespace Compiler.Extraction.AssemblyItemDeinit
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

structure Bytes where
  address : Nat
  length : Nat
  offset : Nat := 0
  deriving DecidableEq, Repr

def byte : Compiler.ZigAir.Memory.Ty := .scalar (.int false 8)

/-- Complete owned byte extent at allocation start; free requires no initialized
contents. Projection from the native optional field remains a caller obligation.
This uses the same allocation registry as normalization. -/
def Owned (allocator : Nat) (slice : Bytes) (state : Session σ) : Prop :=
  slice.length = 0 ∨
    state.heap slice.address = some ⟨allocator, .bytes slice.length⟩ ∧
    ∃ cell, state.memory.heap.lookup slice.address = some cell ∧
      cell.type = .array slice.length byte ∧ cell.writable = true ∧ cell.stack = false ∧ slice.offset = 0

abbrev Release (σ : Type) := Bytes → Session σ → σ

/-- Check the nominal registry extent as well as the physical allocation.
Empty slices never inspect an arbitrary sentinel or invoke native free. -/
def free (external : Release (σ := σ)) (allocator : Nat) (slice : Bytes) (state : Session σ) :
    Except Arguments.ReleaseFault Unit × Session σ :=
  if slice.length = 0 then (.ok (), state) else
  if slice.offset ≠ 0 then (.error (.ownership .bounds), state) else
  let checked : Except Arguments.ReleaseFault (Heap × Compiler.ZigAir.Memory.State) := do
    let heap ← (Memory.release state.heap allocator slice.address).mapError Arguments.ReleaseFault.ownership
    let some allocation := state.heap slice.address | .error (.ownership .unallocated)
    let .bytes length := allocation.block | .error (.ownership .wrongType)
    if length ≠ slice.length then .error (.ownership .bounds) else
    let memory ← (Compiler.ZigAir.Memory.releaseOwned state.memory slice.address
      (.array slice.length byte)).mapError Arguments.ReleaseFault.memory
    .ok (heap, memory)
  match checked with
  | .error fault => (.error fault, state)
  | .ok (heap, memory) => (.ok (), ⟨heap, memory, external slice state⟩)

inductive Stage where
  | payload | invalidate
  deriving DecidableEq, Repr

structure State (σ : Type) where
  memory : Session σ
  invalidated : Bool := false

inductive Fault where
  | release (reason : Arguments.ReleaseFault)
  | invalidDescriptor
  deriving DecidableEq, Repr

/-- `undefined` invalidates the value; it does not release its allocation or
invent initialized bytes. Native struct field reads are not modeled here. -/
def Stage.execute (external : Release (σ := σ)) (allocator : Nat) (payload : Option Bytes)
    (stage : Stage) (before : State σ) : Except Fault Unit × State σ :=
  if before.invalidated then (.error .invalidDescriptor, before) else
  match stage with
  | .payload => match payload with
    | none => (.ok (), before)
    | some slice =>
      let (result, memory) := free external allocator slice before.memory
      (result.mapError Fault.release, { before with memory })
  | .invalidate => (.ok (), { before with invalidated := true })

def execute (external : Release (σ := σ)) (allocator : Nat) (payload : Option Bytes) :
    List Stage → State σ → Except Fault Unit × State σ
  | [], before => (.ok (), before)
  | stage :: rest, before =>
    let (result, reached) := stage.execute external allocator payload before
    match result with
    | .error fault => (.error fault, reached)
    | .ok () => execute external allocator payload rest reached

end Compiler.Extraction.AssemblyItemDeinit
