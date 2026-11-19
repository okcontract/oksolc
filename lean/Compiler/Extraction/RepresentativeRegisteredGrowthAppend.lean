/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredAppend
import Compiler.Extraction.RepresentativeRegisteredCapacity

namespace Compiler.Extraction.RepresentativeArray.Append.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Both adapters retain the exact checked fault reason. Ownership failures are
embedded in the existing registry-fault branch, never turned into native OOM. -/
def growthFault : Backing.Release.Fault → Fault
  | .memory reason => .memory reason
  | .ownership reason => .registry reason

/-- Thread the existing registry alongside private effects at the common append
capacity boundary. This is only a Session adapter, not another heap or executor. -/
def growingCapacity (calls : Growth.Registered.Callbacks σ) (allocate : Backing.Registry.Allocate σ) (allocator : Nat)
    (state : State) (header : Address) (minimum : Nat) (context : Compiler.Extraction.Memory.Heap × σ) :
    (Except Fault (Option Unit) × State) × (Compiler.Extraction.Memory.Heap × σ) :=
  let (outcome, after) := Capacity.Registered.ensure calls allocate allocator header minimum ⟨context.1, state, context.2⟩
  ((outcome.mapError growthFault, after.memory), (after.heap, after.effects))

/-- The same owner/length/capacity/descriptor control now admits captured remap
execution. Native writes, registry allocation/death and private effects all
come from that execution, including partial rejection and ordinary OOM. -/
def runWithGrowth (calls : Growth.Registered.Callbacks σ) (runtimeSafety : Bool)
    (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell)
    (before : Session σ) : Except Fault Bool × Session σ :=
  let ((result, memory), context) := Execution.ownerWithCapacity (fun fault => .memory fault) (growingCapacity calls allocate allocator)
    runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length
    (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects)
  let reached : Session σ := ⟨context.1, memory, context.2⟩
  match result with
  | .error reason => (.error reason, reached)
  | .ok none => (.ok false, reached)
  | .ok (some ()) => finish allocator owner cells cell before reached reached.heap

/-- Registration never rewinds reached native memory or private effects. -/
theorem growth_reached (calls : Growth.Registered.Callbacks σ) (runtimeSafety : Bool)
    (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell)
    (before : Session σ) :
    let native := Execution.ownerWithCapacity (fun fault => (.memory fault : Fault)) (growingCapacity calls allocate allocator)
      runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length
      (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects)
    (runWithGrowth calls runtimeSafety allocate allocator owner cells cell before).2.memory = native.1.2 ∧
    (runWithGrowth calls runtimeSafety allocate allocator owner cells cell before).2.effects = native.2.2 := by
  dsimp only
  unfold runWithGrowth
  generalize Execution.ownerWithCapacity (fun fault => (.memory fault : Fault)) (growingCapacity calls allocate allocator)
    runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length
    (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects) = outcome
  rcases outcome with ⟨⟨result, memory⟩, heap, effects⟩
  cases result with
  | error reason => exact ⟨rfl, rfl⟩
  | ok value => cases value with
    | none => exact ⟨rfl, rfl⟩
    | some value => cases value; exact finish_reached allocator owner cells cell before _ heap

end Compiler.Extraction.RepresentativeArray.Append.Registered
