/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryLifetime
import Compiler.Extraction.StorageExecution

namespace Compiler.Extraction.ExpressionDeinit
open Compiler.Extraction.Storage Compiler.Extraction.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

inductive Stage where
  | itemValue | itemAllocation | arguments | invalidate
  deriving DecidableEq, Repr

/-- Descriptors of the existing representative; invalidation models the source
`self.* = undefined` boundary, not a store of invented initialized bytes. -/
structure Descriptor where
  item : Nat
  arguments : ArgumentSlice
  deriving DecidableEq, Repr

structure State (σ : Type) where
  memory : Session σ
  invalidated : Bool := false

inductive Fault (ε : Type) where
  | item (reason : ε)
  | arguments (reason : Failure)
  | invalidDescriptor
  deriving DecidableEq, Repr

/-- Framed compiler-operation interfaces, not new host assumptions. Item
destruction may inspect the reached session and change private effects. Native
item ownership, payload destruction, typed allocation death and separation
from argument/borrowed allocations still require implementation refinement. -/
structure Items (σ ε : Type) where
  deinit : Nat → Session σ → Except ε Unit × σ
  destroy : Nat → Session σ → Except ε Unit × σ

/-- Item operations may change the shared registry. Each implementation must
establish its own memory contract at the reached state. -/
structure Operations (σ ε : Type) where
  deinit : Nat → Session σ → Except ε Unit × Session σ
  destroy : Nat → Session σ → Except ε Unit × Session σ

/-- Preserve the original framed model as an explicit adapter. -/
def Items.operations (items : Items σ ε) : Operations σ ε where
  deinit id before :=
    let (result, effects) := items.deinit id before
    (result, { before with effects })
  destroy id before :=
    let (result, effects) := items.destroy id before
    (result, { before with effects })

def itemStep (action : Nat → Session σ → Except ε Unit × Session σ) (descriptor : Descriptor)
    (before : State σ) : Except (Fault ε) Unit × State σ :=
  let (result, reached) := action descriptor.item before.memory
  (result.mapError Fault.item, { before with memory := reached })

def Stage.execute (items : Operations σ ε) (external : External σ) (allocator : Nat)
    (descriptor : Descriptor) (stage : Stage) (before : State σ) : Except (Fault ε) Unit × State σ :=
  if before.invalidated then (.error .invalidDescriptor, before) else
  match stage with
  | .itemValue => itemStep items.deinit descriptor before
  | .itemAllocation => itemStep items.destroy descriptor before
  | .arguments =>
    let (result, memory) := free external allocator descriptor.arguments before.memory
    (result.mapError Fault.arguments, { before with memory })
  | .invalidate => (.ok (), { before with invalidated := true })

/-- One source-order traversal for both descriptor and native-field stages. A
rejected operation retains its reached state and stops; no later free or
descriptor invalidation is added. -/
@[simp] def executeStages (step : Stage → State σ → Except ε Unit × State σ) :
    List Stage → State σ → Except ε Unit × State σ
  | [], before => (.ok (), before)
  | stage :: rest, before =>
    let (result, reached) := step stage before
    match result with
    | .error fault => (.error fault, reached)
    | .ok () => executeStages step rest reached

theorem executeStages_rejected (step : Stage → State σ → Except ε Unit × State σ)
    (stage : Stage) (rest : List Stage) (before reached : State σ) (fault : ε)
    (called : step stage before = (.error fault, reached)) :
    executeStages step (stage :: rest) before = (.error fault, reached) := by
  simp only [executeStages, called]

theorem executeStages_advanced (step : Stage → State σ → Except ε Unit × State σ)
    (stage : Stage) (rest : List Stage) (before reached : State σ)
    (called : step stage before = (.ok (), reached)) :
    executeStages step (stage :: rest) before = executeStages step rest reached := by
  simp only [executeStages, called]

/-- Preserve the descriptor-based facade through the shared traversal. -/
def execute (items : Operations σ ε) (external : External σ) (allocator : Nat) (descriptor : Descriptor) :
    List Stage → State σ → Except (Fault ε) Unit × State σ :=
  executeStages (Stage.execute items external allocator descriptor)

end Compiler.Extraction.ExpressionDeinit
