/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceProduction
import Compiler.Extraction.NormalizationHostTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge.HostScope
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray NormalizationOwnership.Trace

/-- Nest the existing recorders around the same physical adapter. Protocol
events include effect-free operations and stay separate from actual host calls.
The existing session retains both transcripts without another memory model. -/
def capture (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session (HostTrace.Recorded σ)) :=
  captured (HostTrace.record external) budget allocator commutative source buffer values exit before

/-- Erase both recorders to the original native result and exact reached
session. Ordinary OOM, semantic faults and incomplete preparation remain distinct;
neither a scope acceptance premise nor a completed-execution premise is used. -/
theorem erases (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session (HostTrace.Recorded σ)) :
    let execution := capture external budget allocator commutative source buffer values exit before
    let native := Normalization.run normalizationOwnershipCode external budget allocator commutative source buffer values exit
      (before.mapEffects HostTrace.Recorded.effects)
    (some native.1, native.2) =
      (ResourceAdapter.observe execution.1 execution.2.effects, execution.2.effects.session.mapEffects HostTrace.Recorded.effects) := by
  have same := capture_native (HostTrace.record external) budget allocator commutative source buffer values exit before
  have projected := congrArg (fun output : Option (Except Failure Outcome) × Session (HostTrace.Recorded σ) =>
    (output.1, output.2.mapEffects HostTrace.Recorded.effects)) same
  dsimp only
  rw [HostTrace.run_erases]
  exact projected.symm

/-- Bind accepted scoped ownership and word semantics to the original native
lifecycle, while retaining the actual recorded host execution. The cursor counts
protocol events, not host calls. This is one normalization lifecycle; recursive
graph operations interleaved between initialization, take and cleanup remain a
separate caller-level obligation. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (commutative : Bool) (source : View)
    (request : Interner.Request) (exit : NormalizationOwnership.Exit) (before : Session (HostTrace.Recorded σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (graph : Interner.Heap) (leading suffix : List (Event Failure))
    (scope : Except Interner.Error NormalizationOwnership.Outcome × Interner.Scoped.Session)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before) (represented : Represents before.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (start : graph.allocationCursor = leading.length)
    (accepted : checked (capture external budget allocator commutative source ⟨before.memory.nextId, 0, 2⟩ request.arguments exit
      { before with memory := memory }) leading suffix request exit graph = .ok scope) :
    let buffer : View := ⟨before.memory.nextId, 0, 2⟩
    let input : Session (HostTrace.Recorded σ) := { before with memory := memory }
    let execution := capture external budget allocator commutative source buffer request.arguments exit input
    let recorded := Normalization.run normalizationOwnershipCode (HostTrace.record external) budget allocator commutative source buffer
      request.arguments exit input
    let native := Normalization.run normalizationOwnershipCode external budget allocator commutative source buffer request.arguments exit
      (input.mapEffects HostTrace.Recorded.effects)
    ∃ protocol, execution.1 = .ok protocol ∧ Scope.observe scope = (some protocol, leading.length + execution.2.events.length) ∧
      recorded.2 = execution.2.effects.session ∧
      native = (recorded.1, execution.2.effects.session.mapEffects HostTrace.Recorded.effects) ∧
      (native.1 = .error .outOfMemory ∨ ∃ outcome, native.1 = .ok outcome) ∧
      Post (HostTrace.record external) budget allocator commutative source buffer request.arguments exit input recorded.1 recorded.2 ∧
      ((∀ id cell, before.memory.heap.lookup id = some cell → native.2.memory.heap.lookup id = some cell) ∧
       (∀ id block, before.heap id = some block → native.2.heap id = some block)) ∧
      (∀ slice, native.1 = .ok (.transferred slice) →
        scope.2.scope.items = slice.items ∧
        request.item.eval (Folding.wordMeaning other) read slice.items sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence) := by
  obtain ⟨protocol, result, observed, reached, ordinary, post, frame, words⟩ :=
    TraceBridge.production_verified (HostTrace.record external) budget allocator commutative source request exit before memory pointer
      graph leading suffix scope other read sequence valid represented allocated decoded (HostTrace.admitted external admitted) start accepted
  have erased := HostTrace.run_erases normalizationOwnershipCode external budget allocator commutative source
    ⟨before.memory.nextId, 0, 2⟩ request.arguments exit { before with memory := memory }
  dsimp only
  rw [erased]
  refine ⟨protocol, result, observed, reached, ?_, ordinary, post, frame, words⟩
  exact congrArg (fun session => (_, session.mapEffects HostTrace.Recorded.effects)) reached

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge.HostScope
