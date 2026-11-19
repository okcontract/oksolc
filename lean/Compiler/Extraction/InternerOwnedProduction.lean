/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedProofs
import Compiler.Extraction.NormalizationMemoryCaller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Compose actual normalization with the owned continuation selected by a
caller. Cache-hit/capacity routing and recursive graph implementation are not
certified by selecting this entry point. Initialization faults retain memory. -/
def entry (external : External σ) (budget allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (commutative deterministic : Bool) (source buffer : View) (before : World σ) : Except Fault NodeId × State σ :=
  let (result, memory) := init normalizationOwnershipCode external budget allocator commutative source buffer request.arguments before.memory
  let world := { before with memory }
  match result with
  | .error failure => (.error (memoryFault failure), ⟨world, { lookup := none }⟩)
  | .ok handle => run external allocator p request deterministic handle world

theorem entry_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (commutative deterministic : Bool) (source buffer : View) (before : World σ)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (contracts : Contracts allocator source request.arguments p) :
    (∀ handle memory, init normalizationOwnershipCode external budget allocator commutative source buffer request.arguments before.memory =
      (.ok handle, memory) → handle.values = normalized commutative source request.arguments) ∧
    (ordinary (entry external budget allocator p request commutative deterministic source buffer before).1 = true →
      Good source request.arguments (entry external budget allocator p request commutative deterministic source buffer before).2.world ∧
      Closed (entry external budget allocator p request commutative deterministic source buffer before).2.scope) := by
  obtain ⟨result, memory, initialized, post⟩ := init_refines external budget allocator commutative source buffer request.arguments
    before.memory valid represented scratch admitted
  constructor
  · intro handle after ran
    rw [initialized] at ran
    cases ran
    exact post.2
  · simp only [entry, initialized]
    cases result with
    | error failure =>
      cases failure with
      | outOfMemory =>
        intro _
        exact ⟨⟨post.2.2, by simpa only [post.2.1] using represented⟩, rfl, Or.inr rfl⟩
      | preparation => simp [ordinary, memoryFault, Fault.recoverable]
      | allocation | release => exact False.elim post
    | ok handle =>
      have checked := run_verified external allocator p request deterministic handle source request.arguments
        { before with memory } post.1 admitted contracts
      intro completed
      have ordinaryBody : ordinary (body external allocator p request handle.values deterministic
          ⟨{ before with memory }, { lookup := some handle }⟩).1 = true := by
        rw [← checked.1]
        exact completed
      exact ⟨(checked.2.2 ordinaryBody).1, (checked.2.2 ordinaryBody).2.1⟩

/-- Production caller scratch is derived from its fresh two-word allocation.
The theorem composes allocation/copy/sort with actual source-bound owned control,
graph interleaving and deferred cleanup under the named graph obligations. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (commutative deterministic : Bool) (source : View) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (admitted : Admitted external) (contracts : Contracts allocator source request.arguments p) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World σ := { before with memory := { before.memory with memory } }
    (∀ handle reached, init normalizationOwnershipCode external budget allocator commutative source buffer request.arguments input.memory =
      (.ok handle, reached) → handle.values = normalized commutative source request.arguments ∧
        normalizeCode.run Compiler.Extraction.InsertionSort.sortIds request.item request.arguments = some handle.values) ∧
    (ordinary (entry external budget allocator p request commutative deterministic source buffer input).1 = true →
      Good source request.arguments (entry external budget allocator p request commutative deterministic source buffer input).2.world ∧
      Closed (entry external budget allocator p request commutative deterministic source buffer input).2.scope) := by
  obtain ⟨selected, sourceKept, scratch, _⟩ := caller_buffer before.memory memory pointer source request.arguments valid represented allocated
  have checked := entry_verified external budget allocator p request commutative deterministic source
    ⟨before.memory.memory.nextId, 0, 2⟩ { before with memory := { before.memory with memory } } selected sourceKept
    (scratch commutative) admitted contracts
  refine ⟨?_, checked.2⟩
  intro handle reached initialized
  have contents := checked.1 handle reached initialized
  exact ⟨contents, by rw [contents]; exact normalized_projection request.item commutative source request.arguments represented.1 decoded⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
