/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublicationProofs
import Compiler.Extraction.OwnedKeysPhysicalFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Successful probing reaches the same source-bound key replacement used by
publication. Old-key release observes the actual probe effects. Empty keys
retain their sentinel, while nonempty replacement retires its old allocation. -/
theorem publish_success (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ)) (effects : σ)
    (valid : Valid before.memory) (input : Input allocator source key owned before)
    (live : SliceValid allocator before.memory.heap owned)
    (response : hostProbe key (forget before.memory) = (true, effects)) :
    ∃ after, publish hostProbe host allocator source key owned id before = commit key id before (.ok (), after) ∧
      OwnedKeys.Physical.Completed (external host) key ⟨owned.address, id⟩
        ⟨before.memory.effects.keys, { before.memory with effects := ⟨before.memory.effects.keys, effects⟩ }⟩ after ∧
      SliceValid allocator after.memory.heap owned := by
  have checked := OwnedKeys.Physical.run_local_spec (probe hostProbe) (external host) allocator key
    ⟨owned.address, id⟩ (physical before) valid input.live
  have succeeded : ∃ after,
      OwnedKeys.Physical.run (probe hostProbe) (external host) allocator key ⟨owned.address, id⟩ (physical before) = (.ok (), after) ∧
      OwnedKeys.Physical.Completed (external host) key ⟨owned.address, id⟩
        ⟨before.memory.effects.keys, { before.memory with effects := ⟨before.memory.effects.keys, effects⟩ }⟩ after := by
    simpa only [physical, probe, response, ↓reduceIte] using checked
  obtain ⟨after, ran, completed⟩ := succeeded
  refine ⟨after, ?_, completed, ?_⟩
  · rw [accepted_body hostProbe host allocator source key owned id before (admit_complete _ _ _ _ _ input)]
    exact congrArg (commit key id before) ran
  · have heap := congrArg OwnedKeys.State.memory completed.logical
    change after.memory.heap = OwnedKeys.retire ⟨before.memory.effects.keys, before.memory.heap⟩ key at heap
    rw [heap]
    exact OwnedKeys.retire_slice allocator _ key owned live (fun old found nonempty _ => input.incoming old found nonempty)

/-- The logical publication uses the very same probe decision as the physical
execution. Replacement and failed allocation retain their actual allocator
effects; only the result and graph are projected here. -/
theorem publish_projection (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ))
    (accepted : Bool) (effects : σ) (valid : Valid before.memory)
    (input : Input allocator source key owned before) (live : SliceValid allocator before.memory.heap owned)
    (response : hostProbe key (forget before.memory) = (accepted, effects)) :
    let ran := publish hostProbe host allocator source key owned id before
    let logical := Interner.publish accepted key id before.graph
    (ran.1, ran.2.graph) = (logical.1.mapError Fault.language, logical.2) := by
  cases accepted with
  | false =>
    rw [publish_oom hostProbe host allocator source key owned id before effects
      (admit_complete _ _ _ _ _ input) response]
    rfl
  | true =>
    obtain ⟨after, called, _, _⟩ := publish_success hostProbe host allocator source key owned id before effects
      valid input live response
    rw [called]
    rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
