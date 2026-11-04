/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitializationVerified

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ResourceAdapter NormalizationOwnership.Trace

/-- One successful source initialization supplies its actual handle and token
before selecting a later take or cache-cleanup suffix. Admission, native
readiness and the exact scoped cursor reuse the ordinary initialization proof. -/
theorem successful_stream (external : External σ) (budget allocator : Nat) (commutative : Bool) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : OwnedCall.State σ)
    (leading : List (Event Failure)) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared)) :
    let input := { before with memory := { before.memory with memory } }
    let execution := capture external budget allocator commutative source ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments input.memory
    ∃ lookup, execution.1 = .ok (some lookup) ∧
      prepared = ⟨⟨before.graph, execution.2.effects.session⟩, { lookup := some execution.2.effects.handle }⟩ ∧
      execution.2.effects.handle.values = values ∧ lookup = token lookup.origin execution.2.effects.handle ∧
      ∀ suffix,
        let scope := Interner.Scoped.initScope
          (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) request
          ⟨{}, { before.graph with allocationCursor := leading.length }⟩
        checked execution leading suffix request { before.graph with allocationCursor := leading.length } = .ok scope ∧
        Coupled allocator source request input (leading.length + execution.2.events.length)
          execution.2.effects.session (.ok values, prepared) scope other read sequence := by
  intro input execution
  obtain ⟨lookup, captured, state, contents, tokenEq⟩ := capture_success external budget allocator commutative
    source ⟨before.memory.memory.nextId, 0, 2⟩ request input values prepared decoded initialized
  refine ⟨lookup, captured, state, contents, tokenEq, ?_⟩
  intro suffix
  have completed : ordinary (Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨input, { lookup := none }⟩).1 = true := by rw [initialized]; rfl
  have proved := production_ordinary external budget allocator commutative source request before memory pointer
    leading suffix other read sequence valid represented allocated decoded admitted completed
  simpa only [initialized] using proved

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
