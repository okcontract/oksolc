/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolScope
import Compiler.Extraction.InternerCallerInitializedStream

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ResourceAdapter Interner.InvocationTrace

attribute [local irreducible] Initialization.capture

/-- One actual initializer supplies the recorded prefix for cache return,
classification failure and either take outcome. Readiness, the token and the
scoped state are derived before choosing later events; no completed caller or
cleanup equation is assumed. -/
theorem initialized_recorded (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source : View) (request : Interner.Request) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared : OwnedCall.State σ) (leading : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared)) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input := { before with memory := { before.memory with memory } }
    let init := Initialization.capture external budget allocator commutative source buffer request.arguments input.memory
    ∃ lookup, init.1 = .ok (some lookup) ∧
      let handle := init.2.effects.handle
      let entry : Recorded σ := ⟨prepared, { lookup := some lookup, items := handle.values },
        leading ++ init.2.events.map Event.normalization⟩
      prepared.scope = { lookup := some handle } ∧ lookup = token lookup.origin handle ∧ handle.values = values ∧
      Ready allocator source request.arguments handle prepared.world.memory ∧
      request.item.eval (Folding.wordMeaning other) read values sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
      record (Caller.initLookup external budget allocator source buffer request)
        (initialization external budget allocator source buffer request) ⟨⟨input, { lookup := none }⟩, {}, leading⟩ =
        (.ok values, entry) ∧
      ∀ suffix : List ProtocolEvent,
        Interner.Scoped.initScope (resources (entry.events ++ suffix) (.preparation .incomplete)) request
          ⟨{}, { before.graph with allocationCursor := leading.length }⟩ = (.ok values, scopeView entry) := by
  intro buffer input init
  obtain ⟨lookup, captured, state, contents, tokenEq, prefixProof⟩ := Initialization.successful_stream external budget allocator
    commutative source request before memory pointer values prepared (normalizations leading) other read sequence
    valid represented allocated decoded admitted initialized
  refine ⟨lookup, captured, ?_⟩
  intro handle entry
  have locals : prepared.scope = { lookup := some handle } := congrArg OwnedCall.State.scope state
  obtain ⟨nativeHandle, _, present, _, _, ready, _, word, _, _⟩ := (prefixProof []).2.2.2.2.2.2 values rfl
  have same : nativeHandle = handle := Option.some.inj (present.symm.trans (congrArg Local.lookup locals))
  subst nativeHandle
  change Caller.initLookup external budget allocator source buffer request ⟨input, { lookup := none }⟩ =
    (.ok values, prepared) at initialized
  change (Initialization.capture external budget allocator commutative source buffer request.arguments input.memory).1 =
    .ok (some lookup) at captured
  have normalized : record (Caller.initLookup external budget allocator source buffer request)
      (initialization external budget allocator source buffer request) ⟨⟨input, { lookup := none }⟩, {}, leading⟩ =
      (.ok values, entry) := by
    simp only [record, initialization, decoded, initialized, captured]
    rfl
  refine ⟨locals, tokenEq, contents, ready, ?_, normalized, ?_⟩
  · simpa only [contents] using word
  · intro suffix
    have scratch := caller_buffer before.memory memory pointer source request.arguments valid represented allocated
    have projected := initialization_projected external budget allocator commutative source buffer request input leading suffix
      other read sequence scratch.1 scratch.2.1 (scratch.2.2.1 commutative) rfl decoded admitted
      (by rw [initialized]; rfl)
    have known := projected.2.2.1
    rw [normalized] at known
    let logical := Interner.Scoped.initScope (resources (entry.events ++ suffix) (.preparation .incomplete)) request
      ⟨{}, { before.graph with allocationCursor := leading.length }⟩
    change (.ok values, scopeView entry) = (logical.1.mapError Fault.language, logical.2) at known
    have result : logical.1 = .ok values := by
      have same := congrArg Prod.fst known
      cases selected : logical.1 with
      | error error => rw [selected] at same; cases same
      | ok items => simpa only [selected, Except.mapError, Except.ok.injEq] using same.symm
    exact Prod.ext result (congrArg Prod.snd known).symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
