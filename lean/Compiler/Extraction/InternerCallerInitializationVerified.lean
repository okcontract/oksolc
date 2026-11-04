/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitializationAdmission

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

/-- Live native/scoped observations needed by the intervening caller actions. -/
def Coupled (allocator : Nat) (source : View) (request : Interner.Request) (before : World σ)
    (cursor : Nat) (reached : Session σ) (called : Except Fault (List NodeId) × OwnedCall.State σ)
    (scope : Except Interner.Error (List NodeId) × Interner.Scoped.Session)
    (other : Meaning) (read : Read) (sequence : BitVec 32) : Prop :=
    called.1 = scope.1.mapError Fault.language ∧
    called.2.world.graph = before.graph ∧ called.2.world.memory = reached ∧
    scope.2.heap = { before.graph with allocationCursor := cursor } ∧
    Valid called.2.world.memory ∧
    (∀ values, called.1 = .ok values → ∃ handle lookup,
      called.2.scope.lookup = some handle ∧ scope.2.scope.lookup = some lookup ∧
      lookup = ResourceAdapter.token lookup.origin handle ∧
      Ready allocator source request.arguments handle called.2.world.memory ∧ handle.values = values ∧
      request.item.eval (Folding.wordMeaning other) read values sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
      called.2.scope = { lookup := some handle } ∧ scope.2.scope = ⟨some lookup, values, .lookup⟩)

/-- Checked live initialization couples the actual caller's ordinary result,
native ready handle and word meaning to its scoped token and exact resource
cursor. The graph observation changes only the cursor; native graph fields
remain unchanged. No completed-normalization postcondition is assumed. -/
theorem coupled (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (request : Interner.Request) (before : World σ) (leading suffix : List (Event Failure))
    (scope : Except Interner.Error (List NodeId) × Interner.Scoped.Session)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (bufferLength : buffer.length = 2) (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (admitted : Admitted external)
    (accepted : checked (capture external budget allocator commutative source buffer request.arguments before.memory)
      leading suffix request { before.graph with allocationCursor := leading.length } = .ok scope) :
    let execution := capture external budget allocator commutative source buffer request.arguments before.memory
    let called := Caller.initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩
    Coupled allocator source request before (leading.length + execution.2.events.length)
      execution.2.effects.session called scope other read sequence := by
  dsimp only [Coupled]
  let execution := capture external budget allocator commutative source buffer request.arguments before.memory
  have scopeShape := Scope.checked_init_scope _ _ _ _ _ (TraceBridge.check_physical_sound _ _ _ accepted).2
  obtain ⟨lookup, result, clean, scopedLookup, scopedResult, scopedGraph, _⟩ := checked_scope external budget allocator commutative
    source buffer request before.memory { before.graph with allocationCursor := leading.length } leading suffix scope
    represented.1 bufferLength decoded rfl accepted
  change execution.1 = .ok lookup at result
  change execution.2.effects.rejected = none at clean
  obtain ⟨nativeResult, nativeAfter, initialized, post⟩ := init_refines external budget allocator commutative source buffer
    request.arguments before.memory valid represented scratch admitted
  have spec := capture_spec external budget allocator commutative source buffer request.arguments before.memory
  dsimp only at spec
  rw [initialized] at spec
  have observation := congrArg Prod.fst spec.1
  have memory := congrArg Prod.snd spec.1
  change observeInit execution.1 execution.2.effects = some nativeResult at observation
  change execution.2.effects.session = nativeAfter at memory
  rw [← memory] at post
  have callRun := caller external budget allocator commutative source buffer request ⟨before, { lookup := none }⟩ decoded
  change (observeInit execution.1 execution.2.effects).map _ = _ at callRun
  rw [observation] at callRun
  have callState := (Option.some.inj callRun).symm
  cases lookup with
  | none =>
    have failed : nativeResult = .error .outOfMemory := by
      simpa only [result, observeInit, clean, Option.some.injEq] using observation.symm
    subst nativeResult
    dsimp only at callState
    simp only [callState, scopedResult, Except.mapError, memoryFault]
    refine ⟨True.intro, True.intro, True.intro, scopedGraph, post.2.2, ?_⟩
    intro values impossible
    cases impossible
  | some lookup =>
    have succeeded : nativeResult = .ok execution.2.effects.handle := by
      simpa only [result, observeInit, clean, Option.some.injEq] using observation.symm
    subst nativeResult
    change Ready allocator source request.arguments execution.2.effects.handle execution.2.effects.session ∧
      execution.2.effects.handle.values = normalized commutative source request.arguments at post
    have aligned := spec.2 lookup result
    dsimp only at callState
    simp only [callState, scopedResult, Except.mapError]
    refine ⟨congrArg Except.ok post.2, True.intro, True.intro, scopedGraph, post.1.valid, ?_⟩
    intro values returned
    cases Except.ok.inj returned
    refine ⟨execution.2.effects.handle, lookup, rfl, scopedLookup, aligned.2.2, post.1, rfl, ?_, rfl, ?_⟩
    · simpa only [post.2] using
        Compiler.Extraction.InsertionSort.normalize_word other request.item request.arguments _ read sequence
          (normalized_projection request.item commutative source request.arguments represented.1 decoded)
    · have contents : scope.2.scope.items = execution.2.effects.handle.values := by
        simpa only [scopedResult, Except.toOption, Option.getD_some, post.2] using scopeShape.1
      rw [← scopedLookup, ← contents, ← scopeShape.2]

/-- The actual caller stack allocation supplies scratch validity and separation;
clients provide the native allocation event, not a normalization invariant. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (commutative : Bool) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (leading suffix : List (Event Failure))
    (scope : Except Interner.Error (List NodeId) × Interner.Scoped.Session)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (accepted : checked (capture external budget allocator commutative source ⟨before.memory.memory.nextId, 0, 2⟩
      request.arguments { before.memory with memory }) leading suffix request
      { before.graph with allocationCursor := leading.length } = .ok scope) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input := { before with memory := { before.memory with memory } }
    let execution := capture external budget allocator commutative source buffer request.arguments input.memory
    let called := Caller.initLookup external budget allocator source buffer request ⟨input, { lookup := none }⟩
    Coupled allocator source request input (leading.length + execution.2.events.length)
      execution.2.effects.session called scope other read sequence := by
  have selected := caller_buffer before.memory memory pointer source request.arguments valid represented allocated
  exact coupled external budget allocator commutative source _ request _ leading suffix scope other read sequence
    selected.1 selected.2.1 (selected.2.2.1 commutative) rfl decoded admitted accepted

/-- Actual ordinary initialization derives checked admission before composing
native validity, ready ownership and word meaning. The existing stack producer
and coupling proof remain shared; no checked-result premise is required. -/
theorem production_ordinary (external : External σ) (budget allocator : Nat) (commutative : Bool) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (leading suffix : List (Event Failure))
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (completed : ordinary (Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩).1 = true) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input := { before with memory := { before.memory with memory } }
    let execution := capture external budget allocator commutative source buffer request.arguments input.memory
    let graph := { before.graph with allocationCursor := leading.length }
    let scope := Interner.Scoped.initScope
      (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) request ⟨{}, graph⟩
    let called := Caller.initLookup external budget allocator source buffer request ⟨input, { lookup := none }⟩
    checked execution leading suffix request graph = .ok scope ∧
      Coupled allocator source request input (leading.length + execution.2.events.length)
        execution.2.effects.session called scope other read sequence := by
  have accepted := checked_ordinary external budget allocator commutative source _ request
    { before with memory := { before.memory with memory } } leading suffix
    { before.graph with allocationCursor := leading.length } represented.1 rfl decoded completed rfl
  exact ⟨accepted, production_verified external budget allocator commutative source request before memory pointer
    leading suffix _ other read sequence valid represented allocated decoded admitted accepted⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
