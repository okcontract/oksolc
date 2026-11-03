/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInit

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- A successful actual initializer has already checked the optional opcode
used by makeKey. Derive key existence for any selected values and sequence. -/
theorem initialized_key (external : External σ) (budget allocator : Nat) (source buffer : View)
    (request : Interner.Request) (before prepared : State σ) (values : List NodeId)
    (initialized : initLookup external budget allocator source buffer request before = (.ok values, prepared)) :
    ∃ key, Interner.makeKey request values = .ok key := by
  unfold initLookup at initialized
  cases decoded : Interner.Scoped.commutative request.item with
  | error error => rw [decoded] at initialized; cases initialized
  | ok commutative =>
    unfold Interner.Scoped.commutative at decoded
    by_cases operation : request.item.kind = 1#32
    · cases instruction : request.item.instruction with
      | none => simp [normalizeCode, Test.run, operation, instruction] at decoded
      | some opcode =>
        exact ⟨⟨1, opcode, 0, values, request.sequence⟩,
          by simp [Interner.makeKey, KeyCode.run, keyCode, Test.run, Scalar.run, operation, instruction]⟩
    · exact ⟨⟨request.item.kind, 0, request.item.data, values, request.sequence⟩,
        by simp [Interner.makeKey, KeyCode.run, keyCode, Test.run, Scalar.run, operation]⟩

/-- Decompose the actual initialized prefix once. Key construction is total
here; deterministic lookup and the untouched owned continuation share that key. -/
theorem find_initialized (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (values : List NodeId) (prepared : State σ)
    (room : q.atCapacity before.graph = false)
    (initialized : initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ = (.ok values, prepared)) :
    ∃ key, Interner.makeKey request values = .ok key ∧
      find external budget allocator p q source buffer request before =
        match q.deterministic request.item with
        | .error error => finish external allocator (.error (.language error) : Except Fault NodeId) prepared
        | .ok deterministic =>
          match if deterministic then before.graph.table key else none with
          | some id => finish external allocator (.ok id) prepared
          | none =>
            let ran := Interner.findCode.controlOwned (execution external budget allocator p q source buffer) request values deterministic prepared
            finish external allocator ran.1 ran.2 := by
  obtain ⟨key, keyed⟩ := initialized_key external budget allocator source buffer request _ prepared values initialized
  refine ⟨key, keyed, ?_⟩
  unfold find invoke findBody Interner.FindCode.controlRun
  simp only [execution, OwnedCall.execution, bind, Effect.bind, room, Bool.false_eq_true, ↓reduceIte, initialized]
  cases classified : q.deterministic request.item with
  | error error => rfl
  | ok deterministic =>
    cases deterministic with
    | false => rfl
    | true =>
      simp only [Except.mapError, ↓reduceIte, keyed, Effect.bind]
      cases before.graph.table key <;> rfl

theorem find_classification_failed (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (values : List NodeId) (prepared : State σ) (error : Interner.Error)
    (room : q.atCapacity before.graph = false)
    (initialized : initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .error error) :
    find external budget allocator p q source buffer request before =
      finish external allocator (.error (.language error) : Except Fault NodeId) prepared := by
  obtain ⟨_, _, routed⟩ := find_initialized external budget allocator p q source buffer request before values prepared room initialized
  simpa only [classified] using routed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
