/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolMissReplay
import Compiler.Extraction.InternerCallerTakenStream
import Compiler.Extraction.InternerCallerProtocolPrefix

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Interner.InvocationTrace

attribute [local irreducible] Initialization.capture Take.capture

/-- The existing admitted initialization/take prefix supplies the actual
recorded entry to a miss. Its handle, token, values and cursor are computed;
the later suffix shares the same scoped resource stream. -/
theorem initialized_taken_recorded (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source : View) (request : Interner.Request) (before : World σ)
    (stack : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared called : OwnedCall.State σ)
    (leading : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, stack))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take external allocator prepared = (.ok (), called)) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let start := { before with memory := { before.memory with memory := stack } }
    let init := Initialization.capture external budget allocator commutative source buffer request.arguments start.memory
    ∃ lookup, init.1 = .ok (some lookup) ∧
      let handle := init.2.effects.handle
      let taken := Take.capture external allocator lookup.origin handle prepared.world.memory
      let missLeading := leading ++ init.2.events.map Event.normalization ++ taken.2.events.map Event.normalization
      ∃ slice remaining, called.scope = ⟨some remaining, some slice, false⟩ ∧
        Normalization.Taken allocator source request.arguments handle prepared.world.memory slice remaining called.world.memory ∧
        slice.items = values ∧ taken.1.2.owned = false ∧ taken.1.2.owner = .caller ∧
        request.item.eval (Folding.wordMeaning other) read values sequence =
          request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
        let input : Recorded σ := ⟨⟨start, { lookup := none }⟩, {}, leading⟩
        let normalized := record (Caller.initLookup external budget allocator source buffer request)
          (initialization external budget allocator source buffer request) input
        let entry : Recorded σ := ⟨called, { lookup := some taken.1.2, items := remaining.values, phase := .cleanup }, missLeading⟩
        normalized.1 = .ok values ∧
        record (OwnedCall.take external allocator) (taking external allocator) normalized.2 = (.ok (), entry) ∧
        ∀ suffix : List ProtocolEvent,
          let r := resources (missLeading ++ suffix) (.preparation .incomplete)
          let initialScope := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
          let takeScope := Interner.Scoped.take r initialScope.2
          initialScope.1 = .ok values ∧ takeScope.1 = .ok () ∧ takeScope.2 = scopeView entry := by
  intro buffer start init
  obtain ⟨lookup, captured, prefixProof⟩ := Take.initialized_taken_stream external budget allocator commutative source request
    before stack pointer values prepared called leading other read sequence valid represented allocated decoded admitted initialized transferred
  refine ⟨lookup, captured, ?_⟩
  intro handle taken missLeading
  obtain ⟨slice, remaining, locals, lifetime, contents, unowned, caller, word, prefixProof⟩ := prefixProof
  refine ⟨slice, remaining, locals, lifetime, lifetime.values.trans contents, unowned, caller, word, ?_⟩
  intro input normalized entry
  obtain ⟨actualLookup, actualCapture, state, _, _, _, _, normalizedState, _⟩ := initialized_recorded external budget allocator
    commutative source request before stack pointer values prepared leading other read sequence
    valid represented allocated decoded admitted initialized
  have same := Option.some.inj (Except.ok.inj (actualCapture.symm.trans captured))
  subst actualLookup
  have present : prepared.scope.lookup = some handle := congrArg Local.lookup state
  change normalized = (.ok values, ⟨prepared, { lookup := some lookup, items := handle.values },
      leading ++ init.2.events.map Event.normalization⟩) at normalizedState
  refine ⟨congrArg Prod.fst normalizedState, ?_, ?_⟩
  · have succeeded := (prefixProof []).2.1
    change (Take.capture external allocator lookup.origin handle prepared.world.memory).1.1 = true at succeeded
    simp only [normalizedState, record, transferred, taking, present, succeeded, ↓reduceIte]
    rw [← lifetime.sameValues]
  · intro suffix r initialScope takeScope
    obtain ⟨initialResult, _, _, _, takeResult, shape⟩ := prefixProof suffix
    exact ⟨initialResult, takeResult, shape⟩

/-- Route the actual source caller through normalization and either take
outcome; only successful take reaches the miss. The cache guard reads the original graph and is conditional
on determinism, exactly as in the source control. -/
theorem findBody_after_take (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (values : List NodeId)
    (before prepared called : Recorded σ) (result : Except Fault Unit)
    (room : q.atCapacity before.native.world.graph = false)
    (normalized : record (Caller.initLookup external budget allocator source buffer request)
      (initialization external budget allocator source buffer request) before = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key)
    (absent : deterministic = true → before.native.world.graph.table key = none)
    (taken : record (OwnedCall.take external allocator) (taking external allocator) prepared = (result, called)) :
    findBody external budget allocator p q observations source buffer request before =
      match result with
      | .error fault => (.error fault, called)
      | .ok () => missBody external budget allocator p q observations source buffer request key deterministic called := by
  simp only [record] at normalized taken
  cases result <;> cases deterministic <;>
    simp only [findBody, Interner.FindCode.controlRun, Interner.FindCode.controlOwned, missBody, execution,
      bind, Effect.bind, record, unchanged, List.append_nil, room, Bool.false_eq_true, ↓reduceIte,
      normalized, classified, Except.mapError, made, taken, pure, Effect.pure]
  all_goals rw [absent rfl]
  all_goals simp only [Effect.bind, Effect.pure, record, unchanged, List.append_nil, taken]

/-- Reduce the actual source caller to its miss only after normalization and
successful take. The cache guard reads the original graph and is conditional
on determinism, exactly as in the source control. -/
theorem findBody_taken (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (values : List NodeId)
    (before prepared called : Recorded σ)
    (room : q.atCapacity before.native.world.graph = false)
    (normalized : record (Caller.initLookup external budget allocator source buffer request)
      (initialization external budget allocator source buffer request) before = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key)
    (absent : deterministic = true → before.native.world.graph.table key = none)
    (taken : record (OwnedCall.take external allocator) (taking external allocator) prepared = (.ok (), called)) :
    findBody external budget allocator p q observations source buffer request before =
      missBody external budget allocator p q observations source buffer request key deterministic called :=
  findBody_after_take external budget allocator p q observations source buffer request key deterministic values
    before prepared called (.ok ()) room normalized classified made absent taken

/-- The scoped source follows the same initialized prefix and cache guard.
The caller below supplies these two local scoped steps from physical admission. -/
theorem scoped_after_take (r : Interner.Scoped.Resources) (model : Interner.Primitives)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (values : List NodeId)
    (before : Interner.Heap) (prepared called : Interner.Scoped.Session) (result : Except Interner.Error Unit)
    (room : model.atCapacity before = false)
    (normalized : Interner.Scoped.initScope r request ⟨{}, before⟩ = (.ok values, prepared))
    (classified : model.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key)
    (absent : deterministic = true → before.table key = none)
    (taken : Interner.Scoped.take r prepared = (result, called)) :
    let miss : Except Interner.Error NodeId × Interner.Scoped.Session := match result with
      | .error error => (.error error, called)
      | .ok () => Interner.findCode.controlMiss (Interner.Scoped.execution r model) request key deterministic called
    Interner.Scoped.findDetailed r model request before = (miss.1, Interner.Scoped.close r miss.2) := by
  cases result <;> cases deterministic <;>
    simp only [Interner.Scoped.findDetailed, Interner.Scoped.finish, Interner.FindCode.controlRun,
      Interner.FindCode.controlOwned, Interner.Scoped.execution, Interner.Scoped.liftGraph, Interner.get, Interner.lift,
      bind, Effect.bind, room, Bool.false_eq_true, ↓reduceIte, normalized, classified, made, taken, pure, Effect.pure]
  all_goals rw [absent rfl]
  all_goals simp only [Effect.bind, Effect.pure, Interner.Scoped.liftGraph, Interner.lift, taken]

/-- The scoped source follows the same successful prefix and cache guard.
The caller below supplies these two local scoped steps from physical admission. -/
theorem scoped_taken (r : Interner.Scoped.Resources) (model : Interner.Primitives)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (values : List NodeId)
    (before : Interner.Heap) (prepared called : Interner.Scoped.Session)
    (room : model.atCapacity before = false)
    (normalized : Interner.Scoped.initScope r request ⟨{}, before⟩ = (.ok values, prepared))
    (classified : model.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key)
    (absent : deterministic = true → before.table key = none)
    (taken : Interner.Scoped.take r prepared = (.ok (), called)) :
    let miss := Interner.findCode.controlMiss (Interner.Scoped.execution r model) request key deterministic called
    Interner.Scoped.findDetailed r model request before = (miss.1, Interner.Scoped.close r miss.2) :=
  scoped_after_take r model request key deterministic values before prepared called (.ok ())
    room normalized classified made absent taken

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
