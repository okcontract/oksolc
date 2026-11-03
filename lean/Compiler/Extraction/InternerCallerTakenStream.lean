/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTakeStream
import Compiler.Extraction.InternerCallerCloseTake
import Compiler.Extraction.InternerInvocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Interner.InvocationTrace

attribute [local irreducible] Initialization.capture capture

/-- Successful native initialization and take supply one reusable tagged
prefix. The suffix is chosen after the actual token and detached handle are
known, so insertion and recursive miss share the same scope and cursor proof.
This does not admit a refused take or invent events for later graph work. -/
theorem initialized_taken_stream (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source : View) (request : Interner.Request) (before : World σ)
    (stack : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared called : OwnedCall.State σ)
    (leading : List (Event Failure ι)) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, stack))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take external allocator prepared = (.ok (), called)) :
    let start := { before with memory := { before.memory with memory := stack } }
    let initialization := Initialization.capture external budget allocator commutative source
      ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments start.memory
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let taken := capture external allocator lookup.origin handle prepared.world.memory
      let missLeading := leading ++ initialization.2.events.map Event.normalization ++ taken.2.events.map Event.normalization
      ∃ slice remaining, called.scope = ⟨some remaining, some slice, false⟩ ∧
        Normalization.Taken allocator source request.arguments handle prepared.world.memory slice remaining called.world.memory ∧
        handle.values = values ∧ taken.1.2.owned = false ∧ taken.1.2.owner = .caller ∧
        request.item.eval (Folding.wordMeaning other) read values sequence =
          request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
        ∀ suffix : List (Event Failure ι),
          let r := resources (missLeading ++ suffix) (.preparation .incomplete)
          let initialScope := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
          let takeScope := Interner.Scoped.take r initialScope.2
          initialScope.1 = .ok values ∧ taken.1.1 = true ∧
          Initialization.checked initialization (normalizations leading) (taken.2.events ++ normalizations suffix) request
            { before.graph with allocationCursor := leading.length } = .ok initialScope ∧
          checked taken (normalizations leading ++ initialization.2.events) (normalizations suffix)
            lookup values initialScope.2.heap = .ok takeScope ∧
          takeScope.1 = .ok () ∧
          takeScope.2 = ⟨⟨some taken.1.2, remaining.values, .cleanup⟩,
            { called.world.graph with allocationCursor := missLeading.length }⟩ := by
  intro start initialization
  obtain ⟨lookup, recorded, present, contents, word, _, known, _, _⟩ :=
    initialized_stream external budget allocator commutative source request before stack pointer values prepared
      (normalizations leading) [] other read sequence valid represented allocated decoded admitted initialized
  refine ⟨lookup, recorded, ?_⟩
  intro handle taken missLeading
  change handle.values = values at contents
  obtain ⟨actualHandle, _, nativeHandle, _, _, ready, _, _, localShape, _⟩ := known.2.2.2.2.2 values rfl
  have sameHandle := Option.some.inj (nativeHandle.symm.trans present)
  subst actualHandle
  have preparedShape : (⟨prepared.world, { lookup := some handle }⟩ : OwnedCall.State σ) = prepared := by rw [← localShape]
  have tokens := Close.take_success external allocator lookup.origin source request.arguments handle prepared.world ready admitted
    (by rw [preparedShape, transferred])
  obtain ⟨slice, remaining, locals, lifetime⟩ := tokens.2.2
  rw [preparedShape, transferred] at locals lifetime
  refine ⟨slice, remaining, locals, lifetime, contents, tokens.1, tokens.2.1, word, ?_⟩
  intro suffix r initialScope takeScope
  obtain ⟨actualLookup, captured, _, _, _, initChecked, initKnown, takeChecked, takeKnown⟩ :=
    initialized_stream external budget allocator commutative source request before stack pointer values prepared
      (normalizations leading) (normalizations suffix) other read sequence valid represented allocated decoded admitted initialized
  have sameLookup := Option.some.inj (Except.ok.inj (captured.symm.trans recorded))
  subst actualLookup
  have initialCheck : Initialization.checked initialization (normalizations leading) (taken.2.events ++ normalizations suffix) request
      { before.graph with allocationCursor := leading.length } = .ok initialScope := by
    simpa only [initialScope, r, missLeading, resources, normalizations_append, normalizations_embed,
      normalizations_length, List.append_assoc] using initChecked
  have takeCheck : checked taken (normalizations leading ++ initialization.2.events) (normalizations suffix)
      lookup values initialScope.2.heap = .ok takeScope := by
    simpa only [takeScope, initialScope, r, missLeading, resources, normalizations_append, normalizations_embed,
      normalizations_length, List.append_assoc] using takeChecked
  have relation : Coupled allocator source request.arguments handle prepared.world
      ((normalizations leading ++ initialization.2.events).length + taken.2.events.length) taken.2.effects.session taken.1
      (.ok (), called) takeScope := by
    simpa only [transferred, takeScope, initialScope, r, missLeading, resources, normalizations_append, normalizations_embed,
      normalizations_length, List.append_assoc] using takeKnown
  have success : takeScope.1 = .ok () := by
    have result := relation.1
    cases selected : takeScope.1 with
    | error reason => simp only [selected, Except.mapError] at result; contradiction
    | ok value => cases value; rfl
  obtain ⟨capturedLookup, captureEq, _, _, tokenEq⟩ := Initialization.capture_success external budget allocator commutative
    source ⟨before.memory.memory.nextId, 0, 2⟩ request start values prepared decoded initialized
  have sameCaptured := Option.some.inj (Except.ok.inj (captureEq.symm.trans recorded))
  subst capturedLookup
  change lookup = ResourceAdapter.token lookup.origin handle at tokenEq
  have recordedSuccess : taken.1.1 = true := by
    have checkedTake := checked_scope external allocator lookup.origin handle prepared.world.memory
      (normalizations leading ++ initialization.2.events) (normalizations suffix) initialScope.2.heap takeScope
      (by simpa only [initialScope, r, missLeading, resources, normalizations_append, normalizations_embed,
        normalizations_length, List.append_assoc, List.length_append] using congrArg Interner.Heap.allocationCursor initKnown.2.2.2.1)
      (by simpa only [contents, ← tokenEq] using takeCheck)
    have result := congrArg Prod.fst checkedTake.2
    rw [success] at result
    change (.ok () : Except Interner.Error Unit) = (if taken.1.1 then .ok () else .error .outOfMemory) at result
    cases chosen : taken.1.1 with
    | false => simp only [chosen, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at result
    | true => rfl
  have initialResult : initialScope.1 = .ok values := by
    have result : (.ok values : Except Fault _) = initialScope.1.mapError Fault.language := by
      simpa only [initialScope, r, missLeading, resources, normalizations_append, normalizations_embed,
        normalizations_length, List.append_assoc] using initKnown.1
    cases returned : initialScope.1 <;> simp only [returned, Except.mapError, Except.ok.injEq, reduceCtorEq] at result
    exact congrArg Except.ok result.symm
  refine ⟨initialResult, recordedSuccess, initialCheck, takeCheck, success, ?_⟩
  rw [relation.2.2.2.1, relation.2.1]
  simp only [recordedSuccess, ↓reduceIte, lifetime.sameValues, missLeading, List.length_append,
    List.length_map, normalizations_length]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
