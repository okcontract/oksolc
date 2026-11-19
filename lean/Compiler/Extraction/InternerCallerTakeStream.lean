/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTakeInitialization
import Compiler.Extraction.InternerCallerInitializedStream

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

/-- Initialization and take consume one bound protocol stream. The first
segment supplies the actual handle, token origin, memory and starting cursor
for the second. Take may succeed or refuse; later graph/cleanup events remain
an explicit suffix, not a claim of complete invocation coverage. -/
theorem initialized_stream (external : External σ) (budget allocator : Nat) (commutative : Bool) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : OwnedCall.State σ)
    (leading suffix : List (Event Failure)) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared)) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input := { before with memory := { before.memory with memory } }
    let initialization := Initialization.capture external budget allocator commutative source buffer request.arguments input.memory
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let execution := capture external allocator lookup.origin handle prepared.world.memory
      let resources := Scope.resources (leading ++ (initialization.2.events ++ (execution.2.events ++ suffix))) (.preparation .incomplete)
      let initialScope := Interner.Scoped.initScope resources request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
      let scope := Interner.Scoped.take resources initialScope.2
      prepared.scope.lookup = some handle ∧ handle.values = values ∧
      request.item.eval (Folding.wordMeaning other) read values sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
      Initialization.checked initialization leading (execution.2.events ++ suffix) request
        { before.graph with allocationCursor := leading.length } = .ok initialScope ∧
      Initialization.Coupled allocator source request input (leading.length + initialization.2.events.length)
        initialization.2.effects.session (.ok values, prepared) initialScope other read sequence ∧
      checked execution (leading ++ initialization.2.events) suffix lookup values initialScope.2.heap = .ok scope ∧
      Coupled allocator source request.arguments handle prepared.world
        ((leading ++ initialization.2.events).length + execution.2.events.length) execution.2.effects.session execution.1
        (OwnedCall.take external allocator prepared) scope := by
  intro buffer input initialization
  obtain ⟨lookup, captured, state, contents, tokenEq, prefixProof⟩ := Initialization.successful_stream external budget allocator
    commutative source request before memory pointer values prepared leading other read sequence
    valid represented allocated decoded admitted initialized
  refine ⟨lookup, captured, ?_⟩
  intro handle execution resources initialScope scope
  have initialProof := prefixProof (execution.2.events ++ suffix)
  have start : initialScope.2.heap.allocationCursor = (leading ++ initialization.2.events).length := by
    rw [initialProof.2.2.2.2.1]
    simp only [List.length_append]
    rfl
  obtain ⟨actualHandle, actualLookup, computed, present, scopedLookup, _, actualValues, word, accepted, projected, coupled⟩ :=
    after_initialization_verified external allocator source request input _ _ (.ok values, prepared) initialScope
      other read sequence values initialProof.2 rfl admitted (leading ++ initialization.2.events) suffix start
  have presentHandle : prepared.scope.lookup = some handle := congrArg (fun s : OwnedCall.State σ => s.scope.lookup) state
  have sameHandle := Option.some.inj (presentHandle.symm.trans present)
  subst actualHandle
  obtain ⟨recorded, returned, _, recordedLookup, _, _, _⟩ := Initialization.checked_scope external budget allocator commutative
    source buffer request input.memory { before.graph with allocationCursor := leading.length } leading
      (execution.2.events ++ suffix) initialScope represented.1 rfl decoded rfl initialProof.1
  have sameRecorded := Except.ok.inj (captured.symm.trans returned)
  rw [← sameRecorded] at recordedLookup
  have sameLookup := Option.some.inj (recordedLookup.symm.trans scopedLookup)
  subst actualLookup
  have sameScope : computed = scope := by simpa only [List.append_assoc] using projected
  rw [sameScope] at accepted coupled
  exact ⟨presentHandle, contents, word, initialProof.1, initialProof.2, accepted, coupled⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
