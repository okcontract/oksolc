/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointHistory
import Compiler.Extraction.InternerInsertionCheckpointMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

attribute [local irreducible] Insertion.Native.insert Insertion.Native.recordExecution Close.capture

/-- One fixed checkpoint model implements every ordinary selected miss and its
recorded close. Insertion consumes its actual checkpoint; publication and
dispatcher errors reuse the existing native suffix proofs. Proper-child frame
and dispatcher projection, input binding and stream admission remain explicit. -/
theorem checkpoint_miss
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (source buffer : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (values : List NodeId) (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (leading stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = slice.items)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let p := physical ops allocate safety owner meaning base growth usizeBits children debug source address input
    let ports := AllocationTrace.graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let decision := MissStream.selected p request key slice deterministic before
    let middle := if deterministic && request.item.kind == 1 then ports.simplify key slice before else []
    let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup
    let bodyEvents := match decision.1 with
      | .ok none => ports.insert key slice deterministic decision.2
      | _ => observed.body
    let history := leading ++ middle ++ bodyEvents ++ observed.cleanup
    let logicalModel := dispatchModel (AllocationTrace.graphReplay seed input slice meaning stream mismatch) model usizeBits debug
    let initialRecord : Recorded (Publication.Effects σ) :=
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩
    let logicalDecision := if deterministic && request.item.kind == 1 then logicalModel.simplify key (scopeView initialRecord).heap
      else (.ok none, (scopeView initialRecord).heap)
    let resources := Interner.InvocationTrace.resources stream (.preparation .incomplete)
    let body := missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
      request key deterministic initialRecord
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources logicalModel)
      request key deterministic (scopeView initialRecord)
    ∀ (_frame : ordinary decision.1 = true → CallFrame safety base.allocator owner rows source values slice address input parent decision.2)
      (_inside : history <+: stream)
      (_selected : decision.1 = logicalDecision.1.mapError Fault.language)
      (_reached : { decision.2.graph with allocationCursor := (leading ++ middle).length } = logicalDecision.2)
      (_completed : ordinary body.1 = true),
      let actual := finish (Publication.external ops.arguments) base.allocator body.1 body.2
      (body.1, scopeView body.2) = (logical.1.mapError Fault.language, logical.2) ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, Interner.Scoped.close resources logical.2) ∧
      actual.2.events = history ∧ actual.2.tokens.incomplete = false := by
  intro p ports decision middle observed bodyEvents history logicalModel initialRecord logicalDecision resources body logical
    frame inside selected reached completed actual
  have recordedHistory := checkpoint_miss_history ops allocate safety owner meaning base growth usizeBits children observations debug
    source buffer address input request key slice deterministic before handle lookup values rows leading aligned detached unowned caller
    (fun ordinaryResult => (frame ordinaryResult).1) completed
  classical
  by_cases chosen : decision.1 = .ok none
  · have cleanup : observed.cleanup = [] := by
      have nativeChosen := chosen
      dsimp only [decision, p, physical] at nativeChosen
      simp only [observed, MissStream.segment, nativeChosen]
    have emitted : bodyEvents = ports.insert key slice deterministic decision.2 := by simp only [bodyEvents, chosen]
    have same := checkpoint_insert_miss ops allocate safety owner meaning base growth usizeBits children observations debug
      source buffer address input request key slice deterministic before handle lookup model seed values rows parent leading stream mismatch
      admitted detached unowned caller chosen (frame (by simp only [chosen, ordinary]))
      (by simpa only [history, emitted, cleanup, List.append_nil] using inside) selected reached completed
    exact ⟨same.1, same.2.1, recordedHistory, same.2.2.2⟩
  · have emitted : bodyEvents = observed.body := by
      cases result : decision.1 with
      | error fault => simp only [bodyEvents, result]
      | ok value => cases value with
        | none => exact False.elim (chosen result)
        | some id => simp only [bodyEvents, result]
    obtain ⟨trailing, admittedStream⟩ := inside
    have streamEq : leading ++ middle ++ observed.body ++ observed.cleanup ++ trailing = stream := by
      simpa only [history, emitted] using admittedStream
    let originalPorts := graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let originalBody := missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries originalPorts source buffer
      request key deterministic initialRecord
    have sameBody : body = originalBody := miss_insert_irrelevant (Publication.external ops.arguments) base.budget base.allocator p
      base.queries ports originalPorts source buffer request key slice deterministic initialRecord rfl rfl rfl chosen
    let originalModel := dispatchModel (MissStream.replay seed stream observed.candidate mismatch) model usizeBits debug
    let originalLogical := Interner.findCode.controlMiss (Interner.Scoped.execution resources originalModel)
      request key deterministic (scopeView initialRecord)
    have notInserted : logicalDecision.1 ≠ .ok none := by
      intro impossible
      apply chosen
      simpa only [impossible, Except.mapError] using selected
    have sameLogical : logical = originalLogical := MissStream.scoped_insert_irrelevant resources logicalModel originalModel
      request key deterministic (scopeView initialRecord) rfl rfl notInserted
    have preserved : ordinary decision.1 = true → InputFrame safety base.allocator owner rows source values slice decision.2 :=
      fun ordinaryResult => (frame ordinaryResult).1
    have completion := MissStream.from_frame ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before values rows aligned preserved handle lookup (leading ++ middle) trailing mismatch detached unowned caller
    have original := miss_from_projection ops allocate safety owner meaning base growth usizeBits children observations debug source buffer address input
      request key slice deterministic before handle lookup (fun _ => leading.length) model seed values rows aligned preserved
      leading trailing mismatch detached unowned caller rfl
      (fun _ => MissStream.projected ops allocate safety owner meaning base growth usizeBits children debug source address input
        request key slice deterministic before handle lookup (fun _ => leading.length) model seed values (leading ++ middle) trailing mismatch
        completion selected reached)
    dsimp only [MissProjected] at original
    change leading ++ Native.middle ops allocate safety owner meaning base growth usizeBits children observations debug source address input
        request key slice deterministic before ++
      (MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
        request key slice deterministic before handle lookup).body ++
      (MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
        request key slice deterministic before handle lookup).cleanup ++ trailing = stream at streamEq
    rw [streamEq] at original
    change ordinary originalBody.1 = true →
      let done := finish (Publication.external ops.arguments) base.allocator originalBody.1 originalBody.2
      (originalBody.1, scopeView originalBody.2) = (originalLogical.1.mapError Fault.language, originalLogical.2) ∧
      (done.1, scopeView done.2) = (originalLogical.1.mapError Fault.language, Interner.Scoped.close resources originalLogical.2) ∧
      done.2.events = leading ++ middle ++ observed.body ++ observed.cleanup ∧ done.2.tokens.incomplete = false at original
    rw [← sameBody, ← sameLogical] at original
    have same := original completed
    exact ⟨same.1, same.2.1, recordedHistory, same.2.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
