/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerArgumentPreparationFailure
import Compiler.Extraction.InternerConstructorProtocolEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace Interner.InvocationTrace

/-- The complete scoped result at the original entry graph and event position.
Native frame and word preservation remain separate obligations. -/
def EntryProjected (model : Interner.Primitives) (request : Interner.Request)
    (before : Interner.Heap) (leading trailing : List ProtocolEvent)
    (actual : Except Fault NodeId × Recorded σ) : Prop :=
  let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
    { before with allocationCursor := leading.length }
  ordinary actual.1 = true →
    (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false

theorem EntryProjected.of_outcome {model : Interner.Primitives} {request : Interner.Request}
    {before : Interner.Heap} {leading trailing : List ProtocolEvent}
    {actual : Except Fault NodeId × Recorded σ} {inner : Except Fault NodeId × Recorded τ}
    (same : outcome actual = outcome inner)
    (checked : EntryProjected model request before leading trailing inner) :
    EntryProjected model request before leading trailing actual := by
  have equal : actual.1 = inner.1 ∧ scopeView actual.2 = scopeView inner.2 ∧
      actual.2.events = inner.2.events ∧ actual.2.tokens.incomplete = inner.2.tokens.incomplete := by
    simpa only [outcome, Prod.mk.injEq] using same
  simpa only [EntryProjected, equal.1, equal.2.1, equal.2.2.1, equal.2.2.2] using checked

variable (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)

/-- One composition handles literal arrays and named copies. The producer and
return equations are instantiated from their existing executable definitions;
the only recursive obligation is the reached item's local miss continuation. -/
theorem prepared_entry_projected (model : Interner.Primitives) (request : Interner.Request)
    (debug : AssemblyItem.Fields.Values) (before : World σ) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (producer : GraphAction σ View) (action : Capture σ NodeId)
    (returned : (Except Fault NodeId × Recorded σ) → Except Fault NodeId × Recorded σ)
    (forwarded : action before leading = match producer before with
      | (.error fault, reached) => (.error fault, start reached leading)
      | (.ok source, prepared) => returned (item context ports source request debug prepared leading))
    (preserves : ∀ ran, outcome (returned ran) = outcome ran)
    (ready : ∀ source prepared, producer before = (.ok source, prepared) → Arguments.Prepared request.arguments before source prepared)
    (rejected : ∀ fault reached, producer before = (.error fault, reached) → ordinary (.error fault : Except Fault NodeId) = false)
    (admitted : Admitted context.external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = context.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = context.queries.deterministic request.item)
    (miss : ∀ source prepared, producer before = (.ok source, prepared) →
      EntryContinuation context ports model source request debug prepared leading trailing) :
    EntryProjected model request before.graph leading trailing (action before leading) := by
  cases ran : producer before with
  | mk result prepared =>
    cases result with
    | error fault =>
      have actual : action before leading = (.error fault, start prepared leading) := by simpa only [ran] using forwarded
      rw [actual]
      intro completed
      rw [rejected fault prepared ran] at completed
      cases completed
    | ok source =>
      have input := ready source prepared ran
      have checked := item_entry_projected context ports model source request debug prepared leading trailing other read sequence
        input.good admitted domain typed (by rw [input.graph]; exact capacityQuery) classificationQuery (miss source prepared ran)
      have projected : EntryProjected model request before.graph leading trailing (item context ports source request debug prepared leading) := by
        simpa only [EntryProjected, input.graph] using checked
      apply projected.of_outcome
      exact (congrArg outcome (by simpa only [ran] using forwarded)).trans (preserves _)

/-- Literal preparation is selected by the execution itself, including empty
arguments, allocation rejection and unsupported arities. -/
theorem literal_entry_projected (model : Interner.Primitives) (opcode : Opcode) (values : List NodeId)
    (debug : AssemblyItem.Fields.Values) (before : World σ) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (admitted : Admitted context.external) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = context.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      context.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (miss : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      EntryContinuation context ports model source (Interner.constructorCode.operationRequest opcode values) debug prepared leading trailing) :
    EntryProjected model (Interner.constructorCode.operationRequest opcode values) before.graph leading trailing
      (literal context ports opcode values debug before leading) :=
  prepared_entry_projected context ports model (Interner.constructorCode.operationRequest opcode values) debug before
    leading trailing other read sequence (Arguments.prepare values) (literal context ports opcode values debug)
    (fun ran => if values.isEmpty then ran else retire before.memory.memory.nextId ran) rfl
    (by intro ran; split; rfl; exact retire_outcome _ _)
    (fun source prepared ran => Arguments.prepare_success values before prepared source valid ran)
    (fun fault reached ran => Arguments.error_nonordinary values valid reached fault ran)
    admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery miss

/-- The named copy and optional overwrite derive the reached input. An unused
index is unrestricted, and retirement uses the original local allocation mark. -/
theorem local_entry_projected (model : Interner.Primitives) (opcode : Opcode) (source : View)
    (left right repeated : NodeId) (selected : Nat) (first : Bool)
    (debug : AssemblyItem.Fields.Values) (before : World σ) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source [left, right] before) (inside : first = true → selected < 2)
    (admitted : Admitted context.external) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = context.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then [left, right].set selected repeated else [left, right])).item =
      context.queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then [left, right].set selected repeated else [left, right])).item)
    (miss : ∀ target prepared, LocalArguments.zigLocal source selected repeated first before = (.ok target, prepared) →
      EntryContinuation context ports model target (Interner.constructorCode.operationRequest opcode
        (if first then [left, right].set selected repeated else [left, right])) debug prepared leading trailing) :
    EntryProjected model (Interner.constructorCode.operationRequest opcode
      (if first then [left, right].set selected repeated else [left, right])) before.graph leading trailing
      (namedLocal context ports opcode source left right repeated selected first debug before leading) :=
  prepared_entry_projected context ports model _ debug before leading trailing other read sequence
    (LocalArguments.zigLocal source selected repeated first)
    (namedLocal context ports opcode source left right repeated selected first debug)
    (retire before.memory.memory.nextId) rfl (retire_outcome _)
    (fun target prepared ran => ViewInput.local_input_optional source target left right repeated selected first before prepared good inside ran)
    (fun fault reached ran => LocalArguments.error_nonordinary left right repeated selected first good inside reached fault ran)
    admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery miss

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
