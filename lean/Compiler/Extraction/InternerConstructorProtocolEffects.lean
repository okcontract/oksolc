/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolEffects
import Compiler.Extraction.InternerConstructorEffects
import Compiler.Extraction.InternerConstructorProtocolReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace

def mapReturn (project : σ → τ) (ran : Except Fault α × Recorded σ) : Except Fault α × Recorded τ :=
  (ran.1, ran.2.mapEffects project)

theorem mapReturn_outcome (project : σ → τ) (ran : Except Fault NodeId × Recorded σ) :
    outcome (mapReturn project ran) = outcome ran := rfl

theorem retire_transport (project : σ → τ) (mark : Nat) (ran : Except Fault NodeId × Recorded σ) :
    retire mark (mapReturn project ran) = mapReturn project (retire mark ran) := by
  unfold retire TemporaryArguments.unwind mapReturn
  split <;> rfl

namespace EffectTransport

theorem frame {left : External σ} {right : External τ} {project : σ → τ}
    (mapped : left.Transport right project) (budget allocator : Nat) {p : Primitives σ} {q : Primitives τ}
    (native : p.Transport q project) (queries : Caller.Queries)
    {ports : GraphObservations σ} {other : GraphObservations τ} (observed : ports.Transport other project)
    (source : View) (request : Interner.Request) (before : World σ) (leading : List ProtocolEvent) :
    ProtocolTrace.frame right budget allocator q queries other source request (before.mapEffects project) leading =
      mapReturn project (ProtocolTrace.frame left budget allocator p queries ports source request before leading) := by
  unfold ProtocolTrace.frame
  simp only [show (before.mapEffects project).graph = before.graph from rfl,
    show (before.mapEffects project).memory.memory = before.memory.memory from rfl]
  split
  · rfl
  · cases Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => rfl
    | ok allocated =>
      rcases allocated with ⟨pointer, memory⟩
      dsimp only
      have called := Caller.ProtocolTrace.EffectTransport.find mapped budget allocator native queries observed source
        ⟨before.memory.memory.nextId, 0, 2⟩ request (start { before with memory := { before.memory with memory } } leading)
      simp only [start, Recorded.mapEffects, OwnedCall.State.mapEffects, World.mapEffects, Session.mapEffects] at called ⊢
      rw [called]
      exact retire_transport project before.memory.memory.nextId _

variable {left : PairInput.Context σ} {right : PairInput.Context τ} {project : σ → τ}
  (mapped : left.Transport right project)
  {ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ}
  {other : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations τ}
  (observed : ∀ source address input, (ports source address input).Transport (other source address input) project)
include mapped observed

theorem item (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (leading : List ProtocolEvent) :
    ProtocolTrace.item right other source request debug (before.mapEffects project) leading =
      mapReturn project (ProtocolTrace.item left ports source request debug before leading) := by
  unfold ProtocolTrace.item
  rw [ConstructorItem.EffectTransport.prepare project]
  cases ConstructorItem.prepare request.item debug before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok address =>
      dsimp only
      rw [← mapped.budget, ← mapped.allocator, ← mapped.queries,
        frame mapped.external left.budget left.allocator (mapped.primitives source address _) left.queries
          (observed source address _) source request reached leading]
      exact retire_transport project before.memory.memory.nextId _

theorem literal (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (leading : List ProtocolEvent) :
    ProtocolTrace.literal right other opcode values debug (before.mapEffects project) leading =
      mapReturn project (ProtocolTrace.literal left ports opcode values debug before leading) := by
  unfold ProtocolTrace.literal
  rw [Arguments.EffectTransport.prepare project]
  cases Arguments.prepare values before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok source =>
      dsimp only
      rw [item mapped observed source _ debug reached leading]
      split
      · rfl
      · exact retire_transport project before.memory.memory.nextId _

theorem namedLocal (opcode : Opcode) (source : View) (leftId rightId repeated : NodeId)
    (selected : Nat) (first : Bool) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (leading : List ProtocolEvent) :
    ProtocolTrace.namedLocal right other opcode source leftId rightId repeated selected first debug (before.mapEffects project) leading =
      mapReturn project (ProtocolTrace.namedLocal left ports opcode source leftId rightId repeated selected first debug before leading) := by
  unfold ProtocolTrace.namedLocal
  rw [LocalArguments.EffectTransport.zigLocal project]
  cases LocalArguments.zigLocal source selected repeated first before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok target =>
      dsimp only
      rw [item mapped observed target _ debug reached leading]
      exact retire_transport project before.memory.memory.nextId _

/-- All five original wrappers preserve the complete capture under the same
local caller bindings. No prepared input, successful child or final frame is
assumed for this execution equality. -/
theorem constructors :
    mapConstructors (m := Capture τ) (n := fun α => World σ → List ProtocolEvent → Except Fault α × Recorded τ)
      (fun action before leading => action (before.mapEffects project) leading) (ProtocolTrace.constructors right other) =
    mapConstructors (fun action before leading => mapReturn project (action before leading))
      (ProtocolTrace.constructors left ports) := by
  unfold mapConstructors ProtocolTrace.constructors
  congr 1
  · funext opcode values debug before leading; exact literal mapped observed opcode values debug before leading
  · funext value debug before leading; exact item mapped observed _ _ debug before leading
  · funext id value debug before leading; exact item mapped observed _ _ debug before leading
  · funext address opcode values debug before leading; exact item mapped observed _ _ debug before leading
  · funext opcode source selected repeated first debug before leading
    dsimp only
    cases items : source.items with
    | nil => rfl
    | cons left rest => cases rest with
      | nil => rfl
      | cons right tail => cases tail with
        | nil => exact namedLocal mapped observed opcode (view source) left right repeated selected first debug before leading
        | cons _ _ => rfl

end EffectTransport
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
