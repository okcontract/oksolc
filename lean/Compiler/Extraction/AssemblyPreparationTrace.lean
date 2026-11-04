/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyPreparationEffects
import Compiler.Extraction.NormalizationHostTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.HostTrace

/-- The common recording step also serves host ports that receive only private
effects. It needs no fabricated memory session for those ports. -/
def recordResult (event : β → Event) (called : β × σ) (before : Recorded σ) : β × Recorded σ :=
  let (result, reached) := called
  (result, ⟨reached, before.events ++ [event result]⟩)

/-- Session-based host requests share one recorder. The reached effects and
complete response are retained, and existing history precedes the new event. -/
def recordRequest (event : α → β → Event) (host : α → Session σ → β × σ) :
    α → Session (Recorded σ) → β × Recorded σ := fun argument before =>
  recordResult (event argument) (host argument (before.mapEffects Recorded.effects)) before.effects

theorem request_observation (event : α → β → Event) (host : α → Session σ → β × σ)
    (argument : α) (before : Session (Recorded σ)) :
    let original := host argument (before.mapEffects Recorded.effects)
    let called := recordRequest event host argument before
    called.1 = original.1 ∧ called.2.effects = original.2 ∧
      called.2.events = before.effects.events ++ [event argument original.1] := ⟨rfl, rfl, rfl⟩

theorem request_transport (event : α → β → Event) (host : α → Session σ → β × σ) :
    HostTransport Recorded.effects (recordRequest event host) host := fun _ _ => rfl

theorem request_prefix (event : α → β → Event) (host : α → Session σ → β × σ) (leading : List Event) :
    HostTransport (prepend leading) (recordRequest event host) (recordRequest event host) := by
  intro argument before
  simp [recordRequest, recordResult, prepend, Session.mapEffects, List.append_assoc]

def recordCreate (host : AssemblyItem.Creation.Allocate σ) : AssemblyItem.Creation.Allocate (Recorded σ) :=
  recordRequest (fun layout response => .itemAllocate layout.bytes layout.alignment response) host

def recordCopy (host : AssemblyClone.Physical.Allocate σ) : AssemblyClone.Physical.Allocate (Recorded σ) :=
  recordRequest Event.payloadAllocate host

theorem create_transport (host : AssemblyItem.Creation.Allocate σ) :
    HostTransport Recorded.effects (recordCreate host) host := request_transport _ host

theorem copy_transport (host : AssemblyClone.Physical.Allocate σ) :
    HostTransport Recorded.effects (recordCopy host) host := request_transport _ host

/-- The original native creation body determines whether any host call occurs.
Its memory/registry validation and every reached failure are derived unchanged. -/
theorem create_erases (host : AssemblyItem.Creation.Allocate σ) (allocator : Nat) (item : Cache.Item) :
    Compiler.Algebraic.Effect.Transport (Session.mapEffects Recorded.effects)
      (AssemblyItem.Creation.create (recordCreate host) allocator item) (AssemblyItem.Creation.create host allocator item) :=
  AssemblyItem.Creation.create_transport _ (create_transport host) allocator item

theorem clone_erases (host : AssemblyClone.Physical.Allocate σ) (allocator : Nat) (input : AssemblyClone.Value Metadata) :
    Compiler.Algebraic.Effect.Transport (Session.mapEffects Recorded.effects)
      (AssemblyClone.Physical.run (recordCopy host) allocator input) (AssemblyClone.Physical.run host allocator input) :=
  AssemblyClone.Physical.run_transport _ (copy_transport host) allocator input

theorem create_prefix (host : AssemblyItem.Creation.Allocate σ) (allocator : Nat) (item : Cache.Item) (leading : List Event) :
    Compiler.Algebraic.Effect.Transport (Session.mapEffects (prepend leading))
      (AssemblyItem.Creation.create (recordCreate host) allocator item) (AssemblyItem.Creation.create (recordCreate host) allocator item) :=
  AssemblyItem.Creation.create_transport _ (request_prefix _ host leading) allocator item

theorem clone_prefix (host : AssemblyClone.Physical.Allocate σ) (allocator : Nat) (input : AssemblyClone.Value Metadata) (leading : List Event) :
    Compiler.Algebraic.Effect.Transport (Session.mapEffects (prepend leading))
      (AssemblyClone.Physical.run (recordCopy host) allocator input) (AssemblyClone.Physical.run (recordCopy host) allocator input) :=
  AssemblyClone.Physical.run_transport _ (request_prefix _ host leading) allocator input

end Compiler.Extraction.Memory.Arguments.Normalization.HostTrace
