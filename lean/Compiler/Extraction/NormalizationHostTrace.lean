/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.HostTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Actual host calls for normalization, item/backing preparation/cleanup and the publication
probe boundary. These differ from the existing ownership protocol trace:
normalization scratch preparation, empty duplication and empty release make no
host call. Keep the full allocator response; a rejected address is not ordinary OOM.
This is instrumentation of the existing executor, with no second memory model. -/
inductive Event where
  | allocate (site : NormalizationOwnership.Allocation) (bytes : Nat) (response : Option Nat)
  | free (slice : ArgumentSlice)
  /-- The exact map probe decision; this does not expose native bucket allocations. -/
  | publicationProbe (key : Key) (succeeded : Bool)
  | itemAllocate (bytes alignment : Nat) (response : Option Nat)
  | payloadAllocate (bytes : Nat) (response : Option Nat)
  | payloadFree (allocation length offset : Nat)
  | itemFree (allocation : Nat)
  | backingAllocate (allocator bytes alignment : Nat) (response : Option Nat)
  | backingFree (allocator base bytes alignment : Nat)
  deriving DecidableEq, Repr

structure Recorded (σ : Type) where
  effects : σ
  events : List Event := []

/-- Forward the original reached session and explicit allocator effects. The
host cannot inspect the log; each actual callback appends exactly one event. -/
def record (host : External σ) : External (Recorded σ) := {
  allocate := fun site before bytes effects =>
    let (response, after) := host.allocate site (before.mapEffects Recorded.effects) bytes effects.effects
    (response, ⟨after, effects.events ++ [.allocate site bytes response]⟩)
  free := fun slice before =>
    ⟨host.free slice (before.mapEffects Recorded.effects), before.effects.events ++ [.free slice]⟩ }

/-- The log binds the actual requested site, byte count and complete response,
not just the allocator's success bit. The private effects are the reached ones. -/
theorem allocation_observation (host : External σ) (site : NormalizationOwnership.Allocation)
    (before : Session (Recorded σ)) (bytes : Nat) (effects : Recorded σ) :
    let original := host.allocate site (before.mapEffects Recorded.effects) bytes effects.effects
    let called := (record host).allocate site before bytes effects
    called.1 = original.1 ∧ called.2.effects = original.2 ∧
      called.2.events = effects.events ++ [.allocate site bytes original.1] := ⟨rfl, rfl, rfl⟩

theorem release_observation (host : External σ) (slice : ArgumentSlice) (before : Session (Recorded σ)) :
    let called := (record host).free slice before
    called.effects = host.free slice (before.mapEffects Recorded.effects) ∧
      called.events = before.effects.events ++ [.free slice] := ⟨rfl, rfl⟩

theorem transport (host : External σ) : External.Transport (record host) host Recorded.effects := by
  constructor <;> intros <;> rfl

theorem admitted (host : External σ) (valid : Admitted host) : Admitted (record host) :=
  (transport host).admitted valid

def prepend (leading : List Event) (before : Recorded σ) : Recorded σ :=
  { before with events := leading ++ before.events }

/-- Existing history cannot alter host observations or responses. -/
theorem prefix_transport (host : External σ) (leading : List Event) :
    External.Transport (record host) (record host) (prepend leading) := by
  constructor <;> intros <;> simp [record, prepend, Session.mapEffects, List.append_assoc]

/-- All native lifecycle outcomes erase exactly, including incomplete sorting,
invalid regions, partial copies, ordinary OOM and rejected cleanup. No validity,
budget-completion or enclosing preservation assumption is required. -/
theorem run_erases (code : NormalizationOwnership.Code) (host : External σ)
    (budget allocator : Nat) (commutative : Bool) (source buffer : View) (values : List NodeId)
    (exit : NormalizationOwnership.Exit) (before : Session (Recorded σ)) :
    Normalization.run code host budget allocator commutative source buffer values exit
        (before.mapEffects Recorded.effects) =
      Step.mapEffects Recorded.effects
        (Normalization.run code (record host) budget allocator commutative source buffer values exit before) :=
  (transport host).run code budget allocator commutative source buffer values exit before

theorem run_prefix (code : NormalizationOwnership.Code) (host : External σ)
    (budget allocator : Nat) (commutative : Bool) (source buffer : View) (values : List NodeId)
    (exit : NormalizationOwnership.Exit) (before : Session (Recorded σ)) (leading : List Event) :
    Normalization.run code (record host) budget allocator commutative source buffer values exit
        (before.mapEffects (prepend leading)) =
      Step.mapEffects (prepend leading)
        (Normalization.run code (record host) budget allocator commutative source buffer values exit before) :=
  (prefix_transport host leading).run code budget allocator commutative source buffer values exit before

end Compiler.Extraction.Memory.Arguments.Normalization.HostTrace
