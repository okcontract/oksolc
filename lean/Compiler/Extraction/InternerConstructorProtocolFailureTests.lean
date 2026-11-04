/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolFailure
import Compiler.Extraction.InternerConstructorEntryFailureTests
import Compiler.Extraction.InternerCallerProtocolLookupTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.FailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace Interner.InvocationTrace
open Publication.OriginTests (Case source request)
open CacheTests (before constructed address stack prepared debug prefix_observed)

attribute [local irreducible] item Caller.initLookup constructed prepared

variable (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))

/-- The existing temporary-allocation refusal now returns through the complete
recorded item constructor. Its actual initializer and scratch allocation are the
old fixture; arbitrary graph callbacks and observers remain unreachable. -/
theorem initialization_oom (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let context : PairInput.Context (Publication.Effects Nat) :=
      ⟨Publication.external (Normalization.Tests.external (fun _ => true)), 160, 11, p, Interner.Queries.queries⟩
    let actual := item context ports (source .temporary) (request .temporary) debug (before .temporary) leading
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete))
      Caller.CacheStream.Tests.model (request .temporary) { (constructed .temporary).graph with allocationCursor := leading.length }
    actual.1 = .error (.language .outOfMemory) ∧
      actual.2.native = { (prepared .temporary (Normalization.Tests.external (fun _ => true)) 160).2 with
        world := returnWorld (before .temporary).memory.memory.nextId (constructed .temporary).memory.memory.nextId
          (prepared .temporary (Normalization.Tests.external (fun _ => true)) 160).2.world } ∧
      Good (source .temporary) (request .temporary).arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro context actual logical
  have observed := prefix_observed .temporary
  obtain ⟨memory, allocated, proved⟩ := item_initialization_failed_projected context ports Caller.CacheStream.Tests.model
    (source .temporary) (request .temporary) debug (before .temporary) (constructed .temporary) address leading trailing
    other read sequence (Publication.OriginTests.initial_good .temporary)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    observed.1 observed.2.2.2.2.1 rfl
  rw [observed.2.1] at allocated
  have same : memory = stack .temporary := congrArg Prod.snd (Except.ok.inj (allocated.symm.trans observed.2.2.1))
  subst memory
  exact proved _ _ EntryFailureTests.failed_prefix rfl

/-- Reuse the six existing ownership inputs and capacity-query override. This
checks source routing, not a fabricated native graph with 2^32-1 rows. -/
theorem capacity_existing_family (case : Case) (leading trailing : List ProtocolEvent) :
    let context : PairInput.Context (Publication.Effects Nat) :=
      ⟨Publication.external Normalization.Tests.success, 0, 11, p, EntryFailureTests.fullQueries⟩
    let model := { Caller.CacheStream.Tests.model with atCapacity := fun _ => true }
    let actual := item context ports (source case) (request case) debug (before case) leading
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model
      (request case) { (constructed case).graph with allocationCursor := leading.length }
    actual.1 = .error (.language .capacity) ∧ Good (source case) (request case).arguments actual.2.native.world ∧
      Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro context model actual logical
  exact item_capacity_projected context ports model (source case) (request case) debug (before case) (constructed case)
    address leading trailing (Publication.OriginTests.initial_good case)
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    (prefix_observed case).1 rfl rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.FailureTests
