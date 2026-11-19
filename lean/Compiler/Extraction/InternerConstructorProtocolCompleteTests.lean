/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolEntry
import Compiler.Extraction.InternerNativeInvocation
import Compiler.Extraction.InternerConstructorProtocolTakeFailureTests
import Compiler.Extraction.InternerRecursiveProtocolBoundReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CompleteTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace Interner.InvocationTrace
open Publication.OriginTests (Case source request)
open CacheTests (debug address stack)

attribute [local irreducible] item Caller.initLookup OwnedCall.take

/-- Reuse all six refused-borrow executions. The general item theorem must
discover the refusal itself; the miss obligation is discharged solely because
the actual take failed. The native result proof supplies ordinary completion,
not the scoped correspondence under test. -/
theorem refused_family (case : Case) (deterministic : Bool)
    (borrowed : case = .scratch ∨ case = .offsetBorrow ∨ case = .replacement)
    (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let context : PairInput.Context (Publication.Effects Nat) :=
      ⟨Publication.external ConstructorItem.TakeFailureTests.host, 160, 11, p, ConstructorItem.TakeFailureTests.queries deterministic⟩
    let model := { Caller.CacheStream.Tests.model with deterministic := context.queries.deterministic }
    let actual := item context ports (source case) (request case) debug (ConstructorItem.TakeFailureTests.before case deterministic) leading
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model
      (request case) { (ConstructorItem.TakeFailureTests.constructed case deterministic).graph with allocationCursor := leading.length }
    (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro context model actual logical
  have observed := ConstructorItem.TakeFailureTests.prefix_observed case deterministic
  have good : Good (source case) (request case).arguments (ConstructorItem.TakeFailureTests.before case deterministic) :=
    by cases deterministic <;> exact Publication.OriginTests.initial_good case
  have preparedItem := (prepare_success (request case).item debug (ConstructorItem.TakeFailureTests.before case deterministic)
    (ConstructorItem.TakeFailureTests.constructed case deterministic) address good.1
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid observed.1).2
  have checked := item_entry_projected context ports model (source case) (request case) debug
    (ConstructorItem.TakeFailureTests.before case deterministic) leading trailing other read sequence good
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    (by cases deterministic <;> rfl) rfl (by
      intro constructed actualAddress memory made _room allocated
      have same := Prod.mk.inj (made.symm.trans observed.1)
      cases Except.ok.inj same.1
      cases same.2
      have sameMemory : memory = stack case := congrArg Prod.snd (Except.ok.inj (allocated.symm.trans observed.2.1))
      subst memory
      intro values key deterministic normalized transferred _ _ _ _ _ succeeded
      change (ConstructorItem.TakeFailureTests.taken case _).1 = .ok () at succeeded
      rw [(ConstructorItem.TakeFailureTests.failed_observed case _ borrowed).1] at succeeded
      cases succeeded)
  have native := (ConstructorItem.TakeFailureTests.failed_contract case deterministic borrowed (p (source case))).1
  have erased := item_erases context ports (source case) (request case) debug (ConstructorItem.TakeFailureTests.before case deterministic) leading
  have result := congrArg Prod.fst erased
  change _ = actual.1 at result
  have observedResult : actual.1 = .error (.language .outOfMemory) := result.symm.trans native
  have completed : ordinary actual.1 = true := by rw [observedResult]; rfl
  simpa only [logical, preparedItem.graph] using checked completed

/-- The actual capacity precheck bypasses scratch and the entire continuation.
The scratch existence theorem is a mathematical preparation fact, not a claim
that this branch executes the allocation. Reuse the existing query override. -/
theorem capacity_family (case : Case)
    (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let context : PairInput.Context (Publication.Effects Nat) :=
      ⟨Publication.external Normalization.Tests.success, 0, 11, p, EntryFailureTests.fullQueries⟩
    let model := { Caller.CacheStream.Tests.model with atCapacity := fun _ => true }
    let actual := item context ports (source case) (request case) debug (CacheTests.before case) leading
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model
      (request case) { (CacheTests.constructed case).graph with allocationCursor := leading.length }
    ordinary actual.1 = true →
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro context model actual logical completed
  have checked := item_entry_projected context ports model (source case) (request case) debug
    (CacheTests.before case) leading trailing other read sequence
    (Publication.OriginTests.initial_good case) (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid rfl rfl
    (by intro constructed actualAddress memory made impossible; cases impossible) completed
  have preparedItem := (prepare_success (request case).item debug (CacheTests.before case) (CacheTests.constructed case)
    address (Publication.OriginTests.initial_good case).1 (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
    AssemblyItem.Initializers.Tests.debug_valid (CacheTests.prefix_observed case).1).2
  simpa only [logical, preparedItem.graph] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CompleteTests
