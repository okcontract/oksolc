/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolTakeFailure
import Compiler.Extraction.InternerConstructorProtocolFailureTests
import Compiler.Extraction.InternerConstructorTakeFailureTests
import Compiler.Extraction.InternerCallerProtocolTakenTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.TakeFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace Interner.InvocationTrace
open Publication.OriginTests (Case source request key sorted)
open CacheTests (debug address stack)
open ConstructorItem.TakeFailureTests (host queries before constructed prepared taken prefix_observed failed_observed missed)

attribute [local irreducible] item Caller.initLookup OwnedCall.take constructed prepared taken

/-- The three existing borrowed inputs exercise both source cache guards.
The nondeterministic override deliberately bypasses a populated cache; these
argument-shape fixtures do not claim opcode word semantics. Actual failed
allocator effects survive the two original local cleanup marks. -/
theorem existing_family (case : Case) (deterministic : Bool)
    (borrowed : case = .scratch ∨ case = .offsetBorrow ∨ case = .replacement)
    (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let context : PairInput.Context (Publication.Effects Nat) := ⟨Publication.external host, 160, 11, p, queries deterministic⟩
    let model := { Caller.CacheStream.Tests.model with deterministic := (queries deterministic).deterministic }
    let actual := item context ports (source case) (request case) debug (before case deterministic) leading
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model
      (request case) { (constructed case deterministic).graph with allocationCursor := leading.length }
    actual.1 = .error (.language .outOfMemory) ∧
      actual.2.native.world = returnWorld (before case deterministic).memory.memory.nextId
        (constructed case deterministic).memory.memory.nextId (taken case deterministic).2.world ∧
      Good (source case) (request case).arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro context model actual logical
  have observed := prefix_observed case deterministic
  obtain ⟨memory, allocated, proved⟩ := item_take_failed_projected context ports model (source case) (request case) debug
    (before case deterministic) (constructed case deterministic) address (Caller.CacheStream.Tests.commutes case)
    leading trailing other read sequence (by cases deterministic <;> exact Publication.OriginTests.initial_good case)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    observed.1 observed.2.2.2.1 (by cases case <;> rfl) (by cases deterministic <;> rfl) rfl
  have same : memory = stack case := congrArg Prod.snd (Except.ok.inj (allocated.symm.trans observed.2.1))
  subst memory
  have initialized : prepared case deterministic = (.ok (sorted case), (prepared case deterministic).2) :=
    Prod.ext observed.2.2.1 rfl
  have failed : taken case deterministic = (.error (.language .outOfMemory), (taken case deterministic).2) :=
    Prod.ext (failed_observed case deterministic borrowed).1 rfl
  conv at initialized => lhs; unfold prepared
  conv at failed => lhs; unfold taken
  exact (proved (sorted case) (prepared case deterministic).2 (taken case deterministic).2 (.language .outOfMemory)
    (key case) deterministic initialized observed.2.2.2.2.1 observed.2.2.2.2.2 (missed case deterministic) failed).2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.TakeFailureTests
