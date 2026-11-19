/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerMissAdmission
import Compiler.Extraction.InternerMissInvocationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.AdmissionTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace
open Insertion.Native CallerSpareSuccessTests
open CallerInputTests (request key)
open AssemblyItem.Creation.NativeFields.Tests (input)

/-- The existing native spare fixture supplies the initial caller frame in
both layouts and for empty/nonempty input. No reached header, rows, publication
admission or ownership is passed into the complete selected-suffix theorem. -/
theorem spare_from_children (safety empty deterministic : Bool)
    (base : ConstructorItem.PairInput.Context (Publication.Effects Nat)) (allocator : base.allocator = 7)
    (growth : Option (Growth.Registered.Callbacks Nat)) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (cursor : World (Publication.Effects Nat) → Nat) (children : Constructors (Publication.Effects Nat))
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (coupled : ∀ rows, (projectionAt (cursorGraph cursor) (fun world => True ∧
      InputFrame safety base.allocator 6 rows (argumentView empty) (request empty).arguments
        (CallerSpareSuccessTests.normalized empty) world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (lookupToken : NormalizationOwnership.State) (unowned : lookupToken.owned = false) (caller : lookupToken.owner = .caller)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) :
    Completion ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children debug
      (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
      (taken safety empty).2.world (lookup empty) lookupToken (request empty).arguments leading trailing (.base .missingArguments) := by
  have entry := derived_input safety empty
  have frame : InputFrame safety base.allocator 6 [old safety empty] (argumentView empty) (request empty).arguments
      (CallerSpareSuccessTests.normalized empty) (taken safety empty).2.world := by
    simpa only [allocator] using (NativeSpareTests.reached_frame safety empty).1
  exact from_children ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children debug
    (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
    (taken safety empty).2.world cursor model seed (fun _ => True) (request empty).arguments [old safety empty]
    trivial frame entry.publication.aligned (fun _ => coupled) (lookup empty) lookupToken leading trailing (.base .missingArguments)
    entry.origin.detached unowned caller

/-- Inhabit the proper-child relation with the existing stuttering controls,
for success, OOM and semantic rejection alike. These are control callbacks,
not certificates for the production recursive constructors. -/
theorem spare_outcomes (safety empty deterministic : Bool)
    (base : ConstructorItem.PairInput.Context (Publication.Effects Nat)) (allocator : base.allocator = 7)
    (growth : Option (Growth.Registered.Callbacks Nat)) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (cursor : World (Publication.Effects Nat) → Nat) (result : Except Interner.Error NodeId) (seed : Interner.Primitives)
    (lookupToken : NormalizationOwnership.State) (unowned : lookupToken.owned = false) (caller : lookupToken.owner = .caller)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) :
    let children := ScopeTests.resultChildren (fun before => (result.mapError Fault.language, before))
    Inserted ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth 6 usizeBits children debug
      (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
      (taken safety empty).2.world (lookup empty) lookupToken leading trailing [old safety empty] (.base .missingArguments) := by
  intro children
  have complete := spare_from_children safety empty deterministic base allocator growth usizeBits debug cursor children
    (ScopeTests.resultChildren (fun before => (result, before))) seed
    (fun _ => (ScopeTests.outcome_children cursor _ result).source.at debug) lookupToken unowned caller leading trailing
  have selection := Tests.spare_selected safety empty deterministic base growth children usizeBits debug
  dsimp only [Completion] at complete
  rw [selection] at complete
  obtain ⟨cells, rows, inserted⟩ := complete
  have same : cells = [old safety empty] := Option.some.inj
    (rows.symm.trans ((derived_input safety empty).origin.graph ▸ (NativeSpareTests.initial_facts safety empty).projected))
  subst cells
  exact inserted

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.AdmissionTests
