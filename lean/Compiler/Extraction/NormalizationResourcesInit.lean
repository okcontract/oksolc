/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResourcesPreparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Observe a live handle without transfer, release or invalidation. Semantic
failures and a malformed descriptor remain separate from ordinary OOM. -/
def observeInit (result : NormalizationOwnership.PreparedInit Failure) (after : State σ) : Option (Except Failure Handle) :=
  match after.rejected with
  | some (.memory failure) => some (.error failure)
  | some .missingSlice => none
  | none =>
    match result with
    | .error (failure, _) => some (.error failure)
    | .ok none => some (.error .outOfMemory)
    | .ok (some _) => some (.ok after.handle)

def initialized (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session σ) :=
  normalizationOwnershipCode.initPrepared commutative source.length buffer.length
    (primitives external budget allocator source buffer values) (initial source values before)

/-- Successful live initialization has no pending rejection or transferred
descriptor. Its logical token names the actual native ownership. -/
def InitAligned (result : NormalizationOwnership.PreparedInit Failure) (after : State σ) : Prop :=
  ∀ lookup, result = .ok (some lookup) →
    after.rejected = none ∧ after.transferred = none ∧ lookup = token lookup.origin after.handle

theorem prepare_init (budget allocator : Nat) (source buffer : View) (values : List NodeId)
    (origin : NormalizationOwnership.Origin) (handle : Handle) (before : Session σ) :
    let lookup := preparedToken origin source buffer
    let execution := prepare budget allocator source buffer values lookup ⟨before, handle, none, none⟩
    let result : NormalizationOwnership.PreparedInit Failure :=
      execution.1.mapError (fun failure => (failure, lookup)) |>.map (fun _ => some lookup)
    (observeInit result execution.2, execution.2.session) =
      (let native := Normalization.prepare normalizationOwnershipCode budget allocator buffer.length source
        (if origin = .scratch then bufferPrefix buffer source.length else handle.items) values (origin == .allocation) before
      (some native.1, native.2)) ∧
    InitAligned result execution.2 := by
  cases prepared : Normalization.prepare normalizationOwnershipCode budget allocator buffer.length source
      (if origin = .scratch then bufferPrefix buffer source.length else handle.items) values (origin == .allocation) before with
  | mk result reached =>
    cases result with
    | error failure => simp [prepare, preparedToken, prepared, observeInit, InitAligned, Except.map, Except.mapError]
    | ok nativeHandle =>
      have aligned := prepared_token budget allocator source _ buffer values (origin == .allocation) origin before reached nativeHandle prepared
      simp only [prepare, preparedToken, prepared, Except.map, Except.mapError]
      simpa [observeInit, InitAligned, preparedToken] using aligned.symm

/-- All actual native outcomes, including incomplete preparation and partial
writes. The returned descriptor stays live for the caller's graph actions. -/
theorem init_spec (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session σ) :
    let execution := initialized external budget allocator commutative source buffer values before
    let native := Normalization.init normalizationOwnershipCode external budget allocator commutative source buffer values before
    (observeInit execution.1 execution.2, execution.2.session) = (some native.1, native.2) ∧
      InitAligned execution.1 execution.2 := by
  cases needed : !commutative || decide (source.length < normalizationOwnershipCode.threshold) with
  | true =>
    simp [initialized, NormalizationOwnership.Code.initPrepared, NormalizationOwnership.Code.initWith,
      Normalization.init, initial, observeInit, InitAligned, token, needed]
  | false =>
    by_cases fits : source.length ≤ buffer.length
    · have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = true := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      have own : normalizationOwnershipCode.ownTemporary.test source.length buffer.length = false := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, Nat.not_lt.mpr fits]
      have prepared := prepare_init budget allocator source buffer values .scratch ⟨source, values, none⟩ before
      cases preparedCall : prepare budget allocator source buffer values (preparedToken .scratch source buffer)
          ⟨before, ⟨source, values, none⟩, none, none⟩ with
      | mk result after =>
        simp only [preparedToken, own, Bool.false_eq_true, ↓reduceIte] at preparedCall
        simp only [show (NormalizationOwnership.Origin.scratch == .allocation) = false from rfl] at prepared
        cases result <;>
          simpa [initialized, NormalizationOwnership.Code.initPrepared, NormalizationOwnership.Code.initWith,
            Normalization.init, primitives, initial, preparedToken, needed, choice, own, Nat.not_lt.mpr fits,
            preparedCall, Except.map, Except.mapError] using prepared
    · have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = false := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      have own : normalizationOwnershipCode.ownTemporary.test source.length buffer.length = true := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, Nat.lt_of_not_ge fits]
      cases reserved : Normalization.reserve external allocator values before with
      | mk result selected =>
        cases result with
        | error failure =>
          cases failure <;>
            simp [initialized, NormalizationOwnership.Code.initPrepared, NormalizationOwnership.Code.initWith,
              Normalization.init, primitives, initial, allocate, failed, observeInit, InitAligned, needed, choice, reserved]
        | ok slice =>
          have prepared := prepare_init budget allocator source buffer values .allocation ⟨view slice, values, some slice⟩ selected
          cases preparedCall : prepare budget allocator source buffer values (preparedToken .allocation source buffer)
              ⟨selected, ⟨view slice, values, some slice⟩, none, none⟩ with
          | mk result after =>
            simp only [preparedToken, own, ↓reduceIte] at preparedCall
            simp only [show (NormalizationOwnership.Origin.allocation == .allocation) = true from rfl] at prepared
            cases result <;>
              simpa [initialized, NormalizationOwnership.Code.initPrepared, NormalizationOwnership.Code.initWith,
                Normalization.init, primitives, initial, allocate, preparedToken, needed, choice, own, reserved,
                preparedCall, Except.map, Except.mapError] using prepared

theorem init_eq (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session σ) :
    let execution := initialized external budget allocator commutative source buffer values before
    let native := Normalization.init normalizationOwnershipCode external budget allocator commutative source buffer values before
    (observeInit execution.1 execution.2, execution.2.session) = (some native.1, native.2) :=
  (init_spec external budget allocator commutative source buffer values before).1

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
