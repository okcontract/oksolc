/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparationFailure
import Compiler.Extraction.InternerInsertionTransferredFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The three permitted allocation failures during duplicated preparation,
observed at their actual reached sessions. This proposition classifies existing
callbacks; it supplies no cleanup result, native frame or alternate executor. -/
inductive PreparationOOM (ops : Operations σ) (allocator : Nat)
    (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (before : Session (Publication.Effects σ)) : Prop where
  | duplicate (failed : Session (Publication.Effects σ))
      (called : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
        ⟨view normalized, normalized.items, none⟩ before = (.error .outOfMemory, failed))
  | create (operands : ArgumentSlice) (remaining : Handle) (duplicated failed : Session (Publication.Effects σ))
      (taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
        ⟨view normalized, normalized.items, none⟩ before = (.ok (operands, remaining), duplicated))
      (called : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.error .outOfMemory, failed))
  | clone (operands : ArgumentSlice) (remaining : Handle) (object : Nat)
      (duplicated allocated failed : Session (Publication.Effects σ))
      (taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
        ⟨view normalized, normalized.items, none⟩ before = (.ok (operands, remaining), duplicated))
      (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
      (called : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.error .outOfMemory, failed))

/-- Every failed preparation executes its existing source cleanup and retains
the same reached key table and old allocations outside the private owner. The
three ownership prefixes share this conclusion without choosing fixture values,
allocator identities, callback budgets or a pre-child normalization origin. -/
theorem preparation_oom_execution (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (safety : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    (valid : Valid before.memory) (live : SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : Admitted ops.arguments) (room : rows.length < 2 ^ 32 - 1)
    (failed : PreparationOOM ops allocator input normalized before.memory) :
    ∃ after closed,
      execution ops allocate safety allocator container source address meaning input key normalized true rows before growth =
        ((.ok (some .allocationFailure), closed), after) ∧
      closed.appended = false ∧ closed.published = false ∧
      Valid (memory after) ∧ Consumed normalized (memory after) ∧
      PrivateFrame normalized before.memory (memory after) := by
  cases failed with
  | duplicate failed called =>
    obtain ⟨after, ran, finalValid, consumed, _, _, _, _, _, _, frame⟩ :=
      duplicate_oom_execution ops allocate safety allocator container source address meaning input key normalized rows before
        failed valid live admitted room called growth
    exact ⟨after, _, ran, rfl, rfl, finalValid, consumed, frame⟩
  | create operands remaining duplicated failed taken called =>
    obtain ⟨_, after, ran, finalValid, _, consumed, _, _, _, _, _, _, _, _, frame⟩ :=
      create_oom_execution ops allocate safety allocator container source address meaning input key normalized operands rows before
        duplicated failed remaining valid live admitted room taken called growth
    exact ⟨after, _, ran, rfl, rfl, finalValid, consumed, frame⟩
  | clone operands remaining object duplicated allocated failed taken created called =>
    obtain ⟨_, _, after, ran, finalValid, _, consumed, _, _, _, _, _, _, _, _, _, _, _, _, frame⟩ :=
      clone_oom_execution ops allocate safety allocator container object source address meaning input key normalized operands rows before
        duplicated allocated failed remaining valid live represented admitted room taken created called growth
    exact ⟨after, _, ran, rfl, rfl, finalValid, consumed, frame⟩

/-- Nondeterministic insertion transfers the existing arguments directly. Its
preparation observations contain creation and cloning, with no duplicate call. -/
inductive TransferredPreparationOOM (ops : Operations σ) (allocator : Nat)
    (input : AssemblyClone.NativeFields.ItemValue) (before : Session (Publication.Effects σ)) : Prop where
  | create (failed : Session (Publication.Effects σ))
      (called : AssemblyItem.Creation.create (observe ops.create) allocator input.item before = (.error .outOfMemory, failed))
  | clone (object : Nat) (allocated failed : Session (Publication.Effects σ))
      (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item before = (.ok object, allocated))
      (called : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.error .outOfMemory, failed))

/-- Select the actual source preparation branch, keeping the two distinct
ownership protocols and their observed allocation failures explicit. -/
def PreparationOOMAt (ops : Operations σ) (allocator : Nat)
    (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (deterministic : Bool) (before : Session (Publication.Effects σ)) : Prop :=
  if deterministic then PreparationOOM ops allocator input normalized before
  else TransferredPreparationOOM ops allocator input before

/-- Both preparation branches derive the same private native frame. Transferred
failure frees one argument owner; duplicated failure retains its two-owner
cleanup. All paths execute the existing source program and cleanup proofs. -/
theorem preparation_oom_execution_at (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (safety : Bool) (allocator container : Nat)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    (valid : Valid before.memory) (live : SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : Admitted ops.arguments) (room : rows.length < 2 ^ 32 - 1)
    (failed : PreparationOOMAt ops allocator input normalized deterministic before.memory) :
    ∃ after closed,
      execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth =
        ((.ok (some .allocationFailure), closed), after) ∧
      closed.appended = false ∧ closed.published = false ∧
      Valid (memory after) ∧ Consumed normalized (memory after) ∧
      PrivateFrame normalized before.memory (memory after) := by
  cases deterministic with
  | true =>
    exact preparation_oom_execution ops allocate growth safety allocator container source address meaning input key normalized
      rows before valid live represented admitted room failed
  | false =>
    cases failed with
    | create history called =>
      obtain ⟨after, ran, post, _⟩ := transferred_create_oom_execution ops allocate safety allocator container
        source address meaning input key normalized before rows growth valid live history room called
      exact ⟨after, _, ran, rfl, rfl, post.valid, post.consumed, post.frame⟩
    | clone object allocated history created called =>
      obtain ⟨_, after, ran, post, _, _, _, _⟩ := transferred_clone_oom_execution ops allocate safety allocator container
        source address meaning input key normalized before rows growth valid live represented object allocated history room created called
      exact ⟨after, _, ran, rfl, rfl, post.valid, post.consumed, post.frame⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
