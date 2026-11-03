/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionSharedRecursionEffects
import Compiler.Extraction.InternerInsertionControlEffectsTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.SharedEffectTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Normalization.HostTrace

def operations (host : External σ) (probe : OwnedKeys.Physical.Probe σ) : Operations σ :=
  { ItemEffectTests.operations (fun _ before => (none, before.effects)) (fun _ before => (none, before.effects)) with
    arguments := host, probe }

/-- Reuse publication's reached world and normalization's actual memory. The
42 dummy rows supply only the publication ID; this callback fixture makes no
claim about a native backing array or a complete insertion. -/
def rows := List.replicate 42 ({ item := ⟨2, none, 0⟩, otherValue := 0, itemAddress := 0 } : Storage.Cell)
def graph (_ : Storage.State) (_ : Frame σ) := Publication.Tests.publicationWorld.graph

def calls (host : External σ) (probe : OwnedKeys.Physical.Probe σ) (normalized : ArgumentSlice) :=
  callbacks (operations host probe) (fun _ _ _ effects => (none, effects)) false 7 0 Publication.Tests.source
    AssemblyItem.Creation.NativeFields.Tests.source AssemblyItem.Creation.NativeFields.Tests.input
    Publication.Tests.forceKey normalized rows 0 graph

def frame (session : Session (Publication.Effects σ)) : Frame σ := ⟨⟨⟨⟨session, false⟩, none⟩, none⟩, none⟩
def capture (before : Frame Nat) := before.mapEffects (fun effects => (⟨effects, []⟩ : Recorded Nat))
def initial := capture (frame ⟨Compiler.Extraction.Memory.Arguments.Tests.logical,
  Compiler.Extraction.Memory.Arguments.Tests.bytes, ⟨fun _ => none, 5⟩⟩)

theorem attempts_erase (host : External Nat) (probe : OwnedKeys.Physical.Probe Nat) (normalized : ArgumentSlice)
    (site : Storage.Allocation) (shared : site = .arguments ∨ site = .publish) (owner : Storage.State) :
    Effect.Transport (State.mapEffects Recorded.effects)
      ((calls (record host) (Publication.Recording.recordProbe probe) normalized).attempt site owner)
      ((calls host probe normalized).attempt site owner) :=
  shared_attempt_transport (left := operations (record host) (Publication.Recording.recordProbe probe))
    (right := operations host probe) (HostTrace.transport host) _ _ false 7 0 Publication.Tests.source
    AssemblyItem.Creation.NativeFields.Tests.source AssemblyItem.Creation.NativeFields.Tests.input
    Publication.Tests.forceKey normalized rows 0 graph graph none none
    (Publication.Recording.probe_transport probe) (fun _ _ => rfl) site shared owner

theorem releases_erase (host : External Nat) (probe : OwnedKeys.Physical.Probe Nat) (normalized : ArgumentSlice)
    (action : Storage.Release) (shared : action = .normalized ∨ action = .arguments) (owner : Storage.State) :
    Effect.Transport (State.mapEffects Recorded.effects)
      ((calls (record host) (Publication.Recording.recordProbe probe) normalized).release action owner)
      ((calls host probe normalized).release action owner) :=
  shared_release_transport (HostTrace.transport host) _ _ false 7 0 _ _ _ _ normalized _ _ _ _ none none action shared owner

def duplicate (host := Normalization.Tests.success) (normalized := Compiler.Extraction.Memory.Arguments.Tests.first) (before := initial) :=
  (calls (record host) (Publication.Recording.recordProbe (Publication.Tests.attempt false)) normalized).attempt .arguments {} before

theorem duplicate_success : duplicate.1 = .ok true ∧ duplicate.2.duplicate = some ⟨3, Normalization.Tests.items⟩ ∧
    (memory duplicate.2).effects.allocator = (⟨17, [.allocate .duplicate 12 (some 60)]⟩ : Recorded Nat) :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem duplicate_refusal : (duplicate (Normalization.Tests.external (fun _ => true))).1 = .ok false ∧
    (duplicate (Normalization.Tests.external (fun _ => true))).2.duplicate = none ∧
    (memory (duplicate (Normalization.Tests.external (fun _ => true))).2).effects.allocator =
      (⟨17, [.allocate .duplicate 12 none]⟩ : Recorded Nat) := ⟨by rfl', by rfl', by rfl'⟩

theorem incoming_ownership_rejected : duplicate Normalization.Tests.success ⟨1, [99]⟩ =
    (.error (.base .incomingOwnership), initial) := by rfl'

theorem empty_arguments_skip_host : (duplicate Normalization.Tests.success ⟨999, []⟩).1 = .ok true ∧
    (memory (duplicate Normalization.Tests.success ⟨999, []⟩).2).effects.allocator.events = [] := ⟨by rfl', by rfl'⟩

theorem invalid_allocation_retained : (duplicate HostTrace.Tests.invalid).1 =
    .error (.base (.arguments (.allocation (.memory .memoryValidity)))) ∧
    (memory (duplicate HostTrace.Tests.invalid).2).effects.allocator.events = [.allocate .duplicate 12 (some 0)] :=
  ⟨by rfl', by rfl'⟩

def partialCopy := duplicate Normalization.Tests.success Compiler.Extraction.Memory.Arguments.Tests.first
  (withMemory initial { memory initial with memory := Duplication.Tests.incomplete })

theorem partial_copy_retained : partialCopy.1 = .error (.base (.arguments (.allocation (.memory .uninitialized)))) ∧
    partialCopy.2.duplicate = none ∧
    (memory partialCopy.2).effects.allocator.events = [.allocate .duplicate 12 (some 56)] ∧
    Compiler.ZigAir.Memory.load (memory partialCopy.2).memory ((⟨3, 0, 3⟩ : View).pointer 0) = .ok (number 3) :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

def cleanup := (calls (record Normalization.Tests.success) (Publication.Recording.recordProbe (Publication.Tests.attempt false))
  Compiler.Extraction.Memory.Arguments.Tests.first).release .arguments {} duplicate.2

theorem duplicate_cleanup : cleanup.1 = .ok () ∧
    (memory cleanup.2).memory.heap.lookup 3 = none ∧
    (memory cleanup.2).effects.allocator =
      (⟨120, [.allocate .duplicate 12 (some 60), .free ⟨3, Normalization.Tests.items⟩]⟩ : Recorded Nat) :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem missing_arguments_skips_host :
    (calls (record Normalization.Tests.success) (Publication.Recording.recordProbe (Publication.Tests.attempt false))
      Compiler.Extraction.Memory.Arguments.Tests.first).release .arguments {} initial = (.error (.base .missingArguments), initial) := by rfl'

theorem alias_selects_normalized (before : Frame (Recorded Nat)) :
    (calls (record Normalization.Tests.success) (Publication.Recording.recordProbe (Publication.Tests.attempt false))
      Compiler.Extraction.Memory.Arguments.Tests.first).release .arguments { aliasesNormalized := true } before =
    (calls (record Normalization.Tests.success) (Publication.Recording.recordProbe (Publication.Tests.attempt false))
      Compiler.Extraction.Memory.Arguments.Tests.first).release .normalized {} before := rfl

def published (fail := false) (session := Publication.Tests.publicationWorld.memory) (normalized : ArgumentSlice := ⟨8, [1, 3]⟩) :=
  (calls (record Publication.Tests.host) (Publication.Recording.recordProbe (Publication.Tests.attempt fail)) normalized).attempt
    .publish {} (capture (frame session))

theorem replacement_success : published.1 = .ok true ∧
    (memory published.2).effects.keys Publication.Tests.forceKey = some ⟨8, 42⟩ ∧
    (memory published.2).effects.allocator =
      (⟨125, [.publicationProbe Publication.Tests.forceKey true, .free ⟨5, [1, 3]⟩]⟩ : Recorded Nat) :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem publication_refusal : (published true).1 = .ok false ∧
    (memory (published true).2).effects.keys Publication.Tests.forceKey = some ⟨5, 42⟩ ∧
    (memory (published true).2).effects.allocator =
      (⟨23, [.publicationProbe Publication.Tests.forceKey false]⟩ : Recorded Nat) := ⟨by rfl', by rfl', by rfl'⟩

def releaseFault := published false { Publication.Tests.publicationWorld.memory with
  memory := Compiler.ZigAir.Memory.erase Publication.Tests.publicationWorld.memory.memory 5 }

theorem release_fault_retains_probe : releaseFault.1 = .error (.base (.publication (.memory (.release (.memory .unallocated))))) ∧
    (memory releaseFault.2).effects.keys Publication.Tests.forceKey = some ⟨5, 42⟩ ∧
    (memory releaseFault.2).effects.allocator =
      (⟨23, [.publicationProbe Publication.Tests.forceKey true]⟩ : Recorded Nat) := ⟨by rfl', by rfl', by rfl'⟩

theorem admission_skips_probe : (published false Publication.Tests.publicationWorld.memory ⟨8, []⟩).1 =
    .error (.base (.publication (.language .safetyFault))) ∧
    (memory (published false Publication.Tests.publicationWorld.memory ⟨8, []⟩).2).effects.allocator.events = [] :=
  ⟨by rfl', by rfl'⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.SharedEffectTests
