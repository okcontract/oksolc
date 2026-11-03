/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.InternerInsertionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.Controls
open Compiler.Extraction.Storage
open RepresentativeArray

/-- Small independent probes keep expected rejection diagnostics bounded. The
complete source-bound execution fixtures are audited and freshly replayed too. -/
def blank : Frame Nat := ⟨⟨⟨⟨⟨fun _ => none, ⟨[], 0, 0⟩, ⟨fun _ => none, 0⟩⟩, false⟩, none⟩, none⟩, none⟩
def calls := callbacks { Insertion.Tests.ops with create := fun _ before => (none, before.effects + 1) }
  (fun _ _ _ effects => (none, effects)) false 7 6 ⟨0, 0, 0⟩ ⟨0, 0⟩
  AssemblyItem.Creation.NativeFields.Tests.input ⟨1, 254, 987, [], 31⟩ ⟨0, []⟩ [] 0
  (fun _ _ => Interner.observedHeap [] (fun _ => none))

theorem creation_oom_effects : (calls.attempt .item {} blank).1 = .ok false ∧
    (memory (calls.attempt .item {} blank).2).effects.allocator = 1 := ⟨by rfl', by rfl'⟩

theorem pop_rejected : (calls.release .pop {} blank).1 = .error (.pop (.memory .unallocated)) := by rfl'

def wrongOwner : Session Unit := ⟨fun _ => some ⟨8, .representatives []⟩, ⟨[], 0, 0⟩, ()⟩
theorem owner_rejected : Append.Registered.admit 7 0 [] wrongOwner = .error .wrongAllocator := by rfl'

def header : Session Unit := ⟨fun _ => none,
  ⟨[(6, AssemblyClone.NativeFields.QueryTests.ownerCell false false)], 7, 2048⟩, ()⟩

theorem header_read : readItems header.memory (Owner.headerAddress ⟨6, 0⟩) =
    .ok (.slice itemsType ⟨7, 0⟩ 1) := by decide +kernel

theorem length_rejected :
    (Append.Registered.finish 7 6 [AssemblyClone.NativeFields.QueryTests.old]
      AssemblyClone.NativeFields.QueryTests.logical header header).1 = .error (.memory .malformed) := by rfl'

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.Controls
