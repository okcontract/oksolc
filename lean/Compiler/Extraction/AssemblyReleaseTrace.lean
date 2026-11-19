/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyReleaseEffects
import Compiler.Extraction.AssemblyPreparationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.HostTrace

/-- A release is a host request with a unit result. Reuse the same recorder so
each actual call retains its reached effects, descriptor and prior history. -/
def recordRelease (event : α → Event) (host : α → Session σ → σ) : α → Session (Recorded σ) → Recorded σ :=
  fun argument before => (recordRequest (fun argument (_ : Unit) => event argument)
    (fun argument state => ((), host argument state)) argument before).2

theorem release_request_observation (event : α → Event) (host : α → Session σ → σ)
    (argument : α) (before : Session (Recorded σ)) :
    let called := recordRelease event host argument before
    called.effects = host argument (before.mapEffects Recorded.effects) ∧
      called.events = before.effects.events ++ [event argument] := ⟨rfl, rfl⟩

theorem release_request_transport (event : α → Event) (host : α → Session σ → σ) :
    HostReleaseTransport Recorded.effects (recordRelease event host) host := by
  intro argument before
  exact congrArg Prod.snd (request_transport (fun argument (_ : Unit) => event argument)
    (fun argument state => ((), host argument state)) argument before)

theorem release_request_prefix (event : α → Event) (host : α → Session σ → σ) (leading : List Event) :
    HostReleaseTransport (prepend leading) (recordRelease event host) (recordRelease event host) := by
  intro argument before
  exact congrArg Prod.snd (request_prefix (fun argument (_ : Unit) => event argument)
    (fun argument state => ((), host argument state)) leading argument before)

def recordBytes (host : AssemblyItemDeinit.Release σ) : AssemblyItemDeinit.Release (Recorded σ) :=
  recordRelease (fun slice => .payloadFree slice.address slice.length slice.offset) host

def recordObject (host : AssemblyItem.Release σ) : AssemblyItem.Release (Recorded σ) :=
  recordRelease Event.itemFree host

theorem bytes_transport (host : AssemblyItemDeinit.Release σ) :
    HostReleaseTransport Recorded.effects (recordBytes host) host := release_request_transport _ host

theorem object_transport (host : AssemblyItem.Release σ) :
    HostReleaseTransport Recorded.effects (recordObject host) host := release_request_transport _ host

theorem native_item_erases (host : AssemblyItemDeinit.Release σ) (allocator : Nat)
    (object : Compiler.ZigAir.Memory.Address) (before : Session (Recorded σ)) :
    AssemblyItemDeinit.Native.run host allocator object (before.mapEffects Recorded.effects) =
      ((AssemblyItemDeinit.Native.run (recordBytes host) allocator object before).1,
       (AssemblyItemDeinit.Native.run (recordBytes host) allocator object before).2.mapEffects Recorded.effects) :=
  AssemblyItemDeinit.Native.run_transport (bytes_transport host) allocator object before

theorem expression_erases (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (descriptor : Compiler.ZigAir.Memory.Address) (before : Session (Recorded σ)) :
    ExpressionDeinit.Native.run bytes objects external allocator descriptor (before.mapEffects Recorded.effects) =
      ((ExpressionDeinit.Native.run (recordBytes bytes) (recordObject objects) (record external) allocator descriptor before).1,
       (ExpressionDeinit.Native.run (recordBytes bytes) (recordObject objects) (record external) allocator descriptor before).2.mapEffects Recorded.effects) :=
  ExpressionDeinit.Native.run_transport (bytes_transport bytes) (object_transport objects) (transport external) allocator descriptor before

theorem expression_prefix (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (descriptor : Compiler.ZigAir.Memory.Address) (leading : List Event) (before : Session (Recorded σ)) :
    ExpressionDeinit.Native.run (recordBytes bytes) (recordObject objects) (record external) allocator descriptor
        (before.mapEffects (prepend leading)) =
      ((ExpressionDeinit.Native.run (recordBytes bytes) (recordObject objects) (record external) allocator descriptor before).1,
       (ExpressionDeinit.Native.run (recordBytes bytes) (recordObject objects) (record external) allocator descriptor before).2.mapEffects (prepend leading)) :=
  ExpressionDeinit.Native.run_transport (release_request_prefix _ bytes leading) (release_request_prefix _ objects leading)
    (prefix_transport external leading) allocator descriptor before

end Compiler.Extraction.Memory.Arguments.Normalization.HostTrace
