/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendEffects
import Compiler.Extraction.AssemblyPreparationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.HostTrace
open RepresentativeArray

/-- Private-effect ports use the same response/history recorder as session
ports. Their evaluated request is recorded exactly once per actual host call. -/
def recordPrivate (event : α → β → Event) (host : α → σ → β × σ) : α → Recorded σ → β × Recorded σ :=
  fun argument before => recordResult (event argument) (host argument before.effects) before

theorem private_observation (event : α → β → Event) (host : α → σ → β × σ) (argument : α) (before : Recorded σ) :
    let original := host argument before.effects
    let called := recordPrivate event host argument before
    called.1 = original.1 ∧ called.2.effects = original.2 ∧ called.2.events = before.events ++ [event argument original.1] := ⟨rfl, rfl, rfl⟩

theorem private_prefix (event : α → β → Event) (host : α → σ → β × σ) (argument : α)
    (leading : List Event) (before : Recorded σ) :
    recordPrivate event host argument (prepend leading before) =
      ((recordPrivate event host argument before).1, prepend leading (recordPrivate event host argument before).2) := by
  simp [recordPrivate, recordResult, prepend, List.append_assoc]

def recordBacking (host : Backing.Registry.Allocate σ) : Backing.Registry.Allocate (Recorded σ) :=
  fun allocator bytes alignment effects => recordPrivate
    (fun (request : Nat × Nat × Nat) response => .backingAllocate request.1 request.2.1 request.2.2 response)
    (fun request before => host request.1 request.2.1 request.2.2 before) (allocator, bytes, alignment) effects

def recordBackingFree (host : Backing.Release.External σ) : Backing.Release.External (Recorded σ) :=
  fun allocator base bytes alignment effects => (recordPrivate
    (fun (request : Nat × Nat × Nat × Nat) (_ : Unit) => .backingFree request.1 request.2.1 request.2.2.1 request.2.2.2)
    (fun request before => ((), host request.1 request.2.1 request.2.2.1 request.2.2.2 before))
    (allocator, base, bytes, alignment) effects).2

def recordGrowth (calls : Growth.Registered.Callbacks σ) : Growth.Registered.Callbacks (Recorded σ) :=
  ⟨calls.remap, recordBackingFree calls.release⟩

theorem backing_transport (host : Backing.Registry.Allocate σ) :
    Backing.Registry.Allocate.Transport Recorded.effects (recordBacking host) host := fun _ _ _ _ => rfl

theorem backing_free_transport (host : Backing.Release.External σ) :
    Backing.Release.External.Transport Recorded.effects (recordBackingFree host) host := fun _ _ _ _ _ => rfl

theorem growth_transport (calls : Growth.Registered.Callbacks σ) :
    Growth.Registered.Callbacks.Transport Recorded.effects (recordGrowth calls) calls := ⟨rfl, backing_free_transport calls.release⟩

theorem optional_growth_transport (calls : Option (Growth.Registered.Callbacks σ)) :
    Growth.Registered.Callbacks.OptionalTransport Recorded.effects (calls.map recordGrowth) calls := by
  cases calls with
  | none => trivial
  | some calls => exact growth_transport calls

theorem backing_prefix (host : Backing.Registry.Allocate σ) (leading : List Event) :
    Backing.Registry.Allocate.Transport (prepend leading) (recordBacking host) (recordBacking host) := by
  intro allocator bytes alignment effects
  exact private_prefix _ _ (allocator, bytes, alignment) leading effects

theorem backing_free_prefix (host : Backing.Release.External σ) (leading : List Event) :
    Backing.Release.External.Transport (prepend leading) (recordBackingFree host) (recordBackingFree host) := by
  intro allocator base bytes alignment effects
  exact congrArg Prod.snd (private_prefix _ _ (allocator, base, bytes, alignment) leading effects)

theorem growth_prefix (calls : Growth.Registered.Callbacks σ) (leading : List Event) :
    Growth.Registered.Callbacks.Transport (prepend leading) (recordGrowth calls) (recordGrowth calls) :=
  ⟨rfl, backing_free_prefix calls.release leading⟩

theorem optional_growth_prefix (calls : Option (Growth.Registered.Callbacks σ)) (leading : List Event) :
    Growth.Registered.Callbacks.OptionalTransport (prepend leading) (calls.map recordGrowth) (calls.map recordGrowth) := by
  cases calls with
  | none => trivial
  | some calls => exact growth_prefix calls leading

/-- Recording does not change captured remap identity, shape of the selected
growth route, or any native append result, local, heap or publication key. -/
theorem append_erases (host : Backing.Registry.Allocate σ) (calls : Option (Growth.Registered.Callbacks σ))
    (runtimeSafety : Bool) (allocator container : Nat) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Cache.Key) (normalized : Storage.ArgumentSlice) :
    OwnedCall.Insertion.Native.AppendTransport Recorded.effects (recordBacking host) host runtimeSafety allocator container
      input key normalized (calls.map recordGrowth) calls :=
  OwnedCall.Insertion.Native.append_transport (backing_transport host) (optional_growth_transport calls) runtimeSafety allocator container input key normalized

end Compiler.Extraction.Memory.Arguments.Normalization.HostTrace
