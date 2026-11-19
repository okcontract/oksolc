/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointCallerReplay
import Compiler.Extraction.InternerCallerInputIdentity

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Caller.ProtocolTrace (ProtocolEvent)

/-- One entry model, fixed before normalization and key selection. Values come
from each key; the original initializer cursor is used only for nondeterministic
transfer. Sorting's private allocation identities are never guessed. -/
def inputGraphReplay (seed : Interner.Primitives) (input : AssemblyClone.NativeFields.ItemValue)
    (incoming : Nat) (meaning : Meaning) (stream : List ProtocolEvent)
    (mismatch : Insertion.Native.Fault) : Interner.Primitives :=
  { seed with
    publish := Interner.InvocationTrace.publish stream
    insert := fun key deterministic => insertionReplay input ⟨incoming, key.arguments⟩ meaning key deterministic stream mismatch }

/-- Native preparation determines all candidate inputs needed by this model.
The actual insertion checkpoint still supplies the later allocation identity. -/
theorem insertionReplay_inputs (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (incoming : Nat) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (aligned : normalized.items = key.arguments)
    (transferred : deterministic = false → normalized.address = incoming) :
    insertionReplay input normalized meaning key deterministic stream mismatch =
      insertionReplay input ⟨incoming, key.arguments⟩ meaning key deterministic stream mismatch := by
  apply congrArg (fun next : Nat × Nat → Interner.Action NodeId => insertionRead stream >>= next)
  funext ids before
  dsimp only [Insertion.Native.allocationReplay]
  rw [Insertion.Native.allocationCandidate_inputs input key normalized _ deterministic ids.1 incoming aligned transferred]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
open Compiler.Extraction.Cache

/-- Source control consults graph ports only at its actual key. This lets a
fixed entry model consume a local native miss without choosing a new model. -/
theorem scoped_ports (resources : Interner.Scoped.Resources) (first second : Interner.Primitives)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (before : Interner.Scoped.Session)
    (simplify : first.simplify key = second.simplify key)
    (publish : first.publish key = second.publish key)
    (insert : first.insert key deterministic = second.insert key deterministic) :
    Interner.findCode.controlMiss (Interner.Scoped.execution resources first) request key deterministic before =
      Interner.findCode.controlMiss (Interner.Scoped.execution resources second) request key deterministic before := by
  rw [scoped_routed resources first, scoped_routed resources second]
  dsimp only
  rw [simplify, publish, insert]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
