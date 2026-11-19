/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (request : Interner.Request)

/-- Transport the existing full miss through an actual outer return that
preserves its scoped/protocol observation. This changes the complete captured
native return, so an outer cleanup mark cannot disappear from the contract. -/
theorem prepared_miss_map (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (action : List ProtocolEvent → Except Fault NodeId × Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (wrapped : List ProtocolEvent → Except Fault NodeId × Recorded τ)
    (returned : (Except Fault NodeId × Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))) →
      Except Fault NodeId × Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (after : (Except Fault NodeId × Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))) →
      Except Fault NodeId × Recorded τ)
    (preserves : ∀ ran, outcome (after ran) = outcome ran)
    (forwarded : ∀ leading, wrapped leading = after (action leading))
    (checked : PreparedMiss ops allocate safety owner meaning base growth usizeBits children observations debug source request before action returned) :
    PreparedMiss ops allocate safety owner meaning base growth usizeBits children observations debug source request before
      wrapped (fun ran => after (returned ran)) := by
  intro constructed address domain typed made room admitted leading other read sequence
  obtain ⟨stack, allocated, initial⟩ := checked constructed address domain typed made room admitted leading other read sequence
  refine ⟨stack, allocated, ?_⟩
  intro values prepared called key deterministic commutative decoded initialized transferred classified keyed absent
  intro buffer start init
  obtain ⟨lookup, captured, projected⟩ := initial values prepared called key deterministic commutative
    decoded initialized transferred classified keyed absent
  refine ⟨lookup, captured, ?_⟩
  intro handle taken missLeading
  obtain ⟨slice, remaining, locals, lifetime, contents, word, projected⟩ := projected
  refine ⟨slice, remaining, locals, lifetime, contents, word, ?_⟩
  intro model seed predicate rows initial frame coupled capacityQuery classificationQuery trailing mismatch
  intro child observedChildren nativeInput p ports middle observed events r logicalModel entry body finished logical actual completed
  have reached := projected model seed predicate rows initial frame coupled capacityQuery classificationQuery trailing mismatch completed
  exact ⟨(congrArg outcome (forwarded leading)).trans ((preserves _).trans reached.1),
    (forwarded leading).trans (congrArg after reached.2)⟩

/-- Literal argument preparation derives the reached input contract. Its
empty route has no argument allocation; a nonempty route retires the original
argument mark after the shared item/scratch/caller return. -/
theorem literal_miss_traced (opcode : Opcode) (values : List NodeId)
    (before prepared : ChildTrace.TracedWorld σ ProtocolEvent) (source : View)
    (valid : Valid before.memory) (ran : Arguments.prepare values before = (.ok source, prepared)) :
    PreparedMiss ops allocate safety owner meaning base growth usizeBits children observations debug source
      (Interner.constructorCode.operationRequest opcode values) prepared
      (literal (NativeRecursion.context (callerContext ops allocate safety owner meaning base growth) owner usizeBits
        (ChildTrace.constructors children observations) debug)
        (Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits
          (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug) opcode values debug before)
      (fun result => if values.isEmpty then result else retire before.memory.memory.nextId result) := by
  have ready := Arguments.prepare_success values before prepared source valid ran
  have inner := item_miss_traced ops allocate safety owner meaning base growth usizeBits children observations debug source
    (Interner.constructorCode.operationRequest opcode values) prepared ready.good
  exact prepared_miss_map ops allocate safety owner meaning base growth usizeBits children observations debug source
    (Interner.constructorCode.operationRequest opcode values) prepared _ _ id
    (fun result => if values.isEmpty then result else retire before.memory.memory.nextId result)
    (by intro result; split; rfl; exact retire_outcome _ _)
    (by intro leading; simp only [literal, ran]) inner

/-- Named-local construction derives the same prepared input from the actual
copy and optional overwrite. It consumes exactly the same full miss theorem,
then returns through the original local mark. The unused slot is unrestricted. -/
theorem local_miss_traced (opcode : Opcode) (source target : View) (left right repeated : NodeId)
    (selected : Nat) (first : Bool) (before prepared : ChildTrace.TracedWorld σ ProtocolEvent)
    (good : Good source [left, right] before) (inside : first = true → selected < 2)
    (ran : LocalArguments.zigLocal source selected repeated first before = (.ok target, prepared)) :
    PreparedMiss ops allocate safety owner meaning base growth usizeBits children observations debug target
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) prepared
      (namedLocal (NativeRecursion.context (callerContext ops allocate safety owner meaning base growth) owner usizeBits
        (ChildTrace.constructors children observations) debug)
        (Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits
          (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug)
        opcode source left right repeated selected first debug before)
      (retire before.memory.memory.nextId) := by
  have ready := ViewInput.local_input_optional source target left right repeated selected first before prepared good inside ran
  have inner := item_miss_traced ops allocate safety owner meaning base growth usizeBits children observations debug target
    (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) prepared ready.good
  exact prepared_miss_map ops allocate safety owner meaning base growth usizeBits children observations debug target
    (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) prepared _ _ id
    (retire before.memory.memory.nextId) (retire_outcome _)
    (by intro leading; simp only [namedLocal, ran]) inner

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
