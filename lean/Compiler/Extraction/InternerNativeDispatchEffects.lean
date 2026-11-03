/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeRecursion
import Compiler.Extraction.InternerPhysicalDispatchEffects
import Compiler.Extraction.InternerPublicationHostTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Erasure keeps the reached typed memory. The native load, its bounds guard
and every memory fault therefore agree, independently of the annotation. -/
theorem operand_erases (project : σ → τ) (source : ArgumentSlice) (index : Nat) (annotation : NodeId) :
    Effect.Transport (World.mapEffects project)
      (operand source index annotation) (operand source index annotation) := by
  intro before
  unfold operand ShiftInput.operand
  simp only [World.mapEffects, Session.mapEffects]
  split
  · cases TemporaryMemory.readId before.memory.memory (view source) index <;> rfl
  · rfl

theorem query_erases (project : σ → τ) (owner : Nat)
    (action : Nested.Reads → Except ReadError α) :
    Effect.Transport (World.mapEffects project) (NativeReads.query owner action) (NativeReads.query owner action) := by
  intro before
  exact (Recursive.erasing project).read (action (NativeReads.reads owner before.memory.memory)) before

/-- Actual native dispatch transports every child field under the proper-child
erasure hypothesis. Snapshot equivalence is derived by the existing timing proof;
indexed operands still read reached memory at their actual source positions. -/
theorem dispatcher_erases (project : σ → τ) (leftBase : PairInput.Context σ) (rightBase : PairInput.Context τ)
    (owner usizeBits : Nat) {left : Constructors σ} {right : Constructors τ}
    (children : (Recursive.erasing project).Constructors left right)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (owned : ArgumentSlice) :
    Effect.Transport (World.mapEffects project)
      (((context leftBase owner usizeBits left debug).primitives source address native).simplify key owned)
      (((context rightBase owner usizeBits right debug).primitives source address native).simplify key owned) := by
  intro before
  simp only [dispatcher_snapshot]
  exact (Recursive.erasing project).simplify_operands children ⟨operand_erases project⟩
    (NativeReads.reads owner before.memory.memory) usizeBits key.instruction key.arguments debug owned.address before

/-- The recursion base retains the original nonordinary exhaustion outcome and
the exact input world; it is not an allocation refusal. -/
theorem exhausted_erases (project : σ → τ) :
    (Recursive.erasing project).Constructors (exhausted (σ := σ)) (exhausted (σ := τ)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
   fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

open Publication Normalization.HostTrace

/-- Consume native dispatch and derived publication erasure together in the
same caller. The remaining proper-child and insertion transports are explicit;
this does not assert their instrumentation or complete invocation coverage. -/
theorem recorded_find_erases (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (budget allocator : Nat) (source buffer : View)
    (leftBase : PairInput.Context (Effects (Recorded σ))) (rightBase : PairInput.Context (Effects σ))
    (owner usizeBits : Nat) {left : Constructors (Effects (Recorded σ))} {right : Constructors (Effects σ)}
    (children : (Recursive.erasing (Effects.mapAllocator Recorded.effects)).Constructors left right)
    (debug : AssemblyItem.Fields.Values) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue)
    (insert : ∀ key slice deterministic, Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      ((leftBase.primitives source address native).insert key slice deterministic)
      ((rightBase.primitives source address native).insert key slice deterministic))
    (queries : Caller.Queries) (request : Interner.Request) (before : World (Effects (Recorded σ))) :
    Caller.find (external host) budget allocator
        (callbacks hostProbe host allocator source ((context rightBase owner usizeBits right debug).primitives source address native))
        queries source buffer request (before.mapEffects (Effects.mapAllocator Recorded.effects)) =
      ((Caller.find (external (record host)) budget allocator
          (callbacks (Recording.recordProbe hostProbe) (record host) allocator source
            ((context leftBase owner usizeBits left debug).primitives source address native))
          queries source buffer request before).1,
       (Caller.find (external (record host)) budget allocator
          (callbacks (Recording.recordProbe hostProbe) (record host) allocator source
            ((context leftBase owner usizeBits left debug).primitives source address native))
          queries source buffer request before).2.mapEffects (Effects.mapAllocator Recorded.effects)) :=
  Recording.find_erases hostProbe host budget allocator source buffer
    (dispatcher_erases (Effects.mapAllocator Recorded.effects) leftBase rightBase owner usizeBits children debug source address native)
    insert queries request before

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
