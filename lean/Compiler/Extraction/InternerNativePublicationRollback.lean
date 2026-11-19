/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeUnrelocatedRollback
import Compiler.Extraction.InternerNativeGrowingRollback
import Compiler.Extraction.InternerUnrelocatedPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache RepresentativeArray

/-- Source-observed publication refusals with derived native completion. No
parent law, final frame or final logical correspondence is part of the union. -/
def RefusedObservation (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (growth : Option (Growth.Registered.Callbacks σ)) (world : World (Publication.Effects σ)) : Prop :=
  FirstPublication ops allocate safety allocator owner meaning input key normalized false world ∨
  SparePublication ops allocate safety allocator owner meaning input key normalized false world ∨
  RelocatedPublication ops allocate safety allocator owner meaning input key normalized growth false world

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- One completion consumed by the general step for first, spare and no-remap
relocated publication refusal. The reached capacity selects only the append
connection; source preparation, rollback and native graph framing are shared. -/
theorem CallFrame.publication_rollback_frame {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (refused : Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key normalized growth world) :
    RollbackReturn safety allocator owner rows normalized world
      (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world) := by
  rcases refused with first | spare | growing
  · obtain ⟨capacityRead, operands, remaining, duplicated, object, allocated, copied, middle,
      base, allocationEffects, probeEffects, duplicateCall, createCall, cloneCall, backing, response, unlocked⟩ := first
    obtain ⟨added, data, capacity, facts, _⟩ := frame.1.1
    have zero : capacity = 0 := by
      have equal := (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
      have zero : (capacity : Int) = 0 := by
        simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq,
          Compiler.ZigAir.Scalar.Value.int.injEq, true_and] using equal
      omega
    have empty : rows ++ added = [] := List.eq_nil_of_length_eq_zero (by have bound := facts.bounded; omega)
    have projected : world.graph.representatives.getD [] = [] := by simp only [facts.projected, Option.getD_some, empty]
    apply frame.unrelocated_rollback_frame ops allocate growth meaning key admitted aligned room 0 object operands remaining
      duplicated allocated middle copied capacityRead (Or.inl rfl)
      (fun _ => ⟨base, allocationEffects, backing, unlocked⟩) duplicateCall createCall cloneCall probeEffects
    simpa only [projected] using response
  · obtain ⟨capacity, capacityRead, spare, operands, remaining, duplicated, object, allocated, copied, middle,
      probeEffects, duplicateCall, createCall, cloneCall, response⟩ := spare
    exact frame.unrelocated_rollback_frame ops allocate growth meaning key admitted aligned room capacity object operands remaining
      duplicated allocated middle copied capacityRead (Or.inr spare) (by intro zero; omega)
      duplicateCall createCall cloneCall probeEffects response
  · exact frame.growing_rollback_frame ops allocate growth meaning key admitted aligned room growing

/-- The original graph-only interface is a projection of the shared rollback
completion. Its read-coherence premise is used only for exact logical equality. -/
theorem CallFrame.publication_rollback {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []))
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (refused : Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key normalized growth world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    actual.1 = .error (.language .outOfMemory) ∧
      (∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity actual.2 (rows ++ added)) ∧
      actual.2.graph = world.graph ∧ Consumed normalized actual.2.memory := by
  exact (frame.publication_rollback_frame ops allocate growth meaning key admitted aligned room refused).graph reads

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
