/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeInsertionFailure
import Compiler.Extraction.InternerInsertionReachedFirstAllocationFailure
import Compiler.Extraction.InternerInsertionReachedGrowthAllocationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache RepresentativeArray

/-- Actual source observations for backing refusal in either ownership mode after
successful preparation. Empty storage admits either adapter with arbitrary
callbacks; nonempty storage selects the existing no-remap growth path.
Installation existence, cleanup and final native frames are derived elsewhere. -/
def BackingAllocationOOMAt (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (allocator owner : Nat) (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (deterministic : Bool) (growth : Option (Growth.Registered.Callbacks σ)) (world : World (Publication.Effects σ)) : Prop :=
  ∃ operands remaining duplicated object allocated copied middle allocationEffects,
    PreparationInput ops allocator normalized operands remaining deterministic world.memory duplicated ∧
    AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated) ∧
    AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle) ∧
    Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok () ∧
    ((readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)) ∧
      ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
        allocate allocator 160 8 installed.effects.allocator = (none, allocationEffects)) ∨
      ∃ (oldCapacity capacity context returnAddress : Nat) (freeBacking : Backing.Release.External σ),
        readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset =
          .ok (.scalar (.int false 64 oldCapacity)) ∧
        oldCapacity ≠ 0 ∧ oldCapacity < Append.nextLength (world.graph.representatives.getD []).length ∧
        capacity = Capacity.grow (Append.nextLength (world.graph.representatives.getD []).length) ∧
        capacity * 32 < Compiler.ZigAir.Memory.addressLimit ∧
        growth = some ⟨.noRemap context returnAddress, freeBacking⟩ ∧
        ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
          allocate allocator (capacity * 32) 8 installed.effects.allocator = (none, allocationEffects))


/-- Original deterministic admission, definitionally the selected source branch. -/
def BackingAllocationOOM (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (allocator owner : Nat) (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (growth : Option (Growth.Registered.Callbacks σ)) (world : World (Publication.Effects σ)) : Prop :=
  BackingAllocationOOMAt ops allocate allocator owner input normalized true growth world

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Reuse both reached backing-refusal proofs before selecting a logical graph
projection. The actual source execution supplies validity, private cleanup and
consumption for clients that need either native frames or exact correspondence. -/
theorem CallFrame.backing_oom_execution_at {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (deterministic : Bool) (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (admitted : Admitted ops.arguments)
    (failed : Insertion.Native.BackingAllocationOOMAt ops allocate allocator owner native normalized deterministic growth world) :
    ∃ after, Insertion.Native.execution ops allocate safety allocator owner source address meaning native key normalized
      deterministic (world.graph.representatives.getD []) world growth =
        ((.ok (some .allocationFailure), Insertion.Native.appendFailureState deterministic), after) ∧
      Valid (Insertion.memory after) ∧ Insertion.Native.PrivateFrame normalized world.memory (Insertion.memory after) ∧
      Consumed normalized (Insertion.memory after) := by
  obtain ⟨operands, remaining, duplicated, object, allocated, copied, middle, allocationEffects,
    duplicateCall, createCall, cloneCall, unlocked, branch⟩ := failed
  obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
  obtain ⟨ownerCell, found, typed, _⟩ := facts.ownerLive
  rcases branch with ⟨capacityRead, response⟩ | ⟨oldCapacity, target, context, returnAddress, release,
      capacityRead, oldNonempty, full, selected, size, selectedGrowth, response⟩
  · have observedZero : (capacity : Int) = 0 := by
      simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq,
        Compiler.ZigAir.Scalar.Value.int.injEq, true_and] using
        (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
    have zero : capacity = 0 := by omega
    subst capacity
    have empty : rows ++ added = [] := List.eq_nil_of_length_eq_zero (by have bound := facts.bounded; omega)
    obtain ⟨after, executed, valid, retained, consumed, _⟩ :=
      Insertion.Native.first_allocation_oom_reached_at ops allocate safety deterministic allocator owner object ownerCell data source address meaning native copied
        key normalized operands remaining world duplicated allocated middle facts.valid frame.1.2.2.1 frame.2.1 (fun _ => admitted) found typed
        (by simpa only [empty, List.length_nil] using readHeader_items _ _ _ _ facts.header)
        capacityRead duplicateCall createCall cloneCall allocationEffects response unlocked growth
    exact ⟨after, (by simpa only [facts.projected, Option.getD_some, empty] using executed), valid, retained, consumed⟩
  · have observedCapacity : (capacity : Int) = oldCapacity := by
      simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq,
        Compiler.ZigAir.Scalar.Value.int.injEq, true_and] using
        (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
    have equal : capacity = oldCapacity := by omega
    subst capacity
    have owned := (facts.storage oldNonempty).1
    have root : data = ⟨data.allocation, 0⟩ := by
      have offset := owned.1
      cases data
      simp_all only
    have backing : Backing.Release.Owned allocator ⟨data.allocation, 0⟩ oldCapacity world.memory := root ▸ owned
    obtain ⟨after, executed, valid, retained, consumed, _⟩ :=
      Insertion.Native.growing_allocation_oom_reached_at ops allocate release safety deterministic allocator owner data.allocation oldCapacity target
        object context returnAddress ownerCell source address meaning native copied key normalized operands remaining world (rows ++ added)
        duplicated allocated middle facts.valid frame.1.2.2.1 frame.2.1 (fun _ => admitted) found typed backing
        ((readHeader_items _ _ _ _ facts.header).trans
          (congrArg (fun pointer => Except.ok (Compiler.ZigAir.Memory.Value.slice itemsType pointer (rows ++ added).length)) root)) capacityRead oldNonempty
        (by simpa only [facts.projected, Option.getD_some] using full)
        (by simpa only [facts.projected, Option.getD_some] using selected) size
        (by simpa only [facts.projected, Option.getD_some] using room)
        duplicateCall createCall cloneCall allocationEffects response unlocked
    exact ⟨after, (by simpa only [facts.projected, Option.getD_some, selectedGrowth] using executed), valid, retained, consumed⟩

/-- Original deterministic completion, sharing the source-selected proof. -/
theorem CallFrame.backing_oom_execution {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (admitted : Admitted ops.arguments)
    (failed : Insertion.Native.BackingAllocationOOM ops allocate allocator owner native normalized growth world) :
    ∃ after, Insertion.Native.execution ops allocate safety allocator owner source address meaning native key normalized
      true (world.graph.representatives.getD []) world growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run
          Storage.preparationOwnership), after) ∧
      Valid (Insertion.memory after) ∧ Insertion.Native.PrivateFrame normalized world.memory (Insertion.memory after) ∧
      Consumed normalized (Insertion.memory after) :=
  frame.backing_oom_execution_at ops allocate true growth meaning key room admitted failed

/-- Backing refusal derives the native frame at the general step's actual
insertion boundary. Both capacity cases share preparation, destructor order,
private-allocation framing and unpublished graph projection. The existing
enclosing-parent cleanup law is sufficient; no new parent law is assumed. -/
theorem CallFrame.backing_oom {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []))
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (admitted : Admitted ops.arguments)
    (failed : Insertion.Native.BackingAllocationOOM ops allocate allocator owner native normalized growth world)
    (parentFrame : ∀ after, Valid after → Insertion.Native.PrivateFrame normalized world.memory after →
      parent { world with memory := after }) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    actual.1 = .error (.language .outOfMemory) ∧
      GraphFrame safety allocator owner rows parent actual.2 ∧ Consumed normalized actual.2.memory := by
  obtain ⟨after, executed, valid, retained, consumed⟩ :=
    frame.backing_oom_execution ops allocate growth meaning key room admitted failed
  have checked := frame.insert_unpublished ops allocate growth meaning key true reads (some .allocationFailure)
    ((Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run Storage.preparationOwnership)
    after executed rfl rfl valid consumed retained (.error (.language .outOfMemory)) rfl parentFrame
  exact ⟨congrArg Prod.fst checked.1, checked.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
