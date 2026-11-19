/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.ExpressionDeinitOwnerFrame
import Compiler.Extraction.ExpressionDeinitFrameProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- The source cleanup interpreter stops on the first semantic rejection and
retains that operation's reached state. Pop sees the successful destructor's
state; it never runs against the pre-cleanup memory. -/
theorem rollback_equation (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : Storage.ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (ownership : Storage.State) (before : Frame σ) :
    (Storage.Cleanup.sequence [.lastValue, .pop]).execute
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph) ownership before =
      let (result, cleaned) := releaseLast ops allocator container before
      match result with
      | .error reason => ((.error reason, ownership), cleaned)
      | .ok () =>
        let (result, after) := pop allocator container cleaned
        ((result, match result with
          | .error _ => Storage.Release.lastValue.run ownership
          | .ok () => Storage.Release.pop.run (Storage.Release.lastValue.run ownership)), after) := by
  cases first : releaseLast ops allocator container before with
  | mk result cleaned =>
    cases result with
    | error reason => simp only [Storage.Cleanup.execute, Storage.releaseAll, Storage.Release.execute, callbacks, first]
    | ok returned =>
      cases returned
      cases second : pop allocator container cleaned with
      | mk result after =>
        cases result with
        | error reason => simp only [Storage.Cleanup.execute, Storage.releaseAll, Storage.Release.execute, callbacks, first, second]
        | ok returned => cases returned; simp only [Storage.Cleanup.execute, Storage.releaseAll, Storage.Release.execute, callbacks, first, second]

/-- Compose the insertion errdefer's native last-row destruction and length
decrement through the existing source cleanup interpreter. Every pop premise
comes from initial ownership/header contents and the destructor frame. This
does not establish those initial facts for arbitrary constructor callers. -/
theorem rollback_verified (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container lifetime capacity object : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (input stored : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized arguments : Storage.ArgumentSlice) (cells : List Storage.Cell) (last : Storage.Cell)
    (value : Word) (graph : Storage.State → Frame σ → Interner.Heap) (ownership : Storage.State) (before : Frame σ)
    (initial : Valid (memory before))
    (ownerFound : (memory before).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (rowOwned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory before))
    (inside : cells.length < capacity)
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1)))
    (capacityRead : readField (memory before).memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator (memory before).heap lifetime (cells ++ [last]))
    (itemOwned : AssemblyItem.Owned allocator object (memory before))
    (itemRead : ExpressionDeinit.Native.Fields.item (memory before).memory ⟨lifetime, cells.length * 32⟩ = .ok ⟨object, 0⟩)
    (argumentRead : Expression.readField (memory before).memory false ⟨lifetime, cells.length * 32⟩ Expression.argumentsOffset =
      .ok (.slice Expression.argumentsType ⟨arguments.address, 0⟩ arguments.items.length))
    (live : Memory.SliceValid allocator (memory before).heap arguments)
    (represented : AssemblyClone.NativeFields.Represents (memory before).memory ⟨object, 0⟩ stored)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory before)) :
    ∃ reached after,
      ExpressionDeinit.Native.run (release ops.bytes) (release ops.objects) (Publication.external ops.arguments)
        allocator ⟨lifetime, cells.length * 32⟩ (memory before) = (.ok (), reached) ∧
      (Storage.Cleanup.sequence [.lastValue, .pop]).execute
        (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph)
        ownership before = ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run ownership), after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap lifetime cells ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      (memory after).effects = reached.memory.effects ∧
      (memory after).memory.nextId = (memory before).memory.nextId ∧
      (memory after).memory.nextAddress = (memory before).memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
      (∀ argumentAllocator survivor, Memory.SliceValid argumentAllocator (memory before).heap survivor →
        (arguments.items ≠ [] → survivor.items ≠ [] → survivor.address ≠ arguments.address) →
        Memory.SliceValid argumentAllocator (memory after).heap survivor) ∧
      Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory after) ∧
      (DescriptorRelation.Prefix (memory before).memory lifetime cells →
        DescriptorRelation.Prefix (memory after).memory lifetime cells) ∧
      (∀ id, id ≠ container → id ≠ lifetime → id ≠ object →
        ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id →
        (arguments.items ≠ [] → id ≠ arguments.address) →
        (memory after).heap id = (memory before).heap id ∧
        (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id) ∧
      (∀ id, (memory before).heap id = none ∧ (memory before).memory.heap.lookup id = none →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) ∧
      (∃ finalOwner, (memory after).memory.heap.lookup container = some finalOwner ∧ ownerCell.SameShape finalOwner) ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id ∨
        (arguments.items ≠ [] ∧ id = arguments.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  obtain ⟨reached, destroyed, reachedValid, marker, registry, backingOwned, _, ownerFrame, nextId, nextAddress, survivorFrame⟩ :=
    ExpressionDeinit.Native.run_owner_verified runtimeSafety (release ops.bytes) (release ops.objects) (Publication.external ops.arguments)
      allocator container lifetime capacity cells.length object ownerCell stored arguments (memory before) initial ownerFound ownerTyped
      rowOwned inside itemOwned itemRead argumentRead live represented payloadOwned
  obtain ⟨framed, framedRun, destructorFrame⟩ := ExpressionDeinit.Native.run_framed
    (release ops.bytes) (release ops.objects) (Publication.external ops.arguments) allocator lifetime capacity cells.length object
    stored arguments (memory before) initial rowOwned inside itemOwned itemRead argumentRead live represented payloadOwned
  have same : framed = reached := congrArg Prod.snd (framedRun.symm.trans destroyed)
  subst framed
  obtain ⟨_, _, backing, found, typed, writable, _⟩ := rowOwned
  have selected := Last.from_array (memory before).memory (Owner.headerAddress ⟨container, 0⟩)
    lifetime capacity cells.length backing initial.memory found typed writable inside header
  have cleanedRun := releaseLast_success ops allocator container before _ reached selected destroyed
  let cleaned := (releaseLast ops allocator container before).2
  have cleanedStatus := congrArg Prod.fst cleanedRun
  have cleanedResult : releaseLast ops allocator container before = (.ok (), cleaned) :=
    Prod.ext cleanedStatus rfl
  have cleanedMemory : memory cleaned = reached.memory := by
    dsimp only [cleaned]
    rw [cleanedRun]
    rfl
  have cleanedLocals : cleaned.item.object = none ∧ cleaned.item.clone.value = none ∧ cleaned.item.clone.execution.invalidated = true := by
    dsimp only [cleaned]
    rw [cleanedRun]
    exact ⟨rfl, rfl, marker⟩
  have reachedHeader := (readField_eq_of_lookup (memory before).memory reached.memory.memory
    (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header
  have reachedCapacity := (readField_eq_of_lookup (memory before).memory reached.memory.memory
    (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead
  obtain ⟨_, _, afterBacking, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  obtain ⟨popped, popRun, poppedValid, poppedHeap, vector, effects, finalHeader, popShape, popNextId, popNextAddress, popFrame, _⟩ :=
    Pop.Registered.verified runtimeSafety reached.memory allocator container lifetime capacity ownerCell afterBacking cells last reachedValid
      (ownerFrame.trans ownerFound) ownerTyped ownerWritable backingFound backingTyped reachedHeader reachedCapacity
      (registry.trans registered) inside
  have poppedRun : Pop.Registered.run allocator container (memory cleaned) = (.ok (), popped) := by
    rw [cleanedMemory]
    exact popRun
  let after := withMemory cleaned popped
  have popDead (id : Nat) (dead : reached.memory.heap id = none ∧ reached.memory.memory.heap.lookup id = none) :
      (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none := by
    have ownerApart : id ≠ container := by
      intro same
      rw [same, ownerFrame, ownerFound] at dead
      cases dead.2
    have backingApart : id ≠ lifetime := by
      intro same
      rw [same, backingFound] at dead
      cases dead.2
    exact ⟨by change popped.heap id = none
              rw [poppedHeap, Memory.write_other _ _ _ _ backingApart]; exact dead.1,
      (popFrame id ownerApart).trans dead.2⟩
  have first := last_value_callback ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph ownership before
  rw [cleanedResult] at first
  have second : (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph).release
      .pop (Storage.Release.lastValue.run ownership) cleaned = (.ok (), after) := by
    rw [pop_callback, poppedRun]
    rfl
  have rowApart := (memory before).memory.heap.lookup_ne_of_type_ne lifetime container backing ownerCell found ownerFound
    (by simp [typed, ownerTyped, Owner.viewType, Backing.type])
  refine ⟨reached, after, destroyed, ?_, poppedValid, vector, finalHeader, effects,
    popNextId.trans nextId, popNextAddress.trans nextAddress,
    cleanedLocals.1, cleanedLocals.2.1, cleanedLocals.2.2, ?_, ?_, ?_, ?_, ?_,
    popShape container ownerCell (ownerFrame.trans ownerFound), ?_⟩
  · simp only [Storage.Cleanup.execute, Storage.releaseAll, Storage.Release.execute, first, second,
      Storage.Cleanup.run, List.foldl_cons, List.foldl_nil]
  · intro argumentAllocator survivor survivorLive separate
    have kept := survivorFrame argumentAllocator survivor survivorLive separate
    change Memory.SliceValid argumentAllocator popped.heap survivor
    rw [poppedHeap]
    rcases kept with empty | stored
    · exact Or.inl empty
    · have apart : survivor.address ≠ lifetime := by
        intro same
        rw [same, registry, registered] at stored
        cases stored
      exact Or.inr ((Memory.write_other _ _ _ _ apart).trans stored)
  · exact ⟨rfl, ⟨cells, vector⟩, afterBacking, (popFrame lifetime rowApart).trans backingFound,
      backingTyped, backingWritable, backingPersistent⟩
  · intro rows
    exact DescriptorRelation.frame reached.memory.memory popped.memory lifetime cells (destructorFrame.rows cells rfl rows)
      (popFrame lifetime rowApart)
  · intro id ownerApart backingApart objectApart untouched argumentsApart
    exact ⟨by change popped.heap id = _
              rw [poppedHeap, Memory.write_other _ _ _ _ backingApart]
              exact destructorFrame.registry id objectApart untouched argumentsApart,
      (popFrame id ownerApart).trans (destructorFrame.allocation id backingApart objectApart untouched argumentsApart)⟩
  · intro id dead
    exact popDead id (destructorFrame.dead id dead)
  · intro id selected
    exact popDead id (destructorFrame.released id selected)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
