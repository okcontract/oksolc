/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedRollback
import Compiler.Extraction.InternerInsertionUnrelocatedAppend

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- First and spare publication refusal share preparation, source composition
and cleanup. Only capacity selection and allocation observations differ.
The old sentinel is unconstrained when capacity is zero; normalized ownership
is that of the actual reached world, not a reconstructed entry origin. -/
theorem unrelocated_publication_oom_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container oldCapacity object : Nat) (oldData : Compiler.ZigAir.Memory.Address)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (remaining : Handle)
    (world : World (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (publication : Publication.Input allocator source key normalized world) (admitted : Admitted ops.arguments)
    (ownerFound : world.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType safety) (ownerWritable : ownerCell.writable = true)
    (header : readHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType oldData cells.length, .scalar (.int false 64 oldCapacity)))
    (bounded : cells.length ≤ oldCapacity)
    (storage : oldCapacity ≠ 0 →
      Backing.Release.Owned allocator oldData oldCapacity world.memory ∧
      Memory.Vector allocator world.memory.heap oldData.allocation cells ∧
      DescriptorRelation.Prefix world.memory.memory oldData.allocation cells)
    (selected : oldCapacity = 0 ∨ cells.length < oldCapacity)
    (first : oldCapacity = 0 → ∃ base allocationEffects,
      (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
        allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base) ∧
      Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ())
    (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append safety allocate allocator container cells input key normalized
        ((key.eval meaning world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2)) =
        (false, probeEffects)) :
    ∃ after,
      execution ops allocate safety allocator container source itemSource meaning input key normalized true cells world growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership), after) ∧
      ∃ lifetime capacity,
        Valid (memory after) ∧ Memory.Vector allocator (memory after).heap lifetime cells ∧
        Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory after) ∧
        readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
          .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
        cells.length < capacity ∧ DescriptorRelation.Prefix (memory after).memory lifetime cells ∧
        (memory after).effects.keys = world.memory.effects.keys ∧
        (∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ container →
          (oldCapacity ≠ 0 → id ≠ oldData.allocation) → (normalized.items ≠ [] → id ≠ normalized.address) →
          (memory after).memory.heap.lookup id = some native ∧ (memory after).heap id = world.memory.heap id) ∧
        (∃ finalOwner, (memory after).memory.heap.lookup container = some finalOwner ∧
          finalOwner.type = Owner.viewType safety ∧ finalOwner.writable = true) ∧
        (normalized.items ≠ [] → (memory after).heap normalized.address = none ∧
          (memory after).memory.heap.lookup normalized.address = none) := by
  let value := (key.eval meaning world.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells world.graph.table
    (cell input key normalized value owner state) key owner
  refine prepare_publication_oom ops allocate safety allocator container object source itemSource meaning
    input copied key normalized operands remaining world cells duplicated allocated middle growth
    initial live represented publication admitted room duplicateCall createCall cloneCall _ ?_
  dsimp only
  intro installed installedPost assigned sameValues operandsLive normalizedLive separate frame keys publicationInput
  have ownerFrame := (frame container ownerCell ownerFound).1.trans ownerFound.symm
  have preparedHeader : readHeader installed.memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType oldData cells.length, .scalar (.int false 64 oldCapacity)) := by
    unfold readHeader readItems
    rw [readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame,
      readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame]
    exact header
  have preparedStorage (positive : oldCapacity ≠ 0) :
      Backing.Release.Owned allocator oldData oldCapacity installed ∧
      Memory.Vector allocator installed.heap oldData.allocation cells ∧
      DescriptorRelation.Prefix installed.memory oldData.allocation cells := by
    obtain ⟨⟨root, _, backing, found, typed, writable, persistent⟩, vector, rows⟩ := storage positive
    have retained := frame oldData.allocation backing found
    have registered : Memory.Vector allocator installed.heap oldData.allocation cells := retained.2.trans vector
    exact ⟨⟨root, ⟨cells, registered⟩, backing, retained.1, typed, writable, persistent⟩, registered,
      DescriptorRelation.frame _ _ oldData.allocation cells rows (retained.1.trans found.symm)⟩
  have preparedFirst (zero : oldCapacity = 0) : ∃ base allocationEffects,
      allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
      Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base ∧
      Owner.NativeLock.checkHeader installed.memory (Owner.headerAddress ⟨container, 0⟩) = .ok () := by
    obtain ⟨base, effects, allocation, unlocked⟩ := first zero
    exact ⟨base, effects, (allocation installed assigned).1, (allocation installed assigned).2,
      (Owner.NativeLock.checkHeader_eq_of_lookup safety world.memory.memory installed.memory container ownerCell
        installedPost.valid.memory ownerFound ownerTyped ownerFrame).trans unlocked⟩
  have argumentBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have contents := (borrowed_ready allocator normalized world.memory initial live).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound world.memory.memory (view normalized) normalized.items contents
    rw [sameValues]; omega
  obtain ⟨lifetime, capacity, appended, appendedOwner, appendRun, originalAppend, appendValid, appendKeys,
      found, typed, writable, owned, inside, vector, finalHeader, itemRead, argumentRead, itemOwned,
      itemRepresented, payloadOwned, argumentsKept, appendedRows, retained⟩ :=
    unrelocated_append_owned allocate safety allocator container oldCapacity object oldData ownerCell input copied key normalized operands
      cells value middle installed growth installedPost (frame _ _ ownerFound).1 ownerTyped ownerWritable
      preparedHeader bounded preparedStorage selected preparedFirst room argumentBound
  have publicationInput := Publication.Input.frame allocator source key normalized
    ⟨graph preparationOwnership (preparedFrame object copied operands installed), installed⟩
    ⟨graph Storage.publicationOwnership appended, memory appended⟩ publicationInput appendKeys (argumentsKept allocator)
  have probed : ops.probe key (Publication.forget (memory appended)) = (false, probeEffects) := by
    have observed := response installed assigned
    change ops.probe key (Publication.forget (memory
      (append safety allocate allocator container cells input key normalized value preparationOwnership
        (preparedFrame object copied operands installed)).2)) = (false, probeEffects) at observed
    simpa only [originalAppend] using observed
  obtain ⟨failed, popped, after, publicationRun, _, rolled, cleaned, _, valid, finalVector, header, _, _,
      _, _, _, _, _, finalOwned, rowsKept, cleanupFrame, _, finalOwner, destroyed, finalKeys⟩ :=
    publication_oom_rollback ops allocate safety allocator container lifetime capacity object appendedOwner source itemSource
      input copied key normalized operands cells _ value graph Storage.publicationOwnership appended appendValid found typed writable owned
      inside finalHeader vector itemOwned itemRead argumentRead (argumentsKept allocator operands operandsLive) itemRepresented payloadOwned
      (argumentsKept allocator normalized normalizedLive) separate publicationInput probeEffects probed growth
  have retainedRows : DescriptorRelation.Prefix (memory appended).memory lifetime cells := by
    intro index row located
    have inside : index < cells.length := (List.getElem?_eq_some_iff.mp located).1
    exact appendedRows index row (by simpa only [List.getElem?_append_left inside] using located)
  have fresh := preparation_cleanup_apart ops allocator object input copied normalized operands remaining
    world.memory duplicated allocated middle initial live admitted duplicateCall createCall cloneCall
  refine ⟨appended, failed, popped, after, appendRun, publicationRun, rolled, cleaned, lifetime, capacity,
    valid, finalVector, finalOwned, header, inside, rowsKept retainedRows, finalKeys.trans (appendKeys.trans keys), ?_, ?_, ?_⟩
  · intro id native located apart oldApart normalizedApart
    have prepared := frame id native located
    have appended := retained id native prepared.1 apart oldApart
    have owners := fresh id native located
    have kept := cleanupFrame id apart appended.2.2 owners.1 owners.2.1 (fun _ => owners.2.2) normalizedApart
    exact ⟨kept.2.trans appended.1, kept.1.trans (appended.2.1.trans prepared.2)⟩
  · obtain ⟨owner, found, shape⟩ := finalOwner
    exact ⟨owner, found, shape.2.1.trans typed, shape.2.2.1.trans writable⟩
  · intro nonempty
    exact destroyed normalized.address (Or.inr (Or.inr (Or.inr ⟨nonempty, rfl⟩)))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
