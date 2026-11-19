/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionOuterCleanup
import Compiler.Extraction.InternerInsertionCleanupEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Publication refusal and rollback depend on the reached appended owners,
not on how capacity was obtained. First, spare and relocated append supply these
owners from their actual execution. The source probe changes only allocator
effects; destruction, pop and normalized release preserve the reached backing
and allocation history while consuming the newly appended value. -/
theorem publication_oom_rollback (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container lifetime capacity object : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (input stored : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (cells : List Storage.Cell) (last : Storage.Cell)
    (value : Word) (graph : Storage.State → Frame σ → Interner.Heap) (ownership : Storage.State) (appended : Frame σ)
    (initial : Valid (memory appended))
    (ownerFound : (memory appended).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (rowOwned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory appended))
    (inside : cells.length < capacity)
    (header : readHeader (memory appended).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator (memory appended).heap lifetime (cells ++ [last]))
    (itemOwned : AssemblyItem.Owned allocator object (memory appended))
    (itemRead : ExpressionDeinit.Native.Fields.item (memory appended).memory ⟨lifetime, cells.length * 32⟩ = .ok ⟨object, 0⟩)
    (argumentRead : Expression.readField (memory appended).memory false ⟨lifetime, cells.length * 32⟩ Expression.argumentsOffset =
      .ok (.slice Expression.argumentsType ⟨operands.address, 0⟩ operands.items.length))
    (live : Memory.SliceValid allocator (memory appended).heap operands)
    (represented : AssemblyClone.NativeFields.Represents (memory appended).memory ⟨object, 0⟩ stored)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory appended))
    (normalizedLive : Memory.SliceValid allocator (memory appended).heap normalized)
    (separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address)
    (publication : Publication.Input allocator source key normalized ⟨graph ownership appended, memory appended⟩)
    (probeEffects : σ)
    (response : ops.probe key (Publication.forget (memory appended)) = (false, probeEffects))
    (growth : Option (Growth.Registered.Callbacks σ) := none) :
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
    ∃ failed popped after,
      calls.attempt .publish ownership appended = (.ok false, failed) ∧
      memory failed = { memory appended with effects := { (memory appended).effects with allocator := probeEffects } } ∧
      (Storage.Cleanup.sequence [.lastValue, .pop]).execute calls ownership failed =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run ownership), popped) ∧
      (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls ownership failed =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run ownership), after) ∧
      free (Publication.external ops.arguments) allocator normalized (memory popped) = (.ok (), memory after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap lifetime cells ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      Memory.Arguments.ReleasePost (memory popped).heap (memory popped).memory allocator normalized
        (memory after).heap (memory after).memory ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory popped).effects
        else (Publication.external ops.arguments).free normalized (memory popped)) ∧
      (memory after).memory.nextId = (memory appended).memory.nextId ∧
      (memory after).memory.nextAddress = (memory appended).memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
      Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory after) ∧
      (DescriptorRelation.Prefix (memory appended).memory lifetime cells →
        DescriptorRelation.Prefix (memory after).memory lifetime cells) ∧
      (∀ id, id ≠ container → id ≠ lifetime → id ≠ object →
        ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id →
        (operands.items ≠ [] → id ≠ operands.address) → (normalized.items ≠ [] → id ≠ normalized.address) →
        (memory after).heap id = (memory appended).heap id ∧
        (memory after).memory.heap.lookup id = (memory appended).memory.heap.lookup id) ∧
      (∀ id, (memory appended).heap id = none ∧ (memory appended).memory.heap.lookup id = none →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) ∧
      (∃ finalOwner, (memory after).memory.heap.lookup container = some finalOwner ∧ ownerCell.SameShape finalOwner) ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) ∧
      (memory after).effects.keys = (memory appended).effects.keys := by
  dsimp only
  have published := Publication.publish_oom ops.probe ops.arguments allocator source key normalized
    (BitVec.ofNat 32 cells.length) ⟨graph ownership appended, memory appended⟩ probeEffects
    (Publication.admit_complete _ _ _ _ _ publication) response
  let failed := withMemory appended { memory appended with effects := { (memory appended).effects with allocator := probeEffects } }
  have failedValid : Valid (memory failed) := ⟨initial.memory, initial.related, initial.injected⟩
  have fields := Append.readHeader_parts (memory appended).memory (Owner.headerAddress ⟨container, 0⟩) _ _ header
  obtain ⟨popped, after, rolled, cleaned, freed, valid, vector, finalHeader, released, effects,
      nextId, nextAddress, cleared, valueCleared, invalidated, owned, rowsKept, frame, dead, finalOwner, destroyed⟩ :=
    rollback_normalized_verified ops allocate runtimeSafety allocator container lifetime capacity object ownerCell source itemSource
      input stored key normalized operands cells last value graph ownership failed failedValid ownerFound ownerTyped ownerWritable
      rowOwned inside fields.1 fields.2 registered itemOwned itemRead argumentRead live represented payloadOwned normalizedLive separate
  have keys := cleanup_sequence_keys ops allocate runtimeSafety allocator container source itemSource input key normalized
    cells value graph none [.lastValue, .pop, .normalized] ownership failed
  change Storage.releaseAll _ _ _ _ = _ at cleaned
  rw [cleaned] at keys
  refine ⟨failed, popped, after, ?_, rfl, rolled, cleaned, freed, valid, vector, finalHeader, released,
    effects, nextId, nextAddress, cleared, valueCleared, invalidated, owned, rowsKept, frame, dead, finalOwner, destroyed, keys⟩
  simp only [callbacks, Insertion.callbacks, published, Except.mapError]
  rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
