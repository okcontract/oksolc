/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapCapacity

namespace Compiler.Extraction.ExpressionMap.Capacity
open Compiler.ZigAir.Memory Initialization Buckets

/-- Both source placements execute their checked field selector. -/
def readField (place : Placement) (safety : Bool) (state : State) (receiver : Nat) (slot : Slot) : Except Fault Value :=
  match place with
  | .embedded => Initialization.read safety state ⟨receiver, 0⟩ slot
  | .localMap => do
    let field ← fieldPointer state (.pointer (.pointer false false (allocationType safety)) ⟨receiver, 0⟩) (slot.offset safety)
    load state field

def readAvailable (place : Placement) (safety : Bool) (state : State) (receiver : Nat) : Except Fault (BitVec 32) := do
  let .scalar (.int false 32 value) ← readField place safety state receiver .available | .error .unsupported
  .ok (BitVec.ofInt 32 value)

/-- capacity() returns zero on null metadata without touching the header.
The nonnull branch reuses the checked header read used by metadata clearing. -/
def readCapacity (place : Placement) (safety : Bool) (state : State) (receiver : Nat) : Except Fault (BitVec 32) := do
  let .optionalObject _ _ payload ← readField place safety state receiver .metadata | .error .unsupported
  match payload with
  | none => .ok 0
  | some (.leaf (.pointer target address)) => do
    if target ≠ metadataPointerType then .error .unsupported else do
    let .scalar (.int false 32 count) ← Metadata.readCapacity state address | .error .unsupported
    .ok (BitVec.ofInt 32 count)
  | _ => .error .unsupported

def selectMemory (place : Placement) (safety : Bool) (state : State) (receiver : Nat) (additional : BitVec 32) :
    Except Fault (Option (BitVec 32)) := do
  let available ← readAvailable place safety state receiver
  if additional.toNat ≤ available.toNat then return none
  let capacity ← readCapacity place safety state receiver
  select safety capacity available additional

structure Observed (place : Placement) (safety : Bool) (state : State) (receiver : Nat)
    (capacity available : BitVec 32) : Prop where
  availableRead : readAvailable place safety state receiver = .ok available
  capacityRead : readCapacity place safety state receiver = .ok capacity

theorem select_memory_room (place : Placement) (safety : Bool) (state : State) (receiver : Nat)
    (available additional : BitVec 32) (read : readAvailable place safety state receiver = .ok available)
    (room : additional.toNat ≤ available.toNat) : selectMemory place safety state receiver additional = .ok none := by
  simp only [selectMemory, read, bind, Except.bind, room, ↓reduceIte, pure, Except.pure]

theorem Observed.select_growth (observed : Observed place safety state receiver capacity available)
    (additional : BitVec 32) (countdown : available.toNat ≤ (Local.Availability.word capacity).toNat)
    (needed : available.toNat < additional.toNat)
    (bounded : (Local.Availability.word capacity).toNat - available.toNat + additional.toNat ≤ maximumSize) :
    selectMemory place safety state receiver additional = .ok (some (target capacity available additional)) ∧
      8 ≤ (target capacity available additional).toNat ∧
      capacity.toNat < (target capacity available additional).toNat ∧
      powerGuard (target capacity available additional) = true := by
  obtain ⟨ran, post⟩ := Capacity.select_growth safety capacity available additional countdown needed bounded
  refine ⟨?_, post⟩
  simp only [selectMemory, observed.availableRead, observed.capacityRead, bind, Except.bind,
    show ¬additional.toNat ≤ available.toNat from by omega, ↓reduceIte, ran, pure, Except.pure]

/-- Recover these two reads from the existing empty-state check. This consumes
its successful observation, including all preceding faults and field guards. -/
theorem observed_empty (safety : Bool) (state : State) (receiver : Nat)
    (observed : Initialization.observeEmpty safety state ⟨receiver, 0⟩ = .ok ()) :
    Observed .embedded safety state receiver 0 0 := by
  simp only [Initialization.observeEmpty, bind, Except.bind] at observed
  repeat' first | split at observed | contradiction
  all_goals constructor <;> simp_all [readAvailable, readCapacity, readField, Slot.value] <;> rfl

theorem local_read (safety : Bool) (state : State) (receiver : Nat) (slot : Slot)
    (cell : Allocation) (valid : state.valid = true) (found : state.heap.lookup receiver = some cell)
    (typed : cell.type = allocationType safety) (ordinary : slot ≠ .lock) :
    readField .localMap safety state receiver slot = load state (Local.field safety receiver slot) := by
  have field := root_fieldPointer state receiver cell (allocationType safety) slot.value.type
    (Placement.localMap.layout safety) (slot.offset safety) false false valid found typed
    (Placement.localMap.layout_checked safety) (by cases slot <;> cases safety <;> simp_all <;> decide)
    (by cases slot <;> cases safety <;> simp_all <;> rfl)
  simp only [readField, field, bind, Except.bind, Local.field]
  rfl

theorem ready_observed (ready : Local.EmptyReady safety receiver bucket capacity base state)
    (positive : 0 < capacity.toNat) :
    Observed .localMap safety state receiver capacity (Local.Availability.word capacity) := by
  obtain ⟨cell, found, typed, _⟩ := ready.receiverLive
  have available := local_read safety state receiver .available cell ready.valid found typed (by decide)
  have metadata : readField .localMap safety state receiver .metadata = .ok (Receiver.value bucket) := ready.metadata
  obtain ⟨bucketCell, bucketFound, _, bucketTyped, _, _⟩ := ready.bucketLive
  refine ⟨?_, ?_⟩
  · simp only [readAvailable, available, ready.available, Local.Availability.value, bind, Except.bind,
      BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [readCapacity, metadata, Receiver.value, bind, Except.bind, ne_self_iff_false, ↓reduceIte,
      Metadata.read_capacity state bucket bucketCell capacity positive ready.valid bucketFound bucketTyped (ready.headers .capacity),
      BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Compiler.Extraction.ExpressionMap.Capacity

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.Ownership
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul

theorem Established.capacity_observed {σ : Type} {safety : Bool} {allocator : Nat}
    {before : Session σ} {after : World (Publication.Effects σ)}
    {owner : Nat} {sentinel : Compiler.ZigAir.Memory.Address} {meaning : Meaning}
    (established : Established safety allocator before after owner sentinel meaning) :
    ExpressionMap.Capacity.Observed .embedded safety after.memory.memory owner 0 0 := by
  have observed := established.nativeKeys
  simp only [keys, bind, Except.bind] at observed
  cases checked : ExpressionMap.Initialization.observeEmpty safety after.memory.memory ⟨owner, 0⟩ with
  | error fault => simp only [checked] at observed; contradiction
  | ok result => exact ExpressionMap.Capacity.observed_empty safety after.memory.memory owner checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.Ownership

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets

inductive GrowthPreparation where
  | enough
  | outOfMemory
  | prepared (capacity : BitVec 32) (bucket : Compiler.ZigAir.Memory.Address)
  deriving DecidableEq, Repr

def GrowthPreparation.ofBucket (capacity : BitVec 32) : Option Compiler.ZigAir.Memory.Address → GrowthPreparation
  | none => .outOfMemory
  | some bucket => .prepared capacity bucket

/-- growIfNeeded through complete temporary-map initialization, before rehash.
Enough room and allocator OOM stay distinct; every rejection retains its prefix. -/
def prepareGrowth (place : ExpressionMap.Initialization.Placement) (safety : Bool) (receiver : Nat)
    (additional : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before : World (Publication.Effects σ)) : Except Compiler.ZigAir.Memory.Fault GrowthPreparation × World (Publication.Effects σ) :=
  match ExpressionMap.Capacity.selectMemory place safety before.memory.memory receiver additional with
  | .error fault => (.error fault, before)
  | .ok none => (.ok .enough, before)
  | .ok (some capacity) =>
    let (result, after) := readyBuckets safety capacity allocate before
    (result.map (GrowthPreparation.ofBucket capacity), after)

/-- Temporary-map preparation changes native storage and allocator effects,
but never publishes a logical key, including on partial failure. -/
theorem prepareGrowth_keys (place : ExpressionMap.Initialization.Placement) (safety : Bool) (receiver : Nat)
    (additional : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before : World (Publication.Effects σ)) :
    (prepareGrowth place safety receiver additional allocate before).2.memory.effects.keys = before.memory.effects.keys := by
  have reserved (capacity : BitVec 32) (world : World (Publication.Effects σ)) :
      (reserveHeader capacity allocate world).2.memory.effects.keys = world.memory.effects.keys := by
    simp only [reserveHeader, PrivateRegion.reserve]
    split <;> rfl
  have allocated (capacity : BitVec 32) (receiver : Nat) (world : World (Publication.Effects σ)) :
      (allocateBuckets safety capacity receiver allocate world).2.memory.effects.keys = world.memory.effects.keys := by
    have frame := reserved capacity world
    simp only [allocateBuckets]
    generalize ran : reserveHeader capacity allocate world = result at *
    rcases result with ⟨result, reached⟩
    cases result with
    | error fault => exact frame
    | ok option => cases option with
      | none => exact frame
      | some bucket => dsimp only; split <;> exact frame
  have prepared (capacity : BitVec 32) (world : World (Publication.Effects σ)) :
      (prepareBuckets safety capacity allocate world).2.memory.effects.keys = world.memory.effects.keys := by
    simp only [prepareBuckets, declareMap]
    split
    · rfl
    · exact allocated capacity _ _
  have locked (capacity : BitVec 32) :
      (lockBuckets safety capacity allocate before).2.memory.effects.keys = before.memory.effects.keys := by
    have frame := prepared capacity before
    simp only [lockBuckets]
    generalize ran : prepareBuckets safety capacity allocate before = result at *
    rcases result with ⟨result, reached⟩
    cases result with
    | error fault => exact frame
    | ok option => cases option with
      | none => exact frame
      | some bucket => dsimp only; split <;> exact frame
  have cleared (capacity : BitVec 32) :
      (clearBuckets safety capacity allocate before).2.memory.effects.keys = before.memory.effects.keys := by
    have frame := locked capacity
    simp only [clearBuckets]
    generalize ran : lockBuckets safety capacity allocate before = result at *
    rcases result with ⟨result, reached⟩
    cases result with
    | error fault => exact frame
    | ok option => cases option <;> exact frame
  have ready (capacity : BitVec 32) :
      (readyBuckets safety capacity allocate before).2.memory.effects.keys = before.memory.effects.keys := by
    have frame := cleared capacity
    simp only [readyBuckets]
    generalize ran : clearBuckets safety capacity allocate before = result at *
    rcases result with ⟨result, reached⟩
    cases result with
    | error fault => exact frame
    | ok option => cases option with
      | none => exact frame
      | some bucket => dsimp only; split <;> exact frame
  unfold prepareGrowth
  split <;> try rfl
  exact ready _

/-- Every allocation/initialization outcome retains the state actually reached,
including errors after partial writes and allocator OOM. -/
theorem prepareGrowth_prefix (place : ExpressionMap.Initialization.Placement) (safety : Bool) (receiver : Nat)
    (additional : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before : World (Publication.Effects σ)) (selected : BitVec 32)
    (result : Except Compiler.ZigAir.Memory.Fault (Option Compiler.ZigAir.Memory.Address))
    (after : World (Publication.Effects σ))
    (selection : ExpressionMap.Capacity.selectMemory place safety before.memory.memory receiver additional = .ok (some selected))
    (ran : readyBuckets safety selected allocate before = (result, after)) :
    prepareGrowth place safety receiver additional allocate before =
      (result.map (GrowthPreparation.ofBucket selected), after) := by
  simp only [prepareGrowth, selection, ran]

theorem Facts.prepare_growth {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (place : ExpressionMap.Initialization.Placement) (receiver : Nat) (oldCapacity available additional : BitVec 32)
    (observed : ExpressionMap.Capacity.Observed place safety before.memory.memory receiver oldCapacity available)
    (countdown : available.toNat ≤ (ExpressionMap.Local.Availability.word oldCapacity).toNat)
    (needed : available.toNat < additional.toNat)
    (bounded : (ExpressionMap.Local.Availability.word oldCapacity).toNat - available.toNat + additional.toNat ≤ ExpressionMap.Capacity.maximumSize)
    (room : ExpressionMap.Local.Room safety before.memory.memory) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest (ExpressionMap.Capacity.target oldCapacity available additional)).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory
      ⟨bytes (ExpressionMap.Capacity.target oldCapacity available additional).toNat, 16⟩ base)
    (apart : base + bytes (ExpressionMap.Capacity.target oldCapacity available additional).toNat ≤ ExpressionMap.Local.stackBase before.memory.memory ∨
      ExpressionMap.Local.stackEnd safety before.memory.memory ≤ base) :
    ∃ after, prepareGrowth place safety receiver additional allocate before =
        (.ok (.prepared (ExpressionMap.Capacity.target oldCapacity available additional) ⟨before.memory.memory.nextId + 1, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      ExpressionMap.Local.EmptyReady safety before.memory.memory.nextId (before.memory.memory.nextId + 1)
        (ExpressionMap.Capacity.target oldCapacity available additional) base after.memory.memory ∧
      8 ≤ (ExpressionMap.Capacity.target oldCapacity available additional).toNat ∧
      oldCapacity.toNat < (ExpressionMap.Capacity.target oldCapacity available additional).toNat ∧
      ExpressionMap.Capacity.powerGuard (ExpressionMap.Capacity.target oldCapacity available additional) = true ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 2 ∧ after.memory.effects.allocator = effects := by
  obtain ⟨selected, minimum, grows, power⟩ := observed.select_growth additional countdown needed bounded
  obtain ⟨after, ran, facts, cursor, reached, ready⟩ := facts.ready_buckets room
    (ExpressionMap.Capacity.target oldCapacity available additional) (by omega) base allocate effects response fits apart
  exact ⟨after, prepareGrowth_prefix place safety receiver additional allocate before _ _ after selected ran,
    facts, ready, minimum, grows, power, cursor, reached⟩

theorem prepareGrowth_enough (place : ExpressionMap.Initialization.Placement) (safety : Bool) (receiver : Nat)
    (available additional : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before : World (Publication.Effects σ))
    (read : ExpressionMap.Capacity.readAvailable place safety before.memory.memory receiver = .ok available)
    (room : additional.toNat ≤ available.toNat) :
    prepareGrowth place safety receiver additional allocate before = (.ok .enough, before) := by
  simp only [prepareGrowth, ExpressionMap.Capacity.select_memory_room place safety before.memory.memory receiver available additional read room]

theorem prepareGrowth_rejected (place : ExpressionMap.Initialization.Placement) (safety : Bool) (receiver : Nat)
    (additional : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before : World (Publication.Effects σ)) (fault : Compiler.ZigAir.Memory.Fault)
    (rejected : ExpressionMap.Capacity.selectMemory place safety before.memory.memory receiver additional = .error fault) :
    prepareGrowth place safety receiver additional allocate before = (.error fault, before) := by
  simp only [prepareGrowth, rejected]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
