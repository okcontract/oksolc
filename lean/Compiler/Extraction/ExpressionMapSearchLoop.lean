/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapSearchReads

namespace Compiler.Extraction.ExpressionMap.Search
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Initialization Buckets
open Compiler.Extraction.Cache (Key)

def lookupLoop (place : Placement) (safety : Bool) (state : State) (receiver : Nat)
    (capacity : BitVec 32) (hash : BitVec 64) (key : Key) (source : View) (remaining index : Nat) : Except Fault (Option Nat) := do
  let (_, action) ← inspect place safety state receiver capacity index remaining (Probe.fingerprint hash) key source
  match action with
  | .hit => .ok (some index)
  | .stop => .ok none
  | .next => match remaining with
    | 0 => .error .memoryValidity
    | n + 1 => lookupLoop place safety state receiver capacity hash key source n (Probe.advance capacity index)
termination_by remaining

def insertionLoop (place : Placement) (safety : Bool) (state : State) (receiver : Nat)
    (capacity : BitVec 32) (hash : BitVec 64) (key : Key) (source : View) (remaining index first : Nat) : Except Fault Probe.Outcome := do
  let (bits, action) ← inspect place safety state receiver capacity index remaining (Probe.fingerprint hash) key source
  match action with
  | .hit => .ok (.hit index)
  | .stop => .ok (.miss index first)
  | .next => match remaining with
    | 0 => .error .memoryValidity
    | n + 1 => do
      let first ← remember place safety state receiver index first (Probe.fingerprint hash) bits
      insertionLoop place safety state receiver capacity hash key source n (Probe.advance capacity index) first
termination_by remaining

/-- Repeated receiver loads are erased only after deriving their original
value. These equations retain failures from every candidate inspection. -/
theorem lookup_loop_eq (read : readBucket place safety state receiver = .ok bucket)
    (capacity : BitVec 32) (hash : BitVec 64) (key : Key) (source : View) (remaining index : Nat) :
    lookupLoop place safety state receiver capacity hash key source remaining index =
      Probe.lookupLoop state capacity bucket hash key source remaining index := by
  induction remaining generalizing index with
  | zero => simp only [lookupLoop, Probe.lookupLoop, inspect, read, bind, Except.bind]; rfl
  | succ remaining ih =>
    rw [lookupLoop, Probe.lookupLoop]
    simp only [inspect, read, bind, Except.bind]
    cases inspected : Candidate.inspect state capacity bucket index (remaining + 1) (Probe.fingerprint hash) key source with
    | error fault => rfl
    | ok pair => obtain ⟨bits, action⟩ := pair; cases action <;> simp [ih]

theorem insertion_loop_eq (read : readBucket place safety state receiver = .ok bucket)
    (count : Capacity.readCapacity place safety state receiver = .ok capacity)
    (hash : BitVec 64) (key : Key) (source : View) (remaining index first : Nat) :
    insertionLoop place safety state receiver capacity hash key source remaining index first =
      Probe.loop state capacity bucket hash key source remaining index first := by
  induction remaining generalizing index first with
  | zero => simp only [insertionLoop, Probe.loop, inspect, read, bind, Except.bind]; rfl
  | succ remaining ih =>
    rw [insertionLoop, Probe.loop]
    simp only [inspect, read, bind, Except.bind]
    cases inspected : Candidate.inspect state capacity bucket index (remaining + 1) (Probe.fingerprint hash) key source with
    | error fault => rfl
    | ok pair =>
      obtain ⟨bits, action⟩ := pair
      cases action <;> simp [remember_eq count, ih]

/-- Source continuation immediately after hash returns. Both capacity() calls
and the final values() receiver load execute in their native order. -/
def lookupAfterHash (place : Placement) (safety : Bool) (state : State) (receiver : Nat)
    (hash : BitVec 64) (key : Key) (source : View) : Except Fault (Option (BitVec 32)) := do
  let capacity ← Capacity.readCapacity place safety state receiver
  if capacity = 0 then .error (Capacity.rejected safety) else do
  let limit ← Capacity.readCapacity place safety state receiver
  let selected ← lookupLoop place safety state receiver capacity hash key source limit.toNat (Probe.start capacity hash)
  match selected with
  | none => .ok none
  | some index => do
    let bucket ← readBucket place safety state receiver
    let .scalar (.int false 32 id) ← Values.read state capacity bucket index | .error .unsupported
    .ok (some (BitVec.ofInt 32 id))

/-- Insertion has a third capacity read for its initial tombstone sentinel. -/
def insertionAfterHash (place : Placement) (safety : Bool) (state : State) (receiver : Nat)
    (hash : BitVec 64) (key : Key) (source : View) : Except Fault Probe.Outcome := do
  let capacity ← Capacity.readCapacity place safety state receiver
  if capacity = 0 then .error (Capacity.rejected safety) else do
  let limit ← Capacity.readCapacity place safety state receiver
  let first ← Capacity.readCapacity place safety state receiver
  insertionLoop place safety state receiver capacity hash key source limit.toNat (Probe.start capacity hash) first.toNat

/-- A composition boundary around the still-unverified hash producer, not a
claim about Wyhash execution. Size zero skips the entire hash continuation. -/
def withHash (place : Placement) (safety : Bool) (state : State) (receiver : Nat)
    (hashes : Key → BitVec 64) (key : Key) (source : View) : Except Fault (Option (BitVec 32)) := do
  let size ← readCount place safety state receiver
  if size = 0 then .ok none else lookupAfterHash place safety state receiver (hashes key) key source

theorem lookup_after_hash_eq (layout : Insertion.Layout place safety receiver bucket capacity state)
    (power : Probe.Power capacity) (hash : BitVec 64) (key : Key) (source : View) :
    lookupAfterHash place safety state receiver hash key source = Probe.getHashed state capacity bucket hash key source := by
  have nonzero : capacity ≠ 0 := by intro zero; have := power.positive; simp [zero] at this
  simp only [lookupAfterHash, layout.read_capacity power.positive, bind, Except.bind, nonzero, ↓reduceIte,
    lookup_loop_eq layout.read_bucket, Probe.getHashed]
  cases selected : Probe.lookupLoop state capacity bucket hash key source capacity.toNat (Probe.start capacity hash) with
  | error fault => rfl
  | ok value => cases value <;> simp [layout.read_bucket]
                rfl

theorem insertion_after_hash_eq (layout : Insertion.Layout place safety receiver bucket capacity state)
    (power : Probe.Power capacity) (hash : BitVec 64) (key : Key) (source : View) :
    insertionAfterHash place safety state receiver hash key source = Probe.run state capacity bucket hash key source := by
  have nonzero : capacity ≠ 0 := by intro zero; have := power.positive; simp [zero] at this
  simp only [insertionAfterHash, layout.read_capacity power.positive, bind, Except.bind, nonzero, ↓reduceIte,
    insertion_loop_eq layout.read_bucket (layout.read_capacity power.positive), Probe.run]

end Compiler.Extraction.ExpressionMap.Search
