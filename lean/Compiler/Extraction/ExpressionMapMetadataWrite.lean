/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapMetadata

namespace Compiler.Extraction.ExpressionMap.Buckets.Metadata
open Compiler.ZigAir.Memory

def value (bits : BitVec 8) : Value := .scalar (.int false 8 bits.toNat)

/-- The two ordered packed-field assignments in Metadata.fill. The first
retains the old fingerprint; the second retains the newly written used bit. -/
def used (bits : BitVec 8) : BitVec 8 := BitVec.ofNat 8 (128 + bits.toNat % 128)
def fingerprint (bits : BitVec 8) (fp : BitVec 7) : BitVec 8 :=
  BitVec.ofNat 8 (bits.toNat / 128 * 128 + fp.toNat)
def occupied (fp : BitVec 7) : BitVec 8 := BitVec.ofNat 8 (128 + fp.toNat)

def readByte (state : State) (bucket index : Nat) : Except Fault (BitVec 8) := do
  let .scalar (.int false 8 bits) ← load state (pointer bucket index) | .error .unsupported
  .ok (BitVec.ofInt 8 bits)

def mark (bucket index : Nat) (fp : BitVec 7) (before : State) : Except Fault Unit × State :=
  match readByte before bucket index with
  | .error fault => (.error fault, before)
  | .ok bits => match store before (pointer bucket index) (value (used bits)) with
    | .error fault => (.error fault, before)
    | .ok middle => match readByte middle bucket index with
      | .error fault => (.error fault, middle)
      | .ok bits => match store middle (pointer bucket index) (value (fingerprint bits fp)) with
        | .error fault => (.error fault, middle)
        | .ok after => (.ok (), after)

theorem packed_exact (bits : BitVec 8) (fp : BitVec 7) :
    (used bits).toNat = 128 + bits.toNat % 128 ∧ fingerprint (used bits) fp = occupied fp ∧
      (occupied fp).toNat = 128 + fp.toNat ∧ isUsed (occupied fp) = true ∧ isFree (occupied fp) = false := by
  have bound := bits.isLt
  have small := fp.isLt
  have first : (used bits).toNat = 128 + bits.toNat % 128 := by simp only [used, BitVec.toNat_ofNat]; omega
  have final : (occupied fp).toNat = 128 + fp.toNat := by simp only [occupied, BitVec.toNat_ofNat]; omega
  refine ⟨first, ?_, final, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [fingerprint, BitVec.toNat_ofNat, first, final]
    omega
  · simp only [isUsed, final, beq_iff_eq]; omega
  · have nonzero : occupied fp ≠ 0#8 := by
      intro same
      have := congrArg BitVec.toNat same
      simp only [final, BitVec.toNat_ofNat] at this
      omega
    simpa only [isFree, beq_eq_false_iff_ne] using nonzero

theorem read_byte_of_load (state : State) (bucket index : Nat) (bits : BitVec 8)
    (read : load state (pointer bucket index) = .ok (value bits)) : readByte state bucket index = .ok bits := by
  simp only [readByte, read, value, bind, Except.bind, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem read_byte_frame (before after : State) (bucket index : Nat)
    (same : load after (pointer bucket index) = load before (pointer bucket index)) :
    readByte after bucket index = readByte before bucket index := by simp only [readByte, same]

theorem observe_read_byte (state : State) (bucket index : Nat) :
    Metadata.observe state bucket index = (readByte state bucket index).map (fun bits => (isFree bits, isUsed bits)) := by
  unfold Metadata.observe readByte
  cases loaded : load state (pointer bucket index) with
  | error fault => rfl
  | ok value =>
    simp only [bind, Except.bind]
    split <;> simp_all [Except.map]

theorem read_byte_free (state : State) (bucket index : Nat)
    (free : Metadata.observe state bucket index = .ok (true, false)) : readByte state bucket index = .ok 0#8 := by
  rw [observe_read_byte] at free
  cases read : readByte state bucket index with
  | error fault => simp only [read, Except.map] at free; contradiction
  | ok bits =>
    simp only [read, Except.map, Except.ok.injEq, Prod.mk.injEq] at free
    have zero : bits = 0#8 := beq_iff_eq.mp free.1
    simp only [zero]

structure Marked (bucket index : Nat) (fp : BitVec 7) (before after : State) : Prop where
  valid : after.valid = true
  shape : before.heap.RetainsShape after.heap
  frame : ∀ other, other ≠ bucket → after.heap.lookup other = before.heap.lookup other
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress
  read : load after (pointer bucket index) = .ok (value (occupied fp))
  outside : ∀ (writable many : Bool) (child : Ty) (offset : Nat),
    (∀ position ∈ child.readOffsets offset, position ≠ 24 + index) →
    load after (.pointer (.pointer writable many child) ⟨bucket, offset⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, offset⟩)

theorem store_outside (before after : State) (bucket index : Nat) (bits : BitVec 8)
    (stored : store before (pointer bucket index) (value bits) = .ok after)
    (writable many : Bool) (child : Ty) (offset : Nat)
    (apart : ∀ position ∈ child.readOffsets offset, position ≠ 24 + index) :
    load after (.pointer (.pointer writable many child) ⟨bucket, offset⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, offset⟩) := by
  apply load_disjoint_after_store before true false byte _ _ after writable many child offset stored
  simpa only [value, Value.leaves, List.mem_singleton, forall_eq, Nat.add_zero] using apart

theorem mark_verified (capacity : BitVec 32) (bucket index : Nat) (fp : BitVec 7)
    (before : State) (cell : Allocation) (bits : BitVec 8) (inside : index < capacity.toNat)
    (valid : before.valid = true) (found : before.heap.lookup bucket = some cell)
    (typed : cell.type = storageType capacity.toNat) (writable : cell.writable = true)
    (read : readByte before bucket index = .ok bits) :
    ∃ after, mark bucket index fp before = (.ok (), after) ∧ Marked bucket index fp before after := by
  obtain ⟨middle, first⟩ := store_byte_total before bucket cell capacity index (used bits) inside valid found typed writable
  change store before (pointer bucket index) (value (used bits)) = .ok middle at first
  have middleValid := store_preserves_valid _ _ _ _ valid first
  have firstShape := store_retains_shape _ _ _ _ first
  obtain ⟨middleCell, middleFound, shape⟩ := firstShape bucket cell found
  obtain ⟨after, second⟩ := store_byte_total middle bucket middleCell capacity index (occupied fp) inside middleValid
    middleFound (shape.2.1.trans typed) (shape.2.2.1.trans writable)
  change store middle (pointer bucket index) (value (occupied fp)) = .ok after at second
  have middleRead := load_after_store _ _ _ _ first
  refine ⟨after, ?_, store_preserves_valid _ _ _ _ middleValid second,
    firstShape.trans (store_retains_shape _ _ _ _ second),
    fun other apart => (heap_after_store_other _ true false byte _ _ _ second other apart).trans
      (heap_after_store_other _ true false byte _ _ _ first other apart),
    (store_keeps_counters _ _ _ _ second).1.trans (store_keeps_counters _ _ _ _ first).1,
    (store_keeps_counters _ _ _ _ second).2.trans (store_keeps_counters _ _ _ _ first).2,
    load_after_store _ _ _ _ second, ?_⟩
  · simp only [mark, read, first,
      read_byte_of_load middle bucket index (used bits) middleRead, (packed_exact bits fp).2.1, second]
  · intro writable many child offset apart
    exact (store_outside middle after bucket index (occupied fp) second writable many child offset apart).trans
      (store_outside before middle bucket index (used bits) first writable many child offset apart)

theorem Marked.headers (post : Marked bucket index fp before after) (capacity : BitVec 32) (slot : Header.Slot) :
    load after (slot.pointer capacity bucket) = load before (slot.pointer capacity bucket) := by
  apply post.outside true false (slot.value capacity bucket).type slot.offset
  cases slot <;> simp [Header.Slot.value, Header.Slot.offset, Value.type, Compiler.ZigAir.Scalar.Value.type,
    Ty.readOffsets] <;> omega

end Compiler.Extraction.ExpressionMap.Buckets.Metadata
