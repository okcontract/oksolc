/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketLayout
import Compiler.Extraction.InternerNativeGraphPrivateRegions

namespace Compiler.Extraction.ExpressionMap.Buckets
open Compiler.ZigAir.Memory

theorem layout (capacity : Nat) : (allocationType capacity).layout = some ⟨bytes capacity, 16⟩ := by
  rfl

/-- Native Size is u32. Every intermediate extent, including rounding slack,
fits usize on the captured 64-bit ABI. This does not prove growth's capacity
selection or admit non-u32 requests. -/
theorem geometry (capacity : Nat) (bounded : capacity < 2 ^ 32) :
    24 + capacity ≤ keysOffset capacity ∧
    keysOffset capacity + capacity * 64 ≤ valuesOffset capacity ∧
    valuesOffset capacity + capacity * 4 ≤ bytes capacity ∧
    keysOffset capacity % 16 = 0 ∧ valuesOffset capacity % 4 = 0 ∧ bytes capacity % 16 = 0 ∧
    0 < bytes capacity ∧ bytes capacity < addressLimit := by
  simp only [keysOffset, valuesOffset, bytes, alignForward, headerBytes, metadataBytes, keyBytes,
    keyAlignment, valueBytes, valueAlignment, allocationAlignment, Nat.mul_one, addressLimit] at *
  omega

/-- Word-level alignment used by the pinned std.mem implementations. Arithmetic
stays in the source width; the bridge below supplies the no-overflow condition. -/
def sourceAlign (shift : Nat) (value : BitVec 64) : BitVec 64 :=
  let mask := BitVec.ofNat 64 (2 ^ shift - 1)
  (value + mask) &&& ~~~mask

theorem sourceAlign_toNat (shift : Nat) (value : BitVec 64) (supported : shift = 2 ∨ shift = 4)
    (bounded : value.toNat + (2 ^ shift - 1) < addressLimit) :
    (sourceAlign shift value).toNat = alignForward value.toNat (2 ^ shift) := by
  have mask : ~~~(BitVec.ofNat 64 (2 ^ shift - 1)) = (BitVec.allOnes 64) <<< shift := by
    rcases supported with rfl | rfl <;> decide +kernel
  dsimp only [sourceAlign]
  rw [mask, ← BitVec.shiftLeft_ushiftRight]
  rcases supported with rfl | rfl
  all_goals
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, alignForward, addressLimit] at *
    omega

/-- The complete allocation-size expression from the pinned native allocate
body, including its usize additions, products and all three alignments. -/
def sourceRequest (capacity : BitVec 32) : BitVec 64 :=
  let count := capacity.setWidth 64
  let keys := sourceAlign 4 (24 + count)
  let values := sourceAlign 2 (keys + count * 64)
  sourceAlign 4 (values + count * 4)

def sourceKeys (capacity : BitVec 32) : BitVec 64 :=
  sourceAlign 4 (24 + capacity.setWidth 64)

def sourceValues (capacity : BitVec 32) : BitVec 64 :=
  sourceAlign 2 (sourceKeys capacity + capacity.setWidth 64 * 64)

/-- The same native arithmetic supplies both pointer offsets and the allocation
extent. Header initialization consumes these offsets without assuming them. -/
theorem source_layout (capacity : BitVec 32) :
    (sourceKeys capacity).toNat = keysOffset capacity.toNat ∧
    (sourceValues capacity).toNat = valuesOffset capacity.toNat ∧
    (sourceRequest capacity).toNat = bytes capacity.toNat := by
  have bounded := capacity.isLt
  have widened : (capacity.setWidth 64).toNat = capacity.toNat := BitVec.toNat_setWidth_of_le (by decide)
  have limits : 24 + capacity.toNat + 15 < addressLimit ∧
      keysOffset capacity.toNat + capacity.toNat * 64 + 3 < addressLimit ∧
      valuesOffset capacity.toNat + capacity.toNat * 4 + 15 < addressLimit := by
    simp only [keysOffset, valuesOffset, alignForward, headerBytes, metadataBytes, keyBytes,
      keyAlignment, valueAlignment, Nat.mul_one, addressLimit]
    omega
  have header : ((24 : BitVec 64) + capacity.setWidth 64).toNat = 24 + capacity.toNat := by
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, widened]
    omega
  have keys : (sourceAlign 4 (24 + capacity.setWidth 64)).toNat = keysOffset capacity.toNat := by
    rw [sourceAlign_toNat 4 _ (Or.inr rfl) (by rw [header]; exact limits.1), header]
    simp only [keysOffset, headerBytes, metadataBytes, keyAlignment, Nat.mul_one]
  have keyBytes : (capacity.setWidth 64 * 64).toNat = capacity.toNat * 64 := by
    simp only [BitVec.toNat_mul, widened, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
    omega
  have keysEnd : (sourceAlign 4 (24 + capacity.setWidth 64) + capacity.setWidth 64 * 64).toNat =
      keysOffset capacity.toNat + capacity.toNat * 64 := by
    simp only [BitVec.toNat_add, keys, keyBytes]
    have small := limits.2.1
    unfold addressLimit at small
    omega
  have values : (sourceAlign 2 (sourceAlign 4 (24 + capacity.setWidth 64) + capacity.setWidth 64 * 64)).toNat =
      valuesOffset capacity.toNat := by
    rw [sourceAlign_toNat 2 _ (Or.inl rfl) (by rw [keysEnd]; exact limits.2.1), keysEnd]
    rfl
  have valueBytes : (capacity.setWidth 64 * 4).toNat = capacity.toNat * 4 := by
    simp only [BitVec.toNat_mul, widened, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
    omega
  have valuesEnd : (sourceAlign 2 (sourceAlign 4 (24 + capacity.setWidth 64) + capacity.setWidth 64 * 64) +
      capacity.setWidth 64 * 4).toNat = valuesOffset capacity.toNat + capacity.toNat * 4 := by
    simp only [BitVec.toNat_add, values, valueBytes]
    have small := limits.2.2
    unfold addressLimit at small
    omega
  refine ⟨keys, values, ?_⟩
  dsimp only [sourceRequest]
  rw [sourceAlign_toNat 4 _ (Or.inr rfl) (by rw [valuesEnd]; exact limits.2.2), valuesEnd]
  rfl

theorem source_request (capacity : BitVec 32) : (sourceRequest capacity).toNat = bytes capacity.toNat :=
  (source_layout capacity).2.2

end Compiler.Extraction.ExpressionMap.Buckets

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The source u32 capacity determines the complete private allocation request.
Header/metadata/key writes and native map ownership are not supplied by reserve. -/
def reserveBuckets (capacity : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before : World (Publication.Effects σ)) :=
  PrivateRegion.reserve (ExpressionMap.Buckets.allocationType capacity.toNat) allocate before

theorem Facts.reserve_buckets {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (bucketCapacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) :
    Facts safety allocator owner data capacity (reserveBuckets bucketCapacity allocate before).2 rows :=
  facts.reserve_private _ allocate

theorem Facts.reserve_buckets_success {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (bucketCapacity : BitVec 32) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (ExpressionMap.Buckets.sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory
      ⟨ExpressionMap.Buckets.bytes bucketCapacity.toNat, 16⟩ base) :
    ∃ after, reserveBuckets bucketCapacity allocate before = (.ok (some ⟨before.memory.memory.nextId, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      after.memory.memory.heap.lookup before.memory.memory.nextId =
        some ⟨base, ExpressionMap.Buckets.allocationType bucketCapacity.toNat, [], true, false⟩ ∧
      after.memory.heap before.memory.memory.nextId = none ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      after.memory.memory.nextAddress = max before.memory.memory.nextAddress (base + ExpressionMap.Buckets.bytes bucketCapacity.toNat) ∧
      after.memory.effects.allocator = effects := by
  have checked := ExpressionMap.Buckets.geometry bucketCapacity.toNat bucketCapacity.isLt
  exact facts.reserve_private_success _ _ base allocate effects (ExpressionMap.Buckets.layout _)
    (Nat.ne_of_gt checked.2.2.2.2.2.2.1) checked.2.2.2.2.2.2.2
    (by simpa only [ExpressionMap.Buckets.source_request] using response) fits

theorem reserveBuckets_oom (before : World (Publication.Effects σ)) (bucketCapacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (valid : before.memory.memory.valid = true)
    (response : allocate (ExpressionMap.Buckets.sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (none, effects)) :
    reserveBuckets bucketCapacity allocate before = (.ok none, { before with memory := { before.memory with
      effects := { before.memory.effects with allocator := effects } } }) := by
  have checked := ExpressionMap.Buckets.geometry bucketCapacity.toNat bucketCapacity.isLt
  exact PrivateRegion.oom before _ ⟨ExpressionMap.Buckets.bytes bucketCapacity.toNat, 16⟩ allocate effects valid
    (ExpressionMap.Buckets.layout _) (Nat.ne_of_gt checked.2.2.2.2.2.2.1) checked.2.2.2.2.2.2.2
    (by simpa only [ExpressionMap.Buckets.source_request] using response)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
