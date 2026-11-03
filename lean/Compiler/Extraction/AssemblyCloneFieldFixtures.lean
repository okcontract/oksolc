/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemCreationFields
import Compiler.Extraction.AssemblyItemCreationTests

namespace Compiler.Extraction.AssemblyItem.Creation.NativeFields.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Extraction.Storage
open AssemblyClone.NativeFields
open Fields
open AssemblyClone.Physical.Tests (bytes objects external)

def metadata : Values
  | .kind => .scalar (.int true 32 2)
  | .instruction => OptionalScalar.byteValue none
  | .pushed => OptionalScalar.unsignedValue 256 (some (2^255))
  | .immutable => OptionalScalar.unsignedValue 64 (some 9)
  | .modifier => .scalar (.int false 64 17)
  | .jump => .scalar (.int true 32 2)
  | selected => Initializers.Tests.values selected

def input : ItemValue := ⟨{ kind := 1, instruction := some 254, data := 987 }, metadata,
  some ⟨2, 3, ⟨3, [8, 9], 1⟩⟩⟩

-- Independent literal field oracle. It neither enumerates `members` nor calls
-- the clone field encoder. Removing a write cannot remove its expected cell.
def expectedCells (payloadAddress payloadOffset : Nat) : Cells := [
  (168, MemberTests.astValue (some (-1))), (144, MemberTests.sourceValue (some (⟨100, 7⟩, 0))),
  (164, .scalar (.int true 32 (2^31-1))), (160, .scalar (.int true 32 (-(2^31)))),
  (120, MemberTests.sourceValue (some (⟨99, 2⟩, 3))), (140, .scalar (.int true 32 17)),
  (136, .scalar (.int true 32 (-1))), (212, .scalar (.int true 32 2)), (200, .scalar (.int false 64 17)),
  (184, OptionalScalar.unsignedValue 64 (some 9)), (32, OptionalScalar.unsignedValue 256 (some (2^255))),
  (80, MemberTests.verbatimValue (some (MemberTests.payload 2 3 ⟨payloadAddress, payloadOffset⟩ 2))),
  (0, .scalar (.int false 256 987)), (216, OptionalScalar.byteValue (some 254)), (208, .scalar (.int true 32 1))]

def sourceCell : Compiler.ZigAir.Memory.Allocation := { Creation.cell 512 with cells := expectedCells 3 1, writable := false }
def initial : Session Nat := { Insertion.Tests.initial with memory :=
  ⟨(5, sourceCell) :: Insertion.Tests.initial.memory.heap, 6, 736⟩ }
def source : Address := ⟨5, 0⟩

theorem initial_frame (id : Nat) (apart : id ≠ 5) :
    initial.memory.heap.lookup id = Insertion.Tests.initial.memory.heap.lookup id := by
  simp only [initial, Heap.lookup_cons, Ne.symm apart, ↓reduceIte]

theorem initial_valid : Valid initial := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id contents nonempty stored
    obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ :=
      Insertion.Tests.initial_valid.related allocator id contents nonempty stored
    have older := (valid_lookup _ id cell Insertion.Tests.initial_valid.memory found).1
    have same := initial_frame id (by change id < 5 at older; omega)
    exact ⟨⟨cell, same.trans found, typed, writable, stack⟩, represented_frame _ _ represented same⟩
  · intro id block stored
    obtain ⟨cell, found, persistent⟩ := Insertion.Tests.initial_valid.injected id block stored
    have older := (valid_lookup _ id cell Insertion.Tests.initial_valid.memory found).1
    exact ⟨cell, (initial_frame id (by change id < 5 at older; omega)).trans found, persistent⟩

theorem source_represented : Represents initial.memory source input := by
  intro selected; cases selected <;> decide +kernel

end Compiler.Extraction.AssemblyItem.Creation.NativeFields.Tests
