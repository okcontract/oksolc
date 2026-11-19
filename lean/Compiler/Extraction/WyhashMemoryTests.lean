/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapWyhashMemory
import Compiler.Extraction.ExpressionMapHashBytesTests
import Compiler.Extraction.ExpressionMapHashOrderTests
import Compiler.Extraction.WyhashHashTests
import Compiler.ZigAir.WyhashInitTests
import Compiler.ZigAir.AggregateAirTests
import Compiler.ZigAir.WyhashUpdateAirTests
import Compiler.ZigAir.WyhashUpdateAirRefinementTests
import Compiler.ZigAir.WyhashUpdateAirLaneRefinement
import Compiler.ZigAir.WyhashUpdateAirLoopTests
import Compiler.ZigAir.WyhashUpdateAirLongTests
import Compiler.ZigAir.WyhashUpdateAirCompleteTests

set_option maxRecDepth 4096

namespace Compiler.Extraction.WyhashMemory.Tests
open Compiler.ZigAir.Memory WyhashLocal

/-- A partially initialized, read-only caller object must survive exactly. -/
def caller (address : Nat := 4096) : State :=
  ⟨[(0, ⟨16, .array 4 ByteSlice.byte, [(1, ByteSlice.value 37)], false, false⟩)], 1, address⟩

theorem caller_valid : (caller).valid = true := by decide +kernel

/-- The first allocation belongs to the caller. The initializer's three locals
retire before its returned sparse value is stored into that first allocation. -/
theorem initialized_local :
    Compiler.ZigAir.WyhashCallerInit.run caller 0 =
      (.ok 1, { caller with
        heap := (1, ⟨4096, objectType, WyhashUpdate.initialCells (WyhashUpdate.seedState 0), true, true⟩) :: caller.heap
        nextId := 5, nextAddress := 4320 }) := by decide +kernel

/-- Every nested allocation failure retains the empty caller-owned hasher and
the reached cursors. Outer invocation cleanup is tested separately below. -/
theorem nested_initialization_failures : [(208, 2, 104), (216, 3, 8), (224, 4, 8)].all (fun (room, nextId, remaining) =>
    let before := caller (addressLimit - room)
    decide (Compiler.ZigAir.WyhashCallerInit.run before 0 =
      (.error .outOfMemory, { before with
        heap := (1, ⟨addressLimit - room, objectType, [], true, true⟩) :: before.heap
        nextId, nextAddress := addressLimit - remaining }))) = true := by decide +kernel

/-- Updates consume the stored local; an absent initializer result cannot be
replaced by a separately supplied initial value. -/
theorem missing_initializer_store_rejected :
    let state := { caller with
      heap := (1, ⟨4096, objectType, [], true, true⟩) :: caller.heap
      nextId := 5, nextAddress := 4320 }
    runInitializedRaw state 1 [[1, 2, 3]] = (.error .uninitialized, state) := by decide +kernel

/-- Reuse captured streams for the buffer, retained suffix and full-block loop.
The heap adapter must return the captured digest and retire all six locals, including the captured initializer call. -/
theorem captured_scoped_results : [0, 6, 11].all (fun index =>
    let (sizes, expected) := WyhashHash.Tests.vectors[index]?.getD ([], 0)
    let (result, after) := run caller 0 (WyhashHash.Tests.chunks index 0 sizes)
    decide (result = .ok expected ∧ after = { caller with nextId := 7, nextAddress := 4440 })) = true := by decide +kernel

/-- Exhaustion at each allocation retains the reached counters, including the
unconditionally allocated scratch in the long buffered branch. -/
theorem allocation_rejections : [(104, 1, 104), (208, 2, 104), (216, 3, 8), (224, 4, 8), (328, 5, 104), (344, 6, 16)].all (fun (room, nextId, remaining) =>
    let before := caller (addressLimit - room)
    let (result, after) := run before 0 (WyhashHash.Tests.chunks 0 0 [4, 1, 32, 0, 4])
    decide (result = .error .outOfMemory ∧ after = { before with nextId, nextAddress := addressLimit - remaining })) = true := by decide +kernel

def emptyLocal : Allocation := ⟨4096, objectType, [], true, true⟩
def localState : State := ⟨[(1, emptyLocal)], 2, 4200⟩

theorem uninitialized_word_rejected : (ops localState 1 emptyLocal).read [] 0 = .error .uninitialized := by decide +kernel

theorem readonly_word_rejected :
    (ops { localState with heap := [(1, { emptyLocal with writable := false })] } 1
      { emptyLocal with writable := false }).write [] 0 7 = .error .readOnly := by decide +kernel

theorem partial_input_cleanup :
    run caller 0 [[1, 2, 3]] = (.error .unsupported, { caller with nextId := 6, nextAddress := 4424 }) := by decide +kernel

end Compiler.Extraction.WyhashMemory.Tests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapScopedWyhashTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ExpressionMap
open MapTableTests (prepared firstKey)

def probed := Search.insertionWithScopedWyhash .localMap true (prepared true).memory.memory 4 firstKey (view ⟨0, []⟩)

def published : Except Compiler.ZigAir.Memory.Fault Unit × World (Publication.Effects Nat) :=
  match probed.1 with
  | .error fault => (.error fault, withMemory (prepared true) probed.2)
  | .ok (.hit _) => (.error .unsupported, withMemory (prepared true) probed.2)
  | .ok (.miss index first) => publishFromReceiver .localMap true 4 index first (WyhashHash.digest (HashInput.encode firstKey))
      firstKey ⟨0, []⟩ 37 (withMemory (prepared true) probed.2)

/-- Publication and the following lookup retain the counters from both hashes. -/
theorem publication_lookup :
    published.1 = .ok () ∧ published.2.memory.memory.nextId = (prepared true).memory.memory.nextId + 8 ∧
    (Search.withScopedWyhash .localMap true published.2.memory.memory 4 firstKey (view ⟨0, []⟩)).1 = .ok (some 37) ∧
    (Search.withScopedWyhash .localMap true published.2.memory.memory 4 firstKey (view ⟨0, []⟩)).2.nextId =
      (prepared true).memory.memory.nextId + 16 := by decide +kernel

theorem original_bytes_consumed :
    (Search.scopedHash MapTableTests.native MapKeyTests.sample ⟨3, 0, 3⟩).1 =
      .ok (WyhashHash.digest (HashInput.encode MapKeyTests.sample)) ∧
    (Search.scopedHash MapTableTests.native MapKeyTests.sample ⟨3, 0, 3⟩).2.heap = MapTableTests.native.heap := by decide +kernel

theorem missing_bytes_rejected :
    Search.scopedHash MapTableTests.native MapKeyTests.sample ⟨999, 0, 3⟩ =
      (.error .unallocated, { MapTableTests.native with
        nextId := MapTableTests.native.nextId + 6, nextAddress := 9328 }) := by decide +kernel

theorem empty_skips_allocation (safety : Bool) (key : Key) :
    Search.withScopedWyhash .embedded safety (GraphInit.Ownership.Tests.owned safety).memory.memory 3 key ⟨999, 0, 1⟩ =
      (.ok none, (GraphInit.Ownership.Tests.owned safety).memory.memory) := by
  have zero : Search.readCount .embedded safety (GraphInit.Ownership.Tests.owned safety).memory.memory 3 = .ok 0 := by cases safety <;> decide +kernel
  simp only [Search.withScopedWyhash, zero, ↓reduceIte]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapScopedWyhashTests
