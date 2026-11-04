/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemorySliceTests
import Compiler.ZigAir.MemoryTests
import Compiler.ZigAir.MemoryLoopTests
import Compiler.ZigAir.MemoryExecutionTests
import Compiler.ZigAir.MemoryFillInvocationTests
import Compiler.ZigAir.MemoryExpSafetyTests
import Compiler.ZigAir.MemoryWordBytesTests
import Compiler.Extraction.InsertionSortHeapTests
import Contract.Check.Declarations
import Lean.Elab.Command

-- Shared memory clients are replayed together; this audit never claims native
-- or source-language preservation from model proofs or finite observations.
open Lean Elab Command Contract.Check in
run_cmd do
  let roots := #[
    ``Compiler.ZigAir.Memory.sliceElementPointer_in_bounds,
    ``Compiler.ZigAir.Memory.sliceElementPointer_out_of_bounds,
    ``Compiler.ZigAir.Memory.sliceElementPointer_address,
    ``Compiler.ZigAir.Memory.WordArray.slice_element,
    ``Compiler.ZigAir.Memory.WordArray.make_slice,
    ``Compiler.ZigAir.Memory.WordArray.writable_allocate,
    ``Compiler.ZigAir.Memory.WordArray.offset_zero,
    ``Compiler.ZigAir.Memory.Cells.write_root,
    ``Compiler.ZigAir.Memory.fresh_store_total,
    ``Compiler.ZigAir.Memory.allocate_fault_of_layout,
    ``Compiler.ZigAir.MemoryAir.Prim.eval_slice_element,
    ``Compiler.ZigAir.MemoryAir.Prim.eval_slice,
    ``Compiler.ZigAir.MemoryAir.Prim.eval_bounds,
    ``Compiler.ZigAir.MemorySliceInvocation.generated_body,
    ``Compiler.ZigAir.MemorySliceInvocation.run_preserves,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.valid_caller,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.case_0,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.case_1,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.case_2,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.case_3,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.case_4,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.case_5,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.case_6,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.case_7,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.exact_slice_bound,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.empty_slice,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.allocation_extent,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.valid_first_exhausted,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.valid_second_exhausted,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.first_allocation_exhausted,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.second_allocation_exhausted,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.uninitialized_address,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.dead_slice,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.oversized_slice,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.zero_sized_child,
    ``Compiler.ZigAir.MemorySliceInvocation.Tests.total_invocation_witness]
  let mut claims := #[]
  for root in roots do
    let .ok dependencies := Declarations.closure (← getEnv) #[root] | throwError "invalid closure: {root}"
    let .ok axioms := Declarations.axioms dependencies | throwError "disallowed axiom: {root}"
    let some info := (← getEnv).find? root | throwError "missing theorem: {root}"
    unless info matches .thmInfo _ do throwError "not a theorem: {root}"
    claims := claims.push <| Json.mkObj [
      ("theorem", .str root.toString), ("statement", Declarations.expression info.type),
      ("axioms", toJson axioms), ("dependencies", toJson (dependencies.map (·.name.toString)))]
  liftIO <| IO.println (Json.mkObj [
    ("schema", .str "oksolc.slice-element-audit.v1"), ("scope", .str "zigFreshAirTypedHeap"),
    ("sourceSafetyVerified", .bool false), ("wholeCompilerVerified", .bool false),
    ("claims", .arr claims)]).pretty
