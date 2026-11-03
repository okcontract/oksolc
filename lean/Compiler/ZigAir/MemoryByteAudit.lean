/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryByteAccessTests
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
    ``Compiler.ZigAir.Memory.ByteAccess.write_store,
    ``Compiler.ZigAir.Memory.ByteAccess.number_valid,
    ``Compiler.ZigAir.Memory.ByteAccess.number_typed,
    ``Compiler.ZigAir.Memory.ByteAccess.wordAddress_atByte,
    ``Compiler.ZigAir.Memory.ByteAccess.atByte_lane,
    ``Compiler.ZigAir.Memory.ByteAccess.read_atByte,
    ``Compiler.ZigAir.Memory.ByteAccess.write_atByte,
    ``Compiler.ZigAir.Memory.ByteAccess.cast_address,
    ``Compiler.ZigAir.Memory.ByteAccess.cast_array,
    ``Compiler.ZigAir.Memory.ByteAccess.read_refines,
    ``Compiler.ZigAir.Memory.ByteAccess.write_refines,
    ``Compiler.ZigAir.Memory.ByteAccess.access_bytes,
    ``Compiler.ZigAir.Memory.ByteAccess.make_byte_slice,
    ``Compiler.ZigAir.Memory.ByteAccess.byte_element,
    ``Compiler.ZigAir.Memory.ByteAccess.cast_slice_element,
    ``Compiler.ZigAir.Memory.ByteAccess.read_alias,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_uninitialized,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.read_uninitialized,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.write_uninitialized,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_readonly,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.read_readonly,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.write_readonly,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_const_upgrade,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.write_const,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_alignment_zero,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_alignment_three,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_alignment_eight,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_alignment_one,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_alignment_two,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_unaligned,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_dead,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_outside,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.cast_wrong_subobject,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.read_byte_array,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.read_pointer_bytes,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.element_exact_bound,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.read_last_byte,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.read_outside,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.write_malformed,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.write_negative,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.air_cast,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.air_load,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.air_failure_retains_heap,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.air_missing_operand,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_0_0_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_0_1_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_0_2_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_0_3_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_1_0_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_1_1_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_1_2_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_1_3_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_2_0_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_2_1_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_2_2_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_2_3_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_3_0_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_3_1_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_3_2_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_3_3_little,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_0_0_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_0_1_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_0_2_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_0_3_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_1_0_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_1_1_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_1_2_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_1_3_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_2_0_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_2_1_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_2_2_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_2_3_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_3_0_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_3_1_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_3_2_big,
    ``Compiler.ZigAir.Memory.ByteAccess.Tests.case_3_3_big,
    ``Compiler.ZigAir.MemoryAir.Prim.eval_word_byte_cast,
    ``Compiler.ZigAir.MemoryAir.Prim.eval_word_byte_load,
    ``Compiler.ZigAir.MemoryAir.Prim.eval_word_byte_store,
    ``Compiler.ZigAir.MemoryAir.Prim.preserves_valid,
    ``Compiler.ZigAir.MemoryAir.Prim.failure_retains_state,
    ``Compiler.ZigAir.MemoryAir.Program.preserves_valid,
    ``Compiler.ZigAir.MemorySliceInvocation.run_preserves,
    ``Compiler.ZigAir.MemoryExp.exp_safe_terminates,
    ``Compiler.ZigAir.MemoryExp.exp_preserves_caller_heap,
    ``Compiler.Extraction.InsertionSort.Heap.run_refines]
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
    ("schema", .str "oksolc.byte-access-audit.v1"), ("scope", .str "typedHeapByteAddressOperations"),
    ("sourceSafetyVerified", .bool false), ("wholeCompilerVerified", .bool false),
    ("claims", .arr claims)]).pretty
