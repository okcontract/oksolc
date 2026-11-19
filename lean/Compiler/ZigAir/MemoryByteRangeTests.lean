/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateExecution

namespace Compiler.ZigAir.Memory.ByteRange.Tests
open AggregateAir
deriving instance DecidableEq for Except

def word : Ty := .scalar (.int false 32)
def input : Allocation := ⟨16, .array 2 word,
  [(0, .scalar (.int false 32 0x04030201)), (4, .scalar (.int false 32 0x08070605))], false, false⟩
def output : Allocation := ⟨32, .array 8 byte, [], true, false⟩
def state : State := ⟨[(0, input), (1, output)], 2, 40⟩
def src : Value := .pointer (.pointer false true byte) ⟨0, 0⟩
def dst : Value := .slice (.slice true byte) ⟨1, 0⟩ 8
def copied : State := (copy state dst src).2

theorem valid_fixture : state.valid = true := by decide +kernel

theorem reads_original_integer_leaves :
    (copy state dst src).1 = .ok () ∧
    read copied ⟨1, 0⟩ 8 = .ok [1, 2, 3, 4, 5, 6, 7, 8] ∧
    copied.heap.lookup 0 = some input ∧ copied.nextId = state.nextId ∧
    copied.nextAddress = state.nextAddress := by decide +kernel

def missing : State := { state with heap := [(0, { input with cells := [(0, .scalar (.int false 32 0x04030201))] }), (1, output)] }
def prefixState : State := (copyLoop missing ⟨0, 0⟩ ⟨1, 0⟩ 0 4).2

theorem fault_retains_initialized_prefix :
    missing.valid = true ∧ copy missing dst src = (.error .uninitialized, prefixState) ∧
    read prefixState ⟨1, 0⟩ 4 = .ok [1, 2, 3, 4] ∧
    ScalarBytes.readAt prefixState ⟨1, 4⟩ = .error .uninitialized := by decide +kernel

theorem call_primitive_keeps_fault_state :
    (AggregateCall.Prim.copyBytes (.constant (.value dst)) (.constant (.value src))).eval
      [] (fun _ => none) missing = (.error .uninitialized, prefixState) := by decide +kernel

theorem alias_and_permissions_reject :
    copy state (.slice (.slice true byte) ⟨0, 1⟩ 4) src = (.error .memoryValidity, state) ∧
    copy state (.slice (.slice false byte) ⟨1, 0⟩ 8) src = (.error .readOnly, state) ∧
    copy state dst (.pointer (.pointer false false (.array 7 byte)) ⟨0, 0⟩) =
      (.error .sourceBounds, state) := by decide +kernel

theorem empty_skips_access :
    copy {} (.slice (.slice true byte) ⟨7, 0⟩ 0) src = (.ok (), {}) := by decide +kernel

theorem array_load_and_bitcast_read_original_bytes :
    (AggregateAir.Prim.loadBytes (.constant (.value
      (.pointer (.pointer false false (.array 8 byte)) ⟨0, 0⟩)))).eval [] (fun _ => none) state =
      (.ok (.bytes [1, 2, 3, 4, 5, 6, 7, 8]), state) ∧
    (AggregateAir.Prim.bytesToWord (.constant (.bytes [1, 2, 3, 4, 5, 6, 7, 8]))).eval
      [] (fun _ => none) state = (.ok (.value (.scalar (.int false 64 0x0807060504030201))), state) := by decide +kernel

theorem assertion_failure_is_terminal :
    (AggregateAir.Prim.booleanNot (.constant (.value (.scalar (.bool false))))).eval
      [] (fun _ => none) state = (.ok (.value (.scalar (.bool true))), state) ∧
    AggregateAir.Prim.unreachable.eval [] (fun _ => none) state =
      (.error (.scalar .illegalBehavior), state) := by decide +kernel

end Compiler.ZigAir.Memory.ByteRange.Tests
