/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashKey
import Compiler.Extraction.ExpressionMapHashInput
import Compiler.ZigAir.SliceBytesAir

namespace Compiler.Extraction.ExpressionMap.HashSlice
open Compiler.ZigAir Compiler.ZigAir.Memory Compiler.ZigAir.AggregateAir
open Compiler.Extraction.Cache (Key)
open Buckets

/-- Execute the captured field selection, descriptor load, complete slice
helper and alignment weakening, retaining the callee's allocation history. -/
def view (state : State) (id : Nat) : Except Fault Register × State :=
  match (GeneratedExpressionHashSlice.argumentsView (.ret (.local 39))).eval AggregateCall.semantics []
      (Control.Env.set (fun _ => none) 3 (.value (.pointer (.pointer false false keyType) ⟨id, 0⟩))) state with
  | .returned value after => (.ok value, after)
  | .fault fault after => (.error fault, after)
  | .jumped _ _ _ after => (.error .malformed, after)

theorem view_verified (state : State) (id : Nat) (key : Key) (source : WordArray.View)
    (valid : state.valid = true) (binding : HashKey.Binding state id key (source.address 0))
    (represented : WordArray.Represents state source key.arguments) (bounded : source.length * 4 < addressLimit) :
    ∃ output after, view state id = (output, after) ∧ StackFrame state after ∧ after.heap = state.heap ∧
      (output = .ok (SliceBytesAir.result source) ∨ output = .error .outOfMemory) := by
  have lengthBound : key.arguments.length < addressLimit := by have := represented.1; omega
  let env : Env := Control.Env.set (fun _ => none) 3 (.value (.pointer (.pointer false false keyType) ⟨id, 0⟩))
  let pointer := Value.pointer (.pointer false false SliceBytesAir.wordSlice) ⟨id, 32⟩
  let e32 := env.set 32 (.value pointer)
  let e33 := e32.set 33 (.value source.readonlySlice)
  have selected := binding.select valid .arguments
  have field : (AggregateCall.Prim.primitive (.fieldPointer (.local 3) 32)).eval [] env state =
      (.ok (.value pointer), state) := by
    exact eval_field _ _ _ _ _ _ _ (value_local env 3 _ (by simp [env, Control.Env.set]) rfl) selected
  have contents : Memory.load state pointer = .ok source.readonlySlice := by
    simpa only [KeyFields.value, KeyFields.offset, Value.type, represented.1] using binding.load valid lengthBound .arguments
  have loaded : (AggregateCall.Prim.primitive (.load (.local 32))).eval [] e32 state =
      (.ok (.value source.readonlySlice), state) := by
    apply eval_load _ _ _ _ pointer
    · exact value_local e32 32 _ (by simp [e32, Control.Env.set]) rfl
    · simp only [AggregateAir.load, pointer, show aggregateType SliceBytesAir.wordSlice = false from rfl,
        Bool.false_eq_true, ↓reduceIte, contents, bind, Except.bind, pure, Except.pure]
  have inputValid := SliceBytesAir.slice_valid source (by omega)
  have inputTyped : (Register.value source.readonlySlice).hasType SliceBytesAir.wordSlice = true := by
    simpa only [Register.hasType, Register.type, WordArray.View.readonlySlice, Value.type,
      decide_true, Bool.true_and] using inputValid
  have called : (AggregateCall.Prim.invoke GeneratedExpressionHashSlice.arguments [.local 33]).eval [] e33 state =
      GeneratedExpressionHashSlice.arguments.run [.value source.readonlySlice] state := by
    simp only [AggregateCall.Prim.eval, List.mapM_cons, List.mapM_nil,
      ref_local e33 33 (.value source.readonlySlice) (by simp [e33, Control.Env.set]) inputValid,
      bind, Except.bind, pure, Except.pure]
  obtain ⟨output, after, ran, frame, heap, returned | failed⟩ := SliceBytesAir.verified state source key.arguments valid represented bounded
  · rw [returned] at ran
    have resultTyped := SliceBytesAir.result_typed source bounded
    change (SliceBytesAir.result source).hasType (.slice false (.scalar (.int false 8))) = true at resultTyped
    have resultValid : (SliceBytesAir.result source).valid = true := by
      have parts := resultTyped
      simp only [Register.hasType, Bool.and_eq_true] at parts
      exact parts.2
    let e38 := e33.set 38 (SliceBytesAir.result source)
    have copied : (AggregateCall.Prim.primitive (.copy (.local 38))).eval [] e38 after =
        (.ok (SliceBytesAir.result source), after) := by
      simp only [AggregateCall.Prim.eval, Prim.eval, Prim.transition,
        ref_local e38 38 _ (by simp [e38, Control.Env.set]) resultValid, bind, Except.bind, pure, Except.pure]
    refine ⟨_, after, ?_, frame, heap, Or.inl rfl⟩
    unfold view
    rw [GeneratedExpressionHashSlice.argumentsView, AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ field (by rfl),
      AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ loaded inputTyped,
      AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ (called.trans ran) resultTyped,
      AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ copied resultTyped]
    have returnRead := ref_local (e38.set 39 (SliceBytesAir.result source)) 39 (SliceBytesAir.result source)
      (by simp [Control.Env.set]) resultValid
    simp only [Control.Code.eval, AggregateCall.semantics, returnRead]
  · rw [failed] at ran
    refine ⟨_, after, ?_, frame, heap, Or.inr rfl⟩
    unfold view
    rw [GeneratedExpressionHashSlice.argumentsView, AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ field (by rfl),
      AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ loaded inputTyped,
      AggregateCall.bind_fault _ _ _ _ _ _ _ _ _ (called.trans ran)]

/-- Interpret precisely the returned byte extent through the shared word-byte
codec. Anonymous empty storage has no pointer identity or readable element. -/
def read (state : State) : Register → Except Fault (List (BitVec 8))
  | .emptyBytes => .ok []
  | .value (.slice (.slice false (.scalar (.int false 8))) address length) =>
    if address.offset % 4 ≠ 0 ∨ length % 4 ≠ 0 then .error .memoryValidity else
    ArgumentScan.bytes state ⟨address.allocation, address.offset / 4, length / 4⟩ 0 (List.range length)
  | _ => .error .unsupported

theorem read_verified (state : State) (source : WordArray.View) (items : List (BitVec 32))
    (represented : WordArray.Represents state source items) :
    read state (SliceBytesAir.result source) = .ok (HashInput.arguments items) := by
  by_cases empty : source.length = 0
  · have itemsEmpty : items = [] := by
      have length := represented.1.trans empty
      cases items with
      | nil => rfl
      | cons head tail => simp only [List.length_cons] at length; omega
    simp only [SliceBytesAir.result, if_pos empty, read, itemsEmpty, HashInput.arguments, List.length_nil,
      Nat.zero_mul, List.range_zero, List.map_nil]
  · simpa only [SliceBytesAir.result, if_neg empty, WordArray.View.byteSlice, ByteAccess.byte, read,
      WordArray.View.address, Nat.add_zero, Nat.mul_mod_left, ne_self_iff_false, or_self, ↓reduceIte,
      Nat.mul_div_cancel _ (by decide : 0 < 4)] using HashInput.arguments_read_verified state source items represented

def bytes (state : State) (id : Nat) : Except Fault (List (BitVec 8)) × State :=
  let (output, after) := view state id
  (output.bind (read after), after)

theorem bytes_verified (state : State) (id : Nat) (key : Key) (source : WordArray.View)
    (valid : state.valid = true) (binding : HashKey.Binding state id key (source.address 0))
    (represented : WordArray.Represents state source key.arguments) (bounded : source.length * 4 < addressLimit) :
    ∃ output after, bytes state id = (output, after) ∧ StackFrame state after ∧ after.heap = state.heap ∧
      (output = .ok (HashInput.arguments key.arguments) ∨ output = .error .outOfMemory) := by
  obtain ⟨output, after, ran, frame, heap, returned | failed⟩ := view_verified state id key source valid binding represented bounded
  · exact ⟨_, after, by simp only [bytes, ran, returned, Except.bind, read_verified after source key.arguments (represented.extend frame)],
      frame, heap, Or.inl rfl⟩
  · exact ⟨_, after, by simp only [bytes, ran, failed, Except.bind], frame, heap, Or.inr rfl⟩

end Compiler.Extraction.ExpressionMap.HashSlice
