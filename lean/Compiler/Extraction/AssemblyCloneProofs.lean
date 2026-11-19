/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssemblyCloneProgram
import Compiler.Extraction.CacheProofs

namespace Compiler.Extraction.AssemblyClone
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
set_option linter.unusedSimpArgs false

theorem clone_none (duplicate : Bytes → σ → Except ε Bytes × σ) (input : Value Metadata)
    (absent : input.verbatim = none) (before : σ) :
    cloneCode.run duplicate input before = (.ok input, before) := by
  simp [CloneCode.run, absent]

theorem clone_some (duplicate : Bytes → σ → Except ε Bytes × σ) (input : Value Metadata)
    (payload : Verbatim) (present : input.verbatim = some payload) (before : σ) :
    cloneCode.run duplicate input before =
      match duplicate payload.data before with
      | (.error error, after) => (.error error, after)
      | (.ok copied, after) => (.ok { input with verbatim := some { payload with data := copied } }, after) := by
  simp only [CloneCode.run, cloneCode, present, Scalar.run, ↓reduceIte]
  cases step : duplicate payload.data before with
  | mk outcome after => cases outcome <;> rfl

/-- Reduces the compiler-owned clone contract to dupe's byte-preservation,
failure-atomicity, frame and ownership contracts. It assumes no clone contract. -/
theorem clone_safe (frame : Heap → Heap → Prop) (owns : Bytes → Bytes → Heap → Heap → Prop)
    (duplicate : Bytes → Effect Heap Error Bytes) (safe : Duplicates frame owns duplicate)
    (input : Value Metadata) (before : Heap) (result : Except Error (Value Metadata)) (after : Heap)
    (ran : cloneCode.run duplicate input before = (result, after)) :
    match result with
    | .error _ => after = before
    | .ok copied => Cloned frame owns input copied before after := by
  cases payload : input.verbatim with
  | none =>
    rw [clone_none duplicate input payload before] at ran
    cases ran
    exact ⟨⟨rfl, rfl, rfl⟩, by simp [payload]⟩
  | some source =>
    rw [clone_some duplicate input source payload before] at ran
    cases step : duplicate source.data before with
    | mk outcome middle =>
      have checked := safe source.data before outcome middle step
      cases outcome with
      | error error =>
        simp only [step] at ran
        cases ran
        exact checked
      | ok copied =>
        simp only [step] at ran
        cases ran
        refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
        · simp [payload, checked.1]
        · simp only [payload]
          exact ⟨{ source with data := copied }, rfl, checked.2⟩

/-- The key projection is copied even before invoking dupe's content contract.
Metadata and verbatim payload correctness are stronger, separate properties. -/
theorem clone_item (duplicate : Bytes → σ → Except ε Bytes × σ) (input copied : Value Metadata)
    (before after : σ) (ran : cloneCode.run duplicate input before = (.ok copied, after)) :
    copied.item = input.item ∧ copied.metadata = input.metadata := by
  cases payload : input.verbatim with
  | none =>
    rw [clone_none duplicate input payload before] at ran
    cases ran
    exact ⟨rfl, rfl⟩
  | some source =>
    rw [clone_some duplicate input source payload before] at ran
    cases step : duplicate source.data before with
    | mk outcome middle =>
      cases outcome with
      | error error => simp [step] at ran
      | ok bytes =>
        simp only [step] at ran
        cases ran
        exact ⟨rfl, rfl⟩

theorem clone_key (duplicate : Bytes → Effect Heap Error Bytes) (input copied : Value Metadata)
    (before after : Heap) (ran : cloneCode.run duplicate input before = (.ok copied, after))
    (arguments : List NodeId) (sequence : BitVec 32) :
    keyCode.run copied.item arguments sequence = keyCode.run input.item arguments sequence := by
  rw [(clone_item duplicate input copied before after ran).1]

theorem clone_denotation (duplicate : Bytes → Effect Heap Error Bytes) (input copied : Value Metadata)
    (before after : Heap) (ran : cloneCode.run duplicate input before = (.ok copied, after))
    (meaning : Meaning) (read : Read) (arguments : List NodeId) (sequence : BitVec 32) :
    copied.item.eval meaning read arguments sequence = input.item.eval meaning read arguments sequence := by
  rw [(clone_item duplicate input copied before after ran).1]

theorem deinit_invalidates (free : Bytes → Heap → Heap) (input : Value Metadata) (before : Heap) :
    (deinitCode.run free input before).1 = none := rfl

theorem deinit_none (free : Bytes → Heap → Heap) (input : Value Metadata)
    (absent : input.verbatim = none) (before : Heap) :
    deinitCode.run free input before = (none, before) := by
  simp [DeinitCode.run, deinitCode, absent]

theorem deinit_some (free : Bytes → Heap → Heap) (input : Value Metadata)
    (payload : Verbatim) (present : input.verbatim = some payload) (before : Heap) :
    deinitCode.run free input before = (none, free payload.data before) := by
  simp [DeinitCode.run, deinitCode, present]

/-- A successful duplicate's matching free restores the caller's logical heap.
This relation is a primitive contract, not a claim that allocator bookkeeping or
machine bytes return to their previous state. No allocation occurs after dupe. -/
theorem clone_cleanup (duplicate : Bytes → Effect Heap Error Bytes) (free : Bytes → Heap → Heap)
    (inverse : ∀ source before copied after, duplicate source before = (.ok copied, after) →
      free copied after = before)
    (input copied : Value Metadata) (before after : Heap)
    (ran : cloneCode.run duplicate input before = (.ok copied, after)) :
    deinitCode.run free copied after = (none, before) := by
  cases payload : input.verbatim with
  | none =>
    rw [clone_none duplicate input payload before] at ran
    cases ran
    exact deinit_none free input payload before
  | some source =>
    rw [clone_some duplicate input source payload before] at ran
    cases step : duplicate source.data before with
    | mk outcome middle =>
      cases outcome with
      | error error => simp [step] at ran
      | ok bytes =>
        simp only [step] at ran
        cases ran
        rw [deinit_some free _ _ rfl, inverse source.data before bytes after step]

end Compiler.Extraction.AssemblyClone
