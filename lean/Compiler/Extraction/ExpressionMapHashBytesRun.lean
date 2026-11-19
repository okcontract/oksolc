/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.GeneratedExpressionHashOrder
import Compiler.Extraction.ExpressionMapWyhash
import Compiler.Extraction.WyhashMemoryRun

namespace Compiler.Extraction.ExpressionMap.HashBytes
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

theorem ordered_images (key : Key) :
    GeneratedHashOrder.inputs.map (Ordered.image key) = HashInput.encode key := by
  simpa only [GeneratedHashOrder.inputs, List.map_cons, List.map_nil, Ordered.image] using field_images key

/-- Materialize the admitted key, initialize the hasher, then execute the
captured view/update order. Every view reads the current heap and every update
reaches the next view. Update/finalization AIR and key-copy admission stay open. -/
def runRaw (state : State) (key : Key) (source : View) : Except Fault (BitVec 64) × State :=
  let (created, middle) := HashKey.create state key (source.address 0)
  match created with
  | .error fault => (.error fault, middle)
  | .ok (_, id) => GeneratedHashOrder.run middle id

def run (state : State) (key : Key) (source : View) : Except Fault (BitVec 64) × State :=
  let (result, after) := runRaw state key source
  (result, cleanup state.nextId after)

theorem runRaw_verified (state : State) (key : Key) (source : View)
    (valid : state.valid = true) (represented : Represents state source key.arguments)
    (budget : key.arguments.length * 4 + 48 < addressLimit) :
    ∃ result after, runRaw state key source = (result, after) ∧ StackFrame state after ∧
      (result = .ok (WyhashHash.digest (HashInput.encode key)) ∨ result = .error .outOfMemory) := by
  have bounded : key.arguments.length < addressLimit := by omega
  obtain ⟨created, middle, made, keyFrame, outcome⟩ := HashKey.create_verified state key (source.address 0) valid bounded
  rcases outcome with failed | ⟨succeeded, binding⟩
  · rw [failed] at made
    exact ⟨.error .outOfMemory, middle, by simp only [runRaw, made], keyFrame, Or.inr rfl⟩
  · rw [succeeded] at made
    have caller : Represents middle source key.arguments := by
      refine ⟨represented.1, ?_⟩
      intro index inside
      exact keyFrame.old_load true false word _ _ (represented.2 index inside)
    obtain ⟨long, total, budgets⟩ := HashInput.wyhash_bounds key budget
    obtain ⟨result, after, ordered, frame, outcome⟩ := Ordered.run_verified middle state.nextId key source
      GeneratedHashOrder.inputs keyFrame.valid binding caller (by have := represented.1; omega)
      (by rw [ordered_images]; exact long) (by rw [ordered_images]; exact total)
      (by
        intro input inside
        apply budgets
        rw [← ordered_images]
        exact List.mem_map.mpr ⟨input, inside, rfl⟩)
    exact ⟨result, after, by simp only [runRaw, made, GeneratedHashOrder.run, ordered],
      keyFrame.trans frame, by simpa only [ordered_images] using outcome⟩

/-- Every digest is derived from the original initialized caller input. Key and
hasher locals are retired on all outcomes, while allocation cursors advance. -/
theorem run_verified (state : State) (key : Key) (source : View)
    (valid : state.valid = true) (represented : Represents state source key.arguments)
    (budget : key.arguments.length * 4 + 48 < addressLimit) :
    (run state key source).2.valid = true ∧ (run state key source).2.heap = state.heap ∧
      ((run state key source).1 = .ok (WyhashHash.digest (HashInput.encode key)) ∨
        (run state key source).1 = .error .outOfMemory) := by
  obtain ⟨result, after, ran, frame, outcome⟩ := runRaw_verified state key source valid represented budget
  simpa only [run, ran] using And.intro frame.cleanup_valid (And.intro frame.cleanup_heap outcome)

end Compiler.Extraction.ExpressionMap.HashBytes
