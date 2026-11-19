/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapPrologueGuarded

/-! Universal confinement of every data-operation attempt in the captured u32
swap, relative to its two argument words and private counter allocation. The
result covers every execution prefix and exhaustion; it does not identify the
typed heap with native addresses or discharge LLVM pointer provenance. -/
namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents)

theorem observed_valid (args : List Value) (fuel : Nat) (config : Config Ty Prim Ref Value State)
    (initial : config.state.valid = true) (event : Observation Ty Prim Value State)
    (present : event ∈ (trace semantics args fuel (.suspended config)).1) : event.state.valid = true := by
  obtain ⟨next, reached, recorded⟩ := trace_reachable semantics args fuel (.suspended config) event present
  have valid := machine_steps_preserve_valid args _ _ reached initial
  cases code : next.code <;> simp_all [observe]
  cases recorded
  exact valid

/-- Entry admission follows from the same explicit array-view premises. Every
observed data reference is resolved within its argument word or the counter;
every pre-state is valid. There is no chosen-budget or successful-run premise. -/
theorem captured_confinement (caller : State) (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : caller.valid = true) (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right) :
    WordPair.validate caller (arguments view left right) = .ok () ∧
      ∀ fuel event, event ∈ (trace semantics (arguments view left right) fuel
          (.suspended ⟨GeneratedMemory.fn_swap_u32.program.body, fun _ => none, caller, []⟩)).1 →
        Footprint view left right ⟨caller.nextId, 0⟩ event ∧ event.state.valid = true := by
  obtain ⟨outcome, path⟩ := body_guarded caller view items left right initial cap represented hl hr apart
  refine ⟨WordPair.validate_view caller view items left right initial cap represented hl hr apart, ?_⟩
  intro fuel event present
  exact ⟨path.terminal_trace semantics _ _ fuel event present, observed_valid _ fuel _ initial event present⟩

/-- Argument bytes are distinct from every byte of the private counter region,
including the whole-word accesses used by the byte representation model. -/
theorem counter_region_separate (caller : State) (view : View) (word : Nat) (byte : Fin 4) (offset : Nat)
    (initial : caller.valid = true) (cap : Writable caller view) :
    ByteAccess.atByte (view.address word) byte ≠ (⟨caller.nextId, offset⟩ : Address) :=
  borrowed_counter_apart view word byte _ (view_older caller view initial cap)

end Compiler.ZigAir.MemoryWordSwap
