/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RuleShiftInputProgram
import Compiler.Extraction.InternerRecursiveChildTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ShiftInput.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.ZigAir.Memory.WordArray
open RecursiveTests Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)

-- Compare the forwarded call at its proved boundary rather than expanding
-- native allocation and normalization when a negative control changes an opcode.
attribute [local irreducible] Arguments.operation

/-- Check the continuation independently of the OOM fixture: that early
failure cannot mask a wrong opcode, borrowed index or final argument order. -/
theorem power_after_constant (context : Context σ) (site : Site) (power : Nat)
    (source : View) (debug : AssemblyItem.Fields.Values) (before after : World σ)
    (constant left right : NodeId) (powerSite : site ≠ .exponentTwo)
    (called : (constructors context).constant (BitVec.ofNat 256 power) debug before = (.ok constant, after))
    (length : source.length = 2)
    (lhs : Compiler.ZigAir.Memory.load after.memory.memory (source.pointer 0) = .ok (number left))
    (rhs : Compiler.ZigAir.Memory.load after.memory.memory (source.pointer 1) = .ok (number right)) :
    zigLiteral context site power source debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        (if site = .divide then Dispatch.opSHR else Dispatch.opSHL)
        [constant, if site = .multiplyLeft then right else left] debug after := by
  cases site with
  | exponentTwo => exact False.elim (powerSite rfl)
  | multiplyLeft => exact after_constant _ _ _ _ _ _ _ _ _ _ called (by rw [length]; decide) rhs
  | multiplyRight => exact after_constant _ _ _ _ _ _ _ _ _ _ called (by rw [length]; decide) lhs
  | divide => exact after_constant _ _ _ _ _ _ _ _ _ _ called (by rw [length]; decide) lhs

theorem exponent_after_constant (context : Context σ) (power : Nat) (source : View)
    (debug : AssemblyItem.Fields.Values) (before after : World σ) (constant id : NodeId)
    (called : (constructors context).constant 1 debug before = (.ok constant, after))
    (length : source.length = 2)
    (loaded : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 1) = .ok (number id)) :
    zigLiteral context .exponentTwo power source debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        Dispatch.opSHL [id, constant] debug after := by
  exact (operand_first _ _ _ _ _ _ _ _ (operand_loaded _ _ _ _ (by rw [length]; decide) loaded)).trans
    (Effect.bind_success _ _ _ _ _ called)

def context (safety : Bool) : Context (Publication.Effects Nat) :=
  ⟨Publication.external ops.arguments, 160, 7, fun _ => childPrimitives safety, Interner.Queries.queries⟩

theorem child_forwarded (safety : Bool) :
    (constructors (context safety)).constant 1 debug (child safety).before =
      ((childFull safety).1, (childFull safety).2.world) := rfl

theorem parent_operand (safety : Bool) (right : Bool) :
    operand rootSource (if right then 1 else 0) (child safety).before = (.ok 0, (child safety).before) := by
  have good : Good rootSource [0, 0] (child safety).before := (parent_established safety).entry.origin.held.1
  apply operand_loaded
  · cases right <;> decide
  · cases right
    · exact good.2.2 0 (by decide)
    · exact good.2.2 1 (by decide)

/-- These are the four selected source segments, not their enclosing query and
branch-selection prefixes. Their child is the existing complete native constant
constructor, including nonempty-backing growth OOM and both child returns. -/
theorem actual_child_failure (safety : Bool) (site : Site) : ∃ after,
    zigLiteral (context safety) site 1 rootSource debug (child safety).before =
      (.error (.language .outOfMemory), childReturned safety after) ∧
    Held 7 rootSource [0, 0] (parent safety).normalized (childReturned safety after) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (childReturned safety after) (RecursiveNonemptyTests.rows safety) ∧
    (∀ id native, (child safety).before.memory.memory.heap.lookup id = some native →
      (childReturned safety after).memory.memory.heap.lookup id = some native) := by
  obtain ⟨after, called, facts, _, native, registry⟩ := child_contract safety
  have forwarded : (constructors (context safety)).constant 1 debug (child safety).before =
      (.error (.language .outOfMemory), childReturned safety after) := by
    rw [child_forwarded, called]
  refine ⟨after, ?_, held_after_child safety _ facts.valid native registry, facts, native⟩
  cases site with
  | exponentTwo =>
    exact (operand_first _ _ _ _ _ _ _ _ (parent_operand safety true)).trans
      (Effect.bind_failure _ _ _ _ _ forwarded)
  | multiplyLeft => exact constant_error _ _ _ _ _ _ _ _ _ forwarded
  | multiplyRight => exact constant_error _ _ _ _ _ _ _ _ _ forwarded
  | divide => exact constant_error _ _ _ _ _ _ _ _ _ forwarded

/-- A failed constant child must not touch even an invalid later borrowed view.
This boundary check distinguishes ordering that a successful readonly load would
otherwise make observationally indistinguishable. -/
theorem failed_child_skips_operand (safety : Bool) (source : View) (index : Nat) : ∃ after,
    run (context safety) true Dispatch.opSHL 1 source index debug (child safety).before =
      (.error (.language .outOfMemory), childReturned safety after) := by
  obtain ⟨after, called, _⟩ := child_contract safety
  refine ⟨after, constant_error _ _ _ _ _ _ _ _ _ ?_⟩
  rw [child_forwarded, called]

/-- The base-two EXP source reads first, so source bounds failure cannot invoke
its child or advance any lifetime, effect or allocation state. -/
theorem exponent_bounds (context : Context σ) (debug : AssemblyItem.Fields.Values) (before : World σ) :
    zigLiteral context .exponentTwo 1 ⟨0, 0, 0⟩ debug before =
      (.error (.memory (.preparation (.memory .sourceBounds))), before) := by
  exact operand_error _ _ _ _ _ _ _ _ _ rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ShiftInput.Tests
