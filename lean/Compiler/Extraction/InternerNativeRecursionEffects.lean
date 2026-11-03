/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorEffects
import Compiler.Extraction.InternerNativeDispatchEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage

/-- Only the nonrecursive boundaries remain premises. Native recursion replaces
the seed simplifier, so no agreement of that unused callback is required. -/
structure BaseTransport (left : PairInput.Context σ) (right : PairInput.Context τ) (project : σ → τ) : Prop where
  external : left.external.Transport right.external project
  budget : left.budget = right.budget
  allocator : left.allocator = right.allocator
  queries : left.queries = right.queries
  publish : ∀ source address native key owned id,
    Effect.Transport (World.mapEffects project)
      ((left.primitives source address native).publish key owned id)
      ((right.primitives source address native).publish key owned id)
  insert : ∀ source address native key owned deterministic,
    Effect.Transport (World.mapEffects project)
      ((left.primitives source address native).insert key owned deterministic)
      ((right.primitives source address native).insert key owned deterministic)

variable {leftBase : PairInput.Context σ} {rightBase : PairInput.Context τ} {project : σ → τ}
  (mapped : BaseTransport leftBase rightBase project)
include mapped

theorem context_erases (owner usizeBits : Nat) {left : Constructors σ} {right : Constructors τ}
    (children : (Recursive.erasing project).Constructors left right) (debug : AssemblyItem.Fields.Values) :
    (context leftBase owner usizeBits left debug).Transport (context rightBase owner usizeBits right debug) project :=
  ⟨mapped.external, mapped.budget, mapped.allocator, mapped.queries,
    fun source address native =>
      ⟨dispatcher_erases project leftBase rightBase owner usizeBits children debug source address native,
       mapped.publish source address native, mapped.insert source address native⟩⟩

/-- One actual recursive step transports all five constructor entries under the
proper-child hypothesis. Preparation and cleanup are derived from their bodies;
neither child success nor a constructor correspondence conclusion is assumed. -/
theorem step_erases (owner usizeBits : Nat) {left : Constructors σ} {right : Constructors τ}
    (children : (Recursive.erasing project).Constructors left right) :
    (Recursive.erasing project).Constructors (step leftBase owner usizeBits left) (step rightBase owner usizeBits right) := by
  have entries debug := ViewInput.EffectTransport.constructors (context_erases mapped owner usizeBits children debug)
  exact ⟨fun opcode values debug => (entries debug).operation opcode values debug,
    fun value debug => (entries debug).constant value debug,
    fun id value debug => (entries debug).materialize id value debug,
    fun address opcode values debug => (entries debug).borrowedOperation address opcode values debug,
    fun opcode source selected repeated first debug => (entries debug).localOperation opcode source selected repeated first debug⟩

/-- Exact erasure at every finite observation depth, including exhaustion and
all reached faults. This removes the proper-child erasure premise by induction;
it does not establish termination, word preservation or complete event coverage. -/
theorem unfold_erases (owner usizeBits depth : Nat) :
    (Recursive.erasing project).Constructors (unfold leftBase owner usizeBits depth) (unfold rightBase owner usizeBits depth) := by
  induction depth with
  | zero => exact exhausted_erases project
  | succ depth children => exact step_erases mapped owner usizeBits children

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
