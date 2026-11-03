/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeDispatch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray Recursive

/-- Native indexed reads retain the exact world on both success and rejection.
This frame fact requires neither an annotation equality nor a successful load. -/
theorem operand_world (source : ArgumentSlice) (index : Nat) (annotation : NodeId) (before : World σ) :
    (operand source index annotation before).2 = before := by
  unfold operand ShiftInput.operand
  split
  · cases TemporaryMemory.readId before.memory.memory (view source) index <;> rfl
  · rfl

theorem operand_keeps (predicate : World σ → Prop) (source : ArgumentSlice) (index : Nat) (annotation : NodeId) :
    Keeps predicate (operand source index annotation) := by
  intro before initial _
  simpa only [operand_world] using initial

/-- A query's result equation selects the same source-backed child obligation.
The query itself retains the world, including on ordinary failure. -/
theorem keeping_read_bind (predicate : World σ → Prop) : Dispatch.Effects.ReadBind (keeping predicate) where
  bind := by
    intro α β result nextLeft nextRight following
    cases result with
    | ok value => exact following value rfl
    | error fault => intro before initial _; cases fault <;> exact initial

/-- Correspondence clients specialize the native-only child frame interface.
The native frame theorem itself needs no model or resource observer. -/
theorem source_constructors_keep (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (reads : Nested.Reads) (debug : Debug) (children : Associative.Constructors Debug (GraphAction σ))
    (model : Associative.Constructors Debug)
    (coupled : (projectionAt observe predicate).SourceConstructorsAt reads debug children model) :
    (keeping predicate).SourceConstructorsAt reads debug children children := by
  constructor
  · intro opcode ids tag before initial completed
    exact (coupled.operation opcode ids tag before initial completed).1
  · intro value tag before initial completed
    exact (coupled.constant value tag before initial completed).1
  · intro id value tag before initial completed
    exact (coupled.materialize id value tag before initial completed).1
  · intro id queried source found opcode tag before initial completed
    exact (coupled.borrowedOperation id queried source found opcode tag before initial completed).1
  · intro id opcode source found shape selected bounded repeated first tag before initial completed
    exact (coupled.localOperation id opcode source found shape selected bounded repeated first tag before initial completed).1

/-- Preserve any native frame through the complete actual dispatcher under
proper-child frame hypotheses. Source-backed calls use the actual native query
snapshot and caller debug value. All indexed reads and branches reuse the
shared dispatcher proof; no logical constructor or word theorem is assumed. -/
theorem dispatcher_keeps (base : PairInput.Context σ) (owner usizeBits : Nat) (children : Constructors σ)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (owned : ArgumentSlice)
    (predicate : World σ → Prop) (before : World σ) (initial : predicate before)
    (proper : (keeping predicate).SourceConstructorsAt (NativeReads.reads owner before.memory.memory) debug children children) :
    let actual := ((context base owner usizeBits children debug).primitives source address native).simplify key owned before
    ordinary actual.1 = true → predicate actual.2 := by
  dsimp only
  rw [dispatcher_snapshot]
  exact Dispatch.Effects.simplify_with_inputs_at (keeping predicate) (keeping_read_bind predicate)
    (NativeReads.reads owner before.memory.memory) operand
    ⟨fun _ _ _ _ index annotation _ => operand_keeps predicate _ index annotation⟩
    debug proper usizeBits key.instruction key.arguments owned.address
    (fun index annotation _ => operand_keeps predicate _ index annotation) before initial

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
