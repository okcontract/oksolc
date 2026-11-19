/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul

/-- Lift exact language errors without recovery or changes to physical state. -/
instance : MonadLift (Except Interner.Error) (GraphAction σ) where
  monadLift result := fun before => (result.mapError Fault.language, before)

abbrev Find (σ : Type) := Interner.Request → GraphAction σ NodeId
abbrev Borrowed (σ : Type) := Compiler.ZigAir.Memory.WordArray.View → Interner.Request → GraphAction σ NodeId

/-- The same extracted constructor request encoding used by the logical
recursive proof. Physical memory is threaded by the supplied recursive call. -/
def constructors (find : Find σ) (borrowed : Borrowed σ := fun _ => find) :
    Associative.Constructors Debug (GraphAction σ) where
  operation := fun opcode ids _ => find (Interner.constructorCode.operationRequest opcode ids)
  constant := fun value _ => find (Interner.constructorCode.constantRequest value)
  materialize := fun _ value _ => find (Interner.constructorCode.constantRequest value)
  borrowedOperation := fun address opcode ids _ =>
    borrowed ⟨address, 0, ids.length⟩ (Interner.constructorCode.operationRequest opcode ids)

/-- All stages and helper paths use the original extracted dispatcher. The
seed simplifier is overwritten; no second copy of its ordered control exists. -/
def callbacks (p : Primitives σ) (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (borrowed : Borrowed σ := fun _ => find) : Primitives σ :=
  { p with simplify := fun key _ before =>
    Dispatch.simplify (reads before.graph) (constructors find borrowed) usizeBits key.instruction key.arguments () before }

theorem operation_request (find : Find σ) (opcode : Opcode) (ids : List NodeId) (debug : Debug) :
    (constructors find).operation opcode ids debug = find (Interner.constructorCode.operationRequest opcode ids) := rfl

/-- Complete graph-array slices retain their existing address. The default
callback erases it only for logical-projection fixtures. A production memory
connection supplies a caller that consumes the forwarded view. -/
theorem borrowed_operation_request (find : Find σ) (borrowed : Borrowed σ) (address : Nat)
    (opcode : Opcode) (ids : List NodeId) (debug : Debug) :
    (constructors find borrowed).borrowedOperation address opcode ids debug =
      borrowed ⟨address, 0, ids.length⟩ (Interner.constructorCode.operationRequest opcode ids) := rfl

theorem constant_request (find : Find σ) (value : Word) (debug : Debug) :
    (constructors find).constant value debug = find (Interner.constructorCode.constantRequest value) := rfl

theorem materialize_request (find : Find σ) (id : NodeId) (value : Word) (debug : Debug) :
    (constructors find).materialize id value debug = find (Interner.constructorCode.constantRequest value) := rfl

theorem actual_dispatcher (p : Primitives σ) (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (key : Key) (slice : ArgumentSlice) (before : World σ) :
    (callbacks p reads usizeBits find).simplify key slice before =
      Dispatch.simplify (reads before.graph) (constructors find) usizeBits key.instruction key.arguments () before := rfl

theorem actual_borrowed_dispatcher (p : Primitives σ) (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat)
    (find : Find σ) (borrowed : Borrowed σ) (key : Key) (slice : ArgumentSlice) (before : World σ) :
    (callbacks p reads usizeBits find borrowed).simplify key slice before =
      Dispatch.simplify (reads before.graph) (constructors find borrowed) usizeBits key.instruction key.arguments () before := rfl

theorem ignores_seed (p : Primitives σ) (ignored : Key → ArgumentSlice → GraphAction σ (Option NodeId))
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ) :
    callbacks { p with simplify := ignored } reads usizeBits find = callbacks p reads usizeBits find := rfl

theorem lift_language_error (before : World σ) (error : Interner.Error) :
    (monadLift (Except.error error : Except Interner.Error α) : GraphAction σ α) before =
      (.error (.language error), before) := rfl

theorem bind_fault_reached (action : GraphAction σ α) (next : α → GraphAction σ β)
    (before after : World σ) (fault : Fault) (ran : action before = (.error fault, after)) :
    Effect.bind action next before = (.error fault, after) := Effect.bind_failure action next before after fault ran

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
