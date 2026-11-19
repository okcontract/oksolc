/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatch
import Compiler.Extraction.InternerConstructorFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.BorrowedConstructor
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- The borrowed dispatcher callback invokes the complete caller on the supplied
view. The callback observes its result and reached world. Ordinary returns have
closed callee locals; rejected semantic outcomes retain the original caller
outcome, including its locals, and are not accepted execution observations. -/
def caller (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) : Borrowed σ :=
  fun source request before =>
    let ran := ConstructorFrame.find external budget allocator p q source request before
    (ran.1, ran.2.world)

theorem operation_forwards (find : Find σ) (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (address : Nat) (opcode : Opcode) (values : List NodeId) (debug : Debug) (before : World σ) :
    (constructors find (caller external budget allocator p q)).borrowedOperation address opcode values debug before =
      let ran := ConstructorFrame.operation external budget allocator p q ⟨address, 0, values.length⟩ opcode values before
      (ran.1, ran.2.world) := rfl

/-- The actual borrowed-constructor execution restores Good and preserves the
word/graph invariant through normalization, transfer, defers and frame cleanup.
Native graph callbacks and the initial represented source remain explicit
compiler obligations; this is not the missing universal recursive simulation. -/
theorem operation_verified (find : Find σ) (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (address : Nat) (opcode : Opcode) (values : List NodeId) (debug : Debug)
    (before : World σ) (other : Meaning) (value : Word)
    (good : Good ⟨address, 0, values.length⟩ values before) (admitted : Admitted external)
    (ownership : OwnedCall.Contracts allocator ⟨address, 0, values.length⟩ values p)
    (contracts : Semantic.Contracts allocator ⟨address, 0, values.length⟩ values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval (Folding.wordMeaning other)
      before.graph.read values Interner.constructorCode.sequence = some value) :
    let ran := (constructors find (caller external budget allocator p q)).borrowedOperation address opcode values debug before
    ordinary ran.1 = true →
      Good ⟨address, 0, values.length⟩ values ran.2 ∧
      Closed (ConstructorFrame.operation external budget allocator p q ⟨address, 0, values.length⟩ opcode values before).2.scope ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
        (fun id after => after.read id = some value) :=
  ConstructorFrame.operation_verified external budget allocator p q _ opcode values before other value
    good admitted ownership contracts valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.BorrowedConstructor
