/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Whole caller memory behavior, conditional on the named graph contracts.
The statement binds the actual body and final execution, including failure
state; it makes no claim about unproved graph semantics or query refinement. -/
def Verified (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (action : Action σ α) (before : World σ) : Prop :=
  let bodyResult := action ⟨before, { lookup := none }⟩
  let execution := invoke external allocator action before
  execution.1 = bodyResult.1 ∧
    (ordinary bodyResult.1 = false → execution.2 = bodyResult.2) ∧
    (ordinary bodyResult.1 = true → Good source values execution.2.world ∧ Closed execution.2.scope ∧
      execution.2.world.graph = bodyResult.2.world.graph)

theorem Verified.closed (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (action : Action σ α) (before : World σ) (checked : Verified external allocator source values action before)
    (completed : ordinary (invoke external allocator action before).1 = true) :
    Good source values (invoke external allocator action before).2.world ∧
      Closed (invoke external allocator action before).2.scope := by
  have bodyOrdinary : ordinary (action ⟨before, { lookup := none }⟩).1 = true := by
    rw [← checked.1]
    exact completed
  exact ⟨(checked.2.2 bodyOrdinary).1, (checked.2.2 bodyOrdinary).2.1⟩

theorem find_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (good : Good source request.arguments before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (contracts : Contracts allocator source request.arguments p) :
    Verified external allocator source request.arguments (findBody external budget allocator p q source buffer request) before :=
  invoke_verified external allocator source request.arguments _ before
    (find_ready external budget allocator p q source buffer request before good scratch admitted contracts)

theorem force_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (id : NodeId) (item : Item) (values : List NodeId) (before : World σ)
    (good : Good source values before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (contracts : Contracts allocator source values p) :
    Verified external allocator source values (forceBody external budget allocator p q source buffer id item values) before :=
  invoke_verified external allocator source values _ before
    (force_ready external budget allocator p q source buffer id item values before good scratch admitted contracts)

/-- One composed theorem for both complete source-bound caller bodies. The
fresh caller stack-buffer contract derives scratch permissions; graph callbacks
and read-only query refinement remain explicit compiler obligations. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source : View) (request : Interner.Request) (id : NodeId) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (good : Good source request.arguments before)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted external) (contracts : Contracts allocator source request.arguments p) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World σ := { before with memory := { before.memory with memory } }
    Verified external allocator source request.arguments (findBody external budget allocator p q source buffer request) input ∧
    Verified external allocator source request.arguments (forceBody external budget allocator p q source buffer id request.item request.arguments) input := by
  obtain ⟨valid, represented, scratch, _⟩ := caller_buffer before.memory memory pointer source request.arguments good.1 good.2 allocated
  exact ⟨find_verified external budget allocator p q source _ request _ ⟨valid, represented⟩ scratch admitted contracts,
    force_verified external budget allocator p q source _ id request.item request.arguments _ ⟨valid, represented⟩ scratch admitted contracts⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
