/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalCaller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Memory and word semantics refer to one actual execution, including its
returned state on failure. Rejected semantic observations retain the body state
through Caller.Verified; they do not acquire an ordinary-error guarantee. -/
def Verified (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (action : Action σ α) (before : World σ) (post : α → Interner.Heap → Prop) : Prop :=
  Caller.Verified external allocator source values action before ∧
    let executed := Caller.invoke external allocator action before
    Ensures meaning before.graph executed.1 executed.2.world.graph post

theorem invoke_safe (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (action : Action σ α) (before : World σ) (post : α → Interner.Heap → Prop)
    (memory : Caller.Verified external allocator source values action before)
    (semantic : let executed := action ⟨before, { lookup := none }⟩
      Ensures meaning before.graph executed.1 executed.2.world.graph post) :
    Verified external allocator source values meaning action before post := by
  refine ⟨memory, ?_⟩
  dsimp only
  intro completed
  have bodyOrdinary : ordinary (action ⟨before, { lookup := none }⟩).1 = true := by
    rw [← memory.1]
    exact completed
  rw [memory.1, (memory.2.2 bodyOrdinary).2.2]
  exact semantic bodyOrdinary

theorem Verified.closed (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (action : Action σ α) (before : World σ) (post : α → Interner.Heap → Prop)
    (checked : Verified external allocator source values meaning action before post)
    (completed : ordinary (Caller.invoke external allocator action before).1 = true) :
    let executed := Caller.invoke external allocator action before
    Good source values executed.2.world ∧ Closed executed.2.scope ∧
      Interner.Invariant meaning executed.2.world.graph ∧ Interner.Stable before.graph executed.2.world.graph ∧
      match executed.1 with | .error _ => True | .ok result => post result executed.2.world.graph := by
  have closed := Caller.Verified.closed external allocator source values action before checked.1 completed
  exact ⟨closed.1, closed.2, checked.2 completed⟩

theorem find_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ) (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (memory : OwnedCall.Contracts allocator source request.arguments p)
    (contracts : Contracts allocator source request.arguments (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments request.sequence = some value) :
    Verified external allocator source request.arguments (Folding.wordMeaning other)
      (Caller.findBody external budget allocator p q source buffer request) before (fun id after => after.read id = some value) :=
  invoke_safe external allocator source request.arguments _ _ before _
    (Caller.find_verified external budget allocator p q source buffer request before good scratch admitted memory)
    (find_body_safe external budget allocator p q source buffer request before other value good scratch admitted memory contracts valid evaluated)

theorem force_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (source buffer : View) (id : NodeId) (item : Item) (values : List NodeId) (before : World σ) (other : Meaning) (value : Word)
    (good : Good source values before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (memory : OwnedCall.Contracts allocator source values p)
    (contracts : GraphContracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : item.eval (Folding.wordMeaning other) before.graph.read values 0 = some value)
    (actual : before.graph.read id = some value) :
    Verified external allocator source values (Folding.wordMeaning other)
      (Caller.forceBody external budget allocator p q source buffer id item values) before (fun _ _ => True) :=
  invoke_safe external allocator source values _ _ before _
    (Caller.force_verified external budget allocator p q source buffer id item values before good scratch admitted memory)
    (force_body_safe external budget allocator p q source buffer id item values before other value good scratch admitted contracts valid evaluated actual)

/-- Complete production caller composition: fresh scratch allocation, actual
normalization/copy/sort/take, graph callbacks, handoff and reached-state cleanup.
Graph implementation and query refinement are still separate compiler obligations. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (source : View) (request : Interner.Request) (id : NodeId) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value) (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted external) (ownership : OwnedCall.Contracts allocator source request.arguments p)
    (contracts : Contracts allocator source request.arguments (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments request.sequence = some value) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World σ := { before with memory := { before.memory with memory } }
    Verified external allocator source request.arguments (Folding.wordMeaning other)
      (Caller.findBody external budget allocator p q source buffer request) input (fun id after => after.read id = some value) ∧
    (request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments 0 = some value → before.graph.read id = some value →
      Verified external allocator source request.arguments (Folding.wordMeaning other)
        (Caller.forceBody external budget allocator p q source buffer id request.item request.arguments) input (fun _ _ => True)) := by
  obtain ⟨validMemory, represented, scratch, _⟩ := caller_buffer before.memory memory pointer source request.arguments good.1 good.2 allocated
  exact ⟨find_verified external budget allocator p q source _ request _ other value
      ⟨validMemory, represented⟩ scratch admitted ownership contracts valid evaluated,
    fun forceValue actual => force_verified external budget allocator p q source _ id request.item request.arguments _ other value
      ⟨validMemory, represented⟩ scratch admitted ownership contracts.toGraphContracts valid forceValue actual⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
