/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorFrame
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- A complete caller invocation with the supplied argument view. Only the
production two-word scratch array is allocated here. Capacity precedes scratch
preparation; ordinary returns unwind the frame after deferred cleanup. Rejected
semantic observations retain reached storage and local ownership. -/
def find (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (before : World σ) :
    Except Fault NodeId × State σ :=
  if q.atCapacity before.graph then (.error (.language .capacity), ⟨before, { lookup := none }⟩) else
  let mark := before.memory.memory.nextId
  match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | .error fault => (.error (.memory (.preparation (.memory fault))), ⟨before, { lookup := none }⟩)
  | .ok (_, memory) =>
    let ran := Caller.find external budget allocator p q source ⟨mark, 0, 2⟩ request
      { before with memory := { before.memory with memory } }
    if ordinary ran.1 then
      (ran.1, { ran.2 with world := { ran.2.world with memory := { ran.2.world.memory with
        memory := Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory } } })
    else ran

/-- The source-bound wrapper forwards the original slice, including its offset
and lifetime. A caller's temporary array must already be represented at this
boundary; it is not invented from the argument values. -/
def operation (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (opcode : Opcode) (values : List NodeId) :=
  find external budget allocator p q source (Interner.constructorCode.operationRequest opcode values)

theorem operation_forwards (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (opcode : Opcode) (values : List NodeId) :
    operation external budget allocator p q source opcode values =
      find external budget allocator p q source (Interner.constructorCode.operationRequest opcode values) := rfl

theorem represented_older (state : Compiler.ZigAir.Memory.State) (source : View) (values : List NodeId)
    (valid : state.valid = true) (represented : Represents state source values) (nonempty : values ≠ []) :
    source.allocation < state.nextId := by
  have inside : 0 < values.length := List.length_pos_iff.mpr nonempty
  have read := represented.2 0 inside
  cases accessed : Compiler.ZigAir.Memory.access state (source.address 0) ⟨4, 4⟩ false with
  | error fault =>
    simp [Compiler.ZigAir.Memory.load, View.pointer, word, Compiler.ZigAir.Memory.Ty.layout,
      accessed, bind, Except.bind] at read
  | ok cell =>
    exact (Compiler.ZigAir.Memory.valid_lookup state source.allocation cell valid
      (Compiler.ZigAir.Memory.access_success_region state _ _ false cell accessed).1).1

theorem represented_cleanup (before after : Compiler.ZigAir.Memory.State) (source : View) (values : List NodeId)
    (valid : before.valid = true) (original : Represents before source values)
    (reached : Represents after source values) :
    Represents (Compiler.ZigAir.Memory.cleanup before.nextId after) source values := by
  by_cases empty : values = []
  · exact ⟨reached.1, by intro index inside; simp [empty] at inside⟩
  · exact represented_frame source values reached (Compiler.ZigAir.Memory.cleanup_lookup_older after before.nextId
      source.allocation (represented_older before source values valid original empty))

/-- Ordinary return restores the complete caller invariant, including persistent
backing of all registry entries, and retains the same reached graph and result. -/
def Post (meaning : Meaning) (source : View) (values : List NodeId) (before : World σ)
    (ran : Except Fault NodeId × State σ) (value : Word) : Prop :=
  ordinary ran.1 = true →
    Good source values ran.2.world ∧ Closed ran.2.scope ∧
      Semantic.Ensures meaning before.graph ran.1 ran.2.world.graph
        (fun id after => after.read id = some value)

theorem find_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (source : View) (request : Interner.Request) (before : World σ) (other : Meaning) (value : Word)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (ownership : OwnedCall.Contracts allocator source request.arguments p)
    (contracts : Semantic.Contracts allocator source request.arguments (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments request.sequence = some value) :
    Post (Folding.wordMeaning other) source request.arguments before
      (find external budget allocator p q source request before) value := by
  unfold find Post
  split
  · intro _
    exact ⟨good, ⟨rfl, Or.inr rfl⟩,
      Semantic.Ensures.error _ _ _ _ valid⟩
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => intro impossible; cases impossible
    | ok pair =>
      rcases pair with ⟨pointer, memory⟩
      simp only
      have checked := (Semantic.production_verified external budget allocator p q source request 0 before memory pointer
        other value good allocated admitted ownership contracts valid evaluated).1
      have closed := Semantic.Verified.closed external allocator source request.arguments _ _ _ _ checked
      change ordinary (Caller.find external budget allocator p q source ⟨before.memory.memory.nextId, 0, 2⟩ request
        { before with memory := { before.memory with memory } }).1 = true → _ at closed
      split
      · rename_i completed
        have facts := closed completed
        intro _
        exact ⟨⟨Valid.cleanup _ facts.1.1 _,
          represented_cleanup _ _ source request.arguments good.1.memory good.2 facts.1.2⟩,
          facts.2.1, fun _ => facts.2.2⟩
      · intro impossible
        contradiction

theorem operation_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (source : View) (opcode : Opcode) (values : List NodeId) (before : World σ) (other : Meaning) (value : Word)
    (good : Good source values before) (admitted : Admitted external)
    (ownership : OwnedCall.Contracts allocator source values p)
    (contracts : Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval (Folding.wordMeaning other)
      before.graph.read values Interner.constructorCode.sequence = some value) :
    Post (Folding.wordMeaning other) source values before
      (operation external budget allocator p q source opcode values before) value :=
  find_verified external budget allocator p q source _ before other value good admitted ownership contracts valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorFrame
