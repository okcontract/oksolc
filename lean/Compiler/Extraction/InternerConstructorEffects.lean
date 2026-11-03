/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerArgumentEffects
import Compiler.Extraction.InternerCallerMemoryEffects
import Compiler.Extraction.InternerViewInput
import Compiler.Extraction.InternerPhysicalDispatchEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.ZigAir.Memory.WordArray

namespace ConstructorItem.EffectTransport
variable (project : σ → τ)

theorem finish (before : World σ) (allocated : Compiler.ZigAir.Memory.State)
    (result : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State) :
    ConstructorItem.finish (before.mapEffects project) allocated result =
      ((ConstructorItem.finish before allocated result).1,
       (ConstructorItem.finish before allocated result).2.mapEffects project) := by
  cases result <;> rfl

theorem enter (item : Item) (debug : AssemblyItem.Fields.Values) (before : World σ)
    (result : Except Compiler.ZigAir.Memory.Fault (Compiler.ZigAir.Memory.Value × Compiler.ZigAir.Memory.State)) :
    ConstructorItem.enter item debug (before.mapEffects project) result =
      ((ConstructorItem.enter item debug before result).1,
       (ConstructorItem.enter item debug before result).2.mapEffects project) := by
  cases result with
  | error fault => rfl
  | ok allocated =>
    rcases allocated with ⟨pointer, memory⟩
    exact finish project before memory
      (AssemblyItem.Fields.assign (AssemblyItem.Initializers.construct item debug) before.memory.memory.nextId memory)

theorem prepare (item : Item) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects project) (ConstructorItem.prepare item debug) (ConstructorItem.prepare item debug) :=
  fun before => enter project item debug before _

end ConstructorItem.EffectTransport

namespace ConstructorFrame.EffectTransport
variable {physical : External σ} {original : External τ} {project : σ → τ}
  (mapped : External.Transport physical original project)
include mapped

/-- Capacity precedes scratch allocation on both sides. All returned scopes and
the ordinary-only stack cleanup come from the actual caller execution. -/
theorem find (budget allocator : Nat) {left : Primitives σ} {right : Primitives τ}
    (callbacks : left.Transport right project) (queries : Caller.Queries)
    (source : View) (request : Interner.Request) (before : World σ) :
    ConstructorFrame.find original budget allocator right queries source request (before.mapEffects project) =
      ((ConstructorFrame.find physical budget allocator left queries source request before).1,
       (ConstructorFrame.find physical budget allocator left queries source request before).2.mapEffects project) := by
  unfold ConstructorFrame.find
  simp only [show (before.mapEffects project).graph = before.graph from rfl,
    show (before.mapEffects project).memory.memory = before.memory.memory from rfl]
  split
  · rfl
  · cases Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => rfl
    | ok allocated =>
      rcases allocated with ⟨pointer, memory⟩
      dsimp only
      have called := Caller.EffectTransport.find mapped budget allocator callbacks queries source
        ⟨before.memory.memory.nextId, 0, 2⟩ request { before with memory := { before.memory with memory } }
      simp only [World.mapEffects, Session.mapEffects] at called ⊢
      rw [called]
      split <;> rfl

end ConstructorFrame.EffectTransport

namespace ConstructorItem.EffectTransport
variable {physical : External σ} {original : External τ} {project : σ → τ}
  (mapped : External.Transport physical original project)
include mapped

theorem invoke (budget allocator : Nat)
    {left : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ}
    {right : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives τ}
    (callbacks : ∀ address native, (left address native).Transport (right address native) project)
    (queries : Caller.Queries) (source : View) (request : Interner.Request)
    (debug : AssemblyItem.Fields.Values) (before : World σ) :
    ConstructorItem.invoke original budget allocator right queries source request debug (before.mapEffects project) =
      ((ConstructorItem.invoke physical budget allocator left queries source request debug before).1,
       (ConstructorItem.invoke physical budget allocator left queries source request debug before).2.mapEffects project) := by
  unfold ConstructorItem.invoke
  rw [prepare project]
  cases ConstructorItem.prepare request.item debug before with
  | mk result reached =>
    cases result with
    | error fault => rfl
    | ok address =>
      dsimp only
      rw [ConstructorFrame.EffectTransport.find mapped budget allocator (callbacks address _) queries source request reached]
      split <;> rfl

end ConstructorItem.EffectTransport

namespace ConstructorItem.Arguments.EffectTransport
variable (project : σ → τ)

theorem prepare (values : List NodeId) :
    Effect.Transport (World.mapEffects project) (Arguments.prepare values) (Arguments.prepare values) := by
  rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
  · exact fun _ => rfl
  · exact TemporaryUnary.EffectTransport.prepare project a
  · exact TemporaryArguments.EffectTransport.prepare project a b
  · exact TemporaryTernary.EffectTransport.prepare project a b c
  · exact fun _ => rfl

theorem returned (values : List NodeId) (mark : Nat) (ran : Except Fault NodeId × State σ) :
    Arguments.returned values mark (ran.1, ran.2.mapEffects project) =
      ((Arguments.returned values mark ran).1, (Arguments.returned values mark ran).2.mapEffects project) := by
  unfold Arguments.returned
  split
  · rfl
  · exact TemporaryArguments.EffectTransport.unwind project mark ran

variable {project} {physical : External σ} {original : External τ}
  (mapped : External.Transport physical original project)
include mapped

theorem operation (budget allocator : Nat)
    {left : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ}
    {right : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives τ}
    (callbacks : ∀ source address native, (left source address native).Transport (right source address native) project)
    (queries : Caller.Queries) (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects project)
      (Arguments.operation physical budget allocator left queries opcode values debug)
      (Arguments.operation original budget allocator right queries opcode values debug) := by
  intro before
  unfold Arguments.operation
  rw [prepare project]
  cases Arguments.prepare values before with
  | mk result reached =>
    cases result with
    | error fault => rfl
    | ok source =>
      dsimp only
      unfold ConstructorItem.operation
      rw [ConstructorItem.EffectTransport.invoke mapped budget allocator (callbacks source) queries source _ debug reached]
      exact returned project values before.memory.memory.nextId _

end ConstructorItem.Arguments.EffectTransport

namespace ConstructorItem

/-- The configuration agrees at each local boundary. No constructor execution,
valid input, successful result or fixed fixture identity is assumed. -/
structure ShiftInput.Context.Transport (physical : ShiftInput.Context σ) (original : ShiftInput.Context τ)
    (project : σ → τ) : Prop where
  external : physical.external.Transport original.external project
  budget : physical.budget = original.budget
  allocator : physical.allocator = original.allocator
  queries : physical.queries = original.queries
  primitives : ∀ source address native,
    (physical.primitives source address native).Transport (original.primitives source address native) project

namespace ViewInput.EffectTransport
variable {left : PairInput.Context σ} {right : PairInput.Context τ} {project : σ → τ}
  (mapped : left.Transport right project)
include mapped

theorem operation (source : View) (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects project)
      (ViewInput.operation left source opcode values debug) (ViewInput.operation right source opcode values debug) := by
  intro before
  unfold ViewInput.operation ConstructorItem.operation
  rw [← mapped.budget, ← mapped.allocator, ← mapped.queries,
    ConstructorItem.EffectTransport.invoke mapped.external left.budget left.allocator
      (mapped.primitives source) left.queries source _ debug before]
  rfl

theorem localOperation (opcode : Opcode) (source : View) (leftId rightId repeated : NodeId)
    (selected : Nat) (first : Bool) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects project)
      (ViewInput.localOperation left opcode source leftId rightId repeated selected first debug)
      (ViewInput.localOperation right opcode source leftId rightId repeated selected first debug) := by
  intro before
  unfold ViewInput.localOperation
  rw [LocalArguments.EffectTransport.zigLocal project]
  cases LocalArguments.zigLocal source selected repeated first before with
  | mk result reached =>
    cases result with
    | error fault => rfl
    | ok target =>
      dsimp only
      unfold ConstructorItem.operation
      rw [← mapped.budget, ← mapped.allocator, ← mapped.queries,
        ConstructorItem.EffectTransport.invoke mapped.external left.budget left.allocator
          (mapped.primitives target) left.queries target _ debug reached]
      exact TemporaryArguments.EffectTransport.unwind project before.memory.memory.nextId _

theorem constant (value : Contract.Yul.Word) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects project)
      ((PairInput.constructors left).constant value debug) ((PairInput.constructors right).constant value debug) := by
  intro before
  unfold PairInput.constructors ShiftInput.constructors ConstructorItem.constant
  dsimp only
  rw [← mapped.budget, ← mapped.allocator, ← mapped.queries,
    ConstructorItem.EffectTransport.invoke mapped.external left.budget left.allocator
      (mapped.primitives ⟨0, 0, 0⟩) left.queries _ _ debug before]
  rfl

/-- All five actual entry bodies share the same caller transport. The native
loads, stack allocations, source guards and exceptional cleanup remain in place. -/
theorem constructors : (Recursive.erasing project).Constructors (ViewInput.constructors left) (ViewInput.constructors right) := by
  constructor
  · intro opcode values debug
    change Effect.Transport (World.mapEffects project)
      (Arguments.operation left.external left.budget left.allocator left.primitives left.queries opcode values debug)
      (Arguments.operation right.external right.budget right.allocator right.primitives right.queries opcode values debug)
    rw [← mapped.budget, ← mapped.allocator, ← mapped.queries]
    exact Arguments.EffectTransport.operation mapped.external left.budget left.allocator mapped.primitives left.queries
      opcode values debug
  · exact constant mapped
  · intro id value debug
    change Effect.Transport (World.mapEffects project)
      ((PairInput.constructors left).materialize id value debug) ((PairInput.constructors right).materialize id value debug)
    rw [PairInput.materialize_forwarded, PairInput.materialize_forwarded]
    exact constant mapped value debug
  · intro address opcode values debug
    exact operation mapped ⟨address, 0, values.length⟩ opcode values debug
  · intro opcode source selected repeated first debug
    change Effect.Transport (World.mapEffects project) _ _
    cases source with | mk address values =>
      rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
      · exact fun _ => rfl
      · exact fun _ => rfl
      · exact localOperation mapped opcode _ a b repeated selected first debug
      · exact fun _ => rfl

end ViewInput.EffectTransport
end ConstructorItem
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
