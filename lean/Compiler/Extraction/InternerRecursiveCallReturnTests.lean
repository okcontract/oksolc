/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveCallTests
import Compiler.Extraction.InternerConstructorNativeReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime growth GraphFacts)

namespace Call
def returnedWorld (call : Call) (world : World (Publication.Effects Nat)) :=
  returnWorld call.before.memory.memory.nextId (call.before.memory.memory.nextId + 1) world

def returned (call : Call) (state : OwnedCall.State (Publication.Effects Nat)) :=
  { state with world := call.returnedWorld state.world }
def invoked (call : Call) (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :=
  invoke (Publication.external ops.arguments) 160 7 p Interner.Queries.queries call.source call.request debug call.before
def continuation (call : Call) (p : Primitives (Publication.Effects Nat)) :=
  Interner.findCode.controlMiss (Caller.execution (Publication.external ops.arguments) 160 7 p Interner.Queries.queries
    call.source ⟨call.before.memory.memory.nextId + 1, 0, 2⟩) call.request call.key true call.taken.2

/-- A reached simplifier error stops publication and insertion and keeps its
world in the same caller scope. Ordinary cleanup or rejection belongs to the
enclosing return, so this rule does not reinterpret observation exhaustion. -/
theorem simplify_error (call : Call) (p : Primitives (Publication.Effects Nat))
    (fault : Fault) (world : World (Publication.Effects Nat))
    (kind : call.request.item.kind = 1)
    (scope : call.taken.2.scope = ⟨some call.lookup, some call.normalized, false⟩)
    (failed : p.simplify call.key call.normalized call.taken.2.world = (.error fault, world)) :
    call.continuation p = (.error fault, ⟨world, call.taken.2.scope⟩) := by
  simp only [continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
    kind, beq_self_eq_true, Bool.and_self, ↓reduceIte, graph, scope, failed, bind, Effect.bind]

/-- Route the actual item allocation, scratch allocation, cache miss and take.
The continuation is the existing source control, and both returns use its
reached result and memory. -/
theorem route (call : Call) (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (observed : call.observations = call.expected)
    (unchanged : call.constructed.graph = call.before.graph)
    (room : Interner.Queries.queries.atCapacity call.constructed.graph = false)
    (classified : Interner.Queries.queries.deterministic call.request.item = .ok true) :
    call.invoked p =
      (let ran := call.continuation (p call.address call.native)
       let done := OwnedCall.finish (Publication.external ops.arguments) 7 ran.1 ran.2
       if ordinary done.1 then (done.1, call.returned done.2) else done) := by
  obtain ⟨made, count, allocated, initialized, transferred, _, missed, keyed⟩ := call.prefix_results observed
  have setup : Caller.initLookup (Publication.external ops.arguments) 160 7 call.source
      ⟨call.constructed.memory.memory.nextId, 0, 2⟩ call.request
      ⟨{ call.constructed with memory := { call.constructed.memory with memory := call.stack } }, { lookup := none }⟩ =
      (.ok call.request.arguments, call.prepared.2) := by
    rw [count]
    exact Prod.ext initialized rfl
  have routed := invoke_after_take (Publication.external ops.arguments) 160 7 p Interner.Queries.queries
    call.source call.request debug call.before call.constructed call.address _ call.stack call.request.arguments
    call.prepared.2 call.taken.2 call.key true made room allocated setup classified keyed
    (by intro _; rw [unchanged]; exact missed)
    (by simpa only [Call.taken] using (Prod.ext transferred rfl : call.taken = (.ok (), call.taken.2)))
  simpa only [count] using routed


theorem returned_valid (call : Call) (world : World (Publication.Effects Nat)) (valid : Valid world.memory) :
    Valid (call.returnedWorld world).memory :=
  returnWorld_valid _ _ world valid

theorem returned_cell (call : Call) (world : World (Publication.Effects Nat)) (valid : Valid call.before.memory)
    (id : Nat) (native : Compiler.ZigAir.Memory.Allocation)
    (found : call.before.memory.memory.heap.lookup id = some native)
    (kept : world.memory.memory.heap.lookup id = some native) :
    (call.returnedWorld world).memory.memory.heap.lookup id = some native := by
  exact returnWorld_cell call.before world (call.before.memory.memory.nextId + 1) valid (Nat.le_succ _)
    id native found kept

theorem returned_frame (call : Call) (world : World (Publication.Effects Nat)) (valid : Valid call.before.memory)
    (frame : ∀ id native, call.before.memory.memory.heap.lookup id = some native → world.memory.memory.heap.lookup id = some native) :
    ∀ id native, call.before.memory.memory.heap.lookup id = some native →
      (call.returnedWorld world).memory.memory.heap.lookup id = some native :=
  returnWorld_frame call.before world (call.before.memory.memory.nextId + 1) valid (Nat.le_succ _) frame
end Call

def closed := (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership

def childSeed : Primitives (Publication.Effects Nat) where
  simplify := fun _ _ before => (.error (.language .unsupported), before)
  publish := Publication.publish ops.probe ops.arguments 7 ⟨0, 0, 0⟩
  insert := fun _ _ _ before => (.error (.language .unsupported), before)
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
