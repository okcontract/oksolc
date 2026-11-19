/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveCallReturnTests
import Compiler.Extraction.InternerOwnedNested
import Compiler.Extraction.InternerCallerReleaseFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops GraphFacts)

namespace Call
theorem cleanup_missing (state : Compiler.ZigAir.Memory.State) (mark id : Nat)
    (valid : state.valid = true) (missing : state.heap.lookup id = none) :
    (Compiler.ZigAir.Memory.cleanup mark state).heap.lookup id = none := by
  cases found : (Compiler.ZigAir.Memory.cleanup mark state).heap.lookup id with
  | none => rfl
  | some cell =>
    have member := (List.mem_filter.mp (Compiler.ZigAir.Memory.Heap.lookup_mem _ _ _ found)).1
    have present := Compiler.ZigAir.Memory.lookup_of_mem_valid state id cell valid member
    rw [missing] at present
    contradiction

/-- Return a reached simplifier OOM through the existing normalized owner and
both constructor locals. The child frame is consumed at the reached state;
the initial heap is never substituted for it. -/
theorem simplifier_oom (call : Call)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (safety : Bool) (backing capacity : Nat) (rows : List Storage.Cell)
    (prior : GraphFacts safety backing capacity call.before rows) (bounded : rows.length ≤ capacity)
    (current : call.Established safety backing capacity rows) (observed : call.observations = call.expected)
    (room : Interner.Queries.queries.atCapacity call.constructed.graph = false)
    (classified : Interner.Queries.queries.deterministic call.request.item = .ok true)
    (kind : call.request.item.kind = 1) (world : World (Publication.Effects Nat))
    (failed : (p call.address call.native).simplify call.key call.normalized call.taken.2.world =
      (.error (.language .outOfMemory), world))
    (valid : Valid world.memory) (sameGraph : world.graph = call.taken.2.world.graph)
    (keys : world.memory.effects.keys = call.taken.2.world.memory.effects.keys)
    (native : ∀ id cell, call.taken.2.world.memory.memory.heap.lookup id = some cell →
      world.memory.memory.heap.lookup id = some cell)
    (registry : ∀ id block, call.taken.2.world.memory.heap id = some block → world.memory.heap id = some block) :
    ∃ cleaned,
      Held 7 call.source call.request.arguments call.normalized world ∧
      free (Publication.external ops.arguments) 7 call.normalized world.memory = (.ok (), cleaned.world.memory) ∧
      call.invoked p = (.error (.language .outOfMemory), call.returned cleaned) ∧
      GraphFacts safety backing capacity (call.returned cleaned).world rows ∧
      cleaned.world.graph = call.before.graph ∧ Closed cleaned.scope ∧
      Consumed call.normalized (call.returned cleaned).world.memory ∧
      cleaned.world.memory.effects =
        (if call.normalized.items.isEmpty then world.memory.effects
         else (Publication.external ops.arguments).free call.normalized world.memory) ∧
      (∀ id cell, call.before.memory.memory.heap.lookup id = some cell →
        (call.returned cleaned).world.memory.memory.heap.lookup id = some cell) ∧
      cleaned.world.memory.effects.keys = call.before.memory.effects.keys ∧
      (∀ id block, call.before.memory.heap id = some block → cleaned.world.memory.heap id = some block) := by
  have origin := current.entry.origin
  have held := held_retained 7 call.source call.request.arguments call.normalized call.taken.2.world world
    origin.held valid native registry
  let reached : OwnedCall.State (Publication.Effects Nat) := ⟨world, call.taken.2.scope⟩
  obtain ⟨cleaned, finished, post⟩ := finish_taken (Publication.external ops.arguments) 7 call.source
    call.request.arguments call.normalized call.lookup reached
    (Except.error (.language .outOfMemory) : Except OwnedCall.Fault NodeId) rfl
    (by change call.taken.2.scope.lookup = _; rw [origin.scope]) origin.detached
    (by change call.taken.2.scope.slice = _; rw [origin.scope]) held.1 (fun _ => held.2.1) held.2.2
  have owned : reached.scope.handedOff = false := by change call.taken.2.scope.handedOff = false; rw [origin.scope]
  have freed := (post.freed owned).1
  obtain ⟨memory, freeCall, _, _, effects, releasedNative, releasedRegistry⟩ :=
    origin.release_frame (Publication.external ops.arguments) world held.1.1 held.2.1
  have same : memory = cleaned.world.memory := congrArg Prod.snd (freeCall.symm.trans freed)
  rw [same] at releasedNative releasedRegistry effects
  have routed := call.route p observed current.item.graph room classified
  rw [call.simplify_error _ _ _ kind origin.scope failed] at routed
  change call.invoked p = (let done := OwnedCall.finish (Publication.external ops.arguments) 7 (.error (.language .outOfMemory)) reached
    if ordinary done.1 then (done.1, call.returned done.2) else done) at routed
  rw [finished] at routed
  have result : call.invoked p = (.error (.language .outOfMemory), call.returned cleaned) := routed
  have initialNative : ∀ id cell, call.before.memory.memory.heap.lookup id = some cell →
      cleaned.world.memory.memory.heap.lookup id = some cell := by
    intro id cell found
    have constructed := current.item.memory id cell found
    exact (releasedNative id cell constructed).trans
      (native id cell (origin.memory id cell constructed))
  have initialRegistry : ∀ id block, call.before.memory.heap id = some block → cleaned.world.memory.heap id = some block := by
    intro id block found
    have constructed : call.constructed.memory.heap id = some block := by rw [current.item.heap]; exact found
    exact (releasedRegistry id block constructed).trans
      (registry id block (origin.registry id block constructed))
  have returnedValid := call.returned_valid cleaned.world post.good.1
  have frame := call.returned_frame cleaned.world prior.valid initialNative
  have graph : cleaned.world.graph = call.before.graph :=
    post.graph.trans (sameGraph.trans (origin.graph.trans current.item.graph))
  have retainedKeys : cleaned.world.memory.effects.keys = call.before.memory.effects.keys := by
    have kept := free_keys ops.arguments 7 call.normalized world.memory
    rw [freed] at kept
    exact kept.trans (keys.trans (current.entry.keys.trans (congrArg Publication.Effects.keys current.item.effects)))
  have facts : GraphFacts safety backing capacity (call.returned cleaned).world rows := by
    apply prior.frame bounded returnedValid
    · exact (congrArg Interner.Heap.representatives graph).trans prior.projected
    · exact congrArg Interner.Heap.table graph
    · exact retainedKeys
    · exact frame
    · exact initialRegistry
  have consumed := (post.freed owned).2
  have returnedDead : Consumed call.normalized (call.returned cleaned).world.memory := by
    rcases consumed with empty | dead
    · exact Or.inl empty
    · refine Or.inr ⟨dead.1, ?_⟩
      apply cleanup_missing _ _ _ (post.good.1.cleanup _ (call.before.memory.memory.nextId + 1)).memory
      exact cleanup_missing _ _ _ post.good.1.memory dead.2
  exact ⟨cleaned, held, freed, result, facts, graph, post.closed, returnedDead, effects, frame, retainedKeys, initialRegistry⟩
end Call
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
