/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionFirstSuccess
import Compiler.Extraction.InternerCallerInsertionInputTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerFirstSuccessTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (world raw argumentView values request key taken normalized remaining duplicated made cloned ready object operands copied owner)

abbrev normalized := CallerInputTests.normalized

/-- Reuse the initialized caller and actual preparation from the OOM fixtures;
only the publication response changes. These are native memory/control fixtures,
not full find routing, recursive-call or word-semantics certificates. -/
def ops : Operations Nat := { CallerInputTests.ops with probe := fun _ state => (true, state.effects * 10 + 8) }
def execute (safety empty : Bool) := execution ops CallerInputTests.allocate safety 7 6 (argumentView empty) source Insertion.Tests.model
  input (key empty) (normalized empty) true [] (taken safety empty).2.world

def value (safety empty : Bool) := ((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0
def row (safety empty : Bool) : Storage.Cell :=
  ⟨(copied empty).item, value safety empty, object empty, (operands empty).items, (key empty).sequence, (operands empty).address⟩

theorem initial_key_table (safety : Bool) : (world safety).memory.effects.keys = fun _ => none := by
  apply initialized_keys safety (world safety).memory.memory ⟨6, 0⟩
  cases safety <;> insertion_kernel_rfl

theorem probe_result (safety empty : Bool) :
    ops.probe (key empty) (Publication.forget (memory (append safety CallerInputTests.allocate 7 6 [] input (key empty)
      (normalized empty) (value safety empty) Storage.preparationOwnership
      (preparedFrame (object empty) (copied empty) (operands empty) (ready safety empty))).2)) =
      (true, CallerInputTests.probeEffects safety empty) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

/-- The caller-derived preconditions establish a populated graph and live key
owner. No reached row, resident graph, payload owner or final table is assumed. -/
theorem derived_contract (safety empty : Bool) : ∃ after,
    execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after) ∧
    Valid (memory after) ∧ Memory.GraphResident 7 (memory after).heap [row safety empty] ∧
    Memory.Vector 7 (memory after).heap (object empty + 2) [row safety empty] ∧
    Backing.Release.Owned 7 ⟨object empty + 2, 0⟩ 5 (memory after) ∧
    DescriptorRelation.Prefix (memory after).memory (object empty + 2) [row safety empty] ∧
    (∀ id, representativeFields (memory after).memory (Owner.headerAddress ⟨6, 0⟩) id =
      .ok ((Storage.representativeProgram.run [row safety empty] id).map (DescriptorRelation.values id.toNat))) ∧
    AssemblyItem.Owned 7 (object empty) (memory after) ∧
    AssemblyClone.NativeFields.Represents (memory after).memory ⟨object empty, 0⟩ (copied empty) ∧
    (∀ slice, AssemblyClone.Physical.payload (copied empty) = some slice → AssemblyItemDeinit.Owned 7 slice (memory after)) ∧
    (∀ payload, (copied empty).verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
    Memory.SliceValid 7 (memory after).heap (normalized empty) ∧
    OwnedKeys.Live 7 ⟨(memory after).effects.keys, (memory after).heap⟩ ∧ OwnedKeys.Unique (memory after).effects.keys ∧
    (memory after).effects.keys = OwnedKeys.store (world safety).memory.effects.keys (key empty) ⟨(normalized empty).address, 0⟩ ∧
    (memory after).effects.allocator = CallerInputTests.probeEffects safety empty ∧
    (memory after).memory.nextId = object empty + 3 ∧ (memory after).memory.nextAddress = 4256 ∧
    (∀ id cell, (world safety).memory.memory.heap.lookup id = some cell → id ≠ 6 →
      (memory after).memory.heap.lookup id = some cell) ∧
    BorrowedQuery.Native.AcceptedQueries 7 (Owner.headerAddress ⟨6, 0⟩) [row safety empty] (memory after) ∧
    OwnedKeys.Apart (memory after).effects.keys (fun id => (operands empty).items ≠ [] ∧ id = (operands empty).address) := by
  have observations := CallerInputTests.preparation safety empty
  have original := CallerInputTests.initialized_owner safety
  have result := CallerInput.first_success ops CallerInputTests.allocate safety 7 6 (object empty) 4096 (owner safety)
    CallerInputTests.sentinel (argumentView empty) source Insertion.Tests.model (request empty) (values empty)
    input (copied empty) (key empty) (normalized empty) (operands empty) (remaining empty) (CallerInputTests.handle empty)
    (world safety) (taken safety empty).2 (duplicated safety empty).2 (made safety empty).2 (cloned safety empty).2
    (CallerInputTests.derived_input safety empty) (Normalization.Tests.external_admitted _) (initial_key_table safety)
    original.1 original.2.1 original.2.2.1 original.2.2.2.1 original.2.2.2.2
    observations.1 observations.2.1 observations.2.2.1 ((ready safety empty).effects.allocator * 10 + 7) (by
      intro installed assigned
      have same := Except.ok.inj (assigned.symm.trans observations.2.2.2)
      rw [same]
      exact CallerInputTests.backing_response safety empty) (CallerInputTests.probeEffects safety empty) (by
      intro installed assigned
      have same := Except.ok.inj (assigned.symm.trans observations.2.2.2)
      rw [same]
      exact probe_result safety empty) (CallerInputTests.initialized_lock safety)
  obtain ⟨after, _, ran, valid, _, _, _, vector, owned, _, rows, queries, resident, itemOwned, itemReads, payloadOwned,
    contents, normalizedLive, live, unique, table, effects, nextId, nextAddress, frame, accepted, apart, _⟩ := result
  have id : (cloned safety empty).2.memory.nextId = object empty + 2 := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have address : max (cloned safety empty).2.memory.nextAddress (4096 + 160) = 4256 := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  rw [id] at vector owned rows nextId
  exact ⟨after, ran, valid, resident, vector, owned, rows, queries, itemOwned, itemReads, payloadOwned, contents,
    normalizedLive, live, unique, table, effects, by simpa only [Nat.add_assoc] using nextId, nextAddress.trans address, frame, accepted (by decide), apart⟩

/-- Use the existing outcome and graph projection at the caller boundary. -/
def insert (safety empty : Bool) (slice : ArgumentSlice) : GraphAction (Publication.Effects Nat) NodeId := fun before =>
  let ran := execution ops CallerInputTests.allocate safety 7 6 (argumentView empty) source Insertion.Tests.model
    input (key empty) slice true [] before
  let value := ((key empty).eval Insertion.Tests.model before.graph.read).getD 0
  let after := Insertion.projected [] before (key empty) (cell input (key empty) slice value ran.1.2 ran.2) ran.1.2 ran.2
  let result := match ran.1.1 with
    | .error _ => .error (.language .safetyFault)
    | .ok outcome => (Interner.insertionOutcome [] outcome).mapError OwnedCall.Fault.language
  (result, after)

def reached (safety empty : Bool) := (insert safety empty (normalized empty) (taken safety empty).2.world).2

theorem insert_result (safety empty : Bool) :
    insert safety empty (normalized empty) (taken safety empty).2.world = (.ok 0, reached safety empty) := by
  obtain ⟨after, ran, _⟩ := derived_contract safety empty
  unfold execute at ran
  apply Prod.ext
  · simp only [insert, ran, Interner.insertionOutcome, Except.mapError]
    rfl
  · rfl

theorem handoff_and_outer_cleanup (safety empty : Bool) :
    (let (result, reached) := (do handoff; graph (insert safety empty) : Action (Publication.Effects Nat) NodeId) (taken safety empty).2
     finish (Publication.external ops.arguments) 7 result reached) =
      (.ok 0, ⟨reached safety empty, ⟨none, some (normalized empty), true⟩⟩) := by
  have finished := (CallerInputTests.derived_input safety empty).handoff_insert ops.arguments (insert safety empty)
  simpa only [insert_result, ordinary, ↓reduceIte, (CallerInputTests.prefix_results safety empty).2.2.2.1] using finished

theorem graph_and_key_projection (safety empty : Bool) :
    (reached safety empty).graph.representatives = some [row safety empty] ∧
    (reached safety empty).graph.table = OwnedKeys.view (reached safety empty).memory.effects.keys := by
  have representatives : (reached safety empty).graph.representatives = some [row safety empty] := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have table : (reached safety empty).memory.effects.keys =
      OwnedKeys.store (fun _ => none) (key empty) ⟨(normalized empty).address, 0⟩ := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have graph : (reached safety empty).graph.table = Cache.put equalityFields (fun _ => none) (key empty) 0 := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  refine ⟨representatives, ?_⟩
  rw [table, OwnedKeys.view_store]
  exact graph

theorem accepted_queries (safety empty : Bool) :
    BorrowedQuery.Native.AcceptedQueries 7 (Owner.headerAddress ⟨6, 0⟩) [row safety empty] (reached safety empty).memory := by
  obtain ⟨after, ran, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, accepted, _⟩ := derived_contract safety empty
  have same : (reached safety empty).memory = memory after := by
    change memory (execute safety empty).2 = memory after
    rw [ran]
  rw [same]
  exact accepted

/-- The actual native hit now supplies checked contents for the next constructor
borrow, including the zero-length sentinel alias. No reached Good is an input. -/
theorem native_borrow_good (safety empty : Bool) :
    Operation.run (reached safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (operands empty)))) ∧
    Good (view (operands empty)) (operands empty).items (reached safety empty) := by
  have accepted := accepted_queries safety empty
  have logical : Storage.operationProgram.run [row safety empty] 0 254 = .ok (some (operands empty)) := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have native := accepted.1 0 254
  rw [logical] at native
  have checked := (accepted.2 (reached safety empty).graph (graph_and_key_projection safety empty).1).2
    0 254 (Operation.returned (operands empty)) native
  obtain ⟨slice, _, observed, good⟩ := checked
  have expected := (accepted.2 (reached safety empty).graph (graph_and_key_projection safety empty).1).1 0 254
  rw [logical] at expected
  have same : slice = operands empty := Option.some.inj (Except.ok.inj (observed.symm.trans expected))
  exact ⟨native, same ▸ good⟩

theorem borrowed_source_apart (safety empty : Bool) (query : Key) (old : OwnedKeys.Entry)
    (found : (reached safety empty).memory.effects.keys query = some old) (nonempty : query.arguments ≠ [])
    (borrowed : (view (operands empty)).length ≠ 0) : (view (operands empty)).allocation ≠ old.address := by
  obtain ⟨after, ran, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, apart⟩ := derived_contract safety empty
  have same : (reached safety empty).memory = memory after := by
    change memory (execute safety empty).2 = memory after
    rw [ran]
  rw [same] at found
  intro aliases
  apply apart query old found nonempty
  refine ⟨?_, aliases.symm⟩
  intro empty
  apply borrowed
  simp only [view, empty, List.length_nil]

theorem original_allocations_retained (safety empty : Bool) :
    [0, 1, 3, 5, 7].map (reached safety empty).memory.memory.heap.lookup =
      [0, 1, 3, 5, 7].map (raw safety).memory.heap.lookup := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem live_allocations (safety empty : Bool) :
    [object empty, object empty + 1, object empty + 2, (normalized empty).address, (operands empty).address].map
      (fun id => ((reached safety empty).memory.memory.heap.lookup id).isSome) = [true, true, true, true, true] := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerFirstSuccessTests
