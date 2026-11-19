/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionSpareSuccess
import Compiler.Extraction.InternerPublicationGraphTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerSpareSuccessTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input)
open CallerInputTests (values request key)

abbrev before := Publication.GraphTests.before
abbrev argumentView := Publication.GraphTests.source
abbrev prepared := Publication.GraphTests.prepared
abbrev taken := Publication.GraphTests.taken
abbrev normalized := Publication.GraphTests.owned
abbrev lookup := Publication.GraphTests.remaining
abbrev itemSource := AssemblyItem.Creation.NativeFields.Tests.source
def old (safety empty : Bool) := CallerFirstSuccessTests.row safety empty
def lifetime (empty : Bool) := CallerInputTests.object empty + 2
def owner (safety empty : Bool) := ((before safety empty).memory.memory.heap.lookup 6).getD (CallerInputTests.owner safety)
def ops := CallerFirstSuccessTests.ops
/-- Spare insertion must never request a backing allocation. -/
def allocate : Backing.Registry.Allocate Nat := fun _ _ _ effects => (none, effects * 10 + 7)
def handle (empty : Bool) : Handle := ⟨view (normalized empty), values empty, none⟩
def duplicated (safety empty : Bool) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
  (handle empty) (taken safety empty).2.world.memory
def made (safety empty : Bool) := AssemblyItem.Creation.create (observe ops.create) 7 input.item (duplicated safety empty).2
def cloned (safety empty : Bool) := AssemblyClone.Physical.run (observe ops.copy) 7 input (made safety empty).2
def object (empty : Bool) : Nat := if empty then 13 else 17
def operands (empty : Bool) : ArgumentSlice := ⟨if empty then 13 else 16, values empty⟩
def copied (empty : Bool) : AssemblyClone.NativeFields.ItemValue :=
  { input with verbatim := some ⟨2, 3, ⟨object empty + 1, [8, 9], 0⟩⟩ }
def ready (safety empty : Bool) := (AssemblyClone.NativeFields.install (copied empty) (object empty) (cloned safety empty).2).toOption.getD
  (cloned safety empty).2
def value (safety empty : Bool) := ((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0
def row (safety empty : Bool) : Storage.Cell :=
  ⟨(copied empty).item, value safety empty, object empty, (operands empty).items, (key empty).sequence, (operands empty).address⟩
def execute (safety empty : Bool) := execution ops allocate safety 7 6 (argumentView empty) itemSource Insertion.Tests.model
  input (key empty) (normalized empty) true [old safety empty] (taken safety empty).2.world

/-- The first insertion supplies all old rows, owners and item correspondence.
No independently constructed populated starting graph is used. -/
theorem initial_representation (safety empty : Bool) :
    Memory.Vector 7 (before safety empty).memory.heap (lifetime empty) [old safety empty] ∧
    Backing.Release.Owned 7 ⟨lifetime empty, 0⟩ 5 (before safety empty).memory ∧
    DescriptorRelation.Prefix (before safety empty).memory.memory (lifetime empty) [old safety empty] ∧
    AssemblyClone.NativeFields.Represents (before safety empty).memory.memory itemSource input ∧
    (∀ logical ∈ [old safety empty], ∃ native, (before safety empty).memory.memory.heap.lookup logical.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item (before safety empty).memory.memory logical) := by
  obtain ⟨after, ran, valid, _, vector, backing, rows, _, itemOwned, itemReads, _, _, _, _, _, _, _, _, _, frame, _, _⟩ :=
    CallerFirstSuccessTests.derived_contract safety empty
  have same : (before safety empty).memory = memory after := by
    change memory (CallerFirstSuccessTests.execute safety empty).2 = memory after
    rw [ran]
  rw [same]
  have represented := (CallerInputTests.source_inputs safety empty).2
  obtain ⟨sourceCell, found⟩ := represented.live
  refine ⟨vector, backing, rows, represented.frame ((frame _ _ found (by decide)).trans found.symm), ?_⟩
  intro logical member
  have equal := List.mem_singleton.mp member
  subst logical
  obtain ⟨_, native, found, typed, _⟩ := itemOwned
  refine ⟨native, found, typed, ?_⟩
  apply AssemblyItem.Query.of_members (memory after).memory (old safety empty) native valid.memory found typed
  · change (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues
    decide
  · simpa only [old, CallerFirstSuccessTests.row, CallerInputTests.copied, AssemblyClone.NativeFields.key_fields] using itemReads .kind
  · simpa only [old, CallerFirstSuccessTests.row, CallerInputTests.copied, AssemblyClone.NativeFields.key_fields] using itemReads .instruction

theorem initial_geometry (safety empty : Bool) :
    (before safety empty).memory.memory.heap.lookup 6 = some (owner safety empty) ∧
    (owner safety empty).type = Owner.viewType safety ∧ (owner safety empty).writable = true ∧
    readItems (before safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨lifetime empty, 0⟩ 1) ∧
    readField (before safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) capacityOffset = .ok (.scalar (.int false 64 5)) := by
  cases safety <;> cases empty <;>
    exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem derived_input (safety empty : Bool) : CallerInput 7 (argumentView empty) itemSource (request empty) (values empty) input
    (key empty) (before safety empty) (taken safety empty).2 (normalized empty) (lookup empty) := by
  have prefixCalls := Publication.GraphTests.prefix_results safety empty
  obtain ⟨slice, remaining, entry⟩ := caller_input ops.arguments 160 7 (argumentView empty) itemSource (request empty) input (before safety empty)
    (Publication.GraphTests.stack safety empty) _ (values empty) (prepared safety empty).2 (taken safety empty).2 (key empty)
    (CallerFirstSuccessTests.native_borrow_good safety empty).2 (Normalization.Tests.external_admitted _)
    (initial_representation safety empty).2.2.2.1 rfl prefixCalls.1 (Prod.ext prefixCalls.2.1 rfl) (Prod.ext prefixCalls.2.2.1 rfl)
    (CallerInputTests.prefix_results safety empty).2.2.2.2 (Publication.GraphTests.initial_facts safety empty).2.1
    (Publication.GraphTests.initial_facts safety empty).2.2.1 (CallerFirstSuccessTests.borrowed_source_apart safety empty (key empty))
  have same := Local.mk.inj (entry.origin.scope.symm.trans prefixCalls.2.2.2)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact entry

theorem preparation_results (safety empty : Bool) :
    duplicated safety empty = (.ok (operands empty, handle empty), (duplicated safety empty).2) ∧
    made safety empty = (.ok (object empty), (made safety empty).2) ∧
    cloned safety empty = (.ok (copied empty), (cloned safety empty).2) ∧
    AssemblyClone.NativeFields.install (copied empty) (object empty) (cloned safety empty).2 = .ok (ready safety empty) := by
  cases safety <;> cases empty <;>
    exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem probe_result (safety empty : Bool) :
    ops.probe (key empty) (Publication.forget (memory (append safety allocate 7 6 [old safety empty] input (key empty) (normalized empty)
      (value safety empty) preparationOwnership (preparedFrame (object empty) (copied empty) (operands empty) (ready safety empty))).2)) =
      (true, (ready safety empty).effects.allocator * 10 + 8) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem derived_contract (safety empty : Bool) : ∃ after,
    execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after) ∧
    Valid (memory after) ∧ Memory.Vector 7 (memory after).heap (lifetime empty) [old safety empty, row safety empty] ∧
    Backing.Release.Owned 7 ⟨lifetime empty, 0⟩ 5 (memory after) ∧
    DescriptorRelation.Prefix (memory after).memory (lifetime empty) [old safety empty, row safety empty] ∧
    Memory.GraphResident 7 (memory after).heap [old safety empty, row safety empty] ∧
    AssemblyItem.Owned 7 (object empty) (memory after) ∧
    AssemblyClone.NativeFields.Represents (memory after).memory ⟨object empty, 0⟩ (copied empty) ∧
    (∀ slice, AssemblyClone.Physical.payload (copied empty) = some slice → AssemblyItemDeinit.Owned 7 slice (memory after)) ∧
    (∀ payload, (copied empty).verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
    Memory.SliceValid 7 (memory after).heap (normalized empty) ∧
    OwnedKeys.Live 7 ⟨(memory after).effects.keys, (memory after).heap⟩ ∧ OwnedKeys.Unique (memory after).effects.keys ∧
    OwnedKeys.Apart (memory after).effects.keys
      (fun address => ∃ logical ∈ [old safety empty, row safety empty], logical.arguments ≠ [] ∧ address = logical.argumentsAddress) ∧
    BorrowedQuery.Native.AcceptedQueries 7 (Owner.headerAddress ⟨6, 0⟩) [old safety empty, row safety empty] (memory after) ∧
    (memory after).effects.keys = OwnedKeys.store (before safety empty).memory.effects.keys (key empty) ⟨(normalized empty).address, 1⟩ ∧
    (memory after).memory.nextId = object empty + 2 ∧
    (∀ id native, (before safety empty).memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ lifetime empty →
      (∀ previous, (before safety empty).memory.effects.keys (key empty) = some previous → (key empty).arguments ≠ [] → id ≠ previous.address) →
      (memory after).memory.heap.lookup id = some native) := by
  have geometry := initial_geometry safety empty
  have initial := initial_representation safety empty
  have observations := preparation_results safety empty
  have result := CallerInput.spare_success ops allocate safety 7 6 (lifetime empty) 5 (object empty) (owner safety empty)
    (argumentView empty) itemSource Insertion.Tests.model (request empty) (values empty) input (copied empty) (key empty)
    (normalized empty) (operands empty) (lookup empty) (handle empty) (before safety empty) (taken safety empty).2 [old safety empty]
    (duplicated safety empty).2 (made safety empty).2 (cloned safety empty).2 (derived_input safety empty)
    (Normalization.Tests.external_admitted _) geometry.1 geometry.2.1 geometry.2.2.1 initial.2.1 geometry.2.2.2.1 geometry.2.2.2.2
    initial.1 initial.2.2.1 (Publication.GraphTests.initial_facts safety empty).1 (Publication.GraphTests.initial_facts safety empty).2.2.2
    initial.2.2.2.2 (by decide) (by change 1 < (5 : Nat); decide) (by change 1 < (2 ^ 32 - 1 : Nat); decide)
    observations.1 observations.2.1 observations.2.2.1
    ((ready safety empty).effects.allocator * 10 + 8) (by
      intro installed assigned
      have same := Except.ok.inj (assigned.symm.trans observations.2.2.2)
      rw [same]
      exact probe_result safety empty)
  obtain ⟨_, _, after, _, _, _, ran, valid, _, _, _, vector, backing, _, rows, resident, itemOwned, represented, payloadOwned, contents,
    normalizedLive, live, unique, apart, accepted, table, _, nextId, _, _, frame, _⟩ := result
  have id : (cloned safety empty).2.memory.nextId = object empty + 2 := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact ⟨after, ran, valid, vector, backing, rows, resident, itemOwned, represented, payloadOwned, contents,
    normalizedLive, live, unique, apart, accepted, table, nextId.trans id, frame⟩

def insert (safety empty : Bool) (slice : ArgumentSlice) : GraphAction (Publication.Effects Nat) NodeId := fun before =>
  let ran := execution ops allocate safety 7 6 (argumentView empty) itemSource Insertion.Tests.model input (key empty) slice true [old safety empty] before
  let value := ((key empty).eval Insertion.Tests.model before.graph.read).getD 0
  let after := Insertion.projected [old safety empty] before (key empty) (cell input (key empty) slice value ran.1.2 ran.2) ran.1.2 ran.2
  let result := match ran.1.1 with
    | .error _ => .error (.language .safetyFault)
    | .ok outcome => (Interner.insertionOutcome [old safety empty] outcome).mapError OwnedCall.Fault.language
  (result, after)
def reached (safety empty : Bool) := (insert safety empty (normalized empty) (taken safety empty).2.world).2

theorem insert_result (safety empty : Bool) : insert safety empty (normalized empty) (taken safety empty).2.world = (.ok 1, reached safety empty) := by
  obtain ⟨after, ran, _⟩ := derived_contract safety empty
  unfold execute at ran
  apply Prod.ext
  · simp only [insert, ran, Interner.insertionOutcome, Except.mapError]
    rfl
  · rfl

theorem handoff_and_outer_cleanup (safety empty : Bool) :
    (let (result, reached) := (do handoff; graph (insert safety empty) : Action (Publication.Effects Nat) NodeId) (taken safety empty).2
     finish (Publication.external ops.arguments) 7 result reached) =
      (.ok 1, ⟨reached safety empty, ⟨none, some (normalized empty), true⟩⟩) := by
  have finished := (derived_input safety empty).handoff_insert ops.arguments (insert safety empty)
  simpa only [insert_result, ordinary, ↓reduceIte, (Publication.GraphTests.prefix_results safety empty).2.2.2] using finished

theorem graph_and_key_projection (safety empty : Bool) :
    (reached safety empty).graph.representatives = some [old safety empty, row safety empty] ∧
    (reached safety empty).graph.table = OwnedKeys.view (reached safety empty).memory.effects.keys := by
  have representatives : (reached safety empty).graph.representatives = some [old safety empty, row safety empty] := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have table : (reached safety empty).memory.effects.keys =
      OwnedKeys.store (before safety empty).memory.effects.keys (key empty) ⟨(normalized empty).address, 1⟩ := by
    obtain ⟨after, ran, _, _, _, _, _, _, _, _, _, _, _, _, _, _, table, _⟩ := derived_contract safety empty
    change (memory (execute safety empty).2).effects.keys = _
    rw [ran]; exact table
  have graph : (reached safety empty).graph.table = Cache.put equalityFields (before safety empty).graph.table (key empty) 1 := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have linked : (before safety empty).graph.table = OwnedKeys.view (before safety empty).memory.effects.keys :=
    (CallerFirstSuccessTests.graph_and_key_projection safety empty).2
  refine ⟨representatives, ?_⟩
  rw [table, OwnedKeys.view_store, ← linked]
  exact graph

theorem accepted_queries (safety empty : Bool) :
    BorrowedQuery.Native.AcceptedQueries 7 (Owner.headerAddress ⟨6, 0⟩) [old safety empty, row safety empty] (reached safety empty).memory := by
  obtain ⟨after, ran, _, _, _, _, _, _, _, _, _, _, _, _, _, accepted, _⟩ := derived_contract safety empty
  have same : (reached safety empty).memory = memory after := by
    change memory (execute safety empty).2 = memory after
    rw [ran]
  rw [same]; exact accepted

/-- The old live argument borrow survives the second insertion; the new row
also supplies a checked native borrow. Neither reached Good is assumed. -/
theorem native_borrows (safety empty fresh : Bool) :
    let id : NodeId := if fresh then 1 else 0
    let slice := if fresh then operands empty else CallerInputTests.operands empty
    Operation.run (reached safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) id 254 = .ok (.ok (some (Operation.returned slice))) ∧
    Good (view slice) slice.items (reached safety empty) := by
  dsimp only
  let id : NodeId := if fresh then 1 else 0
  let slice := if fresh then operands empty else CallerInputTests.operands empty
  have accepted := accepted_queries safety empty
  have logical : Storage.operationProgram.run [old safety empty, row safety empty] id 254 = .ok (some slice) := by
    dsimp only [id, slice]
    cases safety <;> cases empty <;> cases fresh <;> insertion_kernel_rfl
  have native := accepted.1 id 254
  rw [logical] at native
  have checked := accepted.2 (reached safety empty).graph (graph_and_key_projection safety empty).1
  obtain ⟨observed, _, result, good⟩ := checked.2 id 254 (Operation.returned slice) native
  have expected := checked.1 id 254
  rw [logical] at expected
  have same : observed = slice := Option.some.inj (Except.ok.inj (result.symm.trans expected))
  rw [same] at good
  exact ⟨native, good⟩

/-- Both returned borrows satisfy the next caller's key-separation premise. -/
theorem borrowed_source_apart (safety empty fresh : Bool) (query : Key) (previous : OwnedKeys.Entry)
    (found : (reached safety empty).memory.effects.keys query = some previous) (nonempty : query.arguments ≠ [])
    (borrowed : (view (if fresh then operands empty else CallerInputTests.operands empty)).length ≠ 0) :
    (view (if fresh then operands empty else CallerInputTests.operands empty)).allocation ≠ previous.address := by
  obtain ⟨after, ran, _, _, _, _, _, _, _, _, _, _, _, _, apart, _⟩ := derived_contract safety empty
  have same : (reached safety empty).memory = memory after := by
    change memory (execute safety empty).2 = memory after
    rw [ran]
  rw [same] at found
  intro aliases
  apply apart query previous found nonempty
  cases fresh
  · refine ⟨old safety empty, by simp, ?_, aliases.symm⟩
    intro noArguments
    apply borrowed
    change (CallerInputTests.operands empty).items = [] at noArguments
    simp only [Bool.false_eq_true, ↓reduceIte, view, noArguments, List.length_nil]
  · refine ⟨row safety empty, by simp, ?_, aliases.symm⟩
    intro noArguments
    apply borrowed
    change (operands empty).items = [] at noArguments
    simp only [↓reduceIte, view, noArguments, List.length_nil]

theorem reached_lifetimes (safety empty : Bool) :
    ((reached safety empty).memory.memory.heap.lookup 9).isSome = empty ∧
    [CallerInputTests.object empty, CallerInputTests.object empty + 1, lifetime empty, (CallerInputTests.operands empty).address,
      (normalized empty).address, (operands empty).address, object empty, object empty + 1].map
      (fun id => ((reached safety empty).memory.memory.heap.lookup id).isSome) = [true, true, true, true, true, true, true, true] := by
  cases safety <;> cases empty <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerSpareSuccessTests
