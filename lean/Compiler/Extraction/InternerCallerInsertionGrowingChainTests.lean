/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowingChainSetupTests
import Compiler.Extraction.InternerNativeGraphInsertion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- A proof bundle over the existing graph and native memory, used only to
compose the fixture's actual invocations. It introduces no alternate state. -/
structure GraphFacts (safety : Bool) (backing capacity : Nat) (world : World (Publication.Effects Nat)) (rows : List Storage.Cell) : Prop where
  projected : world.graph.representatives = some rows
  linked : world.graph.table = OwnedKeys.view world.memory.effects.keys
  valid : Valid world.memory
  owner : ∃ native, world.memory.memory.heap.lookup 6 = some native ∧ native.type = Owner.viewType safety ∧ native.writable = true
  owned : Backing.Release.Owned 7 ⟨backing, 0⟩ capacity world.memory
  vector : Memory.Vector 7 world.memory.heap backing rows
  header : readHeader world.memory.memory (Owner.headerAddress ⟨6, 0⟩) =
    .ok (.slice itemsType ⟨backing, 0⟩ rows.length, .scalar (.int false 64 capacity))
  descriptors : DescriptorRelation.Prefix world.memory.memory backing rows
  resident : Memory.GraphResident 7 world.memory.heap rows
  items : ∀ logical ∈ rows, ∃ native, world.memory.memory.heap.lookup logical.itemAddress = some native ∧
    native.type = AssemblyItem.viewType ∧ Operation.Item world.memory.memory logical
  nativeInput : ∃ native, world.memory.memory.heap.lookup source.allocation = some native ∧ native.type = AssemblyItem.viewType ∧
    AssemblyClone.NativeFields.Represents world.memory.memory source input
  live : OwnedKeys.Live 7 ⟨world.memory.effects.keys, world.memory.heap⟩
  unique : OwnedKeys.Unique world.memory.effects.keys
  apart : OwnedKeys.Apart world.memory.effects.keys
    (fun address => ∃ logical ∈ rows, logical.arguments ≠ [] ∧ address = logical.argumentsAddress)
  accepted : BorrowedQuery.Native.AcceptedQueries 7 (Owner.headerAddress ⟨6, 0⟩) rows world.memory
  data : ∀ row ∈ rows, Constant.Data world.memory.memory row

structure Prefix (safety empty : Bool) (n : Nat) : Prop where
  result : (run safety empty n).1 = .ok (BitVec.ofNat 32 n)
  facts : GraphFacts safety (lifetime empty) 5 (before safety empty n) (cells safety empty n)
  count : (cells safety empty n).length = n + 1
  first : (cells safety empty n).head? = some (CallerFirstSuccessTests.row safety empty)

/-- The legacy fixture bundle also carries its separate immutable input item.
Project only persistent graph facts into the parameterized native invariant;
the stored accepted-query field is deliberately not used. -/
theorem GraphFacts.native {safety : Bool} {backing capacity : Nat} {world : World (Publication.Effects Nat)}
    {rows : List Storage.Cell} (facts : GraphFacts safety backing capacity world rows) (bounded : rows.length ≤ capacity) :
    NativeGraph.Facts safety 7 6 ⟨backing, 0⟩ capacity world rows :=
  ⟨facts.valid, facts.projected, facts.linked, facts.owner, facts.header, bounded,
    fun _ => ⟨facts.owned, facts.vector, facts.descriptors⟩, facts.resident, facts.items,
    facts.live, facts.unique, facts.apart, facts.data⟩

/-- Rebuild the initialized graph facts from a proved frame of all original
allocations. Failure fixtures share this native readback argument; they do not
establish final graph correspondence by closed evaluation. -/
theorem GraphFacts.frame {safety : Bool} {backing capacity : Nat} {before after : World (Publication.Effects Nat)}
    {rows : List Storage.Cell} (facts : GraphFacts safety backing capacity before rows)
    (bounded : rows.length ≤ capacity) (valid : Valid after.memory)
    (projected : after.graph.representatives = some rows) (table : after.graph.table = before.graph.table)
    (keys : after.memory.effects.keys = before.memory.effects.keys)
    (native : ∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell)
    (registered : ∀ id block, before.memory.heap id = some block → after.memory.heap id = some block) :
    GraphFacts safety backing capacity after rows := by
  have retained := (facts.native bounded).frame (after := after) valid projected table keys
    (fun id cell found _ => native id cell found) registered
  obtain ⟨_, _, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := facts.owned
  have descriptors := DescriptorRelation.frame _ _ backing rows facts.descriptors ((native _ _ backingFound).trans backingFound.symm)
  obtain ⟨inputCell, inputFound, inputTyped, inputReads⟩ := facts.nativeInput
  exact ⟨retained.projected, retained.linked, retained.valid, retained.ownerLive,
    ⟨rfl, ⟨rows, registered _ _ facts.vector⟩, backingCell, native _ _ backingFound, backingTyped, backingWritable, backingPersistent⟩,
    registered _ _ facts.vector, retained.header, descriptors, retained.resident, retained.items,
    ⟨inputCell, native _ _ inputFound, inputTyped, inputReads.frame ((native _ _ inputFound).trans inputFound.symm)⟩,
    retained.live, retained.unique, retained.apart, retained.accepted, retained.data⟩

theorem initial_prefix (safety empty : Bool) : Prefix safety empty 0 := by
  have same : before safety empty 0 = CallerFirstSuccessTests.reached safety empty :=
    congrArg (fun result => result.2.world) (first_result safety empty)
  have rows : cells safety empty 0 = [CallerFirstSuccessTests.row safety empty] := by
    simp only [cells, same, (CallerFirstSuccessTests.graph_and_key_projection safety empty).1, Option.getD_some]
  have represented := CallerSpareSuccessTests.initial_representation safety empty
  have geometry := CallerSpareSuccessTests.initial_geometry safety empty
  have initial := Publication.GraphTests.initial_facts safety empty
  refine ⟨congrArg Prod.fst (first_result safety empty), ?_, by rw [rows]; rfl, by rw [rows]; rfl⟩
  rw [same, rows]
  have typedInput : ((CallerFirstSuccessTests.reached safety empty).memory.memory.heap.lookup source.allocation).map
      (fun native => native.type) = some AssemblyItem.viewType := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  obtain ⟨native, found⟩ := represented.2.2.2.1.live
  change (CallerFirstSuccessTests.reached safety empty).memory.memory.heap.lookup source.allocation = some native at found
  rw [found] at typedInput
  refine ⟨(CallerFirstSuccessTests.graph_and_key_projection safety empty).1,
    (CallerFirstSuccessTests.graph_and_key_projection safety empty).2,
    (CallerFirstSuccessTests.native_borrow_good safety empty).2.1,
    ⟨CallerSpareSuccessTests.owner safety empty, geometry.1, geometry.2.1, geometry.2.2.1⟩,
    represented.2.1, represented.1, ?_, represented.2.2.1, initial.1, represented.2.2.2.2,
    ⟨native, found, Option.some.inj typedInput, represented.2.2.2.1⟩,
    initial.2.1, initial.2.2.1, initial.2.2.2, CallerFirstSuccessTests.accepted_queries safety empty, ?_⟩
  · have items := geometry.2.2.2.1
    have capacity := geometry.2.2.2.2
    change readItems (CallerFirstSuccessTests.reached safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨lifetime empty, 0⟩ 1) at items
    change readField (CallerFirstSuccessTests.reached safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 5)) at capacity
    simp only [readHeader, readItems] at items ⊢
    rw [items, capacity]
    rfl
  · intro row member push
    have rowIs := List.mem_singleton.mp member
    subst row
    change (1 : BitVec 32) = 2 at push
    contradiction

theorem GraphFacts.first_borrow {safety empty : Bool} {backing capacity : Nat} {world : World (Publication.Effects Nat)} {rows : List Storage.Cell}
    (facts : GraphFacts safety backing capacity world rows) (head : rows.head? = some (CallerFirstSuccessTests.row safety empty)) :
    Operation.run world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (CallerInputTests.operands empty)))) ∧ Good (parent empty) (request empty).arguments world := by
  have logical : Storage.operationProgram.run rows 0 254 = .ok (some (CallerInputTests.operands empty)) := by
    have first := head
    cases listed : rows with
    | nil => simp only [listed, List.head?_nil] at first; contradiction
    | cons head tail =>
      simp only [listed, List.head?_cons, Option.some.injEq] at first
      rw [first]
      have found : Storage.representativeProgram.run (CallerFirstSuccessTests.row safety empty :: tail) 0 =
          .ok (CallerFirstSuccessTests.row safety empty) := by
        simp [Storage.Lookup.run, Storage.representativeProgram, Storage.Bound.reject, Storage.Index.eval]
      simp only [Storage.OperationRead.run, Storage.operationProgram, found]
      rfl
  have native := facts.accepted.1 0 254
  rw [logical] at native
  have checked := facts.accepted.2 world.graph facts.projected
  obtain ⟨observed, _, result, good⟩ := checked.2 0 254 (Operation.returned (CallerInputTests.operands empty)) native
  have expected := checked.1 0 254
  rw [logical] at expected
  have same : observed = CallerInputTests.operands empty := Option.some.inj (Except.ok.inj (result.symm.trans expected))
  rw [same] at good
  exact ⟨native, good⟩

theorem Prefix.parent_good {safety empty : Bool} {n : Nat} (prior : Prefix safety empty n) :
    Good (parent empty) (request empty).arguments (before safety empty n) :=
  (prior.facts.first_borrow prior.first).2

theorem Prefix.source_private {safety empty : Bool} {n : Nat} (prior : Prefix safety empty n) :
    Caller.SourcePrivate (parent empty) (before safety empty n).memory.effects.keys := by
  intro key previous found nonempty borrowed aliases
  apply prior.facts.apart key previous found nonempty
  refine ⟨CallerFirstSuccessTests.row safety empty, List.mem_of_head? prior.first, ?_, aliases.symm⟩
  intro noArguments
  apply borrowed
  change (CallerInputTests.operands empty).items = [] at noArguments
  simp only [parent, view, noArguments, List.length_nil]

theorem Prefix.caller_input {safety empty : Bool} {n : Nat} (prior : Prefix safety empty n) (bounded : n < 5) :
    CallerInput 7 (parent empty) source (request empty) (values empty) input (key empty)
      (before safety empty n) (taken safety empty n).2 (normalized safety empty n) (lookup empty) := by
  have prefixCalls := prefix_results safety empty n bounded
  obtain ⟨slice, remaining, entry⟩ := Native.caller_input ops.arguments 160 7 (parent empty) source (request empty) input
    (before safety empty n) (stack safety empty n) _ (values empty) (prepared safety empty n).2 (taken safety empty n).2 (key empty)
    prior.parent_good (Normalization.Tests.external_admitted _) prior.facts.nativeInput.choose_spec.2.2 rfl
    prefixCalls.1 (Prod.ext prefixCalls.2.1 rfl) (Prod.ext prefixCalls.2.2.1 rfl)
    (CallerInputTests.prefix_results safety empty).2.2.2.2 prior.facts.live prior.facts.unique (prior.source_private (key empty))
  have same := Local.mk.inj (entry.origin.scope.symm.trans prefixCalls.2.2.2)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact entry

/-- The input item is distinct from every owned nonempty word-array key.
This follows from the shared typed memory, not a fresh-address assumption. -/
theorem GraphFacts.input_apart {safety : Bool} {backing capacity : Nat} {world : World (Publication.Effects Nat)} {rows : List Storage.Cell}
    (facts : GraphFacts safety backing capacity world rows) (query : Key) (previous : OwnedKeys.Entry)
    (found : world.memory.effects.keys query = some previous) (nonempty : query.arguments ≠ []) : source.allocation ≠ previous.address := by
  obtain ⟨native, located, typed, _⟩ := facts.nativeInput
  have owned := (facts.live query previous found).resolve_left nonempty
  obtain ⟨⟨keyCell, keyFound, keyTyped, _⟩, _⟩ := facts.valid.related 7 previous.address query.arguments nonempty owned
  exact world.memory.memory.heap.lookup_ne_of_type_ne _ _ native keyCell located keyFound
    (by simp [typed, keyTyped, AssemblyItem.viewType])

/-- Derive retained Push data from the same native frame used by insertion
and publication. Item/owner, backing and key separation follow from typed
allocations and live registry owners; they are not extra caller premises. -/
theorem GraphFacts.data_after {safety : Bool} {backing capacity : Nat}
    {before : World (Publication.Effects Nat)} {rows : List Storage.Cell}
    (facts : GraphFacts safety backing capacity before rows) (key : Key)
    (after : Compiler.ZigAir.Memory.State)
    (frame : ∀ id native, before.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ backing →
      (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
      after.heap.lookup id = some native) : ∀ row ∈ rows, Constant.Data after row := by
  exact NativeGraph.data_frame safety 7 6 backing capacity before rows key after
    facts.valid facts.owner facts.owned facts.items facts.live facts.data frame

def reached (safety empty : Bool) (n : Nat) := (insert safety empty (normalized safety empty n) (taken safety empty n).2.world).2

/-- Connect a successful native execution to the actual caller continuation
and its outer defers. All graph facts below refer to this reached world. -/
theorem Prefix.completed {safety empty : Bool} {n : Nat} (prior : Prefix safety empty n) (bounded : n < 5)
    (after : Frame Nat) (ran : execute safety empty n = ((.ok (some .success), Storage.publishedOwnership), after))
    (candidate : cell input (key empty) (normalized safety empty n) (value safety empty n) Storage.publishedOwnership after = row safety empty n) :
    run safety empty (n + 1) = (.ok (BitVec.ofNat 32 (n + 1)),
      ⟨reached safety empty n, ⟨none, some (normalized safety empty n), true⟩⟩) ∧
    reached safety empty n = Insertion.projected (cells safety empty n) (taken safety empty n).2.world (key empty)
      (row safety empty n) Storage.publishedOwnership after := by
  have entry := prior.caller_input bounded
  have rows : (taken safety empty n).2.world.graph.representatives.getD [] = cells safety empty n := by
    rw [entry.origin.graph]; rfl
  have inserted : insert safety empty (normalized safety empty n) (taken safety empty n).2.world =
      (.ok (BitVec.ofNat 32 (n + 1)), reached safety empty n) := by
    apply Prod.ext
    · simp only [insert, insertWith, rows]
      change (match (execute safety empty n).1.1 with
        | .error _ => (Except.error (OwnedCall.Fault.language .safetyFault) : Except OwnedCall.Fault NodeId)
        | .ok outcome => (Interner.insertionOutcome (cells safety empty n) outcome).mapError OwnedCall.Fault.language) = _
      rw [ran]
      simp only [Interner.insertionOutcome, Except.mapError, Storage.idFor, prior.count]
    · rfl
  have finished := entry.handoff_insert ops.arguments (insert safety empty)
  simp only [inserted, ordinary, ↓reduceIte, (prefix_results safety empty n bounded).2.2.2] at finished
  refine ⟨?_, ?_⟩
  · rw [run, prior.result]
    change invoke safety empty (before safety empty n) = _
    rw [invoke, invokeWith, (prefix_results safety empty n bounded).1]
    have initialized : prepared safety empty n = (.ok (values empty), (prepared safety empty n).2) :=
      Prod.ext (prefix_results safety empty n bounded).2.1 rfl
    have transferred : taken safety empty n = (.ok (), (taken safety empty n).2) :=
      Prod.ext (prefix_results safety empty n bounded).2.2.1 rfl
    unfold prepared at initialized
    unfold taken at transferred
    simp only [Caller.invoke, Effect.bind]
    rw [initialized]
    change finish (Publication.external ops.arguments) 7
      (Effect.bind (take (Publication.external ops.arguments) 7)
        (fun _ => (do handoff; graph (insert safety empty) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty n).2).1
      (Effect.bind (take (Publication.external ops.arguments) 7)
        (fun _ => (do handoff; graph (insert safety empty) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty n).2).2 = _
    simp only [Effect.bind]
    rw [transferred]
    exact finished
  · unfold reached insert insertWith
    simp only [rows]
    change Insertion.projected _ _ _ (cell _ _ _ _ (execute safety empty n).1.2 (execute safety empty n).2)
      (execute safety empty n).1.2 (execute safety empty n).2 = _
    rw [ran]
    change Insertion.projected _ _ _ (cell input (key empty) (normalized safety empty n) (value safety empty n)
      Storage.publishedOwnership after) _ _ = _
    rw [candidate]

theorem GraphFacts.capacity_read {safety : Bool} {backing capacity : Nat} {world : World (Publication.Effects Nat)} {rows : List Storage.Cell}
    (facts : GraphFacts safety backing capacity world rows) :
    readField world.memory.memory (Owner.headerAddress ⟨6, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)) :=
  readHeader_capacity _ _ _ _ facts.header

/-- Each spare call starts in the preceding reached world and republishes its
key. Ownership and native correspondence are propagated by the implementation
theorem, including the original item and all earlier representative borrows. -/
theorem spare_step {safety empty : Bool} {n : Nat} (prior : Prefix safety empty n) (spare : n < 4) : Prefix safety empty (n + 1) := by
  have bounded : n < 5 := by omega
  have entry := prior.caller_input bounded
  have observations := preparation_results safety empty n bounded
  obtain ⟨owner, found, typed, writable⟩ := prior.facts.owner
  let probeEffects := (memory (append safety allocate 7 6 (cells safety empty n) input (key empty) (normalized safety empty n)
    (value safety empty n) preparationOwnership (preparedFrame (object safety empty n) (copied safety empty n)
      (operands safety empty n) (ready safety empty n))).2).effects.allocator * 10 + 8
  have result := entry.spare_success ops allocate safety 7 6 (lifetime empty) 5 (object safety empty n) owner
    (parent empty) source Insertion.Tests.model (request empty) (values empty) input (copied safety empty n) (key empty)
    (normalized safety empty n) (operands safety empty n) (lookup empty) (handle safety empty n) (before safety empty n) (taken safety empty n).2
    (cells safety empty n) (duplicated safety empty n).2 (made safety empty n).2 (cloned safety empty n).2
    (Normalization.Tests.external_admitted _) found typed writable prior.facts.owned (readHeader_items _ _ _ _ prior.facts.header)
    prior.facts.capacity_read prior.facts.vector prior.facts.descriptors prior.facts.resident prior.facts.apart prior.facts.items
    (by decide) (by rw [prior.count]; omega) (by rw [prior.count]; omega) observations.1 observations.2.1 observations.2.2
    probeEffects (by
      intro installed assigned
      have same : ready safety empty n = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
      rw [← same]
      rfl)
  obtain ⟨_, _, after, finalOwner, _, _, ran, valid, ownerFound, ownerTyped, ownerWritable, vector, owned, header,
      descriptors, resident, _, _, _, _, _, live, unique, apart, accepted, table, _, _, _, _, frame, _, items, candidate, _⟩ := result
  have selected : selectedGrowth (cells safety empty n) = none := by
    simp only [selectedGrowth, prior.count, show n + 1 ≠ 5 by omega, ↓reduceIte]
  have executed : execute safety empty n = ((.ok (some .success), Storage.publishedOwnership), after) := by
    simpa only [execute, selected] using ran
  have completed := prior.completed bounded after executed candidate
  have same : before safety empty (n + 1) = reached safety empty n := congrArg (fun result => result.2.world) completed.1
  have rows : cells safety empty (n + 1) = cells safety empty n ++ [row safety empty n] := by
    unfold cells
    rw [same, completed.2]
    rfl
  refine ⟨congrArg Prod.fst completed.1, ?_, ?_, ?_⟩
  · rw [same, rows, completed.2]
    obtain ⟨native, located, inputTyped, inputReads⟩ := prior.facts.nativeInput
    have inputFrame := frame source.allocation native located (by decide)
      (by cases empty <;> decide) (prior.facts.input_apart (key empty))
    refine ⟨rfl, ?_, valid, ⟨finalOwner, ownerFound, ownerTyped, ownerWritable⟩, owned, vector, ?_,
      descriptors, resident, items, ⟨native, inputFrame, inputTyped, inputReads.frame (inputFrame.trans located.symm)⟩,
      live, unique, apart, accepted, ?_⟩
    · change Cache.put equalityFields (taken safety empty n).2.world.graph.table (key empty) (Storage.idFor (cells safety empty n)) =
        OwnedKeys.view (memory after).effects.keys
      rw [table, OwnedKeys.view_store, entry.origin.graph, prior.facts.linked]
      rfl
    · simpa only [List.length_append, List.length_singleton] using header
    · intro logical member
      rcases List.mem_append.mp member with old | added
      · exact prior.facts.data_after (key empty) (memory after).memory frame logical old
      · have sameRow := List.mem_singleton.mp added
        subst logical
        exact Constant.Data.nonpush (memory after).memory (row safety empty n)
          (by change (1#32) ≠ 2#32; decide)
  · rw [rows, List.length_append, List.length_singleton, prior.count]
  · rw [rows, List.head?_append]
    rw [prior.first]
    rfl

theorem initialized_prefix (safety empty : Bool) (n : Nat) (bounded : n < 5) : Prefix safety empty n := by
  induction n with
  | zero => exact initial_prefix safety empty
  | succ n previous => exact spare_step (previous (by omega)) (by omega)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests
