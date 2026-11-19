/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparation
import Compiler.Extraction.InternerInsertionCleanupEffects
import Compiler.Extraction.StoragePreparationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- The complete release relation handles empty sentinels without demanding
separation. Nonempty argument owners survive a different buffer's release. -/
theorem release_keeps_arguments (allocator keptAllocator : Nat) (released kept : ArgumentSlice)
    (before after : Session σ)
    (post : Memory.Arguments.ReleasePost before.heap before.memory allocator released after.heap after.memory)
    (live : Memory.SliceValid keptAllocator before.heap kept)
    (separate : released.items ≠ [] → kept.items ≠ [] → kept.address ≠ released.address) :
    Memory.SliceValid keptAllocator after.heap kept := by
  rcases live with empty | stored
  · exact Or.inl empty
  by_cases empty : released.items = []
  · have same := post.logical
    simp only [Memory.releaseSlice, empty, List.isEmpty_nil, ↓reduceIte, Except.ok.injEq] at same
    exact Or.inr (same ▸ stored)
  by_cases keptEmpty : kept.items = []
  · exact Or.inl keptEmpty
  · exact Or.inr ((post.frame kept.address (separate empty keptEmpty)).1.trans stored)

/-- Invert actual duplication OOM. No allocation was created, both heaps are
unchanged, and the failed callback's allocator effects remain reached. -/
theorem duplicate_failed (ops : Operations σ) (allocator : Nat) (normalized : ArgumentSlice)
    (before after : Session (Publication.Effects σ)) (initial : Valid before)
    (live : Memory.SliceValid allocator before.heap normalized) (admitted : Admitted ops.arguments)
    (executed : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before = (.error .outOfMemory, after)) :
    after.heap = before.heap ∧ after.memory = before.memory ∧ Valid after := by
  obtain ⟨result, reached, ran, post⟩ := take_refines (Publication.external ops.arguments) allocator
    (view normalized) normalized.items ⟨view normalized, normalized.items, none⟩ before
    (borrowed_ready allocator normalized before initial live) (Publication.external_admitted ops.arguments admitted)
  rcases Prod.mk.inj (ran.symm.trans executed) with ⟨rfl, rfl⟩
  exact ⟨post.2.1, post.2.2.1, post.2.2.2.valid⟩

theorem free_keeps_dead (external : External σ) (allocator : Nat) (slice : ArgumentSlice)
    (before after : Session σ) (executed : free external allocator slice before = (.ok (), after))
    (post : Memory.Arguments.ReleasePost before.heap before.memory allocator slice after.heap after.memory)
    (id : Nat) (dead : before.heap id = none ∧ before.memory.heap.lookup id = none) :
    after.heap id = none ∧ after.memory.heap.lookup id = none := by
  by_cases empty : slice.items = []
  · rw [free_empty external allocator slice before empty] at executed
    cases Prod.mk.inj executed |>.2
    exact dead
  · by_cases same : id = slice.address
    · subst id; exact post.dead empty
    · exact ⟨(post.frame id same).1.trans dead.1, (post.frame id same).2.trans dead.2⟩

/-- Retained observations after a failed preparation. Fresh allocations may
have been created and retired; the private normalized owner may be consumed.
An empty sentinel excludes no old allocation. Allocation counters and effects
are still supplied by the actual execution, not reset by this frame. -/
structure PrivateFrame (owned : ArgumentSlice) (before after : Session (Publication.Effects σ)) : Prop where
  keys : after.effects.keys = before.effects.keys
  allocations : ∀ id cell, before.memory.heap.lookup id = some cell →
    (owned.items ≠ [] → id ≠ owned.address) →
    after.memory.heap.lookup id = some cell ∧ after.heap id = before.heap id

theorem free_private_frame (host : External σ) (allocator : Nat) (owned : ArgumentSlice)
    (before after : Session (Publication.Effects σ))
    (executed : free (Publication.external host) allocator owned before = (.ok (), after))
    (post : ReleasePost before.heap before.memory allocator owned after.heap after.memory) :
    PrivateFrame owned before after := by
  have keys := free_keys host allocator owned before
  rw [executed] at keys
  refine ⟨keys, ?_⟩
  intro id cell found apart
  by_cases empty : owned.items = []
  · rw [free_empty _ _ _ _ empty] at executed
    cases Prod.mk.inj executed |>.2
    exact ⟨found, rfl⟩
  · have frame := post.frame id (apart empty)
    exact ⟨frame.2.trans found, frame.1⟩

section Callbacks
variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
  (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
  (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
  (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
  (growth : Option (Growth.Registered.Callbacks σ))
local notation "calls" => callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth

/-- Native outer cleanup uses the actual reached memory and its existing owner. -/
theorem normalized_cleanup (before : Frame σ) (initial : Valid (memory before))
    (live : Memory.SliceValid allocator (memory before).heap normalized) :
    ∃ after,
      (∀ owner, (calls).release .normalized owner before = (.ok (), after)) ∧
      Valid (memory after) ∧
      Memory.Arguments.ReleasePost (memory before).heap (memory before).memory allocator normalized
        (memory after).heap (memory after).memory ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory before).effects
        else (Publication.external ops.arguments).free normalized (memory before)) ∧
      (∀ id, (memory before).heap id = none ∧ (memory before).memory.heap.lookup id = none →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) ∧
      after.item.object = before.item.object ∧ after.item.clone.value = before.item.clone.value ∧
      PrivateFrame normalized (memory before) (memory after) := by
  obtain ⟨released, freed, valid, post, effects⟩ := free_valid (Publication.external ops.arguments) allocator normalized
    (memory before) initial live
  refine ⟨withMemory before released, ?_, valid, post, effects,
    free_keeps_dead _ _ _ _ _ freed post, rfl, rfl, free_private_frame _ _ _ _ _ freed post⟩
  intro owner
  simp only [callbacks, Insertion.callbacks, freed, Except.mapError]

/-- Representative arguments and normalized arguments are released in source
order. Both nonempty owners are derived by callers from actual duplication. -/
theorem argument_cleanup (operands : ArgumentSlice) (owner : Storage.State) (before : Frame σ)
    (initial : Valid (memory before)) (present : arguments normalized owner before = some operands)
    (operandLive : Memory.SliceValid allocator (memory before).heap operands)
    (normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)
    (separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address) :
    ∃ freed after : Frame σ,
      (calls).release .arguments owner before = (.ok (), freed) ∧
      (∀ nextOwner, (calls).release .normalized nextOwner freed = (.ok (), after)) ∧
      Valid (memory after) ∧
      Memory.Arguments.ReleasePost (memory before).heap (memory before).memory allocator operands
        (memory freed).heap (memory freed).memory ∧
      Memory.Arguments.ReleasePost (memory freed).heap (memory freed).memory allocator normalized
        (memory after).heap (memory after).memory ∧
      (memory freed).effects = (if operands.items.isEmpty then (memory before).effects
        else (Publication.external ops.arguments).free operands (memory before)) ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory freed).effects
        else (Publication.external ops.arguments).free normalized (memory freed)) ∧
      (∀ id, (memory before).heap id = none ∧ (memory before).memory.heap.lookup id = none →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) ∧
      after.item.object = before.item.object ∧ after.item.clone.value = before.item.clone.value ∧
      PrivateFrame operands (memory before) (memory freed) ∧
      PrivateFrame normalized (memory freed) (memory after) := by
  obtain ⟨released, freed, valid, post, effects⟩ := free_valid (Publication.external ops.arguments) allocator operands
    (memory before) initial operandLive
  have kept := release_keeps_arguments allocator allocator operands normalized (memory before) released post normalizedLive separate
  obtain ⟨after, normalizedCall, finalValid, finalPost, finalEffects, keptDead, objectKept, valueKept, normalizedFrame⟩ :=
    normalized_cleanup ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
      (withMemory before released) valid kept
  refine ⟨withMemory before released, after, ?_, normalizedCall, finalValid, post, finalPost, effects, finalEffects,
    (fun id dead => keptDead id (free_keeps_dead _ _ _ _ _ freed post id dead)), objectKept, valueKept,
    free_private_frame _ _ _ _ _ freed post, normalizedFrame⟩
  simp only [callbacks, Insertion.callbacks, present, freed, Except.mapError]

end Callbacks

theorem arguments_consumed (allocator : Nat) (operands normalized : ArgumentSlice)
    (before freed after : Session σ)
    (first : Memory.Arguments.ReleasePost before.heap before.memory allocator operands freed.heap freed.memory)
    (last : Memory.Arguments.ReleasePost freed.heap freed.memory allocator normalized after.heap after.memory)
    (values : operands.items = normalized.items)
    (separate : normalized.items ≠ [] → normalized.address ≠ operands.address) :
    Consumed operands after ∧ Consumed normalized after := by
  refine ⟨?_, released_consumed last⟩
  by_cases empty : operands.items = []
  · exact Or.inl empty
  · have apart := Ne.symm (separate (by simpa only [← values] using empty))
    exact Or.inr ⟨(last.frame operands.address apart).1.trans (first.dead empty).1,
      (last.frame operands.address apart).2.trans (first.dead empty).2⟩

/-- Ordinary duplication OOM executes the actual outer defer. It never creates
an item or backing, consumes the incoming normalized owner and retains the
failed allocator's effects through that free. -/
theorem duplicate_oom_execution (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ)) (failed : Session (Publication.Effects σ))
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (admitted : Admitted ops.arguments) (room : cells.length < 2 ^ 32 - 1)
    (executed : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before.memory = (.error .outOfMemory, failed))
    (growth : Option (Growth.Registered.Callbacks σ) := none) :
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells before growth =
        ((.ok (some .allocationFailure), Storage.Release.normalized.run Storage.normalizedOwnership), after) ∧
      Valid (memory after) ∧ Consumed normalized (memory after) ∧
      (memory after).effects = (if normalized.items.isEmpty then failed.effects
        else (Publication.external ops.arguments).free normalized failed) ∧
      (memory after).memory.nextId = before.memory.memory.nextId ∧
      (memory after).memory.nextAddress = before.memory.memory.nextAddress ∧
      (∀ id, id ≠ normalized.address → (memory after).heap id = before.memory.heap id ∧
        (memory after).memory.heap.lookup id = before.memory.memory.heap.lookup id) ∧
      after.item.object = none ∧ after.item.clone.value = none ∧
      PrivateFrame normalized before.memory (memory after) := by
  let value := (key.eval meaning before.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩
  let reached := withMemory start failed
  obtain ⟨heap, native, valid⟩ := duplicate_failed ops allocator normalized before.memory failed initial live admitted executed
  have normalizedLive : Memory.SliceValid allocator failed.heap normalized := by rw [heap]; exact live
  obtain ⟨after, normalizedCall, finalValid, post, effects, _, objectKept, valueKept, normalizedFrame⟩ :=
    normalized_cleanup ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
      reached valid normalizedLive
  have duplicateCall : ∀ owner,
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt
        .arguments owner start = (.ok false, reached) := by
    intro owner
    have owned := ownsArguments_complete allocator normalized before.memory.heap live
    simp only [callbacks, Insertion.callbacks, start, memory, owned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      executed, Except.mapError]
    rfl
  refine ⟨after, ?_, finalValid, released_consumed post, effects, post.nextId.trans (congrArg (·.nextId) native),
    post.nextAddress.trans (congrArg (·.nextAddress) native), ?_, objectKept, valueKept, ?_⟩
  · change Storage.insertProgram.execute ⟨true, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth) {} start = _
    rw [show decide (cells.length < 2 ^ 32 - 1) = true from by simp [room]]
    exact Storage.insert_duplicate_oom _ start reached after duplicateCall normalizedCall
  · intro id apart
    have kept := post.frame id apart
    exact ⟨kept.1.trans (congrFun heap id), kept.2.trans (congrArg (fun m => m.heap.lookup id) native)⟩
  · have keys := arguments_keys ops.arguments allocator normalized before.memory
    rw [executed] at keys
    refine ⟨normalizedFrame.keys.trans keys, ?_⟩
    intro id cell found apart
    have kept := normalizedFrame.allocations id cell (by change failed.memory.heap.lookup id = _; rw [native]; exact found) apart
    exact ⟨kept.1, kept.2.trans (congrFun heap id)⟩

/-- Creation OOM retains the completed duplicate until its errdefer runs, then
executes the outer normalized free. The allocation history is not rewound. -/
theorem create_oom_execution (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (duplicated failed : Session (Publication.Effects σ)) (remaining : Handle)
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (admitted : Admitted ops.arguments) (room : cells.length < 2 ^ 32 - 1)
    (taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before.memory = (.ok (operands, remaining), duplicated))
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.error .outOfMemory, failed))
    (growth : Option (Growth.Registered.Callbacks σ) := none) :
    ∃ freed after : Frame σ,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells before growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.arguments, .normalized]).run Storage.duplicatedOwnership), after) ∧
      Valid (memory after) ∧ Consumed operands (memory after) ∧ Consumed normalized (memory after) ∧
      Memory.Arguments.ReleasePost failed.heap failed.memory allocator operands (memory freed).heap (memory freed).memory ∧
      Memory.Arguments.ReleasePost (memory freed).heap (memory freed).memory allocator normalized (memory after).heap (memory after).memory ∧
      (memory freed).effects = (if operands.items.isEmpty then failed.effects
        else (Publication.external ops.arguments).free operands failed) ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory freed).effects
        else (Publication.external ops.arguments).free normalized (memory freed)) ∧
      (memory after).memory.nextId = duplicated.memory.nextId ∧
      (memory after).memory.nextAddress = duplicated.memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧
      PrivateFrame normalized before.memory (memory after) := by
  let value := (key.eval meaning before.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩
  let dupe : Frame σ := { withMemory start duplicated with duplicate := some operands }
  let reached := withMemory dupe failed
  have post := duplicate_taken ops allocator normalized operands before.memory duplicated remaining initial live admitted taken
  obtain ⟨_, _, same⟩ := AssemblyItem.Creation.create_oom (observe ops.create) allocator input.item duplicated failed created
  have valid : Valid failed := by
    rw [same]
    exact ⟨post.ready.valid.memory, post.ready.valid.related, post.ready.valid.injected⟩
  have operandLive : Memory.SliceValid allocator failed.heap operands := by rw [same]; exact post.live
  have normalizedLive : Memory.SliceValid allocator failed.heap normalized := by
    rw [same]
    exact arguments_retained before.memory duplicated initial (fun id cell found => (post.frame id cell found).2) allocator normalized live
  obtain ⟨freed, after, argumentCall, normalizedCall, finalValid, first, last, firstEffects, lastEffects, _, objectKept, valueKept,
      operandFrame, normalizedFrame⟩ :=
    argument_cleanup ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
      operands Storage.duplicatedOwnership reached valid rfl operandLive normalizedLive (fun _ nonempty => post.separate nonempty)
  have consumed := arguments_consumed allocator operands normalized failed (memory freed) (memory after) first last post.values post.separate
  have duplicateCall : ∀ owner,
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt
        .arguments owner start = (.ok true, dupe) := by
    intro owner
    have owned := ownsArguments_complete allocator normalized before.memory.heap live
    simp only [callbacks, Insertion.callbacks, start, memory, owned, Bool.not_true, Bool.false_eq_true, ↓reduceIte, taken, Except.mapError]
    rfl
  have createCall : ∀ owner,
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt
        .item owner dupe = (.ok false, reached) := by
    intro owner
    simp only [callbacks, items, AssemblyItem.Creation.NativeFields.operations, AssemblyItem.Creation.Insertion.operations,
      dupe, start, withMemory, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    change (let result := AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated; _) = _
    rw [created]
    rfl
  refine ⟨freed, after, ?_, finalValid, consumed.1, consumed.2, first, last, firstEffects, lastEffects,
    last.nextId.trans (first.nextId.trans (by change failed.memory.nextId = _; rw [same])),
    last.nextAddress.trans (first.nextAddress.trans (by change failed.memory.nextAddress = _; rw [same])), objectKept, valueKept, ?_⟩
  · change Storage.insertProgram.execute ⟨true, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth) {} start = _
    rw [show decide (cells.length < 2 ^ 32 - 1) = true from by simp [room]]
    exact Storage.insert_create_oom _ start dupe reached freed after duplicateCall createCall argumentCall normalizedCall
  · have duplicateKeys := arguments_keys ops.arguments allocator normalized before.memory
    rw [taken] at duplicateKeys
    have createKeys := create_keys ops.create allocator input.item duplicated
    rw [created] at createKeys
    refine ⟨normalizedFrame.keys.trans (operandFrame.keys.trans (createKeys.trans duplicateKeys)), ?_⟩
    intro id cell found apart
    have older := (Compiler.ZigAir.Memory.valid_lookup before.memory.memory id cell initial.memory found).1
    have fresh := post.freshBorrow rfl
    have duplicatedFrame := post.frame id cell found
    have kept := operandFrame.allocations id cell
      (by change failed.memory.heap.lookup id = _; rw [same]; exact duplicatedFrame.1)
      (fun _ => by omega)
    have final := normalizedFrame.allocations id cell kept.1 apart
    have heap : failed.heap id = duplicated.heap id := by rw [same]
    exact ⟨final.1, final.2.trans (kept.2.trans (heap.trans duplicatedFrame.2))⟩

/-- Ordinary clone OOM derives the item owner from creation and both argument
owners from duplication. Actual source reads precede cloning; all three frees
run at their reached effects, and no payload owner is invented on failure. -/
theorem clone_oom_execution (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (duplicated allocated failed : Session (Publication.Effects σ)) (remaining : Handle)
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory itemSource input)
    (admitted : Admitted ops.arguments) (room : cells.length < 2 ^ 32 - 1)
    (taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before.memory = (.ok (operands, remaining), duplicated))
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.error .outOfMemory, failed))
    (growth : Option (Growth.Registered.Callbacks σ) := none) :
    ∃ destroyed freed after : Frame σ,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells before growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.allocation, .arguments, .normalized]).run Storage.createdOwnership), after) ∧
      Valid (memory after) ∧ Consumed operands (memory after) ∧ Consumed normalized (memory after) ∧
      AssemblyItem.Released object failed (memory destroyed) ∧
      Memory.Arguments.ReleasePost (memory destroyed).heap (memory destroyed).memory allocator operands (memory freed).heap (memory freed).memory ∧
      Memory.Arguments.ReleasePost (memory freed).heap (memory freed).memory allocator normalized (memory after).heap (memory after).memory ∧
      (memory destroyed).effects = release ops.objects object failed ∧
      (memory freed).effects = (if operands.items.isEmpty then (memory destroyed).effects
        else (Publication.external ops.arguments).free operands (memory destroyed)) ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory freed).effects
        else (Publication.external ops.arguments).free normalized (memory freed)) ∧
      (memory after).memory.nextId = allocated.memory.nextId ∧
      (memory after).memory.nextAddress = allocated.memory.nextAddress ∧
      (memory after).heap object = none ∧ (memory after).memory.heap.lookup object = none ∧
      after.item.object = none ∧ after.item.clone.value = none ∧
      PrivateFrame normalized before.memory (memory after) := by
  let value := (key.eval meaning before.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩
  let dupe : Frame σ := { withMemory start duplicated with duplicate := some operands }
  let made : Frame σ := { withMemory dupe allocated with item := { (withMemory dupe allocated).item with object := some object } }
  let reached := withMemory made failed
  have duplicatePost := duplicate_taken ops allocator normalized operands before.memory duplicated remaining initial live admitted taken
  have createdPost := AssemblyItem.Creation.create_verified (observe ops.create) allocator object input.item duplicated allocated duplicatePost.ready.valid created
  obtain ⟨heap, native⟩ := AssemblyClone.Physical.run_oom (observe ops.copy) allocator input allocated failed cloned
  have valid : Valid failed := ⟨by simpa only [native] using createdPost.valid.memory,
    by simpa only [heap, native] using createdPost.valid.related,
    by simpa only [heap, native] using createdPost.valid.injected⟩
  have owned : AssemblyItem.Owned allocator object failed := by
    simpa only [AssemblyItem.Owned, heap, native] using createdPost.owned
  have operandLive : Memory.SliceValid allocator failed.heap operands := by
    rw [heap]
    exact createdPost.arguments allocator object duplicated allocated duplicatePost.ready.valid operands duplicatePost.live
  have normalizedLive : Memory.SliceValid allocator failed.heap normalized := by
    rw [heap]
    exact createdPost.arguments allocator object duplicated allocated duplicatePost.ready.valid normalized
      (arguments_retained before.memory duplicated initial (fun id cell found => (duplicatePost.frame id cell found).2) allocator normalized live)
  obtain ⟨released, destroyedCall, releasedPost, destroyedEffects⟩ := AssemblyItem.destroy_verified (release ops.objects) allocator object failed valid owned
  let destroyed : Frame σ := { withMemory reached released with item := { (withMemory reached released).item with object := none } }
  obtain ⟨freed, after, argumentCall, normalizedCall, finalValid, first, last, firstEffects, lastEffects, keptDead, objectKept, valueKept,
      operandFrame, normalizedFrame⟩ :=
    argument_cleanup ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
      operands (Storage.Release.allocation.run Storage.createdOwnership) destroyed releasedPost.valid rfl
      (releasedPost.arguments object failed released allocator owned allocator operands operandLive)
      (releasedPost.arguments object failed released allocator owned allocator normalized normalizedLive)
      (fun _ nonempty => duplicatePost.separate nonempty)
  have consumed := arguments_consumed allocator operands normalized released (memory freed) (memory after) first last duplicatePost.values duplicatePost.separate
  obtain ⟨sourceCell, sourceFound⟩ := represented.live
  have sourceKept := represented.frame ((duplicatePost.frame itemSource.allocation sourceCell sourceFound).1.trans sourceFound.symm)
  have sourceCreated := AssemblyItem.Creation.NativeFields.represented_after_create duplicated allocated allocator object itemSource input
    duplicatePost.ready.valid sourceKept createdPost
  have duplicateCall : ∀ owner,
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt
        .arguments owner start = (.ok true, dupe) := by
    intro owner
    have incoming := ownsArguments_complete allocator normalized before.memory.heap live
    simp only [callbacks, Insertion.callbacks, start, memory, incoming, Bool.not_true, Bool.false_eq_true, ↓reduceIte, taken, Except.mapError]
    rfl
  have createCall : ∀ owner,
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt
        .item owner dupe = (.ok true, made) := by
    intro owner
    simp only [callbacks, items, AssemblyItem.Creation.NativeFields.operations, AssemblyItem.Creation.Insertion.operations,
      dupe, start, withMemory, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    change (let result := AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated; _) = _
    rw [created]
    rfl
  have cloneCall : ∀ owner,
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt
        .clone owner made = (.ok false, reached) := by
    intro owner
    have called := AssemblyItem.Creation.NativeFields.clone_oom (observe ops.create) (observe ops.copy)
      (release ops.bytes) (release ops.objects) (Publication.external ops.arguments) allocator object itemSource input
      (fun _ _ => (arguments normalized owner made).getD ⟨0, []⟩)
      { attempt := fun _ _ state => (.error .missingObject, state), release := fun _ _ state => (.error .missingObject, state) }
      owner made.item failed rfl sourceCreated cloned
    change (let result := (items ops allocator itemSource input normalized owner made).attempt .clone owner made.item;
      (result.1.mapError Fault.item, { made with item := result.2 })) = _
    simp only [items]
    rw [called]
    rfl
  have allocationCall :
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).release
        .allocation Storage.createdOwnership reached = (.ok (), destroyed) := by
    simp only [callbacks, Insertion.callbacks, itemOperations, AssemblyItem.Creation.Insertion.operations,
      reached, made, withMemory]
    change (let result := AssemblyItem.destroy (release ops.objects) allocator object failed; _) = _
    rw [destroyedCall]
    rfl
  have dead := keptDead object releasedPost.dead
  refine ⟨destroyed, freed, after, ?_, finalValid, consumed.1, consumed.2, releasedPost, first, last, destroyedEffects,
    firstEffects, lastEffects, last.nextId.trans (first.nextId.trans (releasedPost.nextId.trans (congrArg (·.nextId) native))),
    last.nextAddress.trans (first.nextAddress.trans (releasedPost.nextAddress.trans (congrArg (·.nextAddress) native))),
    dead.1, dead.2, objectKept, valueKept, ?_⟩
  · change Storage.insertProgram.execute ⟨true, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth) {} start = _
    rw [show decide (cells.length < 2 ^ 32 - 1) = true from by simp [room]]
    exact Storage.insert_clone_oom _ start dupe made reached destroyed freed after duplicateCall createCall cloneCall allocationCall argumentCall normalizedCall
  · have duplicateKeys := arguments_keys ops.arguments allocator normalized before.memory
    rw [taken] at duplicateKeys
    have createKeys := create_keys ops.create allocator input.item duplicated
    rw [created] at createKeys
    have cloneKeys := clone_keys ops.copy allocator input allocated
    rw [cloned] at cloneKeys
    have destroyKeys := destroy_keys ops.objects allocator object failed
    rw [destroyedCall] at destroyKeys
    refine ⟨normalizedFrame.keys.trans (operandFrame.keys.trans (destroyKeys.trans (cloneKeys.trans (createKeys.trans duplicateKeys)))), ?_⟩
    intro id cell found apart
    have duplicatedFrame := duplicatePost.frame id cell found
    have older := (Compiler.ZigAir.Memory.valid_lookup before.memory.memory id cell initial.memory found).1
    have fresh := duplicatePost.freshBorrow rfl
    have olderObject := (Compiler.ZigAir.Memory.valid_lookup duplicated.memory id cell duplicatePost.ready.valid.memory duplicatedFrame.1).1
    have objectFresh := createdPost.fresh
    have objectApart : id ≠ object := by omega
    have createdFrame := createdPost.frame id objectApart
    have destroyedFrame := releasedPost.frame id objectApart
    have kept := operandFrame.allocations id cell
      (destroyedFrame.2.trans ((congrArg (fun m => m.heap.lookup id) native).trans (createdFrame.2.trans duplicatedFrame.1)))
      (fun _ => by omega)
    have final := normalizedFrame.allocations id cell kept.1 apart
    exact ⟨final.1, final.2.trans (kept.2.trans (destroyedFrame.1.trans ((congrFun heap id).trans (createdFrame.1.trans duplicatedFrame.2))))⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
