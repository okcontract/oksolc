/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionProduction
import Compiler.Extraction.AssemblyCloneQueryRegistryTests
import Compiler.Extraction.InternerPublicationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

def base : Meaning where
  operation := fun _ _ _ => none
  atom := fun _ data _ _ => some data
def model := Folding.wordMeaning base
def push (value : Word) : Storage.Cell := { item := ⟨2, none, value⟩, otherValue := value, itemAddress := 0 }
def heap := Interner.observedHeap [push 5] (fun _ => none)
def initial := AssemblyItem.Creation.Insertion.Tests.initial
def world : World (Publication.Effects Nat) := ⟨heap, ⟨initial.heap, initial.memory, ⟨fun _ => none, 0⟩⟩⟩
def source : View := ⟨1, 0, 1⟩
def normalized := AssemblyItem.Creation.Insertion.Tests.incoming
def input := { AssemblyClone.Physical.Tests.input with item := ⟨26, none, 42⟩ }
def key : Key := ⟨input.item.kind, 0, input.item.data, normalized.items, 77⟩

def argumentHost (fail : Bool) : External Nat :=
  if fail then { ExpressionDeinit.Tests.external with allocate := fun _ _ _ effects => (none, effects * 10 + 1) }
  else ExpressionDeinit.Tests.external

/-- Explicit host outcomes with a trace of reached operations. Fresh byte/object
regions are above the current high-water mark. These are fixtures, not native
allocator or vector/hash-map implementation proofs. -/
def ops (failure : Option Storage.Allocation := none) : Operations Nat where
  arguments := argumentHost (failure == some .arguments)
  create wanted before := (if failure = some .item then none else some ((before.memory.nextAddress / wanted.alignment + 1) * wanted.alignment), before.effects * 10 + 5)
  copy _ before := (if failure = some .clone then none else some (before.memory.nextAddress + 1), before.effects * 10 + 6)
  bytes := AssemblyClone.Physical.Tests.bytes
  objects := AssemblyClone.Physical.Tests.objects
  append _ before := (failure != some .append, before.effects * 10 + 7)
  probe _ before := (failure != some .publish, before.effects * 10 + 8)

theorem admitted (failure : Option Storage.Allocation) : Admitted (ops failure).arguments := by
  dsimp only [ops, argumentHost]
  split
  · intro _ _ _ _ _ _ _ impossible; cases (Prod.mk.inj impossible).1
  · exact ExpressionDeinit.Tests.external_admitted

def run (failure : Option Storage.Allocation := none) (deterministic := true) :=
  insert (ops failure) 7 source model input key normalized deterministic world

theorem initial_good : Good source [99] world :=
  ⟨⟨AssemblyItem.Creation.Insertion.Tests.initial_valid.memory,
    AssemblyItem.Creation.Insertion.Tests.initial_valid.related, AssemblyItem.Creation.Insertion.Tests.initial_valid.injected⟩,
    (AssemblyItem.Creation.Insertion.Tests.initial_valid.related 11 1 [99] (by decide) (by rfl')).2⟩

theorem graph_valid : Interner.Invariant model heap := by
  refine ⟨?_, rfl, ?_⟩
  · intro _ _ impossible; cases impossible
  · simp [Storage.Coherent, push, Cache.Item.eval, Cache.readArguments, model, Folding.wordMeaning, Storage.Cell.value, Storage.Cell.isPush, Storage.Cell.dataValue, base]

theorem success : run.1 = .ok 1 ∧ run.2.memory.effects.allocator = 15678 ∧
    run.2.memory.heap 5 = some ⟨7, .arguments [0]⟩ ∧
    run.2.memory.heap 6 = some ⟨7, .item input.item⟩ ∧ run.2.memory.heap 7 = some ⟨7, .bytes 3⟩ ∧
    run.2.memory.effects.keys key = some ⟨0, 1⟩ ∧ run.2.graph.table key = some 1 := by
  exact ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem representative_descriptors :
    (run.2.graph.representatives.bind (fun cells => cells[1]?)).map (fun c => (c.itemAddress, c.argumentsAddress, c.arguments)) =
      some (6, 5, [0]) := by rfl'

theorem publication_oom : (run (some .publish)).1 = .error (.language .outOfMemory) ∧
    (run (some .publish)).2.memory.effects.allocator = 156782344 ∧
    (run (some .publish)).2.memory.heap 0 = none ∧ (run (some .publish)).2.memory.heap 5 = none ∧
    (run (some .publish)).2.memory.memory.heap.lookup 6 = none ∧
    (run (some .publish)).2.memory.memory.heap.lookup 7 = none ∧
    (run (some .publish)).2.graph.representatives = some [push 5] := by
  exact ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem append_oom : (run (some .append)).1 = .error (.language .outOfMemory) ∧
    (run (some .append)).2.memory.effects.allocator = 15672344 := ⟨by rfl', by rfl'⟩
theorem clone_oom : (run (some .clone)).1 = .error (.language .outOfMemory) ∧
    (run (some .clone)).2.memory.effects.allocator = 156344 := ⟨by rfl', by rfl'⟩
theorem creation_oom : (run (some .item)).1 = .error (.language .outOfMemory) ∧
    (run (some .item)).2.memory.effects.allocator = 1544 := ⟨by rfl', by rfl'⟩
theorem duplication_oom : (run (some .arguments)).1 = .error (.language .outOfMemory) ∧
    (run (some .arguments)).2.memory.effects.allocator = 14 ∧
    (run (some .arguments)).2.memory.heap 0 = none ∧
    (run (some .arguments)).2.memory.memory.nextId = world.memory.memory.nextId :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem transferred_success : (run none false).1 = .ok 1 ∧
    (run none false).2.memory.effects.allocator = 567 ∧
    (run none false).2.memory.heap 0 = world.memory.heap 0 ∧
    (run none false).2.memory.effects.keys key = none := ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem transferred_oom : (run (some .append) false).1 = .error (.language .outOfMemory) ∧
    (run (some .append) false).2.memory.effects.allocator = 567234 ∧
    (run (some .append) false).2.memory.heap 0 = none := ⟨by rfl', by rfl', by rfl'⟩

theorem verified (failure : Option Storage.Allocation) (deterministic : Bool)
    (completed : ordinary (run failure deterministic).1 = true) :
    Good source [99] (run failure deterministic).2 ∧
    Interner.Invariant model (run failure deterministic).2.graph ∧
    Interner.Stable world.graph (run failure deterministic).2.graph ∧
    match (run failure deterministic).1 with
    | .error _ => True
    | .ok id => (run failure deterministic).2.graph.read id = some input.item.data := by
  have semantic := body_semantics (ops failure) 7 source model input key normalized deterministic _ world input.item.data
    rfl initial_good.1 (admitted failure) graph_valid (by rfl') completed
  refine ⟨body_memory (ops failure) 7 source [99] model input key normalized deterministic _ world initial_good
    (admitted failure) completed, semantic.1, semantic.2.1, ?_⟩
  have returned := semantic.2.2
  have same : body (ops failure) 7 source model input key normalized deterministic [push 5] world = run failure deterministic := rfl
  rw [same] at returned
  cases response : (run failure deterministic).1 with
  | error fault => trivial
  | ok id => simpa only [response] using returned


/-- The source-frame checker rejects a consumed borrow, retaining the actual
post-cleanup state instead of pretending the original allocation survived. -/
theorem consumed_source_rejected :
    (insert (ops (some .append)) 7 (view normalized) model input key normalized true world).1 = .error (.language .safetyFault) ∧
    (insert (ops (some .append)) 7 (view normalized) model input key normalized true world).2.memory.heap 0 = none :=
  ⟨by rfl', by rfl'⟩
theorem wrong_key_rejected : (insert (ops) 7 source model input { key with data := key.data + 1 } normalized true world).1 =
    .error (.language .safetyFault) := by rfl'
theorem absent_graph_rejected : insert (ops) 7 source model input key normalized true
    { world with graph := { heap with representatives := none } } =
    (.error (.language .safetyFault), { world with graph := { heap with representatives := none } }) := by rfl'

def oldKey := (takeOwned normalizationOwnershipCode (Publication.external (ops).arguments) 7
  ⟨view normalized, normalized.items, none⟩ world.memory).2
def replacementWorld : World (Publication.Effects Nat) := { world with memory := { oldKey with
  effects := { oldKey.effects with keys := fun k => if k = key then some ⟨5, 0⟩ else none } } }
def replaced := insert (ops) 7 source model input key normalized true replacementWorld
theorem replacement : replaced.1 = .ok 1 ∧ replaced.2.memory.effects.allocator = 1156784 ∧
    replaced.2.memory.heap 5 = none ∧ replaced.2.memory.memory.heap.lookup 5 = none ∧
    replaced.2.memory.effects.keys key = some ⟨0, 1⟩ ∧ replaced.2.graph.table key = some 1 :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def broken := insert (ops) 7 source model { input with verbatim := some ⟨1, 2, ⟨999, [7, 8, 9], 0⟩⟩ } key normalized true world
theorem copy_fault_retains : broken.1 = .error (.language .safetyFault) ∧
    broken.2.memory.effects.allocator = 156 ∧ broken.2.memory.heap 0 = world.memory.heap 0 ∧
    broken.2.memory.heap 6 = some ⟨7, .item input.item⟩ ∧
    (broken.2.memory.memory.heap.lookup 7).isSome = true := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem missing_locals_rejected : admitOutput (Metadata := Nat) source key 42 world
    input
    (some .success) {} normalized ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩ = false := by rfl'

def executed (failure : Option Storage.Allocation := none) (deterministic := true) :=
  execution (ops failure) 7 source model input key normalized deterministic [push 5] world

/-- Every ordinary allocation cut is inhabited before output admission, for
both the duplicated and transferred argument paths. -/
theorem control_completes (failure : Option Storage.Allocation) (deterministic : Bool) :
    ∃ outcome, (executed failure deterministic).1.1 = .ok outcome := by
  cases failure with
  | none => cases deterministic <;> exact ⟨_, by rfl'⟩
  | some site => cases site <;> cases deterministic <;> exact ⟨_, by rfl'⟩

theorem fields_before_admission (failure : Option Storage.Allocation) (deterministic : Bool) :
    Fields input normalized (executed failure deterministic).2 := by
  obtain ⟨outcome, completed⟩ := control_completes failure deterministic
  exact execution_fields (ops failure) 7 source model input key normalized deterministic [push 5] world outcome
    initial_good.1 (admitted failure) completed

def forged := { (executed).2 with duplicate := some ⟨0, []⟩ }

/-- Input admission cannot replace the new execution invariant. Corrupting a
reached duplicate would pass input/frame checks, but cannot satisfy Fields. -/
theorem admission_is_not_field_correspondence :
    admitOutput source key 42 world input (some .success) (executed).1.2 normalized forged = true ∧
    ¬Fields input normalized forged := by
  refine ⟨by rfl', ?_⟩
  intro fields
  have impossible := congrArg List.length fields.duplicate
  change (0 : Nat) = 1 at impossible
  contradiction

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Tests
