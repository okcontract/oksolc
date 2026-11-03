/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionExecution
import Compiler.Extraction.AssemblyItemCreationFields
import Compiler.Extraction.RepresentativeRegisteredGrowthAppend
import Compiler.Extraction.AssemblyItemDeinitNative
import Compiler.Extraction.ExpressionDeinitNative
import Compiler.Extraction.RepresentativeLastExpression
import Compiler.Extraction.RepresentativeRegisteredPop

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

abbrev Frame (σ : Type) := Insertion.State AssemblyItem.Fields.Values σ

inductive Fault where
  | base (reason : Rejection)
  | item (reason : AssemblyItem.Creation.NativeFields.Fault)
  | append (reason : Append.Registered.Fault)
  | cleanup (reason : AssemblyItemDeinit.Native.Fault)
  | lastRow (reason : Compiler.ZigAir.Memory.Fault)
  | expression (reason : ExpressionDeinit.Native.Fault)
  | pop (reason : Pop.Registered.Fault)
  deriving DecidableEq, Repr

/-- The same allocator identity selects the backing request. Allocator-private
effects cannot overwrite the publication interpreter's owned key table. -/
def allocation (allocate : Backing.Registry.Allocate σ) : Backing.Registry.Allocate (Publication.Effects σ) :=
  fun allocator bytes alignment effects =>
    let (result, reached) := allocate allocator bytes alignment effects.allocator
    (result, { effects with allocator := reached })

theorem allocation_keys (allocate : Backing.Registry.Allocate σ) (allocator bytes alignment : Nat)
    (effects : Publication.Effects σ) :
    (allocation allocate allocator bytes alignment effects).2.keys = effects.keys := rfl

/-- Preserve the publication-owned table while forwarding the captured remap
identity and exact backing-release request to the allocator-private effects. -/
def growthCallbacks (calls : Growth.Registered.Callbacks σ) : Growth.Registered.Callbacks (Publication.Effects σ) :=
  ⟨calls.remap, fun allocator base bytes alignment effects =>
    { effects with allocator := calls.release allocator base bytes alignment effects.allocator }⟩

theorem growth_release_keys (calls : Growth.Registered.Callbacks σ) (allocator base bytes alignment : Nat)
    (effects : Publication.Effects σ) :
    ((growthCallbacks calls).release allocator base bytes alignment effects).keys = effects.keys := rfl

theorem growth_release_effects (calls : Growth.Registered.Callbacks σ) (allocator base bytes alignment : Nat)
    (effects : Publication.Effects σ) :
    ((growthCallbacks calls).release allocator base bytes alignment effects).allocator =
      calls.release allocator base bytes alignment effects.allocator := rfl

def items (ops : Operations σ) (allocator : Nat) (source : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice) (owner : Storage.State) (before : Frame σ) :=
  AssemblyItem.Creation.NativeFields.operations (observe ops.create) (observe ops.copy) (release ops.bytes) (release ops.objects)
    (Publication.external ops.arguments) allocator source input
    (fun _ _ => (arguments normalized owner before).getD ⟨0, []⟩)
    { attempt := fun _ _ state => (.error .missingObject, state)
      release := fun _ _ state => (.error .missingObject, state) }

/-- Native append consumes the actual reached object, clone and argument
locals. No fallback descriptor can be admitted through an absent local. -/
def append (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator container : Nat)
    (cells : List Storage.Cell) (input : AssemblyClone.NativeFields.ItemValue) (key : Key)
    (normalized : ArgumentSlice) (value : Word) (owner : Storage.State) (before : Frame σ)
    (growth : Option (Growth.Registered.Callbacks σ) := none) : Except Fault Bool × Frame σ :=
  if before.item.object.isNone || before.item.clone.value.isNone || (arguments normalized owner before).isNone then
    (.error (.base .missingValue), before)
  else
    let (result, reached) := match growth with
      | none => Append.Registered.run runtimeSafety (allocation allocate) allocator container cells
          (cell input key normalized value owner before) (memory before)
      | some calls => Append.Registered.runWithGrowth (growthCallbacks calls) runtimeSafety (allocation allocate) allocator container cells
          (cell input key normalized value owner before) (memory before)
    (result.mapError Fault.append, withMemory before reached)

/-- The value errdefer reads the owned object's native optional field. Clear the
clone local only after both payload release and typed invalidation succeed;
keep every reached allocator effect on rejection. Expression invalidation is a
separate later operation, so its marker is unchanged here. -/
def releaseValue (ops : Operations σ) (allocator : Nat) (before : Frame σ) :
    Except Fault Unit × Frame σ :=
  match before.item.object with
  | none => (.error (.base (.creation .missingObject)), before)
  | some object =>
    let (result, reached) := AssemblyItemDeinit.Native.run (release ops.bytes) allocator ⟨object, 0⟩ (memory before)
    let next := withMemory before reached.memory
    match result with
    | .error reason => (.error (.cleanup reason), next)
    | .ok () => (.ok (), { next with item := { next.item with clone := { next.item.clone with value := none } } })

theorem releaseValue_success (ops : Operations σ) (allocator object : Nat) (before : Frame σ)
    (after : AssemblyItemDeinit.State (Publication.Effects σ))
    (present : before.item.object = some object)
    (executed : AssemblyItemDeinit.Native.run (release ops.bytes) allocator ⟨object, 0⟩ (memory before) = (.ok (), after)) :
    releaseValue ops allocator before =
      let next := withMemory before after.memory
      (.ok (), { next with item := { next.item with clone := { next.item.clone with value := none } } }) := by
  simp only [releaseValue, present, executed]

theorem releaseValue_rejected (ops : Operations σ) (allocator object : Nat) (before : Frame σ)
    (after : AssemblyItemDeinit.State (Publication.Effects σ)) (fault : AssemblyItemDeinit.Native.Fault)
    (present : before.item.object = some object)
    (executed : AssemblyItemDeinit.Native.run (release ops.bytes) allocator ⟨object, 0⟩ (memory before) = (.error fault, after)) :
    releaseValue ops allocator before = (.error (.cleanup fault), withMemory before after.memory) := by
  simp only [releaseValue, present, executed]

/-- Publication rollback consumes the row selected by the reached native
header. Transferred locals do not supply its item or argument pointers. Every
rejection retains completed cleanup; locals clear only after row invalidation. -/
def releaseLast (ops : Operations σ) (allocator container : Nat) (before : Frame σ) :
    Except Fault Unit × Frame σ :=
  match Last.select (memory before).memory (Owner.headerAddress ⟨container, 0⟩) with
  | .error reason => (.error (.lastRow reason), before)
  | .ok descriptor =>
    let (result, reached) := ExpressionDeinit.Native.run (release ops.bytes) (release ops.objects)
      (Publication.external ops.arguments) allocator descriptor (memory before)
    let next := withMemory before reached.memory
    match result with
    | .error reason => (.error (.expression reason), next)
    | .ok () => (.ok (), { next with item := { next.item with object := none, clone := { next.item.clone with value := none, execution := reached } } })

theorem releaseLast_unselected (ops : Operations σ) (allocator container : Nat) (before : Frame σ)
    (fault : Compiler.ZigAir.Memory.Fault)
    (rejected : Last.select (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .error fault) :
    releaseLast ops allocator container before = (.error (.lastRow fault), before) := by
  simp only [releaseLast, rejected]

theorem releaseLast_success (ops : Operations σ) (allocator container : Nat) (before : Frame σ)
    (descriptor : Compiler.ZigAir.Memory.Address) (after : ExpressionDeinit.State (Publication.Effects σ))
    (selected : Last.select (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .ok descriptor)
    (executed : ExpressionDeinit.Native.run (release ops.bytes) (release ops.objects)
      (Publication.external ops.arguments) allocator descriptor (memory before) = (.ok (), after)) :
    releaseLast ops allocator container before =
      let next := withMemory before after.memory
      (.ok (), { next with item := { next.item with object := none, clone := { next.item.clone with value := none, execution := after } } }) := by
  simp only [releaseLast, selected, executed]

theorem releaseLast_rejected (ops : Operations σ) (allocator container : Nat) (before : Frame σ)
    (descriptor : Compiler.ZigAir.Memory.Address) (after : ExpressionDeinit.State (Publication.Effects σ))
    (fault : ExpressionDeinit.Native.Fault)
    (selected : Last.select (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .ok descriptor)
    (executed : ExpressionDeinit.Native.run (release ops.bytes) (release ops.objects)
      (Publication.external ops.arguments) allocator descriptor (memory before) = (.error fault, after)) :
    releaseLast ops allocator container before = (.error (.expression fault), withMemory before after.memory) := by
  simp only [releaseLast, selected, executed]

/-- The native decrement precedes the logical vector refinement. Preserve the
same reached session on registry rejection, including earlier cleanup. -/
def pop (allocator container : Nat) (before : Frame σ) : Except Fault Unit × Frame σ :=
  let (result, reached) := Pop.Registered.run allocator container (memory before)
  (result.mapError Fault.pop, withMemory before reached)

theorem pop_memory (allocator container : Nat) (before : Frame σ) :
    memory (pop allocator container before).2 = (Pop.Registered.run allocator container (memory before)).2 := by
  unfold pop
  generalize Pop.Registered.run allocator container (memory before) = outcome
  obtain ⟨result, reached⟩ := outcome
  rfl

/-- Reuse the source-bound insertion program, locals, argument preparation and
publication interpreter. Item creation/clone now install every native member;
append retains native header/descriptor writes, and lastValue selects and
destroys the native last row before the native length decrement and registry pop.
Initial header/count, graph/table and allocator-field correspondence remain
compiler obligations, not new host assumptions or consequences of this adapter. -/
def callbacks (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ) := none) : Storage.Operations (Frame σ) Fault :=
  let base := Insertion.callbacks ops allocator cells.length source input key normalized graph
  { attempt := fun site owner before => match site with
      | .item | .clone =>
        let (result, reached) := (items ops allocator itemSource input normalized owner before).attempt site owner before.item
        (result.mapError Fault.item, { before with item := reached })
      | .append => append runtimeSafety allocate allocator container cells input key normalized value owner before growth
      | _ => let (result, reached) := base.attempt site owner before; (result.mapError Fault.base, reached)
    release := fun action owner before => match action with
      | .value => releaseValue ops allocator before
      | .lastValue => releaseLast ops allocator container before
      | .pop => pop allocator container before
      | _ => let (result, reached) := base.release action owner before; (result.mapError Fault.base, reached) }

theorem value_callback (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (owner : Storage.State) (before : Frame σ) :
    (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph).release .value owner before =
      releaseValue ops allocator before := rfl

theorem last_value_callback (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (owner : Storage.State) (before : Frame σ) :
    (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph).release .lastValue owner before =
      releaseLast ops allocator container before := rfl

theorem pop_callback (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (owner : Storage.State) (before : Frame σ) :
    (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph).release .pop owner before =
      let (result, reached) := Pop.Registered.run allocator container (memory before)
      (result.mapError Fault.pop, withMemory before reached) := rfl

theorem append_callback (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (owner : Storage.State) (before : Frame σ) (object : Nat) (copied : AssemblyClone.NativeFields.ItemValue) (slice : ArgumentSlice)
    (objectPresent : before.item.object = some object) (clonePresent : before.item.clone.value = some copied)
    (argumentsPresent : arguments normalized owner before = some slice) :
    (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph).attempt .append owner before =
      let (result, reached) := Append.Registered.run runtimeSafety (allocation allocate) allocator container cells
        ⟨copied.item, value, object, slice.items, key.sequence, slice.address⟩ (memory before)
      (result.mapError Fault.append, withMemory before reached) := by
  simp only [callbacks, append, objectPresent, clonePresent, argumentsPresent, Option.isNone_some, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, cell, Option.getD_some]

/-- The actual insertion call site forwards reached locals and captured growth
operations. Ownership and graph premises are proved by the caller, not here. -/
theorem append_growth_callback (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (owner : Storage.State) (before : Frame σ) (calls : Growth.Registered.Callbacks σ)
    (object : Nat) (copied : AssemblyClone.NativeFields.ItemValue) (slice : ArgumentSlice)
    (objectPresent : before.item.object = some object) (clonePresent : before.item.clone.value = some copied)
    (argumentsPresent : arguments normalized owner before = some slice) :
    (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph (some calls)).attempt .append owner before =
      let (result, reached) := Append.Registered.runWithGrowth (growthCallbacks calls) runtimeSafety (allocation allocate) allocator container cells
        ⟨copied.item, value, object, slice.items, key.sequence, slice.address⟩ (memory before)
      (result.mapError Fault.append, withMemory before reached) := by
  simp only [callbacks, append, objectPresent, clonePresent, argumentsPresent, Option.isNone_some, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, cell, Option.getD_some]

/-- Shared invocation of the admitted source body. The logical interface below
computes room from its rows; the native count adapter checks those rows against
the reached header before supplying the same input. -/
def executionWithRoom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic room : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ) := none) :=
  let value := (key.eval meaning before.graph.read).getD 0
  let projection := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  Storage.insertProgram.execute ⟨deterministic, room, fun _ => false⟩
    (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value projection growth) {}
    ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩

def execution (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ) := none) :=
  executionWithRoom ops allocate runtimeSafety allocator container source itemSource meaning input key normalized
    deterministic (decide (cells.length < 2 ^ 32 - 1)) cells before growth

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
