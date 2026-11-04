/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchDebugEffects
import Compiler.Extraction.InternerNativeInput
import Compiler.Extraction.InternerNativeGraphFrame
import Compiler.Extraction.InternerCallerGraphCustody
import Compiler.Extraction.InternerPhysicalDispatchPreservation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Recursive

/-- The parent frame carried by proper children: the reached graph may append
and relocate, while the caller retains its normalized allocation privately
from every reached key and representative operand. It also retains the original
source view separately from key owners. Input preparation and normalization produce
these facts; child insertion must preserve them even for equal-content buffers.
This predicate is a recursive implementation obligation, not a host assumption. -/
def InputFrame (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (world : World (Publication.Effects σ)) : Prop :=
  (∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity world (rows ++ added) ∧
    Caller.GraphCustody allocator normalized (rows ++ added) world.memory ∧
    Caller.SourcePrivate source world.memory.effects.keys) ∧
    Held allocator source values normalized world

theorem InputFrame.initial {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice} {world : World (Publication.Effects σ)}
    (facts : NativeGraph.Facts safety allocator owner data capacity world rows)
    (held : Held allocator source values normalized world)
    (custody : Caller.GraphCustody allocator normalized rows world.memory)
    (privateSource : Caller.SourcePrivate source world.memory.effects.keys) :
    InputFrame safety allocator owner rows source values normalized world :=
  ⟨⟨[], data, capacity, by simpa only [List.append_nil] using facts,
    by simpa only [List.append_nil] using custody, privateSource⟩, held⟩

/-- The actual normalization/take prefix establishes the induction frame.
Native graph correspondence is transported through its derived allocation
frames; parent privacy comes from the same fresh normalized owner. -/
theorem InputFrame.caller {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {itemSource : Compiler.ZigAir.Memory.Address} {request : Interner.Request}
    {input : AssemblyClone.NativeFields.ItemValue} {key : Key} {lookup : Handle}
    {before : World (Publication.Effects σ)} {taken : OwnedCall.State (Publication.Effects σ)}
    (entry : Insertion.Native.CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys) :
    InputFrame safety allocator owner rows source request.arguments normalized taken.world := by
  have reached := facts.frame entry.origin.held.1.1
    (by rw [entry.origin.graph]; exact facts.projected)
    (congrArg Interner.Heap.table entry.origin.graph) entry.keys
    (fun id cell found _ => entry.origin.memory id cell found) entry.origin.registry
  exact InputFrame.initial reached entry.origin.held (entry.graph_custody rows facts.resident)
    (by rw [entry.keys]; exact privateSource)

theorem projection_at_read_bind (observe : World σ → Interner.Heap) (predicate : World σ → Prop) : Dispatch.Effects.ReadBind (projectionAt observe predicate) where
  bind := by
    intro α β result nextLeft nextRight following
    cases result with
    | ok value => exact following value rfl
    | error error =>
      intro before held completed
      cases error <;> exact ⟨held, rfl, rfl⟩

theorem projection_read_bind (predicate : World σ → Prop) : Dispatch.Effects.ReadBind (projection predicate) :=
  projection_at_read_bind World.graph predicate

theorem InputFrame.queries_at {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    (observe : World (Publication.Effects σ) → Interner.Heap)
    (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety allocator owner rows source values normalized world)
    (heap : Interner.Heap) (projected : heap.representatives = some rows) :
    Dispatch.Effects.Inputs (projectionAt observe predicate)
      (Interner.representativeReads heap) operand where
  queried := by
    intro id opcode slice queried index annotation item before frame completed
    obtain ⟨added, data, capacity, facts, _⟩ := (input before frame).1
    have query : Storage.operationProgram.run rows id opcode = .ok (some slice) := by
      simpa only [Interner.representativeReads, projected, Nested.storageReads] using queried
    obtain ⟨inside, atIndex⟩ := List.getElem?_eq_some_iff.mp item
    have loaded := facts.operand_after_append rows added id opcode slice query index inside annotation
    rw [atIndex] at loaded
    exact ⟨by simpa only [loaded] using frame, by simp only [loaded]; rfl, by simp only [loaded]; rfl⟩

theorem InputFrame.queries {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety allocator owner rows source values normalized world)
    (heap : Interner.Heap) (projected : heap.representatives = some rows) :
    Dispatch.Effects.Inputs (projection predicate)
      (Interner.representativeReads heap) operand :=
  InputFrame.queries_at World.graph predicate input heap projected

theorem InputFrame.root_at {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    (observe : World (Publication.Effects σ) → Interner.Heap)
    (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety allocator owner rows source values normalized world) :
    Dispatch.Effects.SliceInput (projectionAt observe predicate) operand normalized := by
  intro index annotation item before frame completed
  have held := (input before frame).2
  have valid := held.1.1
  have represented := (BorrowedQuery.slice_sound allocator normalized before.memory
    (BorrowedQuery.slice_complete allocator normalized before.memory valid held.2.1)).2.1
  obtain ⟨inside, atIndex⟩ := List.getElem?_eq_some_iff.mp item
  have loaded : operand normalized index annotation before = (.ok annotation, before) := by
    exact (ShiftInput.operand_good (view normalized) normalized.items before ⟨valid, represented⟩ index inside).trans
      (by rw [atIndex])
  exact ⟨by simpa only [loaded] using frame, by simp only [loaded]; rfl, by simp only [loaded]; rfl⟩

theorem InputFrame.root {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety allocator owner rows source values normalized world) :
    Dispatch.Effects.SliceInput (projection predicate) operand normalized :=
  InputFrame.root_at World.graph predicate input

/-- Connect the actual recursive context to the complete shared dispatcher.
Proper-child simulation is the induction premise; indexed loads and the root
input premise are derived from its reached graph and live parent frame. -/
theorem dispatch_projects_framed_at (observe : World (Publication.Effects σ) → Interner.Heap) (safety : Bool) (owner : Nat) (base : PairInput.Context (Publication.Effects σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    (projected : before.graph.representatives = some rows) (aligned : key.arguments = normalized.items)
    (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety base.allocator owner rows source values normalized world)
    (coupled : (projectionAt observe predicate).SourceConstructorsAt (Nested.storageReads rows) debug children model) :
    ProjectsAt observe predicate
      (Dispatch.simplifyWithInputs (Interner.representativeReads before.graph) children usizeBits
        key.instruction key.arguments debug operand normalized.address)
      (Dispatch.simplify (Interner.representativeReads before.graph) model usizeBits
        key.instruction key.arguments debug) := by
  exact Dispatch.Effects.simplify_with_inputs_at _ (projection_at_read_bind observe _) _ operand
    (InputFrame.queries_at observe predicate input before.graph projected) debug
    (by simpa only [Interner.representativeReads, projected] using coupled) usizeBits key.instruction key.arguments normalized.address
    (by simpa only [aligned] using (InputFrame.root_at observe predicate input))

theorem dispatch_projects_framed (safety : Bool) (owner : Nat) (base : PairInput.Context (Publication.Effects σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    (projected : before.graph.representatives = some rows) (aligned : key.arguments = normalized.items)
    (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety base.allocator owner rows source values normalized world)
    (coupled : (projection predicate).SourceConstructorsAt (Nested.storageReads rows) debug children model) :
    Projects predicate
      (Dispatch.simplifyWithInputs (Interner.representativeReads before.graph) children usizeBits
        key.instruction key.arguments debug operand normalized.address)
      (Dispatch.simplify (Interner.representativeReads before.graph) model usizeBits
        key.instruction key.arguments debug) :=
  dispatch_projects_framed_at World.graph safety owner base usizeBits children model debug source values key normalized rows before
    projected aligned predicate input coupled

/-- The original input-only interface specializes the same framed proof. -/
theorem dispatch_projects (safety : Bool) (owner : Nat) (base : PairInput.Context (Publication.Effects σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    (projected : before.graph.representatives = some rows) (aligned : key.arguments = normalized.items)
    (coupled : (projection (InputFrame safety base.allocator owner rows source values normalized)).SourceConstructorsAt (Nested.storageReads rows) debug children model) :
    Projects (InputFrame safety base.allocator owner rows source values normalized)
      (Dispatch.simplifyWithInputs (Interner.representativeReads before.graph) children usizeBits
        key.instruction key.arguments debug operand normalized.address)
      (Dispatch.simplify (Interner.representativeReads before.graph) model usizeBits
        key.instruction key.arguments debug) :=
  dispatch_projects_framed safety owner base usizeBits children model debug source values key normalized rows before
    projected aligned _ (fun _ frame => frame) coupled

/-- The actual context returns the exact model result and reached graph, and
keeps native graph facts and both parent inputs, on every ordinary outcome.
The premise is on proper children, not on the enclosing dispatcher result. -/
theorem dispatcher_projects_cursor (cursor : World (Publication.Effects σ) → Nat) (safety : Bool) (owner : Nat) (base : PairInput.Context (Publication.Effects σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (aligned : key.arguments = normalized.items) (held : Held base.allocator source values normalized before)
    (custody : Caller.GraphCustody base.allocator normalized rows before.memory)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (coupled : (projectionAt (cursorGraph cursor) (InputFrame safety base.allocator owner rows source values normalized)).SourceConstructorsAt (Nested.storageReads rows) debug children model) :
    let executed := ((context base owner usizeBits children debug).primitives source address native).simplify key normalized before
    let logical := Dispatch.simplify (Interner.representativeReads before.graph) model usizeBits
      key.instruction key.arguments debug (cursorGraph cursor before)
    ordinary executed.1 = true →
      InputFrame safety base.allocator owner rows source values normalized executed.2 ∧
      executed.1 = logical.1.mapError Fault.language ∧ cursorGraph cursor executed.2 = logical.2 := by
  simp only [dispatcher_snapshot]
  rw [facts.reads]
  exact dispatch_projects_framed_at (cursorGraph cursor) safety owner base usizeBits children model debug source values key normalized rows before
    facts.projected aligned _ (fun _ frame => frame) coupled before (InputFrame.initial facts held custody privateSource)

/-- The original native dispatcher observes its existing graph cursor. -/
theorem dispatcher_projects (safety : Bool) (owner : Nat) (base : PairInput.Context (Publication.Effects σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (aligned : key.arguments = normalized.items) (held : Held base.allocator source values normalized before)
    (custody : Caller.GraphCustody base.allocator normalized rows before.memory)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (coupled : (projection (InputFrame safety base.allocator owner rows source values normalized)).SourceConstructorsAt (Nested.storageReads rows) debug children model) :
    let executed := ((context base owner usizeBits children debug).primitives source address native).simplify key normalized before
    let logical := Dispatch.simplify (Interner.representativeReads before.graph) model usizeBits
      key.instruction key.arguments debug before.graph
    ordinary executed.1 = true →
      InputFrame safety base.allocator owner rows source values normalized executed.2 ∧
      executed.1 = logical.1.mapError Fault.language ∧ executed.2.graph = logical.2 := by
  simpa only [cursorGraph] using dispatcher_projects_cursor (fun world => world.graph.allocationCursor)
    safety owner base usizeBits children model debug source values address native key normalized rows before
    facts aligned held custody privateSource coupled

/-- The same native execution inherits the universal word theorem, without a
separate logical dispatcher or postulated result ID. Native child simulation
and its word contract are still the recursive induction obligations. -/
theorem dispatcher_verified_cursor (cursor : World (Publication.Effects σ) → Nat) (safety : Bool) (owner : Nat) (base : PairInput.Context (Publication.Effects σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (aligned : key.arguments = normalized.items) (held : Held base.allocator source values normalized before)
    (custody : Caller.GraphCustody base.allocator normalized rows before.memory)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (coupled : (projectionAt (cursorGraph cursor) (InputFrame safety base.allocator owner rows source values normalized)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (env : AddressMask.Environment) (other : Meaning)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : key.eval (Dispatch.wordDispatchMeaning env other) before.graph.read = some expected) :
    let executed := ((context base owner usizeBits children debug).primitives source address native).simplify key normalized before
    Semantic.Ensures (Dispatch.wordDispatchMeaning env other) (cursorGraph cursor before) executed.1 (cursorGraph cursor executed.2)
      (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  simp only [dispatcher_snapshot]
  rw [facts.reads]
  exact ProjectsAt.safe (cursorGraph cursor) _ _ _
    (dispatch_projects_framed_at (cursorGraph cursor) safety owner base usizeBits children model debug source values key normalized rows before
      facts.projected aligned _ (fun _ frame => frame) coupled) _ before (InputFrame.initial facts held custody privateSource) _
    (Dispatch.default_key_simplify_safe env other _ model correct addresses shifts (cursorGraph cursor before) (valid.with_cursor (cursor before))
      (Interner.representative_reads_sound _ before.graph valid) key operation expected debug usizeBits evaluated)

/-- The existing word-preservation endpoint specializes the cursor-aware proof. -/
theorem dispatcher_verified (safety : Bool) (owner : Nat) (base : PairInput.Context (Publication.Effects σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (aligned : key.arguments = normalized.items) (held : Held base.allocator source values normalized before)
    (custody : Caller.GraphCustody base.allocator normalized rows before.memory)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (coupled : (projection (InputFrame safety base.allocator owner rows source values normalized)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (env : AddressMask.Environment) (other : Meaning)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : key.eval (Dispatch.wordDispatchMeaning env other) before.graph.read = some expected) :
    let executed := ((context base owner usizeBits children debug).primitives source address native).simplify key normalized before
    Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph executed.1 executed.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  simpa only [cursorGraph] using dispatcher_verified_cursor (fun world => world.graph.allocationCursor)
    safety owner base usizeBits children model debug source values address native key normalized rows before
    facts aligned held custody privateSource coupled env other correct addresses shifts expected operation valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
