/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveProtocolTrace
import Compiler.Extraction.InternerResourceProjection

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)
open ConstructorItem.ProtocolTrace (Capture mapConstructors eraseCapture prefixCapture start)

/-- Observe native allocation identity before executing the existing constructor.
The slot carries no successful-allocation, returned-value or graph premise. -/
def entry (before : World σ) : ProtocolEvent :=
  .nativeEntry before.memory.memory.nextId before.memory.memory.nextAddress

def mark (action : Capture σ NodeId) : Capture σ NodeId := fun before leading =>
  action before (leading ++ [entry before])

def Begins (action : Capture σ NodeId) : Prop :=
  ∀ before leading, ∃ trailing, (action before leading).2.events = leading ++ entry before :: trailing

structure Marked (captured : ProtocolTrace.Captures σ) : Prop where
  operation : ∀ opcode values debug, Begins (captured.operation opcode values debug)
  constant : ∀ value debug, Begins (captured.constant value debug)
  materialize : ∀ id value debug, Begins (captured.materialize id value debug)
  borrowed : ∀ address opcode values debug, Begins (captured.borrowedOperation address opcode values debug)
  namedLocal : ∀ opcode source selected repeated first debug,
    Begins (captured.localOperation opcode source selected repeated first debug)

theorem mark_begins (action : Capture σ NodeId)
    (prefixed : ∀ before earlier leading, action before (earlier ++ leading) =
      (let called := action before leading
       (called.1, Caller.ProtocolTrace.prepend earlier called.2))) : Begins (mark action) := by
  intro before leading
  refine ⟨(action before []).2.events, ?_⟩
  have same := congrArg (fun result => result.2.events) (prefixed before (leading ++ [entry before]) [])
  simpa only [mark, List.append_nil, Caller.ProtocolTrace.prepend, List.append_assoc, List.singleton_append] using same

theorem marked_map (captured : ProtocolTrace.Captures σ)
    (prefixed : ∀ earlier leading,
      mapConstructors (m := Capture (Publication.Effects σ))
        (n := fun _ => World (Publication.Effects σ) → Except Fault NodeId × Caller.ProtocolTrace.Recorded (Publication.Effects σ))
        (fun action before => action before (earlier ++ leading)) captured =
      mapConstructors (prefixCapture earlier leading) captured) : Marked (mapConstructors mark captured) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro opcode values debug
    apply mark_begins
    intro before earlier leading
    exact congrArg (fun family => family.operation opcode values debug before) (prefixed earlier leading)
  · intro value debug
    apply mark_begins
    intro before earlier leading
    exact congrArg (fun family => family.constant value debug before) (prefixed earlier leading)
  · intro id value debug
    apply mark_begins
    intro before earlier leading
    exact congrArg (fun family => family.materialize id value debug before) (prefixed earlier leading)
  · intro address opcode values debug
    apply mark_begins
    intro before earlier leading
    exact congrArg (fun family => family.borrowedOperation address opcode values debug before) (prefixed earlier leading)
  · intro opcode source selected repeated first debug
    apply mark_begins
    intro before earlier leading
    exact congrArg (fun family => family.localOperation opcode source selected repeated first debug before) (prefixed earlier leading)

theorem mark_erases (captured : ProtocolTrace.Captures σ) (native : Constructors (Publication.Effects σ))
    (correct : ∀ leading, mapConstructors (eraseCapture leading) captured = native)
    (leading : List ProtocolEvent) :
    mapConstructors (eraseCapture leading) (mapConstructors mark captured) = native := by
  rcases captured with ⟨operation, constant, materialize, borrowed, namedLocal⟩
  rcases native with ⟨nativeOperation, nativeConstant, nativeMaterialize, nativeBorrowed, nativeLocal⟩
  dsimp only [mapConstructors]
  congr 1
  · funext opcode values debug before
    exact congrArg (fun family => family.operation opcode values debug before) (correct (leading ++ [entry before]))
  · funext value debug before
    exact congrArg (fun family => family.constant value debug before) (correct (leading ++ [entry before]))
  · funext id value debug before
    exact congrArg (fun family => family.materialize id value debug before) (correct (leading ++ [entry before]))
  · funext address opcode values debug before
    exact congrArg (fun family => family.borrowedOperation address opcode values debug before) (correct (leading ++ [entry before]))
  · funext opcode source selected repeated first debug before
    exact congrArg (fun family => family.localOperation opcode source selected repeated first debug before) (correct (leading ++ [entry before]))

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)

/-- Observe the reached input of the real insertion port. Recursive children
may have allocated since constructor entry; neither their returned graph nor
the insertion's final candidate supplies these identities. -/
def insertionEntry (before : World σ) : ProtocolEvent :=
  .nativeInsertion before.memory.memory.nextId before.memory.memory.nextAddress

def graphObservations (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue) :
    Caller.ProtocolTrace.GraphObservations (Publication.Effects σ) :=
  let original := Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits
    children observations debug source address input
  { original with insert := fun key slice deterministic before =>
      insertionEntry before :: original.insert key slice deterministic before }

/-- The allocation-aware family uses the shared constructor recorder with a
reached insertion observation. Publication and child observations are reused. -/
def step (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) : ProtocolTrace.Captures σ :=
  ProtocolTrace.stepWith ops allocate safety owner meaning base growth usizeBits children
    (graphObservations ops allocate safety owner meaning base growth usizeBits children observations)

theorem step_erases (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (leading : List ProtocolEvent) :
    mapConstructors (eraseCapture leading) (step ops allocate safety owner meaning base growth usizeBits children observations) =
      NativeRecursion.step (callerContext ops allocate safety owner meaning base growth) owner usizeBits children :=
  ProtocolTrace.stepWith_erases ops allocate safety owner meaning base growth usizeBits children _ leading

theorem step_prefix (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (earlier leading : List ProtocolEvent) :
    mapConstructors (m := Capture (Publication.Effects σ))
      (n := fun _ => World (Publication.Effects σ) → Except Fault NodeId × Caller.ProtocolTrace.Recorded (Publication.Effects σ))
      (fun action before => action before (earlier ++ leading)) (step ops allocate safety owner meaning base growth usizeBits children observations) =
    mapConstructors (prefixCapture earlier leading) (step ops allocate safety owner meaning base growth usizeBits children observations) :=
  ProtocolTrace.stepWith_prefix ops allocate safety owner meaning base growth usizeBits children _ earlier leading

/-- Every depth reuses the existing wrapper and caller capture. Only its child
observations change, so nested entries are recorded at their actual inputs.
Exhaustion retains its explicit failure and still records the attempted call. -/
def unfold : Nat → ProtocolTrace.Captures σ
  | 0 => mapConstructors mark (ProtocolTrace.unfold ops allocate safety owner meaning base growth usizeBits 0)
  | depth + 1 => mapConstructors mark
      (step ops allocate safety owner meaning base growth usizeBits
        (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
        (ProtocolTrace.observe (unfold depth)))

/-- The richer observation executes the same native body at every depth and
through all five entry routes, including failed and exhausted executions. -/
theorem unfold_erases (depth : Nat) (leading : List ProtocolEvent) :
    mapConstructors (eraseCapture leading) (unfold ops allocate safety owner meaning base growth usizeBits depth) =
      NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth := by
  cases depth with
  | zero => rfl
  | succ depth =>
    exact mark_erases _ _ (step_erases ops allocate safety owner meaning base growth usizeBits _ _) leading

/-- Entries come from each actual native input, including nested calls,
allocation refusal and exhaustion. No caller-supplied observation is used. -/
theorem unfold_marked (depth : Nat) : Marked (unfold ops allocate safety owner meaning base growth usizeBits depth) := by
  cases depth with
  | zero => exact marked_map _ (ProtocolTrace.unfold_prefix ops allocate safety owner meaning base growth usizeBits 0)
  | succ depth => exact marked_map _ (step_prefix ops allocate safety owner meaning base growth usizeBits _ _)

def children (depth : Nat) : Constructors (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
  ChildTrace.constructors
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth))

theorem children_recorded (depth : Nat) :
    children ops allocate safety owner meaning base growth usizeBits depth =
      mapConstructors (fun captured => ChildTrace.record (eraseCapture [] captured)
        (fun before => (captured before []).2.events)) (unfold ops allocate safety owner meaning base growth usizeBits depth) := by
  unfold children
  rw [← unfold_erases ops allocate safety owner meaning base growth usizeBits depth []]
  rfl

theorem children_erases (depth : Nat) :
    (Recursive.erasing (Publication.Effects.mapAllocator Prod.fst)).Constructors
      (children ops allocate safety owner meaning base growth usizeBits depth)
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth) :=
  ChildTrace.constructors_erase _ _

/-- Admission selects the exact entry slot at this child's starting cursor.
An equal protocol decision list without native entry slots cannot supply it. -/
theorem admitted_entry (action : Capture (Publication.Effects σ) NodeId) (marked : Begins action)
    (stream : List ProtocolEvent) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (admitted : Resource.Admitted ChildTrace.history stream
      (ChildTrace.record (eraseCapture [] action) (fun world => (action world []).2.events)) before) :
    stream[(ChildTrace.history before).length]? = some (entry before) := by
  obtain ⟨trailing, recorded⟩ := marked (ChildTrace.erase before) []
  simp only [List.nil_append] at recorded
  change ChildTrace.history before ++ (action (ChildTrace.erase before) []).2.events <+: stream at admitted
  rw [recorded] at admitted
  obtain ⟨tail, rfl⟩ := admitted
  simp only [List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.cons_append,
    List.getElem?_cons_zero]
  rfl

/-- The same stream position derives equality of both native allocation
cursors. Neither returned values nor final graphs are assumptions. -/
theorem admitted_identity (left right : Capture (Publication.Effects σ) NodeId)
    (leftMarked : Begins left) (rightMarked : Begins right)
    (stream : List ProtocolEvent) (before other : ChildTrace.TracedWorld σ ProtocolEvent)
    (position : (ChildTrace.history before).length = (ChildTrace.history other).length)
    (leftAdmitted : Resource.Admitted ChildTrace.history stream
      (ChildTrace.record (eraseCapture [] left) (fun world => (left world []).2.events)) before)
    (rightAdmitted : Resource.Admitted ChildTrace.history stream
      (ChildTrace.record (eraseCapture [] right) (fun world => (right world []).2.events)) other) :
    before.memory.memory.nextId = other.memory.memory.nextId ∧
      before.memory.memory.nextAddress = other.memory.memory.nextAddress := by
  have first := admitted_entry left leftMarked stream before leftAdmitted
  have second := admitted_entry right rightMarked stream other rightAdmitted
  rw [position, second] at first
  have same := Interner.InvocationTrace.Event.nativeEntry.inj (Option.some.inj first)
  exact ⟨same.1.symm, same.2.symm⟩

/-- The constructor replay consumes the entry slot explicitly. Other protocol
consumers reject it as foreign, so no allocation decision can skip this step. -/
def enter (stream : List ProtocolEvent) : Interner.Action (Nat × Nat) := fun before =>
  match stream[before.allocationCursor]? with
  | some (.nativeEntry id address) => (.ok (id, address), { before with allocationCursor := before.allocationCursor + 1 })
  | _ => (.error .safetyFault, { before with allocationCursor := stream.length + 1 })

theorem enter_admitted (action : Capture (Publication.Effects σ) NodeId) (marked : Begins action)
    (stream : List ProtocolEvent) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (admitted : Resource.Admitted ChildTrace.history stream
      (ChildTrace.record (eraseCapture [] action) (fun world => (action world []).2.events)) before) :
    enter stream (cursorGraph (fun world => (ChildTrace.history world).length) before) =
      (.ok (before.memory.memory.nextId, before.memory.memory.nextAddress),
        { before.graph with allocationCursor := (ChildTrace.history before).length + 1 }) := by
  simp only [enter, cursorGraph, admitted_entry action marked stream before admitted, entry]

/-- Equal starting observations on the admitted stream derive matching actual
native allocations, including refusal. The shared memory theorem supplies the
connection; graph equality after execution and allocation success are not inputs. -/
theorem admitted_allocate (left right : Capture (Publication.Effects σ) NodeId)
    (leftMarked : Begins left) (rightMarked : Begins right)
    (stream : List ProtocolEvent) (before other : ChildTrace.TracedWorld σ ProtocolEvent)
    (observed : cursorGraph (fun world => (ChildTrace.history world).length) before =
      cursorGraph (fun world => (ChildTrace.history world).length) other)
    (leftAdmitted : Resource.Admitted ChildTrace.history stream
      (ChildTrace.record (eraseCapture [] left) (fun world => (left world []).2.events)) before)
    (rightAdmitted : Resource.Admitted ChildTrace.history stream
      (ChildTrace.record (eraseCapture [] right) (fun world => (right world []).2.events)) other)
    (valid : before.memory.memory.valid = true) (otherValid : other.memory.memory.valid = true)
    (child : Compiler.ZigAir.Memory.Ty) :
    (Compiler.ZigAir.Memory.allocate before.memory.memory child).map
      (fun result => (result.1, result.2.nextId, result.2.nextAddress)) =
    (Compiler.ZigAir.Memory.allocate other.memory.memory child).map
      (fun result => (result.1, result.2.nextId, result.2.nextAddress)) := by
  have position := congrArg Interner.Heap.allocationCursor observed
  obtain ⟨identity, address⟩ := admitted_identity left right leftMarked rightMarked stream before other position leftAdmitted rightAdmitted
  exact Compiler.ZigAir.Memory.allocate_same_cursors _ _ child valid otherValid identity address

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
