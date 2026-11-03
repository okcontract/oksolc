/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolScope
import Compiler.Extraction.InternerViewInput

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray
open Caller.ProtocolTrace

/-- Constructor-local metadata accompanies the original native world. It remains
available after wrapper return; projecting events alone is not an admission. -/
abbrev Capture (σ α : Type) := World σ → List ProtocolEvent → Except Fault α × Recorded σ

def start (before : World σ) (leading : List ProtocolEvent) : Recorded σ :=
  ⟨⟨before, { lookup := none }⟩, {}, leading⟩

/-- Use the existing ordinary-return unwinder. Neither stack retirement nor a
semantic rejection changes the captured protocol token or history. -/
def retire (mark : Nat) (ran : Except Fault NodeId × Recorded σ) : Except Fault NodeId × Recorded σ :=
  let returned := TemporaryArguments.unwind mark (ran.1, ran.2.native)
  (returned.1, { ran.2 with native := { ran.2.native with world := returned.2 } })

theorem retire_native (mark : Nat) (ran : Except Fault NodeId × Recorded σ) :
    ((retire mark ran).1, (retire mark ran).2.native) =
      (if ordinary ran.1 then
        (ran.1, { ran.2.native with world := { ran.2.native.world with memory := { ran.2.native.world.memory with
          memory := Compiler.ZigAir.Memory.cleanup mark ran.2.native.world.memory.memory } } })
      else (ran.1, ran.2.native)) := by
  unfold retire TemporaryArguments.unwind
  split <;> rfl

theorem retire_prefix (mark : Nat) (ran : Except Fault NodeId × Recorded σ) (leading : List ProtocolEvent) :
    retire mark (ran.1, prepend leading ran.2) = ((retire mark ran).1, prepend leading (retire mark ran).2) := rfl

theorem retire_metadata (mark : Nat) (ran : Except Fault NodeId × Recorded σ) :
    (retire mark ran).2.tokens = ran.2.tokens ∧ (retire mark ran).2.events = ran.2.events := ⟨rfl, rfl⟩

/-- Stack/item retirement preserves the complete scoped observation, including
ordinary OOM and semantic rejection. Only native scratch memory is retired. -/
theorem retire_scope (mark : Nat) (ran : Except Fault NodeId × Recorded σ) :
    scopeView (retire mark ran).2 = scopeView ran.2 := by
  unfold scopeView retire TemporaryArguments.unwind
  split <;> rfl

variable (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (ports : Caller.ProtocolTrace.GraphObservations σ) (source : View) (request : Interner.Request)

/-- Capacity precedes scratch allocation, exactly as in ConstructorFrame.find.
Preparation failure contributes no caller events. The same initialized scratch
view enters the existing source caller recorder. -/
def frame : Capture σ NodeId := fun before leading =>
  if q.atCapacity before.graph then (.error (.language .capacity), start before leading) else
  let mark := before.memory.memory.nextId
  match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | .error fault => (.error (.memory (.preparation (.memory fault))), start before leading)
  | .ok (_, memory) => retire mark
      (Caller.ProtocolTrace.find external budget allocator p q ports source ⟨mark, 0, 2⟩ request
        (start { before with memory := { before.memory with memory } } leading))

theorem frame_erases (before : World σ) (leading : List ProtocolEvent) :
    let captured := frame external budget allocator p q ports source request before leading
    ConstructorFrame.find external budget allocator p q source request before = (captured.1, captured.2.native) := by
  unfold frame ConstructorFrame.find
  split
  · rfl
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => rfl
    | ok pair =>
      rcases pair with ⟨pointer, memory⟩
      dsimp only
      rw [Caller.ProtocolTrace.find_erases external budget allocator p q ports source _ request _ leading]
      exact (retire_native _ _).symm

theorem frame_prefix (before : World σ) (earlier leading : List ProtocolEvent) :
    frame external budget allocator p q ports source request before (earlier ++ leading) =
      (let captured := frame external budget allocator p q ports source request before leading
       (captured.1, prepend earlier captured.2)) := by
  unfold frame
  split
  · rfl
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => rfl
    | ok pair =>
      rcases pair with ⟨pointer, memory⟩
      dsimp only
      simp only [start]
      rw [(Caller.ProtocolTrace.find_segment external budget allocator p q ports source _ request _ (earlier ++ leading)).2,
        (Caller.ProtocolTrace.find_segment external budget allocator p q ports source _ request _ leading).2]
      simp only [retire, TemporaryArguments.unwind, prepend, List.append_assoc]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace

variable (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)

/-- Execute the existing item initializer before choosing the caller's item
address and fields. All rejected initializer states are retained verbatim. -/
def item (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values) : Capture σ NodeId := fun before leading =>
  match ConstructorItem.prepare request.item debug before with
  | (.error fault, reached) => (.error fault, start reached leading)
  | (.ok address, prepared) => retire before.memory.memory.nextId
      (frame context.external context.budget context.allocator (context.primitives source address (input request.item debug))
        context.queries (ports source address (input request.item debug)) source request prepared leading)

theorem item_erases (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (leading : List ProtocolEvent) :
    let captured := item context ports source request debug before leading
    ConstructorItem.invoke context.external context.budget context.allocator (context.primitives source)
      context.queries source request debug before = (captured.1, captured.2.native) := by
  unfold item ConstructorItem.invoke
  cases prepared : ConstructorItem.prepare request.item debug before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok address =>
      dsimp only
      rw [frame_erases context.external context.budget context.allocator _ context.queries (ports source address _) source request reached leading]
      exact (retire_native _ _).symm

theorem item_prefix (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (earlier leading : List ProtocolEvent) :
    item context ports source request debug before (earlier ++ leading) =
      (let captured := item context ports source request debug before leading
       (captured.1, prepend earlier captured.2)) := by
  unfold item
  cases prepared : ConstructorItem.prepare request.item debug before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok address => dsimp only; rw [frame_prefix]; exact retire_prefix _ _ _

/-- The native literal preparation supplies the actual view and reached world.
Only nonempty literals have an outer argument frame. -/
def literal (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values) : Capture σ NodeId := fun before leading =>
  match Arguments.prepare values before with
  | (.error fault, reached) => (.error fault, start reached leading)
  | (.ok source, prepared) =>
    let called := item context ports source (Interner.constructorCode.operationRequest opcode values) debug prepared leading
    if values.isEmpty then called else retire before.memory.memory.nextId called

theorem literal_erases (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (leading : List ProtocolEvent) :
    let captured := literal context ports opcode values debug before leading
    Arguments.operation context.external context.budget context.allocator context.primitives context.queries opcode values debug before =
      (captured.1, captured.2.native.world) := by
  unfold literal Arguments.operation
  cases prepared : Arguments.prepare values before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok source =>
      dsimp only
      unfold ConstructorItem.operation
      rw [item_erases context ports]
      unfold Arguments.returned
      split <;> rfl

theorem literal_prefix (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (earlier leading : List ProtocolEvent) :
    literal context ports opcode values debug before (earlier ++ leading) =
      (let captured := literal context ports opcode values debug before leading
       (captured.1, prepend earlier captured.2)) := by
  unfold literal
  cases prepared : Arguments.prepare values before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok source => dsimp only; rw [item_prefix]; split <;> rfl

/-- A named local uses the source copy/overwrite executor; the logical values
cannot replace its native reads or hide partial preparation failure. -/
def namedLocal (opcode : Opcode) (source : View) (left right repeated : NodeId) (selected : Nat) (first : Bool)
    (debug : AssemblyItem.Fields.Values) : Capture σ NodeId := fun before leading =>
  match LocalArguments.zigLocal source selected repeated first before with
  | (.error fault, reached) => (.error fault, start reached leading)
  | (.ok target, prepared) => retire before.memory.memory.nextId
      (item context ports target (Interner.constructorCode.operationRequest opcode
        (if first then [left, right].set selected repeated else [left, right])) debug prepared leading)

theorem local_erases (opcode : Opcode) (source : View) (left right repeated : NodeId) (selected : Nat) (first : Bool)
    (debug : AssemblyItem.Fields.Values) (before : World σ) (leading : List ProtocolEvent) :
    let captured := namedLocal context ports opcode source left right repeated selected first debug before leading
    ViewInput.localOperation context opcode source left right repeated selected first debug before =
      (captured.1, captured.2.native.world) := by
  unfold namedLocal ViewInput.localOperation
  cases prepared : LocalArguments.zigLocal source selected repeated first before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok target => dsimp only; unfold ConstructorItem.operation; rw [item_erases context ports]; rfl

theorem local_prefix (opcode : Opcode) (source : View) (left right repeated : NodeId) (selected : Nat) (first : Bool)
    (debug : AssemblyItem.Fields.Values) (before : World σ) (earlier leading : List ProtocolEvent) :
    namedLocal context ports opcode source left right repeated selected first debug before (earlier ++ leading) =
      (let captured := namedLocal context ports opcode source left right repeated selected first debug before leading
       (captured.1, prepend earlier captured.2)) := by
  unfold namedLocal
  cases prepared : LocalArguments.zigLocal source selected repeated first before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok target => dsimp only; rw [item_prefix]; exact retire_prefix _ _ _

/-- The five original entry routes share the parameterized item and scratch
proofs. Borrowed operands keep their source allocation; materialization follows
the source's constant route, which does not inspect the old expression ID. -/
def constructors : Associative.Constructors AssemblyItem.Fields.Values (Capture σ) where
  operation := literal context ports
  constant := fun value debug => item context ports ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug
  materialize := fun _ value debug => item context ports ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug
  borrowedOperation := fun address opcode values debug =>
    item context ports ⟨address, 0, values.length⟩ (Interner.constructorCode.operationRequest opcode values) debug
  localOperation := fun opcode source selected repeated first debug =>
    match source.items with
    | [left, right] => namedLocal context ports opcode (view source) left right repeated selected first debug
    | _ => fun before leading => (.error .outsideOwnedContinuation, start before leading)

/-- A single five-field map keeps erasure and observation on the same entries. -/
def mapConstructors {m n : Type → Type} (f : m NodeId → n NodeId) (children : Associative.Constructors Debug m) :
    Associative.Constructors Debug n where
  operation := fun opcode values debug => f (children.operation opcode values debug)
  constant := fun value debug => f (children.constant value debug)
  materialize := fun id value debug => f (children.materialize id value debug)
  borrowedOperation := fun address opcode values debug => f (children.borrowedOperation address opcode values debug)
  localOperation := fun opcode source selected repeated first debug => f (children.localOperation opcode source selected repeated first debug)

def eraseCapture (leading : List ProtocolEvent) (action : Capture σ NodeId) : GraphAction σ NodeId := fun before =>
  let captured := action before leading
  (captured.1, captured.2.native.world)

def prefixCapture (earlier leading : List ProtocolEvent) (action : Capture σ NodeId) (before : World σ) :=
  let captured := action before leading
  (captured.1, prepend earlier captured.2)

attribute [local irreducible] item literal namedLocal ConstructorItem.invoke Arguments.operation ViewInput.localOperation

theorem constructors_erases (leading : List ProtocolEvent) :
    mapConstructors (eraseCapture leading) (constructors context ports) = ViewInput.constructors context := by
  unfold mapConstructors constructors ViewInput.constructors PairInput.constructors ShiftInput.constructors
  congr 1
  · funext opcode values debug before
    exact (literal_erases context ports opcode values debug before leading).symm
  · funext value debug before
    exact (congrArg (fun ran => (ran.1, ran.2.world)) (item_erases context ports ⟨0, 0, 0⟩ _ debug before leading)).symm
  · funext id value debug before
    exact (congrArg (fun ran => (ran.1, ran.2.world)) (item_erases context ports ⟨0, 0, 0⟩ _ debug before leading)).symm
  · funext address opcode values debug before
    exact (congrArg (fun ran => (ran.1, ran.2.world)) (item_erases context ports ⟨address, 0, values.length⟩ _ debug before leading)).symm
  · funext opcode source selected repeated first debug before
    dsimp only [eraseCapture, prefixCapture]
    cases items : source.items with
    | nil => rfl
    | cons left rest => cases rest with
      | nil => rfl
      | cons right tail => cases tail with
        | nil => exact (local_erases context ports opcode (view source) left right repeated selected first debug before leading).symm
        | cons _ _ => rfl

theorem constructors_prefix (earlier leading : List ProtocolEvent) :
    mapConstructors (m := Capture σ) (n := fun _ => World σ → Except Fault NodeId × Recorded σ) (fun action before => action before (earlier ++ leading)) (constructors context ports) =
      mapConstructors (prefixCapture earlier leading) (constructors context ports) := by
  unfold mapConstructors constructors
  congr 1
  · funext opcode values debug before; exact literal_prefix context ports opcode values debug before earlier leading
  · funext value debug before; exact item_prefix context ports _ _ debug before earlier leading
  · funext id value debug before; exact item_prefix context ports _ _ debug before earlier leading
  · funext address opcode values debug before; exact item_prefix context ports _ _ debug before earlier leading
  · funext opcode source selected repeated first debug before
    dsimp only [eraseCapture, prefixCapture]
    cases items : source.items with
    | nil => rfl
    | cons left rest => cases rest with
      | nil => rfl
      | cons right tail => cases tail with
        | nil => exact local_prefix context ports opcode (view source) left right repeated selected first debug before earlier leading
        | cons _ _ => rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
