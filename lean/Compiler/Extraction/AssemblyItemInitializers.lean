/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemQuery
import Compiler.Extraction.ConstructorProgram

namespace Compiler.Extraction.AssemblyItem.Initializers
open Compiler.ZigAir.Memory Compiler.Algebraic Contract.Yul
open Compiler.Extraction.Cache Compiler.Extraction.Interner
open Fields

def debugMember : Member → Bool
  | .nativeStart | .nativeEnd | .nativeSource | .originStart | .originEnd | .originSource | .astId => true
  | _ => false

/-- The caller's evaluated DebugData, with every field represented in the
existing record vocabulary. Borrowed source-name descriptors keep their exact
identity and offset; this check does not assert pointee liveness. -/
def DebugTyped (values : Values) : Prop := (debugValue values).hasType debugDataType = true

theorem debug_typed (values : Values) : DebugTyped values ↔
    ∀ selected, debugMember selected = true → (values selected).hasType selected.type = true := by
  have debugGeometry := debug_record_valid
  have locationGeometry := location_record_valid
  dsimp only [debugDataType, sourceLocationType] at debugGeometry locationGeometry
  simp [DebugTyped, debugValue, locationValue, debugDataType, sourceLocationType,
    ObjectValue.hasType, objectFieldsTyped, Field.type, debugGeometry, locationGeometry,
    debug_data_native_locationOffset, debug_data_origin_locationOffset, debug_data_ast_idOffset,
    source_location_source_nameOffset, source_location_startOffset, source_location_endOffset]
  constructor
  · intro all selected isDebug
    have complete : ∀ field, debugMember field = true → (values field).type = field.type ∧ (values field).valid = true := by
      rcases all with ⟨⟨nativeSource, nativeStart, nativeEnd⟩, ⟨originSource, originStart, originEnd⟩, astId⟩
      intro field selected
      cases field <;> first | contradiction | assumption
    simpa only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] using complete selected isDebug
  · intro all
    have complete (field : Member) (selected : debugMember field = true) :
        (values field).type = field.type ∧ (values field).valid = true := by
      simpa only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] using all field selected
    exact ⟨⟨complete .nativeSource rfl, complete .nativeStart rfl, complete .nativeEnd rfl⟩,
      ⟨complete .originSource rfl, complete .originStart rfl, complete .originEnd rfl⟩, complete .astId rfl⟩

/-- Complete struct-literal defaults and the forwarded debug argument for the
admitted initPush/initInstruction constructor paths. The existing constructor
extraction checks those bodies, initPush's initType delegation, and every
AssemblyItem declaration/default through the full member scanner. -/
def construct (item : Item) (debug : Values) : Values
  | .kind => .scalar (.int true 32 item.kind.toNat)
  | .instruction => OptionalScalar.byteValue item.instruction
  | .data => .scalar (.int false 256 item.data.toNat)
  | .verbatim => .optionalObject verbatimType ⟨40, 8⟩ none
  | .pushed => OptionalScalar.unsignedValue 256 none
  | .immutable => OptionalScalar.unsignedValue 64 none
  | .modifier => .scalar (.int false 64 0)
  | .jump => .scalar (.int true 32 0)
  | selected => debug selected

theorem debug_forwarded (item : Item) (debug : Values) : debugValue (construct item debug) = debugValue debug := rfl

theorem construct_typed (item : Item) (debug : Values) (domain : (item.kind.toNat : Int) ∈ itemTagValues)
    (debugTyped : DebugTyped debug) : (construct item debug).Typed := by
  have debugFields := (debug_typed debug).mp debugTyped
  intro selected
  cases selected with
  | kind =>
    have bound : -(2^31) ≤ (item.kind.toNat : Int) ∧ (item.kind.toNat : Int) < 2^31 := by
      simp [itemTagValues] at domain
      omega
    simpa only [construct, Member.type, Value.hasType, Value.type, Compiler.ZigAir.Scalar.Value.type, decide_true, Bool.true_and,
      Value.valid, Compiler.ZigAir.Scalar.Value.valid, Compiler.ZigAir.Scalar.Ty.contains, Compiler.ZigAir.Scalar.Ty.lower, Compiler.ZigAir.Scalar.Ty.upper, decide_eq_true_eq] using bound
  | instruction => exact OptionalScalar.byteValue_typed item.instruction
  | data =>
    have bound := item.data.isLt
    simp only [construct, Member.type, Value.hasType, Value.type, Compiler.ZigAir.Scalar.Value.type, decide_true, Bool.true_and,
      Value.valid, Compiler.ZigAir.Scalar.Value.valid, Compiler.ZigAir.Scalar.Ty.contains, Compiler.ZigAir.Scalar.Ty.lower, Compiler.ZigAir.Scalar.Ty.upper, decide_eq_true_eq]
    change 0 ≤ (item.data.toNat : Int) ∧ (item.data.toNat : Int) < ((2^256 : Nat) : Int)
    constructor <;> omega
  | pushed => exact OptionalScalar.unsignedValue_typed _ _
  | immutable => exact OptionalScalar.unsignedValue_typed _ _
  | verbatim | modifier | jump => rfl
  | nativeStart => exact debugFields _ rfl
  | nativeEnd => exact debugFields _ rfl
  | nativeSource => exact debugFields _ rfl
  | originStart => exact debugFields _ rfl
  | originEnd => exact debugFields _ rfl
  | originSource => exact debugFields _ rfl
  | astId => exact debugFields _ rfl

theorem construct_complete (item : Item) (debug : Values) (domain : (item.kind.toNat : Int) ∈ itemTagValues)
    (debugTyped : DebugTyped debug) : (objectValue (construct item debug)).hasType viewType = true :=
  (objectValue_typed _).mpr (construct_typed item debug domain debugTyped)

/-- Derive the query's initial item relation from the complete actual write.
Every constructor field is initialized, even though the query only observes
kind and the conditional instruction. No final reader or graph invariant is a
premise, and assignment frames all other allocations and lifetime counters. -/
theorem assign_query (state : State) (logical : Storage.Cell) (cell : Allocation) (debug : Values)
    (domain : (logical.item.kind.toNat : Int) ∈ itemTagValues) (debugTyped : DebugTyped debug)
    (valid : state.valid = true) (found : state.heap.lookup logical.itemAddress = some cell)
    (typed : cell.type = viewType) (writable : cell.writable = true) :
    ∃ after, assign (construct logical.item debug) logical.itemAddress state = .ok after ∧
      Written (construct logical.item debug) logical.itemAddress members state after ∧
      (∀ selected, member after ⟨logical.itemAddress, 0⟩ selected = .ok (construct logical.item debug selected)) ∧
      RepresentativeArray.Operation.Item after logical := by
  obtain ⟨after, assigned, post, reads⟩ := assign_total (construct logical.item debug) logical.itemAddress state cell
    (construct_typed logical.item debug domain debugTyped) valid found typed writable
  obtain ⟨finalCell, finalFound, shape⟩ := post.shape logical.itemAddress cell found
  have finalTyped := shape.2.1.trans typed
  exact ⟨after, assigned, post, reads, Query.of_members after logical finalCell post.valid finalFound finalTyped domain
    (reads .kind) (reads .instruction)⟩

def constant (value : Word) (debug : Values) : Values := construct (constructorCode.constantRequest value).item debug
def operation (opcode : Opcode) (debug : Values) : Values := construct (constructorCode.operationRequest opcode []).item debug

theorem constant_typed (value : Word) (debug : Values) (typed : DebugTyped debug) : (constant value debug).Typed :=
  construct_typed _ debug (by change (2 : Int) ∈ itemTagValues; decide) typed

theorem operation_typed (opcode : Opcode) (debug : Values) (typed : DebugTyped debug) : (operation opcode debug).Typed :=
  construct_typed _ debug (by change (1 : Int) ∈ itemTagValues; decide) typed

theorem constant_arguments (value : Word) (debug : Values) :
    constant value debug .kind = .scalar (.int true 32 2) ∧
    constant value debug .instruction = OptionalScalar.byteValue none ∧
    constant value debug .data = .scalar (.int false 256 value.toNat) ∧
    debugValue (constant value debug) = debugValue debug := ⟨rfl, rfl, rfl, rfl⟩

theorem operation_arguments (opcode : Opcode) (debug : Values) :
    operation opcode debug .kind = .scalar (.int true 32 1) ∧
    operation opcode debug .instruction = OptionalScalar.byteValue (some opcode) ∧
    operation opcode debug .data = .scalar (.int false 256 0) ∧
    debugValue (operation opcode debug) = debugValue debug := ⟨rfl, rfl, rfl, rfl⟩

/-- An admitted allocator response supplies the complete writable item. The
same execution then initializes every field, preserves session ownership and
argument representations, and establishes the query relation. Constructor
callers instantiate `logical.item` with the source-bound request item. -/
theorem create_initialize (request : Creation.Allocate σ) (allocator base : Nat) (logical : Storage.Cell)
    (debug : Values) (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ) (effects : σ)
    (initial : Compiler.Extraction.Memory.Arguments.Normalization.Valid before)
    (response : request Creation.layout before = (some base, effects))
    (fits : RegionAllocation.Fits before.memory Creation.layout base)
    (domain : (logical.item.kind.toNat : Int) ∈ itemTagValues) (debugTyped : DebugTyped debug) :
    ∃ allocated after,
      Creation.create request allocator logical.item before = (.ok before.memory.nextId, allocated) ∧
      assign (construct logical.item debug) before.memory.nextId allocated.memory = .ok after ∧
      Written (construct logical.item debug) before.memory.nextId members allocated.memory after ∧
      Compiler.Extraction.Memory.Arguments.Normalization.Valid { allocated with memory := after } ∧
      Owned allocator before.memory.nextId { allocated with memory := after } ∧
      (∀ selected, member after ⟨before.memory.nextId, 0⟩ selected = .ok (construct logical.item debug selected)) ∧
      RepresentativeArray.Operation.Item after { logical with itemAddress := before.memory.nextId } := by
  have made := Creation.create_from_response request allocator base logical.item before effects initial response fits
  let allocated := (Creation.create request allocator logical.item before).2
  have created : Creation.create request allocator logical.item before = (.ok before.memory.nextId, allocated) := by
    simp only [allocated, made.1]
  have post : Creation.Created allocator before.memory.nextId before allocated := by
    simpa only [allocated, made.1] using made.2
  obtain ⟨cell, found, typed, writable, _⟩ := post.owned.2
  obtain ⟨after, assigned, written, reads, queried⟩ := assign_query allocated.memory
    { logical with itemAddress := before.memory.nextId } cell debug domain debugTyped post.valid.memory found typed writable
  have preserved := written.session _ allocator _ _ allocated after post.valid post.owned
  exact ⟨allocated, after, created, assigned, written, preserved.1, preserved.2, reads, queried⟩

end Compiler.Extraction.AssemblyItem.Initializers
