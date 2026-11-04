/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashKey
import Compiler.Extraction.ExpressionMapHashSlice
import Compiler.ZigAir.GeneratedExpressionHashBytes

namespace Compiler.Extraction.ExpressionMap.HashBytes
open Compiler.ZigAir Compiler.ZigAir.Memory Compiler.ZigAir.AggregateAir
open Compiler.Extraction.Cache (Key)
open Buckets

/-- The four scalar views share one execution proof. Argument storage is
observed through the complete captured slice helper. -/
inductive Field where
  | kind | instruction | data | sequence
  deriving DecidableEq, Repr

def Field.slot : Field → KeyFields.Slot
  | .kind => .kind | .instruction => .instruction | .data => .data | .sequence => .sequence

def Field.bits : Field → Nat
  | .kind | .sequence => 32 | .instruction => 8 | .data => 256

def Field.value (key : Key) : (field : Field) → BitVec field.bits
  | .kind => key.kind | .instruction => key.instruction | .data => key.data | .sequence => key.sequence

def Field.registers : Field → Nat × Nat × Nat
  | .kind => (8, 13, 14) | .instruction => (16, 21, 22)
  | .data => (24, 29, 30) | .sequence => (41, 46, 47)

def Field.program : Field → Program
  | .kind => GeneratedExpressionHashBytes.kind
  | .instruction => GeneratedExpressionHashBytes.instruction
  | .data => GeneratedExpressionHashBytes.data
  | .sequence => GeneratedExpressionHashBytes.sequence

def Field.fragment : Field → AggregateCall.Code → AggregateCall.Code
  | .kind => GeneratedExpressionHashBytes.kindView
  | .instruction => GeneratedExpressionHashBytes.instructionView
  | .data => GeneratedExpressionHashBytes.dataView
  | .sequence => GeneratedExpressionHashBytes.sequenceView

theorem Field.program_eq (field : Field) : field.program =
    ScalarBytesAir.castProgram (.scalar (.int false field.bits))
      (KeyFields.layout field.slot).alignment (KeyFields.layout field.slot).bytes := by
  cases field <;> rfl

theorem Field.fragment_eq (field : Field) (next : AggregateCall.Code) : field.fragment next =
    .bind field.registers.1 (.pointer false false (.scalar (.int false field.bits)))
      (.primitive (.fieldPointer (.local 3) (KeyFields.offset field.slot)))
      (ScalarBytesAir.viewCode field.program (.local field.registers.1) field.registers.2.1 field.registers.2.2
        (KeyFields.layout field.slot).bytes next) := by
  cases field <;> rfl

theorem Field.value_eq (field : Field) (key : Key) (arguments : Address) :
    KeyFields.value key arguments field.slot = .scalar (.int false field.bits (field.value key).toNat) := by
  cases field <;> rfl

def Field.address (field : Field) (id : Nat) : Address := ⟨id, KeyFields.offset field.slot⟩
def Field.slice (field : Field) (id : Nat) : Value :=
  .slice (.slice false ScalarBytesAir.byte) (field.address id) (KeyFields.layout field.slot).bytes

def view (state : State) (id : Nat) (field : Field) : Except Fault Value :=
  match (field.fragment (.ret (.local field.registers.2.2))).eval AggregateCall.semantics []
      (Control.Env.set (fun _ => none) 3 (.value (.pointer (.pointer false false keyType) ⟨id, 0⟩))) state with
  | .returned (.value value) _ => .ok value
  | .fault fault _ => .error fault
  | _ => .error .malformed

theorem view_verified (state : State) (id : Nat) (key : Key) (arguments : Address)
    (field : Field) (valid : state.valid = true) (binding : HashKey.Binding state id key arguments) :
    view state id field = .ok (field.slice id) := by
  obtain ⟨cell, accessed, typed, _⟩ := binding.access valid field.slot
  have selected := binding.select valid field.slot
  rw [field.value_eq] at selected
  let env : Env := Control.Env.set (fun _ => none) 3 (.value (.pointer (.pointer false false keyType) ⟨id, 0⟩))
  let pointer := Value.pointer (.pointer false false (.scalar (.int false field.bits))) (field.address id)
  have fieldRun : (AggregateCall.Prim.primitive (.fieldPointer (.local 3) (KeyFields.offset field.slot))).eval [] env state =
      (.ok (.value pointer), state) := by
    exact eval_field _ _ _ _ _ _ _ (value_local _ _ _ (by simp [env, Control.Env.set]) rfl) selected
  have pointerTyped : (Register.value pointer).hasType (.pointer false false (.scalar (.int false field.bits))) = true := by
    simp [pointer, Register.hasType, Register.type, Register.valid, Value.type, Value.valid]
  have geometry := KeyFields.field_geometry key arguments field.slot
  rw [field.value_eq] at geometry
  have called := ScalarBytesAir.view_verified state (field.address id) cell false field.bits
    (KeyFields.layout field.slot).alignment (KeyFields.layout field.slot).bytes field.registers.2.1 field.registers.2.2
    (KeyFields.layout field.slot) (.local field.registers.1) [] (env.set field.registers.1 (.value pointer))
    (.ret (.local field.registers.2.2)) valid (by cases field <;> decide)
    (ref_local _ _ _ (by simp [Control.Env.set, pointer]) rfl) geometry.1 (by cases field <;> decide) (by cases field <;> decide)
    (by cases field <;> rfl) rfl (by cases field <;> decide) accessed
    (by rw [typed]; cases field <;> rfl)
  unfold view
  rw [field.fragment_eq, AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ fieldRun pointerTyped, field.program_eq, called]
  simp [Control.Code.eval, AggregateCall.semantics, Ref.eval, Control.Env.set, ScalarBytesAir.slice,
    Register.valid, Value.valid, Field.slice, bind, Except.bind,
    show (KeyFields.layout field.slot).bytes < addressLimit from by cases field <;> decide]


set_option maxHeartbeats 1000000 in
theorem Field.locate (field : Field) (index : Nat) (inside : index < (KeyFields.layout field.slot).bytes) :
    ScalarBytes.locate keyType (KeyFields.offset field.slot + index) =
      some (KeyFields.offset field.slot, false, field.bits) := by
  have scalar : ScalarBytes.locateField (.scalar (.int false field.bits)) index = some (0, false, field.bits) :=
    ScalarBytes.locateField_integer false field.bits index (KeyFields.layout field.slot)
      (by cases field <;> rfl) (by cases field <;> decide) (by cases field <;> decide)
      (by cases field <;> rfl) inside
  cases field <;> simp only [Field.slot, Field.bits, KeyFields.layout, KeyFields.offset] at *
  all_goals simp only [keyType, ScalarBytes.locate, show Ty.aggregateValid ⟨64, 16⟩
      [(0, .scalar (.int false 256)), (32, .slice false (.int false 32)),
       (48, .scalar (.int false 32)), (52, .scalar (.int false 32)), (56, .scalar (.int false 8))] = true from rfl,
    ↓reduceIte, ScalarBytes.locateFields, Compiler.ZigAir.Memory.Field.contains, Compiler.ZigAir.Memory.Field.layout, Compiler.ZigAir.Memory.Field.type]
  all_goals simp (disch := omega) [Nat.add_sub_cancel_left, bind, Option.bind, scalar, if_pos, if_neg]
  all_goals try omega
  have zero : index = 0 := by omega
  rw [zero] at scalar
  rw [scalar]
  rfl

def read (state : State) (id : Nat) (field : Field) : Except Fault (List (BitVec 8)) := do
  let bytes ← view state id field
  ScalarBytes.bytes state bytes

def Field.image (field : Field) (key : Key) : List (BitVec 8) :=
  (List.range (KeyFields.layout field.slot).bytes).map
    (fun i => BitVec.ofNat 8 ((field.value key).toNat / 256 ^ i))

theorem read_verified (state : State) (id : Nat) (key : Key) (arguments : Address)
    (field : Field) (valid : state.valid = true) (binding : HashKey.Binding state id key arguments)
    (bounded : key.arguments.length < addressLimit) :
    read state id field = .ok (field.image key) := by
  obtain ⟨cell, accessed, typed, _⟩ := binding.access valid field.slot
  have loaded := binding.load valid bounded field.slot
  rw [field.value_eq] at loaded
  have each (index : Nat) (inside : index ∈ List.range (KeyFields.layout field.slot).bytes) :
      ScalarBytes.read state (field.slice id) index = .ok (BitVec.ofNat 8 ((field.value key).toNat / 256 ^ index)) := by
    have small := List.mem_range.mp inside
    have observed := ScalarBytes.readAt_of_load state (field.address id) cell false field.bits index
      (field.value key).toNat (KeyFields.layout field.slot) accessed small (by rw [typed]; exact field.locate index small) loaded
    simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq] at observed
    simpa only [ScalarBytes.read, Field.slice, ScalarBytesAir.byte, if_neg (by omega : ¬index ≥ (KeyFields.layout field.slot).bytes)] using observed
  simp only [read, view_verified state id key arguments field valid binding, bind, Except.bind,
    ScalarBytes.bytes, Field.slice, ScalarBytesAir.byte]
  change (List.range (KeyFields.layout field.slot).bytes).mapM _ = (Except.ok (field.image key) : Except Fault _)
  unfold Field.image
  generalize List.range (KeyFields.layout field.slot).bytes = indices at each ⊢
  change indices.mapM (ScalarBytes.read state (field.slice id)) = (Except.ok (indices.map (fun i => BitVec.ofNat 8 ((field.value key).toNat / 256 ^ i))) : Except Fault _)
  induction indices with
  | nil => rfl
  | cons head tail ih =>
    have first := each head (by simp)
    have rest := ih (fun i member => each i (by simp [member]))
    simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure, List.map_cons]


/-- Both scalar and argument inputs now execute their captured native views.
The argument helper retires its locals while retaining allocation history. -/
abbrev argumentBytes := HashSlice.bytes

def inputs (state : State) (id : Nat) : Except Fault (List (List (BitVec 8))) × State :=
  let scalars : Except Fault (List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) := do
    let kind ← read state id .kind
    let instruction ← read state id .instruction
    let data ← read state id .data
    .ok (kind, instruction, data)
  match scalars with
  | .error fault => (.error fault, state)
  | .ok (kind, instruction, data) =>
    let (arguments, after) := argumentBytes state id
    ((do let arguments ← arguments
         let sequence ← read after id .sequence
         .ok [kind, instruction, data, arguments, sequence]), after)

theorem argumentBytes_verified (state : State) (id : Nat) (key : Key) (source : WordArray.View)
    (valid : state.valid = true) (binding : HashKey.Binding state id key (source.address 0))
    (represented : WordArray.Represents state source key.arguments) (bounded : source.length * 4 < addressLimit) :
    ∃ output after, argumentBytes state id = (output, after) ∧ StackFrame state after ∧ after.heap = state.heap ∧
      (output = .ok (HashInput.arguments key.arguments) ∨ output = .error .outOfMemory) :=
  HashSlice.bytes_verified state id key source valid binding represented bounded

theorem field_images (key : Key) :
    [Field.image .kind key, Field.image .instruction key, Field.image .data key,
      HashInput.arguments key.arguments, Field.image .sequence key] = HashInput.encode key := by
  have kind : Field.image .kind key = HashInput.word key.kind := rfl
  have sequence : Field.image .sequence key = HashInput.word key.sequence := rfl
  have data : Field.image .data key = HashInput.data key.data := rfl
  have instruction : Field.image .instruction key = [key.instruction] := by
    simp [Field.image, Field.slot, KeyFields.layout, Field.value, Field.bits, List.range_succ]
  rw [kind, instruction, data, sequence]
  rfl

theorem inputs_verified (state : State) (id : Nat) (key : Key) (source : WordArray.View)
    (valid : state.valid = true) (binding : HashKey.Binding state id key (source.address 0))
    (represented : WordArray.Represents state source key.arguments) (bounded : source.length * 4 < addressLimit) :
    ∃ output after, inputs state id = (output, after) ∧ StackFrame state after ∧ after.heap = state.heap ∧
      (output = .ok (HashInput.encode key) ∨ output = .error .outOfMemory) := by
  have lengthBound : key.arguments.length < addressLimit := by have := represented.1; omega
  have scalar := read_verified state id key (source.address 0)
  have images := field_images key
  obtain ⟨output, after, observed, frame, heap, returned | failed⟩ :=
    argumentBytes_verified state id key source valid binding represented bounded
  · have sequence := read_verified after id key (source.address 0) .sequence frame.valid (binding.extend frame) lengthBound
    refine ⟨.ok (HashInput.encode key), after, ?_, frame, heap, Or.inl rfl⟩
    simp only [inputs, scalar .kind valid binding lengthBound, scalar .instruction valid binding lengthBound,
      scalar .data valid binding lengthBound, bind, Except.bind, observed, returned, sequence, images]
  · refine ⟨.error .outOfMemory, after, ?_, frame, heap, Or.inr rfl⟩
    simp only [inputs, scalar .kind valid binding lengthBound, scalar .instruction valid binding lengthBound,
      scalar .data valid binding lengthBound, bind, Except.bind, observed, failed]

end Compiler.Extraction.ExpressionMap.HashBytes
