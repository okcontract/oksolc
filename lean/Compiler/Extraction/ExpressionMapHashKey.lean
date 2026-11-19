/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapKey
import Compiler.ZigAir.MemoryStackFrame

set_option maxRecDepth 4096

namespace Compiler.Extraction.ExpressionMap.HashKey
open Compiler.ZigAir.Memory Compiler.Extraction.Cache
open Buckets

/-- The evaluated by-value key uses the same field values and sparse typed
leaves as publication. No padding or argument contents are copied into it. -/
def cells (key : Key) (arguments : Address) : Cells :=
  ([.data, .arguments, .kind, .sequence, .instruction] : List KeyFields.Slot).flatMap
    (fun slot => (KeyFields.value key arguments slot).leaves (KeyFields.offset slot))

theorem layout : keyType.layout = some ⟨64, 16⟩ := by decide

theorem cells_valid (key : Key) (arguments : Address) (bounded : key.arguments.length < addressLimit) :
    (cells key arguments).valid keyType = true := by
  have length := Value.usize_valid key.arguments.length bounded
  simp only [Cells.valid, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro entry member
    simp only [cells, List.flatMap_cons, List.flatMap_nil, KeyFields.value, KeyFields.offset,
      Value.leaves, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [leafFits, Bool.and_eq_true, decide_eq_true_eq]
    all_goals refine ⟨rfl, ?_⟩
    · exact KeyFields.value_valid key arguments bounded .data
    · rfl
    · exact length
    · exact KeyFields.value_valid key arguments bounded .kind
    · exact KeyFields.value_valid key arguments bounded .sequence
    · exact KeyFields.value_valid key arguments bounded .instruction
  · simp [cells, KeyFields.value, KeyFields.offset, Value.leaves, List.pairwise_cons]

private theorem read_leaf (key : Key) (arguments : Address) (offset : Nat) (value : Value)
    (typed : leafType keyType offset = some value.type)
    (found : (cells key arguments).lookup offset = some value) (valid : value.valid = true) :
    (cells key arguments).readLeaf keyType offset value.type = .ok value := by
  simp only [Cells.readLeaf, typed, ne_self_iff_false, ↓reduceIte, found,
    Value.hasType, valid, decide_true, Bool.true_and]

private theorem scalar_read (stored : Cells) (owner : Ty) (offset : Nat) (type : Compiler.ZigAir.Scalar.Ty)
    (viewed : acceptsView owner offset (.scalar type) = true) :
    stored.read owner offset (.scalar type) = stored.readLeaf owner offset (.scalar type) := by
  simp only [Cells.read, viewed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

private theorem scalar_leaf (key : Key) (arguments : Address) (bounded : key.arguments.length < addressLimit)
    (slot : KeyFields.Slot) (notSlice : slot ≠ .arguments) :
    (cells key arguments).readLeaf keyType (KeyFields.offset slot) (KeyFields.value key arguments slot).type =
      .ok (KeyFields.value key arguments slot) := by
  apply read_leaf _ _ _ _ _ _ (KeyFields.value_valid key arguments bounded slot)
  · cases slot <;> first | contradiction | rfl
  · cases slot <;> first | contradiction | rfl

private theorem slice_read (key : Key) (arguments : Address) (bounded : key.arguments.length < addressLimit) :
    (cells key arguments).read keyType 32 (.slice false (.scalar (.int false 32))) =
      .ok (.slice (.slice false (.scalar (.int false 32))) arguments key.arguments.length) := by
  have pointer := read_leaf key arguments 32
    (.pointer (.pointer false true (.scalar (.int false 32))) arguments) rfl rfl rfl
  have lengthValid := Value.usize_valid key.arguments.length bounded
  have length := read_leaf key arguments 40 (.scalar (.int false 64 key.arguments.length)) rfl rfl lengthValid
  simp only [Value.type, Compiler.ZigAir.Scalar.Value.type] at pointer length
  exact Cells.read_slice_of_parts _ _ _ false _ _ _ rfl pointer length

theorem cells_read (key : Key) (arguments : Address) (bounded : key.arguments.length < addressLimit)
    (slot : KeyFields.Slot) :
    (cells key arguments).read keyType (KeyFields.offset slot) (KeyFields.value key arguments slot).type =
      .ok (KeyFields.value key arguments slot) := by
  cases slot
  · exact (scalar_read _ _ _ _ rfl).trans (scalar_leaf key arguments bounded .kind (by decide))
  · exact (scalar_read _ _ _ _ rfl).trans (scalar_leaf key arguments bounded .instruction (by decide))
  · exact (scalar_read _ _ _ _ rfl).trans (scalar_leaf key arguments bounded .data (by decide))
  · exact slice_read key arguments bounded
  · exact (scalar_read _ _ _ _ rfl).trans (scalar_leaf key arguments bounded .sequence (by decide))

def create (state : State) (key : Key) (arguments : Address) : Except Fault (Unit × Nat) × State :=
  CellFrame.create state keyType (fun _ => .ok ((), cells key arguments))

def Binding (state : State) (id : Nat) (key : Key) (arguments : Address) : Prop :=
  ∃ cell, state.heap.lookup id = some cell ∧ cell.type = keyType ∧
    cell.cells = cells key arguments ∧ cell.writable = true

theorem create_verified (state : State) (key : Key) (arguments : Address)
    (valid : state.valid = true) (bounded : key.arguments.length < addressLimit) :
    ∃ result after, create state key arguments = (result, after) ∧ StackFrame state after ∧
      (result = .error .outOfMemory ∨ result = .ok ((), state.nextId) ∧ Binding after state.nextId key arguments) := by
  obtain ⟨result, after, ran, stack, failed | ⟨returned, cell, found, typed, contents, writable⟩⟩ :=
    StackFrame.create state keyType ⟨64, 16⟩ (fun _ => .ok ((), cells key arguments)) () (cells key arguments)
      valid layout (by decide) rfl (cells_valid key arguments bounded)
  · exact ⟨result, after, ran, stack, Or.inl failed⟩
  · exact ⟨result, after, ran, stack, Or.inr ⟨returned, cell, found, typed, contents, writable⟩⟩

theorem Binding.extend {before after : State} {id : Nat} {key : Key} {arguments : Address}
    (binding : Binding before id key arguments) (frame : StackFrame before after) :
    Binding after id key arguments := by
  obtain ⟨cell, found, typed, contents, writable⟩ := binding
  exact ⟨cell, frame.old_lookup id cell found, typed, contents, writable⟩


theorem Binding.access {state : State} {id : Nat} {key : Key} {arguments : Address}
    (binding : Binding state id key arguments) (valid : state.valid = true) (slot : KeyFields.Slot) :
    ∃ cell, access state ⟨id, KeyFields.offset slot⟩ (KeyFields.layout slot) false = .ok cell ∧
      cell.type = keyType ∧ cell.cells = cells key arguments := by
  obtain ⟨cell, found, typed, contents, writable⟩ := binding
  have root := root_access state id cell ⟨64, 16⟩ false valid found (typed ▸ layout) (by decide) (by simp)
  obtain ⟨_, positive, inside, aligned, divided⟩ := KeyFields.field_geometry key arguments slot
  have selected := access_subregion state ⟨id, 0⟩ ⟨64, 16⟩ (KeyFields.layout slot)
    (KeyFields.offset slot) false cell root positive inside aligned divided
  exact ⟨cell, by simpa only [Nat.zero_add] using selected, typed, contents⟩

theorem Binding.load {state : State} {id : Nat} {key : Key} {arguments : Address}
    (binding : Binding state id key arguments) (valid : state.valid = true)
    (bounded : key.arguments.length < addressLimit) (slot : KeyFields.Slot) :
    Compiler.ZigAir.Memory.load state (.pointer (.pointer false false (KeyFields.value key arguments slot).type)
      ⟨id, KeyFields.offset slot⟩) = .ok (KeyFields.value key arguments slot) := by
  obtain ⟨cell, accessed, typed, contents⟩ := binding.access valid slot
  have shaped := (KeyFields.field_geometry key arguments slot).1
  simp only [Compiler.ZigAir.Memory.load, shaped, accessed, bind, Except.bind, readCell, typed, contents]
  exact cells_read key arguments bounded slot


theorem Binding.select {state : State} {id : Nat} {key : Key} {arguments : Address}
    (binding : Binding state id key arguments) (valid : state.valid = true) (slot : KeyFields.Slot) :
    fieldPointer state (.pointer (.pointer false false keyType) ⟨id, 0⟩) (KeyFields.offset slot) =
      .ok (.pointer (.pointer false false (KeyFields.value key arguments slot).type) ⟨id, KeyFields.offset slot⟩) := by
  obtain ⟨cell, found, typed, _, _⟩ := binding
  simpa only [Nat.zero_add] using root_fieldPointer state id cell keyType _ ⟨64, 16⟩ _ false false
    valid found typed layout (by decide) (KeyFields.field_selected key arguments slot)

end Compiler.Extraction.ExpressionMap.HashKey
