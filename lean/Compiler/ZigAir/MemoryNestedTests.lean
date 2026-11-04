/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryRecordViews
import Compiler.ZigAir.MemoryRecordWrites

namespace Compiler.ZigAir.Memory.NestedTests

deriving instance DecidableEq for Except

def word : Ty := .scalar (.int false 32)
def header : Ty := .aggregate "fixture.header" ⟨24, 8⟩
  [(0, .slice true (.int false 32)), (16, .scalar (.int false 64))]
def fields : List (Nat × Field) :=
  [(0, .object (.record "fixture.allocator" ⟨16, 8⟩)), (16, .object header),
   (40, .object (.record "fixture.cache" ⟨16, 8⟩))]
def owner : Ty := .aggregate "fixture.owner" ⟨56, 8⟩ fields
def items : Ty := .slice true word
def cell : Allocation := ⟨8, owner, [], true, true⟩
def initial : State := ⟨[(3, cell)], 4, 64⟩
def pointer (writable : Bool) (type : Ty) (id offset : Nat) : Value :=
  .pointer (.pointer writable false type) ⟨id, offset⟩
def itemValue : Value := .slice items ⟨9, 4⟩ 2
def withItems : State :=
  { initial with heap := [(3, { cell with cells := (itemValue.leaves 16).reverse })] }
def completed : State :=
  { initial with heap := [(3, { cell with cells := (32, .scalar (.int false 64 5)) :: (itemValue.leaves 16).reverse })] }

theorem complete_layout_and_initial_valid : owner.layout = some ⟨56, 8⟩ ∧ initial.valid = true := by decide

theorem nested_type_equality_retains_fields :
    owner ≠ .aggregate "fixture.owner" ⟨56, 8⟩ (fields.take 2) ∧
    header ≠ .aggregate "fixture.header" ⟨24, 8⟩ [(0, .slice false (.int false 32)), (16, .scalar (.int false 64))] := by decide

theorem nested_header_selection (writable : Bool) :
    fieldPointer initial (pointer writable owner 3 0) 16 = .ok (pointer writable header 3 16) := by
  cases writable <;> decide

theorem nested_components_keep_byte_offsets :
    fieldType owner 16 = some header ∧ fieldType owner 24 = some usize ∧
      fieldType owner 32 = some usize ∧ leafType owner 16 = some (.pointer true true word) ∧
      leafType owner 24 = some usize ∧ leafType owner 32 = some usize := by decide

theorem nested_header_field_selection (writable : Bool) :
    fieldPointer initial (pointer writable header 3 16) 0 = .ok (pointer writable items 3 16) ∧
      fieldPointer initial (pointer writable header 3 16) 16 = .ok (pointer writable usize 3 32) := by
  cases writable <;> decide

theorem typed_selection_supplies_no_initialization :
    load initial (pointer false items 3 16) = .error .uninitialized ∧
      load initial (pointer false usize 3 32) = .error .uninitialized := by decide

theorem actual_nested_header_stores :
    store initial (pointer true items 3 16) itemValue = .ok withItems ∧
      store withItems (pointer true usize 3 32) (.scalar (.int false 64 5)) = .ok completed := by decide

theorem nested_readback_and_validity :
    load completed (pointer false items 3 16) = .ok itemValue ∧
      load completed (pointer false usize 3 32) = .ok (.scalar (.int false 64 5)) ∧
      completed.valid = true := by decide

theorem reached_prefix_does_not_initialize_capacity :
    load withItems (pointer false items 3 16) = .ok itemValue ∧
      load withItems (pointer false usize 3 32) = .error .uninitialized := by decide

theorem partial_nested_slice_rejects :
    let state : State := { initial with heap := [(3, { cell with cells := [(16, .pointer (.pointer true true word) ⟨9, 4⟩)] })] }
    state.valid = true ∧ load state (pointer false items 3 16) = .error .uninitialized := by decide

theorem opaque_fields_and_whole_objects_stay_unsupported :
    fieldPointer initial (pointer true owner 3 0) 0 = .ok (pointer true (.record "fixture.allocator" ⟨16, 8⟩) 3 0) ∧
      load initial (pointer false (.record "fixture.allocator" ⟨16, 8⟩) 3 0) = .error .unsupported ∧
      load completed (pointer false header 3 16) = .error .unsupported ∧
      load completed (pointer false owner 3 0) = .error .unsupported := by decide

theorem nominal_same_extent_cannot_admit_header :
    let state : State := { initial with heap := [(3, { cell with type := .record "fixture.owner" ⟨56, 8⟩ })] }
    recordView state header (pointer false (.record "fixture.header" ⟨24, 8⟩) 3 16) = .error .unsupported := by decide

theorem exact_nested_record_view_retains_permissions (writable : Bool) :
    recordView initial header (pointer writable (.record "fixture.header" ⟨24, 8⟩) 3 16) =
      .ok (pointer writable header 3 16) := by cases writable <;> decide

theorem altered_nested_fields_cannot_admit_view :
    recordView initial (.aggregate "fixture.header" ⟨24, 8⟩ [(0, .slice true (.int false 32))])
      (pointer false (.record "fixture.header" ⟨24, 8⟩) 3 16) = .error .unsupported := by decide

def arrayCell : Allocation := ⟨8, .array 2 owner, [], true, true⟩
def arrayState : State := ⟨[(7, arrayCell)], 8, 120⟩

theorem nonzero_owner_offset_keeps_lifetime :
    arrayState.valid = true ∧
      fieldPointer arrayState (pointer false owner 7 56) 16 = .ok (pointer false header 7 72) ∧
      fieldPointer arrayState (pointer false header 7 72) 16 = .ok (pointer false usize 7 88) := by decide

theorem nested_array_owner_bound_rejects :
    fieldPointer arrayState (pointer false owner 7 112) 16 = .error .memoryValidity ∧
      leafType (.array 2 owner) 144 = none := by decide

theorem nested_array_child_bounds_are_retained :
    let type : Ty := .aggregate "fixture.array" ⟨16, 4⟩ [(4, .object (.array 2 word))]
    type.layout = some ⟨16, 4⟩ ∧ fieldType type 8 = some word ∧
      leafType type 8 = some word ∧ leafType type 12 = none ∧
      acceptsView type 12 word = false := by decide

theorem padding_and_interior_are_not_leaves :
    leafType owner 12 = none ∧ leafType owner 17 = none ∧ leafType owner 56 = none ∧
      fieldType owner 17 = none := by decide

theorem invalid_nested_child_layout_rejects :
    let malformed : Ty := .aggregate "fixture.child" ⟨8, 8⟩ [(0, .scalar (.int false 64)), (0, .scalar (.int false 64))]
    let type : Ty := .aggregate "fixture.parent" ⟨16, 8⟩ [(8, .object malformed)]
    type.layout = none ∧ leafType type 8 = none ∧ acceptsView type 8 usize = false := by decide

theorem invalid_parent_view_rejects :
    let type : Ty := .aggregate "fixture.short" ⟨32, 8⟩ [(16, .object header)]
    leafType type 32 = none ∧ acceptsView type 32 usize = false := by decide

theorem nested_parent_geometry_rejects :
    (Ty.aggregate "fixture.short" ⟨32, 8⟩ [(16, .object header)]).layout = none ∧
      (Ty.aggregate "fixture.unaligned" ⟨40, 8⟩ [(12, .object header)]).layout = none ∧
      (Ty.aggregate "fixture.alignment" ⟨40, 4⟩ [(16, .object header)]).layout = none ∧
      (Ty.aggregate "fixture.overlap" ⟨56, 8⟩ [(0, .object header), (16, .object header)]).layout = none := by decide

theorem readonly_nested_access_cannot_store :
    store initial (pointer false items 3 16) itemValue = .error .readOnly ∧
      store { initial with heap := [(3, { cell with writable := false })] } (pointer true items 3 16) itemValue = .error .readOnly := by decide

theorem stale_nested_lifetime_and_cleanup_reject :
    fieldPointer initial (pointer false header 4 16) 16 = .error .unallocated ∧
      fieldPointer (cleanup 3 initial) (pointer false header 3 16) 16 = .error .unallocated ∧
      (cleanup 3 initial).nextId = initial.nextId ∧ (cleanup 3 initial).nextAddress = initial.nextAddress := by decide

theorem nested_cells_require_declared_leaf_type :
    ({ initial with heap := [(3, { cell with cells := [(24, .scalar (.int false 32 2))] })] } : State).valid = false ∧
      ({ initial with heap := [(3, { cell with cells := [(17, .scalar (.int false 64 2))] })] } : State).valid = false := by decide

end Compiler.ZigAir.Memory.NestedTests
