/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemorySlots
import Compiler.ZigAir.MemoryByteAccessProofs

/-! Exact framing of one saved stack object. Prefixing a disjoint allocation
preserves old reads and commutes with old stores, including their faults.
Counters belong to the invocation and are not rewound by cleanup. -/
namespace Compiler.ZigAir.Memory

def prepend (id : Nat) (cell : Allocation) (nextId nextAddress : Nat) (state : State) : State :=
  ⟨(id, cell) :: state.heap, nextId, nextAddress⟩

theorem access_prepend (state : State) (id : Nat) (cell : Allocation) (nextId nextAddress : Nat)
    (address : Address) (layout : Layout) (write : Bool) (apart : address.allocation ≠ id) :
    access (prepend id cell nextId nextAddress state) address layout write = access state address layout write := by
  simp only [access, prepend, Heap.lookup_cons, if_neg (Ne.symm apart)]

theorem load_prepend (state : State) (id : Nat) (cell : Allocation) (nextId nextAddress : Nat)
    (writable many : Bool) (child : Ty) (address : Address) (apart : address.allocation ≠ id) :
    load (prepend id cell nextId nextAddress state) (.pointer (.pointer writable many child) address) =
      load state (.pointer (.pointer writable many child) address) := by
  apply load_eq_of_lookup
  simp only [prepend, Heap.lookup_cons, if_neg (Ne.symm apart)]

theorem store_prepend (state : State) (id : Nat) (cell : Allocation) (nextId nextAddress : Nat)
    (writable many : Bool) (child : Ty) (address : Address) (value : Value) (apart : address.allocation ≠ id) :
    store (prepend id cell nextId nextAddress state) (.pointer (.pointer writable many child) address) value =
      (store state (.pointer (.pointer writable many child) address) value).map (prepend id cell nextId nextAddress) := by
  simp only [store]
  split
  · rfl
  · split
    · rfl
    · cases shaped : child.layout with
      | none => rfl
      | some layout =>
        simp only [access_prepend state id cell nextId nextAddress address layout true apart]
        cases accessed : access state address layout true with
        | error reason => rfl
        | ok target =>
          simp only [bind, Except.bind]
          cases written : writeCell target address.offset value with
          | error reason => rfl
          | ok after =>
            simp only [prepend, Heap.replace_cons, if_neg (Ne.symm apart)]
            rfl

theorem valid_heap_ids (state : State) (initial : state.valid = true) :
    ∀ entry ∈ state.heap, entry.1 < state.nextId := by
  simp only [State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at initial
  intro entry present
  exact (initial.1.2 entry present).1.1

theorem Heap.replace_absent (heap : Heap) (id : Nat) (cell : Allocation)
    (absent : ∀ entry ∈ heap, entry.1 ≠ id) : heap.replace id cell = heap := by
  induction heap with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key, old⟩
    simp only [Heap.replace_cons, if_neg (absent (key, old) (by simp))]
    rw [ih (fun entry present => absent entry (by simp [present]))]

theorem saved_slot_prefix (state allocated saved : State) (value : Value)
    (initial : state.valid = true)
    (allocation : allocate state value.type = .ok (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩, allocated))
    (written : store allocated (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩) value = .ok saved) :
    ∃ cell, cell.stack = true ∧ saved = prepend state.nextId cell saved.nextId saved.nextAddress state := by
  obtain ⟨layout, base, _, _, shape⟩ := allocate_shape state value.type _ allocated allocation
  obtain ⟨many, child, address, accessLayout, cell, contents, same, _, _, accessed, _, after⟩ :=
    store_success allocated _ value saved written
  cases same
  have found := (access_success_region allocated ⟨state.nextId, 0⟩ accessLayout true cell accessed).1
  rw [shape] at found
  simp only [Heap.lookup_cons, ↓reduceIte] at found
  cases Option.some.inj found
  have absent : ∀ entry ∈ state.heap, entry.1 ≠ state.nextId :=
    fun entry present => Nat.ne_of_lt (valid_heap_ids state initial entry present)
  rw [shape] at after
  simp only [Heap.replace_cons, ↓reduceIte, Heap.replace_absent state.heap state.nextId _ absent] at after
  subst saved
  exact ⟨_, rfl, rfl⟩

theorem cleanup_initial (state : State) (initial : state.valid = true) : cleanup state.nextId state = state := by
  have frame := valid_initial_frame state initial
  have heap := (cleanup_eq_older state state.nextId frame.1).trans frame.2
  cases state
  simp_all [cleanup]

theorem cleanup_prepend (state : State) (cell : Allocation) (nextId nextAddress : Nat)
    (initial : state.valid = true) (stack : cell.stack = true) :
    (cleanup state.nextId (prepend state.nextId cell nextId nextAddress state)).heap = state.heap := by
  have same := congrArg State.heap (cleanup_initial state initial)
  simpa only [cleanup, prepend, stack, Bool.not_true, Nat.lt_irrefl, decide_false,
    Bool.or_self, List.filter_cons, Bool.false_eq_true, ↓reduceIte] using same

namespace WordArray

theorem writable_heap_eq (before after : State) (view : View) (same : after.heap = before.heap)
    (cap : Writable before view) : Writable after view := by
  simpa only [Writable, same] using cap

theorem represents_heap_eq (before after : State) (view : View) (items : List (BitVec 32))
    (same : after.heap = before.heap) (represented : Represents before view items) : Represents after view items := by
  refine ⟨represented.1, ?_⟩
  intro index inside
  exact (load_eq_of_lookup before after true false word (view.address index) (by rw [same])).trans
    (represented.2 index inside)

end WordArray

namespace WordByteView

theorem read_prepend (order : WordBytes.Order) (state : State) (id : Nat) (cell : Allocation)
    (nextId nextAddress : Nat) (writable many : Bool) (address : Address) (offset : Nat)
    (apart : address.allocation ≠ id) :
    read order (prepend id cell nextId nextAddress state) (.pointer (.pointer writable many WordArray.word) address) offset =
      read order state (.pointer (.pointer writable many WordArray.word) address) offset := by
  simp only [read, load_prepend state id cell nextId nextAddress writable many WordArray.word address apart]

theorem write_prepend (order : WordBytes.Order) (state : State) (id : Nat) (cell : Allocation)
    (nextId nextAddress : Nat) (writable many : Bool) (address : Address) (offset : Nat) (byte : BitVec 8)
    (apart : address.allocation ≠ id) :
    write order (prepend id cell nextId nextAddress state) (.pointer (.pointer writable many WordArray.word) address) offset byte =
      (write order state (.pointer (.pointer writable many WordArray.word) address) offset byte).map (prepend id cell nextId nextAddress) := by
  simp only [write, load_prepend state id cell nextId nextAddress writable many WordArray.word address apart]
  split
  · split
    · rfl
    · exact store_prepend state id cell nextId nextAddress writable many WordArray.word address _ apart
    · rfl
  · rfl

end WordByteView

namespace ByteAccess

theorem read_prepend (order : WordBytes.Order) (state : State) (id : Nat) (cell : Allocation)
    (nextId nextAddress : Nat) (writable many : Bool) (address : Address) (apart : address.allocation ≠ id) :
    read order (prepend id cell nextId nextAddress state) (pointer writable many address) =
      read order state (pointer writable many address) := by
  simp only [read, pointer, byte, WordByteView.read, wordPointer]
  rw [load_prepend state id cell nextId nextAddress writable false WordArray.word (wordAddress address) apart]

theorem write_prepend (order : WordBytes.Order) (state : State) (id : Nat) (cell : Allocation)
    (nextId nextAddress : Nat) (writable many : Bool) (address : Address) (value : Value)
    (apart : address.allocation ≠ id) :
    write order (prepend id cell nextId nextAddress state) (pointer writable many address) value =
      (write order state (pointer writable many address) value).map (prepend id cell nextId nextAddress) := by
  simp only [write, pointer, byte]
  split
  next bits =>
    split
    · rfl
    · simp only [WordByteView.write, wordPointer]
      split
      next inside =>
        rw [load_prepend state id cell nextId nextAddress writable false WordArray.word (wordAddress address) apart]
        split
        · rfl
        · exact store_prepend state id cell nextId nextAddress writable false WordArray.word (wordAddress address) _ apart
        · rfl
      · rfl
  · rfl

end ByteAccess
end Compiler.ZigAir.Memory
