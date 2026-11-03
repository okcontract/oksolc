/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.WyhashBuffer

set_option maxRecDepth 4096

namespace Compiler.Extraction.WyhashUpdate
open Compiler.ZigAir.Memory WyhashLocal

def store (cells : Cells) (offset : Nat) (bits : BitVec 64) : Except Fault Cells :=
  cells.write objectType offset (word bits)

def seedState (seed : BitVec 64) : BitVec 64 := seed ^^^ mix (seed ^^^ secret0) secret1

/-- The fresh local starts undefined. Initializer stores and the two subsequent
state copies use actual typed accesses; no a/b or buffer value is fabricated. -/
def initFields (value : BitVec 64) : Except Fault Cells := do
  let cells ← store [] 40 0
  let cells ← store cells 48 0
  let cells ← store cells 16 value
  let first ← nativeOps.read cells 2
  let cells ← store cells 24 first
  let first ← nativeOps.read cells 2
  store cells 32 first

def init (seed : BitVec 64) : Except Fault Cells := initFields (seedState seed)

def secret (lane : Fin 3) : BitVec 64 :=
  if lane.val = 0 then secret1 else if lane.val = 1 then 0x8ebc6af09c88c6e3 else 0x589965cc75374cc3

/-- Self-buffer reads observe the current cells after each lane store. External
bytes belong to a distinct admitted input object, whose heap separation is an
enclosing obligation rather than a correctness assumption on a callback. -/
inductive Input where
  | external (cells : Cells) (view : ByteSlice.View)
  | buffer

def Input.cells : Input → Cells → Cells
  | .external source _, _ => source
  | .buffer, current => current

def Input.view : Input → ByteSlice.View
  | .external _ view => view
  | .buffer => WyhashBuffer.buffer 0 48

def lane (input : Input) (offset : Nat) (index : Fin 3) (cells : Cells) : Except Fault Cells := do
  let a ← ByteSlice.readLE (input.cells cells) input.view (offset + 16 * index.val) 8
  let b ← ByteSlice.readLE (input.cells cells) input.view (offset + 16 * index.val + 8) 8
  let old ← nativeOps.read cells ⟨2 + index.val, by omega⟩
  store cells (16 + 8 * index.val) (mix (a ^^^ secret index) (b ^^^ old))

def round (input : Input) (offset : Nat) (cells : Cells) : Except Fault Cells := do
  let cells ← lane input offset 0 cells
  let cells ← lane input offset 1 cells
  lane input offset 2 cells

/-- Strict native loop. The explicit native-width rejection is unreachable from
the caller-derived input budget; it is not silently interpreted as wraparound. -/
def loop (source : Cells) (view : ByteSlice.View) (index : Nat) (cells : Cells) : Except Fault (Cells × Nat) :=
  if addressLimit ≤ index + 48 then .error .memoryValidity else
  if index + 48 < view.length then do
    let cells ← round (.external source view) index cells
    loop source view (index + 48) cells
  else .ok (cells, index)
termination_by view.length - index
decreasing_by omega

def fill (source : Cells) (view : ByteSlice.View) (length : Nat) (cells : Cells) : Except Fault (Cells × Nat) :=
  if length > 0 then do
    let index := 48 - length
    let cells ← ByteSlice.copy source view (WyhashBuffer.buffer 0 48) 0 length index cells
    let cells ← round .buffer 0 cells
    let cells ← store cells 48 0
    .ok (cells, index)
  else .ok (cells, 0)

/-- Common post-loop suffix and final-buffer work, consumed by native AIR
composition as well as the complete update invariant. -/
def remainder (source : Cells) (view : ByteSlice.View) (index : Nat) (cells : Cells) : Except Fault Cells := do
  let remaining := view.length - index
  let cells ← if remaining < 16 ∧ index ≥ 48 then
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48)
        (index - (16 - remaining)) (48 - (16 - remaining)) (16 - remaining) cells
    else .ok cells
  let cells ← ByteSlice.copy source view (WyhashBuffer.buffer 0 48) index 0 remaining cells
  store cells 48 (BitVec.ofNat 64 remaining)

def updateBody (source : Cells) (view : ByteSlice.View) (length : Nat) (cells : Cells) : Except Fault Cells :=
  if view.length ≤ 48 - length then do
    let cells ← ByteSlice.copy source view (WyhashBuffer.buffer 0 48) 0 length view.length cells
    store cells 48 (BitVec.ofNat 64 (length + view.length))
  else do
    let (cells, index) ← fill source view length cells
    let (cells, index) ← loop source view index cells
    remainder source view index cells

def update (source : Cells) (view : ByteSlice.View) (cells : Cells) : Except Fault Cells := do
  let total ← nativeOps.read cells 5
  if addressLimit ≤ total.toNat + view.length then .error .memoryValidity else
  let cells ← store cells 40 (BitVec.ofNat 64 (total.toNat + view.length))
  let length ← WyhashBuffer.readLength cells
  if length > 48 then .error .sourceBounds else
  updateBody source view length cells

def ByteAt (cells : Cells) (offset : Nat) : Prop :=
  ∃ bits, cells.lookup offset = some (ByteSlice.value bits)

def WordAt (cells : Cells) (offset : Nat) : Prop :=
  ∃ bits, cells.lookup offset = some (word bits)

structure Core (cells : Cells) (total : Nat) : Prop where
  valid : cells.valid objectType = true
  a : cells.lookup 0 = none
  b : cells.lookup 8 = none
  lanes : ∀ i : Fin 3, WordAt cells (16 + 8 * i.val)
  count : cells.lookup 40 = some (word (BitVec.ofNat 64 total))

/-- One invariant for both update paths and finalization. It permits undefined
gaps. The short-total relation derives when a retained suffix is required. -/
structure Invariant (cells : Cells) (total length : Nat) : Prop where
  core : Core cells total
  totalBound : total < addressLimit
  lengthField : cells.lookup 48 = some (word (BitVec.ofNat 64 length))
  bounded : length ≤ 48
  included : length ≤ total
  small : total ≤ 48 → length = total
  head : ∀ i < length, ByteAt cells (56 + i)
  suffix : 16 < total → length < 16 → ∀ i, 48 - (16 - length) ≤ i → i < 48 → ByteAt cells (56 + i)

theorem word_geometry (offset : Nat) (member : offset ∈ [16, 24, 32, 40, 48]) :
    leafType objectType offset = some usize ∧ acceptsView objectType offset usize = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem store_eq (cells : Cells) (offset : Nat) (bits : BitVec 64)
    (member : offset ∈ [16, 24, 32, 40, 48]) :
    store cells offset bits = .ok (cells.set offset (word bits)) := by
  apply Cells.write_single
  · exact word_valid bits
  · exact (word_geometry offset member).2
  · simp only [leafFits, (word_geometry offset member).1, word_type, decide_true, Bool.true_and, word_valid]
  · rfl

theorem store_valid (cells : Cells) (offset : Nat) (bits : BitVec 64)
    (valid : cells.valid objectType = true) (member : offset ∈ [16, 24, 32, 40, 48]) :
    (cells.set offset (word bits)).valid objectType = true :=
  Cells.write_preserves_valid cells objectType offset (word bits) _ valid (store_eq cells offset bits member)

theorem read_slot (cells : Cells) (slot : Fin 6) (bits : BitVec 64)
    (found : cells.lookup (8 * slot.val) = some (word bits)) :
    nativeOps.read cells slot = .ok bits := by
  rw [nativeOps_eq]
  exact read_word cells (8 * slot.val) bits found

def initialCells (value : BitVec 64) : Cells :=
  ((((Cells.set [] 40 (word 0)).set 48 (word 0)).set 16 (word value)).set
    24 (word value)).set 32 (word value)

theorem initFields_eq (value : BitVec 64) : initFields value = .ok (initialCells value) := by
  have first (cells : Cells) : nativeOps.read (cells.set 16 (word value)) 2 = .ok value :=
    read_slot _ 2 _ (Cells.lookup_set ..)
  have second (cells : Cells) :
      nativeOps.read ((cells.set 16 (word value)).set 24 (word value)) 2 = .ok value := by
    apply read_slot
    change ((cells.set 16 (word value)).set 24 (word value)).lookup 16 = _
    rw [Cells.lookup_set_other _ _ _ _ (by decide : 16 ≠ 24), Cells.lookup_set]
  unfold initFields
  refine bind_result _ _ _ _ (store_eq [] 40 0 (by decide)) ?_
  refine bind_result _ _ _ _ (store_eq _ 48 0 (by decide)) ?_
  refine bind_result _ _ _ _ (store_eq _ 16 value (by decide)) ?_
  refine bind_result _ _ _ _ (first _) ?_
  refine bind_result _ _ _ _ (store_eq _ 24 value (by decide)) ?_
  refine bind_result _ _ _ _ (second _) ?_
  exact store_eq _ 32 value (by decide)

theorem init_eq (seed : BitVec 64) : init seed = .ok (initialCells (seedState seed)) :=
  initFields_eq (seedState seed)

/-- One word-store preservation rule for lanes, the total and buffered length. -/
theorem Core.store_word (core : Core cells total) (offset : Nat) (bits : BitVec 64)
    (member : offset ∈ [16, 24, 32, 40, 48]) :
    Core (cells.set offset (word bits)) (if offset = 40 then bits.toNat else total) := by
  have bounds : 16 ≤ offset ∧ offset ≤ 48 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  refine ⟨store_valid _ _ bits core.valid member, ?_, ?_, ?_, ?_⟩
  · rw [Cells.lookup_set_other _ _ _ _ (by omega)]
    exact core.a
  · rw [Cells.lookup_set_other _ _ _ _ (by omega)]
    exact core.b
  · intro i
    by_cases same : 16 + 8 * i.val = offset
    · exact ⟨bits, by rw [same, Cells.lookup_set]⟩
    · obtain ⟨old, found⟩ := core.lanes i
      exact ⟨old, by rw [Cells.lookup_set_other _ _ _ _ same]; exact found⟩
  · by_cases same : offset = 40
    · subst offset
      simp only [↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq, Cells.lookup_set]
    · rw [if_neg same, Cells.lookup_set_other _ _ _ _ (Ne.symm same)]
      exact core.count

theorem Core.byte_frame (core : Core before total) (valid : after.valid objectType = true)
    (frame : ∀ offset < 56, after.lookup offset = before.lookup offset) : Core after total := by
  refine ⟨valid, ?_, ?_, ?_, ?_⟩
  · rw [frame 0 (by decide)]; exact core.a
  · rw [frame 8 (by decide)]; exact core.b
  · intro i
    obtain ⟨bits, found⟩ := core.lanes i
    refine ⟨bits, ?_⟩
    rw [frame (16 + 8 * i.val) (by have := i.isLt; omega)]
    exact found
  · rw [frame 40 (by decide)]; exact core.count

theorem initialCells_explicit (value : BitVec 64) :
    initialCells value = [(32, word value), (24, word value), (16, word value), (48, word 0), (40, word 0)] := rfl

theorem init_invariant (seed : BitVec 64) : Invariant (initialCells (seedState seed)) 0 0 := by
  have empty : Cells.valid [] objectType = true := by decide
  have valid := store_valid _ 40 0 empty (by decide)
  have valid := store_valid _ 48 0 valid (by decide)
  have valid := store_valid _ 16 (seedState seed) valid (by decide)
  have valid := store_valid _ 24 (seedState seed) valid (by decide)
  have valid := store_valid _ 32 (seedState seed) valid (by decide)
  refine ⟨⟨valid, ?_, ?_, ?_, ?_⟩, by decide, ?_, by decide, by decide, by simp, ?_, ?_⟩
  · rw [initialCells_explicit]; rfl
  · rw [initialCells_explicit]; rfl
  · intro i
    have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by have := i.isLt; omega
    refine ⟨seedState seed, ?_⟩
    rcases cases with h | h | h <;> simp [initialCells_explicit, Cells.lookup, h]
  · rw [initialCells_explicit]; rfl
  · rw [initialCells_explicit]; rfl
  · intro i inside; omega
  · intro long; omega

def byteAt (cells : Cells) (offset : Nat) : BitVec 8 :=
  match cells.lookup offset with
  | some (.scalar (.int false 8 bits)) => BitVec.ofInt 8 bits
  | _ => 0

theorem byteAt_lookup (cells : Cells) (offset : Nat) (present : ByteAt cells offset) :
    cells.lookup offset = some (ByteSlice.value (byteAt cells offset)) := by
  obtain ⟨bits, found⟩ := present
  simp only [byteAt, found, ByteSlice.value, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

def Input.Ready (input : Input) (cells : Cells) : Prop :=
  ByteSlice.Geometry input.view ∧ ∀ i < input.view.length,
    ByteAt (input.cells cells) (input.view.base + i)

theorem Input.Ready.represented {input : Input} {cells : Cells} (ready : Input.Ready input cells) :
    ByteSlice.Represents (input.cells cells) input.view
      (fun i => byteAt (input.cells cells) (input.view.base + i)) := by
  intro i inside
  exact byteAt_lookup _ _ (ready.2 i inside)

theorem Input.Ready.store_word {input : Input} {cells : Cells} (ready : Input.Ready input cells) (offset : Nat) (bits : BitVec 64)
    (beforeBuffer : offset < 56) : Input.Ready input (cells.set offset (word bits)) := by
  cases input with
  | external source view => exact ready
  | buffer =>
    refine ⟨ready.1, ?_⟩
    intro i inside
    obtain ⟨byte, found⟩ := ready.2 i inside
    refine ⟨byte, ?_⟩
    change (cells.set offset (word bits)).lookup (56 + i) = _
    rw [Cells.lookup_set_other _ _ _ _ (by omega)]
    exact found

/-- A native lane changes only its state word. In particular, the next lane
may safely read the same self-buffer after this actual store. -/
theorem lane_verified (input : Input) (offset : Nat) (index : Fin 3) (cells : Cells) (total : Nat)
    (core : Core cells total) (ready : Input.Ready input cells)
    (inside : offset + 48 ≤ input.view.length) :
    ∃ after, lane input offset index cells = .ok after ∧ Core after total ∧ Input.Ready input after ∧
      (∀ query, query < 16 ∨ 40 ≤ query → after.lookup query = cells.lookup query) := by
  have laneBound := index.isLt
  have selected : 16 + 8 * index.val ∈ [16, 24, 32, 40, 48] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨a, loadedA⟩ : ∃ a, ByteSlice.readLE (input.cells cells) input.view (offset + 16 * index.val) 8 = .ok a :=
    ⟨_, ByteSlice.readLE_verified _ _ _ ready.1 ready.represented _ _ (by omega)⟩
  obtain ⟨b, loadedB⟩ : ∃ b, ByteSlice.readLE (input.cells cells) input.view (offset + 16 * index.val + 8) 8 = .ok b :=
    ⟨_, ByteSlice.readLE_verified _ _ _ ready.1 ready.represented _ _ (by omega)⟩
  obtain ⟨old, found⟩ := core.lanes index
  have oldRead : nativeOps.read cells ⟨2 + index.val, by omega⟩ = .ok old := by
    apply read_slot
    have position : 8 * (2 + index.val) = 16 + 8 * index.val := by omega
    simpa only [position] using found
  let value := mix (a ^^^ secret index) (b ^^^ old)
  refine ⟨cells.set (16 + 8 * index.val) (word value), ?_, ?_, ?_, ?_⟩
  · unfold lane
    refine bind_result _ _ _ _ loadedA ?_
    refine bind_result _ _ _ _ loadedB ?_
    refine bind_result _ _ _ _ oldRead ?_
    exact store_eq _ _ value selected
  · simpa only [if_neg (by omega : ¬16 + 8 * index.val = 40)] using core.store_word _ value selected
  · exact ready.store_word _ value (by omega)
  · intro query outside
    exact Cells.lookup_set_other _ _ _ _ (by omega)

theorem round_verified (input : Input) (offset : Nat) (cells : Cells) (total : Nat)
    (core : Core cells total) (ready : Input.Ready input cells)
    (inside : offset + 48 ≤ input.view.length) :
    ∃ after, round input offset cells = .ok after ∧ Core after total ∧ Input.Ready input after ∧
      (∀ query, query < 16 ∨ 40 ≤ query → after.lookup query = cells.lookup query) := by
  obtain ⟨first, ran0, core0, ready0, frame0⟩ := lane_verified input offset 0 cells total core ready inside
  obtain ⟨second, ran1, core1, ready1, frame1⟩ := lane_verified input offset 1 first total core0 ready0 inside
  obtain ⟨after, ran2, core2, ready2, frame2⟩ := lane_verified input offset 2 second total core1 ready1 inside
  refine ⟨after, ?_, core2, ready2, ?_⟩
  · exact bind_result _ _ _ _ ran0 (bind_result _ _ _ _ ran1 ran2)
  · intro query outside
    exact (frame2 query outside).trans ((frame1 query outside).trans (frame0 query outside))

/-- Every buffer copy uses the same typed writes and core frame. -/
theorem copy_buffer (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (total src dst count : Nat) (core : Core cells total)
    (sourceBound : src + count ≤ view.length) (targetBound : dst + count ≤ 48) :
    ∃ after, ByteSlice.copy source view (WyhashBuffer.buffer 0 48) src dst count cells = .ok after ∧
      Core after total ∧
      (∀ i < count, ByteAt after (56 + (dst + i))) ∧
      (∀ offset, offset < 56 + dst ∨ 56 + dst + count ≤ offset → after.lookup offset = cells.lookup offset) := by
  obtain ⟨after, ran, copied, frame⟩ := ByteSlice.copy_verified source cells view (WyhashBuffer.buffer 0 48)
    bytes geometry (WyhashBuffer.buffer_geometry 0 48 (by decide)) represented src dst count sourceBound targetBound
  have framed : ∀ offset, offset < 56 + dst ∨ 56 + dst + count ≤ offset → after.lookup offset = cells.lookup offset := by
    simpa only [WyhashBuffer.buffer, Nat.add_zero] using frame
  refine ⟨after, ran, ?_, ?_, framed⟩
  · exact core.byte_frame (ByteSlice.copy_valid source view (WyhashBuffer.buffer 0 48)
      src dst count cells after core.valid ran) (fun offset inside => framed offset (Or.inl (by omega)))
  · intro i inside
    exact ⟨bytes (src + i), by simpa only [WyhashBuffer.buffer, Nat.add_zero] using copied i inside⟩

/-- Both native update paths consume the same counter store and length read
before executing their derived body. -/
theorem update_from_body (source cells : Cells) (view : ByteSlice.View) (total length : Nat)
    (invariant : Invariant cells total length) (sumBound : total + view.length < addressLimit)
    (after : Cells)
    (body : updateBody source view length
      (cells.set 40 (word (BitVec.ofNat 64 (total + view.length)))) = .ok after) :
    update source view cells = .ok after := by
  let counted := cells.set 40 (word (BitVec.ofNat 64 (total + view.length)))
  have totalWord : total < 2 ^ 64 := invariant.totalBound
  have totalRead := read_slot cells 5 _ invariant.core.count
  have stored := store_eq cells 40 (BitVec.ofNat 64 (total + view.length)) (by decide)
  have lengthField : counted.lookup 48 = some (word (BitVec.ofNat 64 length)) := by
    simpa only [counted, Cells.lookup_set_other _ _ _ _ (by decide : 48 ≠ 40)] using invariant.lengthField
  have lengthRead := WyhashBuffer.readLength_verified counted length invariant.bounded lengthField
  have notLong : ¬length > 48 := by have := invariant.bounded; omega
  unfold update
  refine bind_result _ _ _ _ totalRead ?_
  rw [show (BitVec.ofNat 64 total).toNat = total from Nat.mod_eq_of_lt totalWord,
    if_neg (show ¬addressLimit ≤ total + view.length by omega)]
  refine bind_result _ _ _ _ stored ?_
  refine bind_result _ _ _ _ lengthRead ?_
  rw [if_neg notLong]
  exact body

theorem fill_verified (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (total length : Nat) (core : Core cells total) (bounded : length ≤ 48)
    (head : ∀ i < length, ByteAt cells (56 + i)) (more : 48 - length < view.length) :
    ∃ after index, fill source view length cells = .ok (after, index) ∧ Core after total ∧
      index < view.length ∧ (length = 0 → index = 0) ∧
      (0 < length → ∀ i < 48, ByteAt after (56 + i)) := by
  by_cases nonempty : length > 0
  · obtain ⟨copied, ran, copiedCore, newBytes, frame⟩ := copy_buffer source cells view bytes geometry represented
      total 0 length (48 - length) core (by omega) (by omega)
    have full : ∀ i < 48, ByteAt copied (56 + i) := by
      intro i inside
      by_cases old : i < length
      · simpa only [ByteAt, frame (56 + i) (Or.inl (by omega))] using head i old
      · have atIndex := newBytes (i - length) (by omega)
        have position : length + (i - length) = i := by omega
        simpa only [position] using atIndex
    have ready : Input.Ready .buffer copied :=
      ⟨WyhashBuffer.buffer_geometry 0 48 (by decide), full⟩
    obtain ⟨rounded, roundedRun, roundedCore, _, roundedFrame⟩ := round_verified .buffer 0 copied total copiedCore ready (by decide)
    let after := rounded.set 48 (word 0)
    have afterCore : Core after total := roundedCore.store_word 48 0 (by decide)
    refine ⟨after, 48 - length, ?_, afterCore, more, by omega, ?_⟩
    · rw [fill, if_pos nonempty]
      refine bind_result _ _ _ _ ran ?_
      refine bind_result _ _ _ _ roundedRun ?_
      refine bind_result _ _ _ _ (store_eq rounded 48 0 (by decide)) ?_
      rfl
    · intro _ i inside
      simpa only [after, ByteAt, Cells.lookup_set_other _ _ _ _ (by omega : 56 + i ≠ 48),
        roundedFrame (56 + i) (Or.inr (by omega))] using full i inside
  · refine ⟨cells, 0, by simp only [fill, if_neg nonempty], core, by omega, by simp, ?_⟩
    intro positive
    omega

/-- One induction for all complete source blocks. It returns the actual index,
retains the last full block, and frames the retained buffer for the short tail. -/
theorem loop_verified (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (total index : Nat) (core : Core cells total) (inside : index < view.length)
    (budget : view.length + 48 < addressLimit) :
    ∃ after stop, loop source view index cells = .ok (after, stop) ∧ Core after total ∧
      (∀ query, query < 16 ∨ 40 ≤ query → after.lookup query = cells.lookup query) ∧
      index ≤ stop ∧ stop < view.length ∧ view.length ≤ stop + 48 ∧ (stop = index ∨ 48 ≤ stop) := by
  rw [loop, if_neg (by omega : ¬addressLimit ≤ index + 48)]
  by_cases more : index + 48 < view.length
  · rw [if_pos more]
    have ready : Input.Ready (.external source view) cells :=
      ⟨geometry, fun i inside => ⟨bytes i, represented i inside⟩⟩
    obtain ⟨middle, ran, nextCore, _, frame⟩ := round_verified (.external source view) index cells total core ready (Nat.le_of_lt more)
    obtain ⟨after, stop, finished, finalCore, finalFrame, lower, upper, ended, _⟩ :=
      loop_verified source middle view bytes geometry represented total (index + 48) nextCore more budget
    refine ⟨after, stop, bind_result _ _ _ _ ran finished, finalCore, ?_, by omega, upper, ended, Or.inr (by omega)⟩
    intro query outside
    exact (finalFrame query outside).trans (frame query outside)
  · refine ⟨cells, index, by simp only [if_neg more], core, ?_, Nat.le_refl _, inside, by omega, Or.inl rfl⟩
    intro query _
    rfl
termination_by view.length - index
decreasing_by omega

theorem close_buffer (cells : Cells) (total length : Nat) (core : Core cells total)
    (budget : total < addressLimit) (bounded : length ≤ 48) (included : length ≤ total)
    (small : total ≤ 48 → length = total) (head : ∀ i < length, ByteAt cells (56 + i))
    (tail : 16 < total → length < 16 → ∀ i, 48 - (16 - length) ≤ i → i < 48 → ByteAt cells (56 + i)) :
    ∃ after, store cells 48 (BitVec.ofNat 64 length) = .ok after ∧ Invariant after total length := by
  refine ⟨cells.set 48 (word (BitVec.ofNat 64 length)), store_eq _ _ _ (by decide),
    ⟨?_, budget, Cells.lookup_set .., bounded, included, small, ?_, ?_⟩⟩
  · exact core.store_word 48 _ (by decide)
  · intro i inside
    simpa only [ByteAt, Cells.lookup_set_other _ _ _ _ (by omega : 56 + i ≠ 48)] using head i inside
  · intro long short i lower upper
    simpa only [ByteAt, Cells.lookup_set_other _ _ _ _ (by omega : 56 + i ≠ 48)] using tail long short i lower upper

/-- All native update paths preserve one invariant. The original input supplies
bytes and geometry; the caller-derived budgets discharge every arithmetic guard.
No successful read/write, post-round state or retained suffix is supplied. -/
theorem update_verified (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (total length : Nat) (invariant : Invariant cells total length)
    (sumBound : total + view.length < addressLimit) (inputBudget : view.length + 48 < addressLimit) :
    ∃ after buffered, update source view cells = .ok after ∧ Invariant after (total + view.length) buffered := by
  have totalValue : (BitVec.ofNat 64 total).toNat = total := Nat.mod_eq_of_lt invariant.totalBound
  have newValue : (BitVec.ofNat 64 (total + view.length)).toNat = total + view.length := Nat.mod_eq_of_lt sumBound
  have totalRead : nativeOps.read cells 5 = .ok (BitVec.ofNat 64 total) := read_slot _ 5 _ invariant.core.count
  let counted := cells.set 40 (word (BitVec.ofNat 64 (total + view.length)))
  have countedCore : Core counted (total + view.length) := by
    simpa only [↓reduceIte, newValue] using invariant.core.store_word 40 (BitVec.ofNat 64 (total + view.length)) (by decide)
  have lengthField : counted.lookup 48 = some (word (BitVec.ofNat 64 length)) := by
    simpa only [counted, Cells.lookup_set_other _ _ _ _ (by decide : 48 ≠ 40)] using invariant.lengthField
  have lengthRead := WyhashBuffer.readLength_verified counted length invariant.bounded lengthField
  have countedFrame (i : Nat) : counted.lookup (56 + i) = cells.lookup (56 + i) :=
    Cells.lookup_set_other _ _ _ _ (by omega)
  have oldHead : ∀ i < length, ByteAt counted (56 + i) := by
    intro i inside
    simpa only [ByteAt, countedFrame i] using invariant.head i inside
  have oldTail : 16 < total → length < 16 → ∀ i, 48 - (16 - length) ≤ i → i < 48 → ByteAt counted (56 + i) := by
    intro long short i lower upper
    simpa only [ByteAt, countedFrame i] using invariant.suffix long short i lower upper
  have body : ∃ after buffered, updateBody source view length counted = .ok after ∧
      Invariant after (total + view.length) buffered := by
    simp only [updateBody, remainder]
    by_cases fits : view.length ≤ 48 - length
    · rw [if_pos fits]
      obtain ⟨copied, copiedRun, copiedCore, newBytes, frame⟩ := copy_buffer source counted view bytes geometry represented
        (total + view.length) 0 length view.length countedCore (by omega) (by have := invariant.bounded; omega)
      have head : ∀ i < length + view.length, ByteAt copied (56 + i) := by
        intro i inside
        by_cases old : i < length
        · simpa only [ByteAt, frame (56 + i) (Or.inl (by omega))] using oldHead i old
        · have atIndex := newBytes (i - length) (by omega)
          have position : length + (i - length) = i := by omega
          simpa only [position] using atIndex
      have tail : 16 < total + view.length → length + view.length < 16 → ∀ i,
          48 - (16 - (length + view.length)) ≤ i → i < 48 → ByteAt copied (56 + i) := by
        intro long short i lower upper
        have oldLong : 16 < total := by
          by_cases long : 16 < total
          · exact long
          · have same := invariant.small (by omega)
            omega
        have retained := oldTail oldLong (by omega) i (by omega) upper
        simpa only [ByteAt, frame (56 + i) (Or.inr (by omega))] using retained
      obtain ⟨after, closed, final⟩ := close_buffer copied (total + view.length) (length + view.length) copiedCore sumBound
        (by have := invariant.bounded; omega) (by have := invariant.included; omega)
        (by intro small; have same := invariant.small (by omega); omega) head tail
      exact ⟨after, length + view.length, bind_result _ _ _ _ copiedRun closed, final⟩
    · rw [if_neg fits]
      have more : 48 - length < view.length := by omega
      obtain ⟨filled, start, fillRun, fillCore, startBound, noFill, full⟩ := fill_verified source counted view bytes
        geometry represented (total + view.length) length countedCore invariant.bounded oldHead more
      obtain ⟨rounded, index, loopRun, loopCore, loopFrame, lower, upper, ending, advanced⟩ :=
        loop_verified source filled view bytes geometry represented (total + view.length) start fillCore startBound inputBudget
      let remaining := view.length - index
      have remainingBound : remaining ≤ 48 := by dsimp only [remaining]; omega
      have suffix : ∃ retained,
          (if remaining < 16 ∧ index ≥ 48 then
            ByteSlice.copy source view (WyhashBuffer.buffer 0 48)
              (index - (16 - remaining)) (48 - (16 - remaining)) (16 - remaining) rounded
          else .ok rounded) = .ok retained ∧ Core retained (total + view.length) ∧
          (remaining < 16 → ∀ i, 48 - (16 - remaining) ≤ i → i < 48 → ByteAt retained (56 + i)) := by
        by_cases copyTail : remaining < 16 ∧ index ≥ 48
        · obtain ⟨retained, tailRun, tailCore, copied, _⟩ := copy_buffer source rounded view bytes geometry represented
            (total + view.length) (index - (16 - remaining)) (48 - (16 - remaining)) (16 - remaining) loopCore
            (by omega) (by omega)
          refine ⟨retained, by rw [if_pos copyTail]; exact tailRun, tailCore, ?_⟩
          intro _ i first last
          have atIndex := copied (i - (48 - (16 - remaining))) (by omega)
          have position : 48 - (16 - remaining) + (i - (48 - (16 - remaining))) = i := by omega
          simpa only [position] using atIndex
        · refine ⟨rounded, by rw [if_neg copyTail], loopCore, ?_⟩
          intro short i first last
          have nonempty : 0 < length := by
            by_cases positive : 0 < length
            · exact positive
            · have empty : length = 0 := by omega
              have zero := noFill empty
              omega
          simpa only [ByteAt, loopFrame (56 + i) (Or.inr (by omega))] using full nonempty i last
      obtain ⟨retained, suffixRun, suffixCore, retainedTail⟩ := suffix
      obtain ⟨copied, copiedRun, copiedCore, headBytes, copyFrame⟩ := copy_buffer source retained view bytes geometry represented
        (total + view.length) index 0 remaining suffixCore (by dsimp only [remaining]; omega) (by omega)
      have head : ∀ i < remaining, ByteAt copied (56 + i) := by
        simpa only [Nat.zero_add] using headBytes
      have tail : 16 < total + view.length → remaining < 16 → ∀ i,
          48 - (16 - remaining) ≤ i → i < 48 → ByteAt copied (56 + i) := by
        intro _ short i first last
        simpa only [ByteAt, copyFrame (56 + i) (Or.inr (by omega))] using retainedTail short i first last
      obtain ⟨after, closed, final⟩ := close_buffer copied (total + view.length) remaining copiedCore sumBound
        remainingBound (by dsimp only [remaining]; omega)
        (by intro small; have := invariant.included; have := invariant.bounded; omega) head tail
      refine ⟨after, remaining, ?_, final⟩
      refine bind_result _ _ (filled, start) after fillRun ?_
      refine bind_result _ _ (rounded, index) after loopRun ?_
      dsimp only
      split
      · rename_i selected
        refine bind_result _ _ retained after (by simpa only [remaining, if_pos selected] using suffixRun) ?_
        exact bind_result _ _ copied after copiedRun closed
      · rename_i selected
        refine bind_result _ _ retained after (by simpa only [remaining, if_neg selected] using suffixRun) ?_
        exact bind_result _ _ copied after copiedRun closed
  obtain ⟨after, buffered, bodyRun, final⟩ := body
  refine ⟨after, buffered, ?_, final⟩
  unfold update
  refine bind_result _ _ _ _ totalRead ?_
  rw [totalValue, if_neg (by omega : ¬addressLimit ≤ total + view.length)]
  refine bind_result _ _ _ _ (store_eq cells 40 (BitVec.ofNat 64 (total + view.length)) (by decide)) ?_
  refine bind_result _ _ _ _ lengthRead ?_
  rw [if_neg (by have := invariant.bounded; omega : ¬length > 48)]
  exact bodyRun

/-- The invariant immediately supplies the existing complete finalizer. Every
tail byte and lane comes from the reached cells; there is no supplied result. -/
theorem Invariant.final (invariant : Invariant cells total length) (long : 16 < total) :
    ∃ digest, WyhashBuffer.run cells = .ok digest := by
  obtain ⟨s0, h0⟩ := invariant.core.lanes 0
  obtain ⟨s1, h1⟩ := invariant.core.lanes 1
  obtain ⟨s2, h2⟩ := invariant.core.lanes 2
  have represented : WyhashLocal.Represents cells none none s0 s1 s2 (BitVec.ofNat 64 total) :=
    ⟨invariant.core.a, invariant.core.b, h0, h1, h2, invariant.core.count⟩
  have totalValue : (BitVec.ofNat 64 total).toNat = total := by
    exact Nat.mod_eq_of_lt invariant.totalBound
  have buffer : WyhashBuffer.Represents cells length (fun i => byteAt cells (56 + i)) := by
    constructor
    · intro i inside
      exact byteAt_lookup cells (56 + i) (invariant.head i inside)
    · intro short i lower upper
      exact byteAt_lookup cells (56 + i) (invariant.suffix long short i lower upper)
  exact ⟨_, WyhashBuffer.run_verified cells none none s0 s1 s2 (BitVec.ofNat 64 total) length
    (fun i => byteAt cells (56 + i)) invariant.core.valid represented invariant.lengthField
    invariant.bounded (by simpa only [totalValue] using long) buffer⟩

end Compiler.Extraction.WyhashUpdate
