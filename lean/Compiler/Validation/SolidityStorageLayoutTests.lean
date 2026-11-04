/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorageSource

namespace Compiler.Validation.SolidityStorage.LayoutTests
open Contract.Evm Contract.Interaction

def mixed : Layout := [⟨"a", .boolean⟩, ⟨"b", .boolean⟩,
  ⟨"word", .word⟩, ⟨"c", .boolean⟩]

theorem declaration_order_packing :
    (List.range 4).map (fun i => (mixed.locate i).map Prod.snd) =
      [some ⟨0, 0⟩, some ⟨0, 1⟩, some ⟨1, 0⟩, some ⟨2, 0⟩] := by decide

theorem byte_boundary :
    (Location.allocate ⟨7, 31⟩ .boolean).2 = ⟨8, 0⟩ ∧
    (Location.allocate ⟨7, 31⟩ .word).1 = ⟨8, 0⟩ := by decide

theorem word_layout_compatibility (names : List String) (cursor index : Nat) :
    (Layout.words names).locateFrom ⟨cursor, 0⟩ index =
      (names[index]?).map (fun name => (⟨name, .word⟩, ⟨cursor + index, 0⟩)) := by
  induction names generalizing cursor index with
  | nil => simp [Layout.words, Layout.locateFrom]
  | cons name rest ih =>
    cases index with
    | zero => simp [Layout.words, Layout.locateFrom, Location.allocate]
    | succ index =>
      simpa [Layout.words, Layout.locateFrom, Location.allocate, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih (cursor + 1) index

def dirty : Stateful.Slots := fun _ => 0xabcdef0200

theorem noncanonical_storage_byte_normalizes :
    mixed.read "a" dirty = 0 ∧ mixed.read "b" dirty = 1 := by decide

theorem packed_writes_preserve_neighbors :
    ((mixed.write 0 1 dirty).map fun cells => [cells 0, cells 1]) =
      some [0xabcdef0201, 0xabcdef0200] ∧
    ((mixed.write 1 0 dirty).map fun cells => [cells 0, cells 1]) =
      some [0xabcdef0000, 0xabcdef0200] := by decide

theorem absent_field_rejected : mixed.write 4 0 dirty = none := rfl

def receiver : Receive := { body := [.branch (.not (.boolean (.input "a"))) [.revert] []] }
def source : ContractSource := { variables := mixed, functions := [], receive := some receiver }

attribute [local simp] select outcome emptyOutcome source receiver Receive.result bodyResult
  statements statement Condition.eval expression mixed locals Layout.write Layout.read
  Layout.names Layout.locate Layout.locateFrom Location.allocate Variable.read
  PackedBool.read PackedBool.encode PackedBool.mask SolidityWord.Expr.evalChecked dirty

theorem empty_receive_guard :
    outcome source {} dirty false = .reverted [] ∧
    outcome source {} (fun _ => 1) true = .returned [] (fun _ => 1) := by
  constructor <;> simp +decide

theorem receive_is_payable :
    outcome source { value := 123 } (fun _ => 1) false = .returned [] (fun _ => 1) := by
  simp +decide

theorem short_data_does_not_select_receive :
    outcome source { calldata := [0] } (fun _ => 1) false = .reverted [] ∧
    outcome source { calldata := [0, 0, 0] } (fun _ => 1) false = .reverted [] := by
  constructor <;> simp +decide

theorem unknown_selector_does_not_select_receive :
    outcome source { calldata := [0, 0, 0, 0] } (fun _ => 1) false = .reverted [] := by
  simp +decide

theorem bool_static_write_faults :
    (Receive.result mixed { body := [.assignBool 0 (.literal true)] } {} dirty true) = .fault := by
  simp +decide

theorem bare_return_skips_revert :
    (Receive.result mixed { body := [.stop, .revert] } {} dirty false) = .returned [] dirty := by
  simp +decide

theorem revert_discards_written_state :
    (Receive.result mixed { body := [.assignBool 0 (.literal true), .revert] } {} dirty false) = .reverted [] := by
  simp +decide

end Compiler.Validation.SolidityStorage.LayoutTests
