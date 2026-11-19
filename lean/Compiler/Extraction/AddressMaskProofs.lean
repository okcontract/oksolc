/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AddressMaskProgram

namespace Compiler.Extraction.AddressMask
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul
set_option linter.unusedSimpArgs false

private theorem pure_ok (value : α) : (pure value : Except ReadError α) = .ok value := rfl
private theorem bind_ok (value : α) (next : α → Except ReadError β) :
    ((.ok value : Except ReadError α) >>= next) = next value := rfl
private theorem bind_error (error : ReadError) (next : α → Except ReadError β) :
    ((.error error : Except ReadError α) >>= next) = .error error := rfl
attribute [local simp] pure_ok bind_ok bind_error

theorem native_mask : nativeMask = mask := rfl

theorem native_mask_subtraction :
    Folding.Zig.checkedSub (((1 : Word) <<< 160).toNat) 1 = .ok nativeMask.toNat := by rfl

theorem supported_opcode (opcode : Opcode) :
    opcode ∈ addressOpcodes ↔ ∃ kind : Kind, opcode = kind.opcode := by
  constructor
  · intro member
    simp only [addressOpcodes, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨.address, rfl⟩
    · exact ⟨.caller, rfl⟩
    · exact ⟨.origin, rfl⟩
    · exact ⟨.coinbase, rfl⟩
  · rintro ⟨kind, rfl⟩
    cases kind <;> decide

/-- An earlier probe completed normally without a zero-argument match. Faults
cannot be skipped, and a successful earlier match cannot be overwritten. -/
def Skipped (reads : Reads) (id : NodeId) (opcode : Opcode) : Prop :=
  ∃ option, reads.operation id opcode = .ok option ∧
    ∀ slice, option = some slice → slice.items ≠ []

theorem search_found (reads : Reads) (id : NodeId) (opcodes : List Opcode) (opcode : Opcode)
    (found : search reads id opcodes = .ok (some opcode)) :
    ∃ earlierOpcodes suffix slice, opcodes = earlierOpcodes ++ opcode :: suffix ∧
      (∀ earlier ∈ earlierOpcodes, Skipped reads id earlier) ∧
      reads.operation id opcode = .ok (some slice) ∧ slice.items = [] := by
  induction opcodes with
  | nil => simp [search] at found
  | cons head tail ih =>
    cases lookup : reads.operation id head with
    | error error => simp [search, lookup] at found
    | ok option =>
      have advance (miss : Skipped reads id head) (next : search reads id tail = .ok (some opcode)) :
          ∃ earlierOpcodes suffix slice, head :: tail = earlierOpcodes ++ opcode :: suffix ∧
            (∀ earlier ∈ earlierOpcodes, Skipped reads id earlier) ∧
            reads.operation id opcode = .ok (some slice) ∧ slice.items = [] := by
        obtain ⟨earlierOpcodes, suffix, slice, same, skipped, actual, empty⟩ := ih next
        refine ⟨head :: earlierOpcodes, suffix, slice, by simp [same], ?_, actual, empty⟩
        intro earlier member
        rcases List.mem_cons.mp member with rfl | member
        · exact miss
        · exact skipped earlier member
      cases option with
      | none =>
        apply advance ⟨none, lookup, by simp⟩
        simpa [search, lookup] using found
      | some slice =>
        by_cases empty : slice.items = []
        · simp [search, lookup, empty] at found
          subst opcode
          exact ⟨[], tail, slice, rfl, by simp, lookup, empty⟩
        · apply advance ⟨some slice, lookup, by intro other same; cases same; exact empty⟩
          simpa [search, lookup, empty] using found

theorem address_found (reads : Reads) (id maskId : NodeId) (opcode : Opcode)
    (found : addressInstruction reads id maskId = .ok (some opcode)) :
    reads.constant maskId = .ok (some mask) ∧ opcode ∈ addressOpcodes ∧
      ∃ slice, reads.operation id opcode = .ok (some slice) ∧ slice.items = [] := by
  cases lookup : reads.constant maskId with
  | error error => simp [addressInstruction, lookup] at found
  | ok option =>
    by_cases correct : option = some nativeMask
    · subst option
      have next : search reads id addressOpcodes = .ok (some opcode) := by
        simpa [addressInstruction, lookup] using found
      obtain ⟨earlierOpcodes, suffix, slice, same, _, actual, empty⟩ := search_found reads id addressOpcodes opcode next
      refine ⟨by simp only [native_mask], ?_, slice, actual, empty⟩
      rw [same]
      simp
    · simp [addressInstruction, lookup, correct] at found

theorem found_sound (env : Environment) (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (meaning env other) read reads) (id maskId : NodeId) (opcode : Opcode)
    (found : addressInstruction reads id maskId = .ok (some opcode)) :
    ∃ kind : Kind, opcode = kind.opcode ∧ read maskId = some mask ∧ read id = some (kind.value env) := by
  obtain ⟨maskFound, member, slice, lookup, empty⟩ := address_found reads id maskId opcode found
  obtain ⟨kind, rfl⟩ := (supported_opcode opcode).mp member
  obtain ⟨sequence, values, value, arguments, actual, denotation⟩ := sound.operation id kind.opcode slice lookup
  have noArgs : values = [] := by simpa [empty, readArguments] using arguments.symm
  subst values
  rw [address_operation] at denotation
  have same : kind.value env = value := Option.some.inj denotation
  exact ⟨kind, rfl, sound.constant maskId mask maskFound, same ▸ actual⟩

theorem search_total (reads : Reads) (id : NodeId) (opcodes : List Opcode)
    (total : ∀ opcode ∈ opcodes, ∃ result, reads.operation id opcode = .ok result) :
    ∃ result, search reads id opcodes = .ok result := by
  induction opcodes with
  | nil => exact ⟨none, rfl⟩
  | cons head tail ih =>
    obtain ⟨option, lookup⟩ := total head (by simp)
    obtain ⟨result, next⟩ := ih (by intro opcode member; exact total opcode (by simp [member]))
    cases option with
    | none => exact ⟨result, by simp [search, lookup, next]⟩
    | some slice =>
      by_cases empty : slice.items = []
      · exact ⟨some head, by simp [search, lookup, empty]⟩
      · exact ⟨result, by simp [search, lookup, empty, next]⟩

theorem storage_total (model : Meaning) (cells : List Cell) (coherent : Coherent model cells)
    (id maskId : NodeId) : ∃ result, addressInstruction (storageReads cells) id maskId = .ok result := by
  have lookup := constant_correct cells maskId
  obtain ⟨result, next⟩ := search_total (storageReads cells) id addressOpcodes
    (by intro opcode _; exact operation_no_fault model cells coherent id opcode)
  unfold addressInstruction
  change ∃ result, (do
    if (← constantProgram.run cells maskId) != some nativeMask then return none
    search (storageReads cells) id addressOpcodes) = .ok result
  rw [lookup]
  simp only [bind_ok]
  split
  · exact ⟨none, rfl⟩
  · exact ⟨result, next⟩

def Constructs (env : Environment) (other : Meaning) (build : OperationBuilder Debug) : Prop :=
  ∀ (kind : Kind) debug before, Invariant (meaning env other) before →
    Safe (meaning env other) (build kind.opcode [] debug) before
      (fun id after => after.read id = some (kind.value env))

theorem interner_constructs (env : Environment) (other : Meaning) (p : Primitives)
    (contracts : Contracts (meaning env other) p) :
    Constructs env other (internerBuilder p : OperationBuilder Debug) := by
  intro kind debug before valid
  apply find_safe _ p contracts _ before _ valid
  change (meaning env other).operation kind.opcode 0 [] = some (kind.value env)
  exact address_operation env other kind 0 []

/-- The dispatcher's successful address-mask case can use the actual extracted
native operation constructor. The environment is fixed across its old sequence
and the constructor's default sequence; other instructions retain their epochs. -/
theorem interner_rebuild_safe (env : Environment) (other : Meaning) (p : Primitives)
    (contracts : Contracts (meaning env other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (meaning env other) before) (sound : Sound (meaning env other) before.read reads)
    (id maskId : NodeId) (opcode : Opcode) (value maskValue : Word) (debug : Debug)
    (valueRead : before.read id = some value) (maskRead : before.read maskId = some maskValue)
    (found : addressInstruction reads id maskId = .ok (some opcode)) :
    Safe (meaning env other) (internerBuilder p opcode [] debug) before
      (fun result after => after.read result = some (value &&& maskValue)) := by
  obtain ⟨kind, rfl, maskFound, valueFound⟩ := found_sound env other before.read reads sound id maskId opcode found
  have valueSame : value = kind.value env := Option.some.inj (valueRead.symm.trans valueFound)
  have maskSame : maskValue = mask := Option.some.inj (maskRead.symm.trans maskFound)
  rw [valueSame, maskSame, (kind_mask env kind).1]
  exact interner_constructs env other p contracts kind debug before valid

end Compiler.Extraction.AddressMask
