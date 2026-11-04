/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryRecordFields

namespace Compiler.ZigAir.Memory

/-- Resolve a captured nominal record reference to its complete admitted field
view in the same heap. Identity/extent equality alone is insufficient: the live
allocation must contain the exact complete target subobject. This proof-side
check adds no native cast or branch and preserves the source's permissions. -/
def recordView (state : State) (target : Ty) (source : Value) : Except Fault Value := do
  let .pointer (.pointer writable many (.record name declared)) address := source | .error .unsupported
  let .aggregate identity captured _ := target | .error .unsupported
  if name ≠ identity ∨ declared ≠ captured then .error .unsupported else
  let some layout := target.layout | .error .unsupported
  let cell ← access state address layout false
  if !acceptsView cell.type address.offset target then .error .unsupported else
  .ok (.pointer (.pointer writable many target) address)

/-- A complete declaration in the live root allocation derives the nominal
view. Matching identity/extent alone does not supply this declaration. -/
theorem recordView_root (state : State) (id : Nat) (cell : Allocation) (name : String)
    (layout : Layout) (fields : List (Nat × Field)) (writable many : Bool)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = .aggregate name layout fields)
    (shaped : (Ty.aggregate name layout fields).layout = some layout) (positive : 0 < layout.bytes) :
    recordView state (.aggregate name layout fields) (.pointer (.pointer writable many (.record name layout)) ⟨id, 0⟩) =
      .ok (.pointer (.pointer writable many (.aggregate name layout fields)) ⟨id, 0⟩) := by
  have accessed := root_access state id cell layout false valid found (typed ▸ shaped) positive (by simp)
  have admitted : acceptsView cell.type 0 (.aggregate name layout fields) = true := by
    rw [typed]; exact acceptsView_self _
  simp only [recordView, ne_self_iff_false, or_self, ↓reduceIte, shaped, accessed, bind, Except.bind,
    admitted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem recordView_address (state : State) (target : Ty) (writable many : Bool)
    (name : String) (declared : Layout) (address : Address) (result : Value)
    (accepted : recordView state target (.pointer (.pointer writable many (.record name declared)) address) = .ok result) :
    result = .pointer (.pointer writable many target) address := by
  cases target with
  | aggregate identity captured fields =>
    simp only [recordView] at accepted
    split at accepted
    · contradiction
    · cases shaped : (Ty.aggregate identity captured fields).layout with
      | none => simp [shaped] at accepted
      | some layout =>
        simp only [shaped] at accepted
        cases accessed : access state address layout false with
        | error fault => simp [accessed, bind, Except.bind] at accepted
        | ok cell =>
          simp only [accessed, bind, Except.bind] at accepted
          split at accepted
          · contradiction
          · exact (Except.ok.inj accepted).symm
  | _ => simp [recordView] at accepted

theorem recordView_parent (state : State) (target : Ty) (writable many : Bool)
    (name : String) (declared : Layout) (address : Address) (result : Value)
    (accepted : recordView state target (.pointer (.pointer writable many (.record name declared)) address) = .ok result) :
    ∃ fields layout cell, target = .aggregate name declared fields ∧ target.layout = some layout ∧
      access state address layout false = .ok cell ∧ acceptsView cell.type address.offset target = true := by
  cases target with
  | aggregate identity captured fields =>
    simp only [recordView] at accepted
    split at accepted
    · contradiction
    · rename_i identities
      have same : name = identity ∧ declared = captured := by simpa using identities
      obtain ⟨rfl, rfl⟩ := same
      cases shaped : (Ty.aggregate name declared fields).layout with
      | none => simp [shaped] at accepted
      | some layout =>
        simp only [shaped] at accepted
        cases accessed : access state address layout false with
        | error fault => simp [accessed, bind, Except.bind] at accepted
        | ok cell =>
          simp only [accessed, bind, Except.bind] at accepted
          split at accepted
          · contradiction
          · rename_i typed
            exact ⟨fields, layout, cell, rfl, rfl, accessed, by simpa using typed⟩
  | _ => simp [recordView] at accepted

/-- A resolved record result retains the checked live parent, even when the
source value's pointer shape has not yet been exposed by its caller. -/
theorem recordView_result_parent (state : State) (target : Ty) (source : Value) (writable many : Bool) (address : Address)
    (accepted : recordView state target source = .ok (.pointer (.pointer writable many target) address)) :
    ∃ layout cell, target.layout = some layout ∧ access state address layout false = .ok cell ∧
      acceptsView cell.type address.offset target = true := by
  cases source with
  | pointer sourceType sourceAddress =>
    cases sourceType with
    | pointer sourceWritable sourceMany child =>
      cases child with
      | record name declared =>
        have linked := recordView_address state target sourceWritable sourceMany name declared sourceAddress _ accepted
        have same : address = sourceAddress := congrArg (fun value => match value with
          | .pointer _ result => result
          | _ => ⟨0, 0⟩) linked
        subst address
        obtain ⟨_, layout, cell, _, shaped, accessed, declared⟩ :=
          recordView_parent state target sourceWritable sourceMany name declared sourceAddress _ accepted
        exact ⟨layout, cell, shaped, accessed, declared⟩
      | _ => simp [recordView] at accepted
    | _ => simp [recordView] at accepted
  | _ => simp [recordView] at accepted

end Compiler.ZigAir.Memory
