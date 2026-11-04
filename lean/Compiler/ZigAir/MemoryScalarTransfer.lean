/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryInvalidation

namespace Compiler.ZigAir.Memory

/-- Transfer one scalar's initialization state between declared local objects.
Missing storage remains missing; this is not an evaluated scalar read and does
not supply a value to arithmetic. Heap access/permissions are checked by callers
that use these local cells through a pointer. No pointer or aggregate copy is
admitted. Existing evaluated reads still reject every missing leaf. -/
def Cells.transferScalar (source : Cells) (sourceOwner : Ty) (sourceOffset : Nat)
    (target : Cells) (targetOwner : Ty) (targetOffset : Nat) (type : Scalar.Ty) : Except Fault Cells := do
  if leafType sourceOwner sourceOffset ≠ some (.scalar type) ∨
      leafType targetOwner targetOffset ≠ some (.scalar type) ∨
      !acceptsView targetOwner targetOffset (.scalar type) then .error .unsupported else
  let some layout := (Ty.scalar type).layout | .error .unsupported
  if layout.bytes = 0 then .error .unsupported else
  match source.readLeaf sourceOwner sourceOffset (.scalar type) with
  | .ok value => target.write targetOwner targetOffset value
  | .error .uninitialized => .ok (target.forget targetOffset layout.bytes)
  | .error fault => .error fault

/-- Initialization transfer retains validity in both the defined and absent
cases by reusing the ordinary writer and invalidation rules. -/
theorem Cells.transferScalar_valid (source target after : Cells) (sourceOwner targetOwner : Ty)
    (sourceOffset targetOffset : Nat) (type : Scalar.Ty)
    (valid : target.valid targetOwner = true)
    (ran : source.transferScalar sourceOwner sourceOffset target targetOwner targetOffset type = .ok after) :
    after.valid targetOwner = true := by
  unfold Cells.transferScalar at ran
  split at ran
  · contradiction
  · cases shaped : (Ty.scalar type).layout with
    | none => simp [shaped] at ran
    | some layout =>
      simp only [shaped] at ran
      split at ran
      · contradiction
      · cases read : source.readLeaf sourceOwner sourceOffset (.scalar type) with
        | ok value => exact Cells.write_preserves_valid _ _ _ _ _ valid (by simpa only [read] using ran)
        | error fault =>
          cases fault <;> simp only [read] at ran
          all_goals try contradiction
          cases Except.ok.inj ran
          exact Cells.forget_valid _ _ _ _ valid

/-- A valid declared source leaf contains a typed value or is absent. The latter
is preserved by transfer rather than converted into a fabricated scalar. -/
theorem Cells.lookup_typed (cells : Cells) (owner : Ty) (offset : Nat) (wanted : Ty)
    (valid : cells.valid owner = true) (declared : leafType owner offset = some wanted) :
    ∀ value, cells.lookup offset = some value → value.hasType wanted = true := by
  intro value found
  obtain ⟨entry, present, same⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_find?_eq_some present
  have atOffset : entry.1 = offset := by simpa using List.find?_some present
  simp only [Cells.valid, Bool.and_eq_true] at valid
  have fit := List.all_eq_true.mp valid.1 entry member
  simp only [leafFits, Bool.and_eq_true, decide_eq_true_eq] at fit
  have typed : entry.2.type = wanted := Option.some.inj (fit.1.symm.trans (atOffset ▸ declared))
  simpa only [← same, Value.hasType, typed, decide_true, Bool.true_and] using fit.2

/-- A single scalar transfer has the same result as set/forget on the existing
sparse representation; checked geometry and source validity derive the result. -/
theorem Cells.transferScalar_eq (source target : Cells) (sourceOwner targetOwner : Ty)
    (sourceOffset targetOffset : Nat) (type : Scalar.Ty) (layout : Layout)
    (valid : source.valid sourceOwner = true)
    (sourceDeclared : leafType sourceOwner sourceOffset = some (.scalar type))
    (targetDeclared : leafType targetOwner targetOffset = some (.scalar type))
    (view : acceptsView targetOwner targetOffset (.scalar type) = true)
    (shaped : (Ty.scalar type).layout = some layout) (positive : 0 < layout.bytes) :
    source.transferScalar sourceOwner sourceOffset target targetOwner targetOffset type = .ok
      (match source.lookup sourceOffset with
       | none => target.forget targetOffset layout.bytes
       | some value => target.set targetOffset value) := by
  have checks : ¬(leafType sourceOwner sourceOffset ≠ some (.scalar type) ∨
      leafType targetOwner targetOffset ≠ some (.scalar type) ∨ !acceptsView targetOwner targetOffset (.scalar type)) := by
    simp [sourceDeclared, targetDeclared, view]
  simp only [Cells.transferScalar, if_neg checks, shaped, if_neg (by omega : layout.bytes ≠ 0)]
  cases found : source.lookup sourceOffset with
  | none => simp [Cells.readLeaf, sourceDeclared, found]
  | some value =>
    have typed := Cells.lookup_typed source sourceOwner sourceOffset (.scalar type) valid sourceDeclared value found
    have parts : value.type = .scalar type ∧ value.valid = true := by
      simpa only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] using typed
    have same := parts.1
    have single : value.leaves targetOffset = [(targetOffset, value)] := by
      cases value with
      | scalar | optionalScalar | optionalObject | pointer => rfl
      | slice ty address length =>
        change ty = .scalar type at same
        subst ty
        have impossible : false = true := parts.2
        contradiction
    have written := Cells.write_single target targetOwner targetOffset value parts.2 (same ▸ view)
      (by simp [leafFits, targetDeclared, same, parts.2]) single
    simpa only [Cells.readLeaf, sourceDeclared, ne_self_iff_false, ↓reduceIte, found, typed] using written

end Compiler.ZigAir.Memory
