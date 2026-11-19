/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeSignExtendDispatch
import Compiler.Extraction.InternerNativeDivisionTests
import Compiler.Extraction.DispatchSignExtendTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeSignExtendTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open NativeAlgebraicTests

def innerOp (shifted : Bool) : Folding.Op := if shifted then .shr else .signextend

/-- The new case reads a queried operand after a recursive constant child.
The alternate query exercises two ordered loads before SAR construction. -/
def reads (shifted : Bool) (outer inner : Word) (items : List NodeId := [1, 2]) : Nested.Reads where
  constant := fun id => .ok (if id = 4 then some outer else if id = 1 then some inner else none)
  operation := fun id opcode => .ok (if id = 3 ∧ opcode = (innerOp shifted).opcode then some ⟨17, items⟩ else none)

def fixture (memory : Session Nat) (shifted : Bool) (outer inner base : Word) : World Nat :=
  ⟨{ read := fun id => some (if id = 1 then inner else if id = 2 then base
      else if id = 3 then (innerOp shifted).value inner base 0 else if id = 4 then outer else 0),
     table := fun _ => none }, memory⟩

theorem fixture_valid (meaning : Meaning) (memory : Session Nat) (shifted : Bool) (outer inner base : Word) :
    Interner.Invariant meaning (fixture memory shifted outer inner base).graph := by
  constructor
  · intro key id found
    cases found
  · trivial

theorem reads_sound (other : Meaning) (memory : Session Nat) (shifted : Bool) (outer inner base : Word) :
    Nested.Sound (ArithmeticShift.meaning other) (fixture memory shifted outer inner base).graph.read (reads shifted outer inner) := by
  constructor
  · intro id word found
    by_cases left : id = 4
    · subst id
      have same : outer = word := by simpa [reads] using found
      exact same ▸ rfl
    · by_cases index : id = 1
      · subst id
        have same : inner = word := by simpa [reads] using found
        exact same ▸ rfl
      · simp only [reads, left, index, ↓reduceIte] at found
        cases found
  · intro id opcode slice found
    by_cases selected : id = 3 ∧ opcode = (innerOp shifted).opcode
    · obtain ⟨rfl, rfl⟩ := selected
      have same : (⟨17, [1, 2]⟩ : Storage.ArgumentSlice) = slice := by simpa [reads] using found
      subst slice
      refine ⟨0, [inner, base], (innerOp shifted).value inner base 0, rfl, rfl, ?_⟩
      cases shifted <;> exact Folding.word_meaning_operation (ArithmeticShift.shiftMeaning other) _ 0 [inner, base]
    · simp only [reads, selected, ↓reduceIte] at found
      cases found
  · intro left right a b equal lhs rhs
    simp only [Nested.sameExpression, reads, beq_iff_eq] at equal
    subst right
    exact Option.some.inj (lhs.symm.trans rhs)

/-- Reuse the existing state-changing load, with an optional failure at the
actual queried index. Later initializers and children must then stop. -/
def loading (failureIndex : Option Nat) : Nested.OperandRead (GraphAction Nat) :=
  fun source index annotation before =>
    if failureIndex = some index then (.error (.language .outOfMemory), before.mapEffects Nat.succ)
    else NativeUnaryTests.loading source index annotation before

theorem inputs (meaning : Meaning) (queries : Nested.Reads) (failureIndex : Option Nat)
    (before : World Nat) (valid : ready before ∧ Interner.Invariant meaning before.graph) :
    Dispatch.UnaryPreservation.Inputs (Semantic.builderLogic meaning ready) queries (loading failureIndex) before := by
  intro id opcode source found index annotation item
  change Semantic.NativeSafe meaning ready (loading failureIndex source index annotation) before
    (fun loaded _ => loaded = annotation)
  by_cases failed : failureIndex = some index
  all_goals
    simp only [Semantic.NativeSafe, loading, failed, ↓reduceIte]
    exact fun _ => ⟨valid.1, valid.2, fun _ _ same => same, by trivial⟩

theorem operation_rule (meaning : Meaning) (op : Folding.Op) :
    Dispatch.Preservation.OperationRule (Semantic.builderLogic meaning ready) children () op := by
  intro ids values value before valid actual evaluated
  exact fun _ => ⟨valid.1, valid.2, fun _ _ same => same, trivial⟩

theorem sar_rule (meaning : Meaning) :
    Dispatch.Preservation.SarRule (Semantic.builderLogic meaning ready) children () := by
  intro left right amount value before valid lhs rhs
  exact fun _ => ⟨valid.1, valid.2, fun _ _ same => same, trivial⟩

theorem nested_outcome (before : World Nat) (fail : Bool) :
    (Dispatch.simplifyWithInputs (reads false 1 0) children 64 Dispatch.opSIGNEXTEND [4, 3] ()
      (loading (if fail then some 1 else none)) 0) before =
      (.error (.language .outOfMemory), if fail then (before.mapEffects Nat.succ).mapEffects Nat.succ
        else ((before.mapEffects Nat.succ).mapEffects Nat.succ).mapEffects Nat.succ) := by
  cases fail <;> rfl

theorem first_child_oom (before : World Nat) :
    (Dispatch.simplifyWithInputs (reads false 7 2) children 64 Dispatch.opSIGNEXTEND [4, 3] () (loading (some 1)) 0) before =
      (.error (.language .outOfMemory), before.mapEffects Nat.succ) := rfl

theorem sar_outcome (before : World Nat) (fail : Option Bool) :
    (Dispatch.simplifyWithInputs (reads true 0 248) children 64 Dispatch.opSIGNEXTEND [4, 3] ()
      (loading (fail.map (fun second => if second then 1 else 0))) 0) before =
      (.error (.language .outOfMemory), match fail with
        | some false => before.mapEffects Nat.succ
        | some true => (before.mapEffects Nat.succ).mapEffects Nat.succ
        | none => ((before.mapEffects Nat.succ).mapEffects Nat.succ).mapEffects Nat.succ) := by
  cases fail with
  | none => rfl
  | some second => cases second <;> rfl

theorem large_index_keeps_right (before : World Nat) :
    (Dispatch.simplifyWithInputs (reads true 31 0) children 64 Dispatch.opSIGNEXTEND [4, 3] () (loading (some 0)) 0) before =
      (.ok (some 3), before) := rfl

theorem malformed_miss (before : World Nat) :
    (Dispatch.simplifyWithInputs (reads false 2 0 [1]) children 64 Dispatch.opSIGNEXTEND [4, 3] () (loading (some 1)) 0) before =
      (.ok none, before) := rfl

def indexFailure (error : Storage.ReadError) : Nested.Reads :=
  { reads false 1 0 with constant := fun id => if id = 1 then .error error else .ok (if id = 4 then some 1 else none) }

theorem index_read_failure (before : World Nat) (error : Storage.ReadError) :
    (Dispatch.simplifyWithInputs (indexFailure error) children 64 Dispatch.opSIGNEXTEND [4, 3] () (loading none) 0) before =
      (.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before) := by
  cases error <;> rfl

/-- This callback probe checks the reached private state as well as address,
index and argument order, starting its observation counter at zero. It makes
no word-preservation claim for the probe. -/
theorem forwarded_after_constant (before : World Nat) :
    (Dispatch.simplifyWithInputs (reads false 1 0)
      { children with operation := fun opcode ids _ world =>
          (if opcode = Dispatch.opSIGNEXTEND ∧ ids = [0, 2] then .ok 0 else .error .missingHandle, world.mapEffects Nat.succ) }
      64 Dispatch.opSIGNEXTEND [4, 3] ()
      (fun source index annotation world =>
        if world.memory.effects = 1 ∧ source.address = 17 ∧ index = 1 ∧ annotation = 2
        then NativeUnaryTests.loading source index annotation world else (.error .missingHandle, world)) 0) (before.mapEffects (fun _ => 0)) =
      (.ok (some 0), (((before.mapEffects (fun _ => 0)).mapEffects Nat.succ).mapEffects Nat.succ).mapEffects Nat.succ) := rfl

theorem preserved (other : Meaning) (memory : Session Nat) (shifted : Bool) (outer inner base : Word)
    (failureIndex : Option Nat) :
    let before := fixture memory shifted outer inner base
    let ran := (Dispatch.simplifyWithInputs (reads shifted outer inner) children 64 Dispatch.opSIGNEXTEND [4, 3] () (loading failureIndex) 0) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (ArithmeticShift.meaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some (Folding.Op.signextend.value outer ((innerOp shifted).value inner base 0) 0)) := by
  exact NativeRecursion.signextend_dispatch_verified other (reads shifted outer inner) children 64 4 3 ()
    (fixture memory shifted outer inner base) ready rfl (fixture_valid _ memory shifted outer inner base)
    (rules _) (operation_rule _ _) (sar_rule _) (reads_sound other memory shifted outer inner base) outer _ rfl rfl
    (loading failureIndex) 0 (inputs _ _ failureIndex)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeSignExtendTests
