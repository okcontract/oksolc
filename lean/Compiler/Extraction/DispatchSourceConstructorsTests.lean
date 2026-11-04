/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchDebugEffects
import Compiler.Extraction.InternerConstructorEnclosingInduction

namespace Compiler.Extraction.Dispatch.Effects.SourceTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

local instance : MonadLift (Except Interner.Error) (Except Interner.Error) where
  monadLift value := value

def equality : Effects (Except Interner.Error) (Except Interner.Error) where
  related := Eq
  pure := fun _ => rfl
  bind := fun paired next => by rw [paired]; congr; funext value; exact next value
  lift := fun _ => rfl

def slice : Storage.ArgumentSlice := ⟨37, [3, 4]⟩
def reads : Reads :=
  { constant := fun _ => .ok none
    operation := fun id opcode => if id == 9 && opcode == opXOR then .ok (some slice) else .ok none }

def logical : Associative.Constructors Unit (Except Interner.Error) :=
  { operation := fun _ _ _ => .ok 7, constant := fun _ _ => .ok 7, materialize := fun _ _ _ => .ok 7 }

/-- An intentionally partial child: only query-backed storage is accepted.
Scalar and logical results agree, but arbitrary native addresses do not. -/
def physical : Associative.Constructors Unit (Except Interner.Error) :=
  { logical with
    borrowedOperation := fun address _ ids _ =>
      if address = slice.address ∧ ids = slice.items then .ok 7 else .error .unsupported
    localOperation := fun _ source selected _ _ _ =>
      if source = slice ∧ selected < 2 then .ok 7 else .error .unsupported }

theorem source_coupled : SourceConstructors equality reads physical logical := by
  refine ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, ?_, ?_⟩
  · intro id queried source found opcode debug
    simp only [reads] at found
    split at found
    · cases found; simp [equality, physical, logical]
    · cases found
  · intro id opcode source found shape selected bounded repeated first debug
    simp only [reads] at found
    split at found
    · cases found; simp [equality, physical, logical, bounded, localBuilder]
    · cases found

theorem arbitrary_borrow_rejected : ¬ Constructors equality physical logical := by
  intro all
  have wrong := all.borrowedOperation 0 opEQ slice.items ()
  simp [equality, physical, logical, slice] at wrong

theorem read_bind : ReadBind equality := by
  constructor
  intro α β result nextLeft nextRight paired
  cases result with
  | ok value => exact paired value rfl
  | error error => cases error <;> rfl

/-- The complete shared dispatcher consumes the weaker relation. The XOR query
can feed EQ construction: source opcode and requested opcode are independent. -/
theorem dispatch :
    simplifyWithInputs reads physical 64 opISZERO [9] () logicalOperand 0 =
      Dispatch.simplify reads logical 64 opISZERO [9] () := by
  apply simplify_with_inputs equality read_bind reads logicalOperand
    ⟨fun _ _ _ _ _ _ _ => rfl⟩ source_coupled 64 opISZERO [9] () 0
  intro _ _ _; rfl

theorem dispatch_success : simplifyWithInputs reads physical 64 opISZERO [9] () logicalOperand 0 = .ok (some 7) := by
  rw [dispatch]
  rfl

/-- The current debug value is admitted, while unrelated values are rejected.
The source-backed slice behavior is inherited from the existing fixture. -/
def physicalDebug : Associative.Constructors Bool (Except Interner.Error) where
  operation := fun opcode ids debug => if debug then physical.operation opcode ids () else .error .unsupported
  constant := fun value debug => if debug then physical.constant value () else .error .unsupported
  materialize := fun id value debug => if debug then physical.materialize id value () else .error .unsupported
  borrowedOperation := fun address opcode ids debug =>
    if debug then physical.borrowedOperation address opcode ids () else .error .unsupported
  localOperation := fun opcode source selected repeated first debug =>
    if debug then physical.localOperation opcode source selected repeated first () else .error .unsupported

def logicalDebug : Associative.Constructors Bool (Except Interner.Error) :=
  { operation := fun _ _ _ => .ok 7, constant := fun _ _ => .ok 7, materialize := fun _ _ _ => .ok 7 }

theorem current_debug : SourceConstructorsAt equality reads true physicalDebug logicalDebug := by
  change SourceConstructors equality reads physical logical
  exact source_coupled

theorem other_debug_rejected : ¬ SourceConstructors equality reads physicalDebug logicalDebug := by
  intro all
  have wrong := all.constant 0 false
  simp [equality, physicalDebug, logicalDebug] at wrong

theorem dispatch_current_debug :
    simplifyWithInputs reads physicalDebug 64 opISZERO [9] true logicalOperand 0 =
      Dispatch.simplify reads logicalDebug 64 opISZERO [9] true := by
  exact simplify_with_inputs_at equality read_bind reads logicalOperand
    ⟨fun _ _ _ _ _ _ _ => rfl⟩ true current_debug 64 opISZERO [9] 0 (fun _ _ _ => rfl)

theorem current_debug_success :
    simplifyWithInputs reads physicalDebug 64 opISZERO [9] true logicalOperand 0 = .ok (some 7) := by
  rw [dispatch_current_debug]
  rfl

end Compiler.Extraction.Dispatch.Effects.SourceTests
