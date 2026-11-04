/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Control

/-! Checked finite projections for proofs about generated loop bodies. No
instruction is erased: a backedge or loop makes the projection fail. Selecting
a block is syntactic lookup; clients must prove its place in the generated
program rather than treating an identifier as a control-flow certificate. -/
namespace Compiler.ZigAir.Control

def Code.finite? : Code Ty Prim Ref true → Option (Code Ty Prim Ref)
  | .bind id ty prim next => do return .bind id ty prim (← next.finite?)
  | .branch ref yes no => do return .branch ref (← yes.finite?) (← no.finite?)
  | .block id ty body next => do return .block id ty (← body.finite?) (← next.finite?)
  | .jump target ref => some (.jump target ref)
  | .ret ref => some (.ret ref)
  | .loop .. | .repeat .. => none

def Code.block? (target : Nat) : Code Ty Prim Ref loops → Option (Code Ty Prim Ref loops)
  | .bind _ _ _ next => next.block? target
  | .branch _ yes no => (yes.block? target).or (no.block? target)
  | .block id ty body next => if target = id then some (.block id ty body next)
      else (body.block? target).or (next.block? target)
  | .loop _ _ body => body.block? target
  | .jump .. | .ret .. | .repeat .. => none

def Code.blockBody? (target : Nat) (code : Code Ty Prim Ref loops) : Option (Code Ty Prim Ref loops) := do
  match ← code.block? target with
  | .block _ _ body _ => some body
  | _ => none

/-- Split a leading sequence of bindings for compositional symbolic execution.
Stop at the first control instruction; no branch or loop is crossed. -/
def Code.dropBindings : Nat → Code Ty Prim Ref loops → Code Ty Prim Ref loops
  | 0, code => code
  | n + 1, .bind _ _ _ next => next.dropBindings n
  | _ + 1, code => code

def Code.prefixBindings : Nat → Code Ty Prim Ref loops → Code Ty Prim Ref loops → Code Ty Prim Ref loops
  | 0, _, tail => tail
  | n + 1, .bind id ty prim next, tail => .bind id ty prim (next.prefixBindings n tail)
  | _ + 1, code, _ => code

/-- The split must reassemble the complete captured code. It is a proof
decomposition, not an admission rule that drops inconvenient instructions. -/
theorem Code.prefix_drop (count : Nat) (code : Code Ty Prim Ref loops) :
    code.prefixBindings count (code.dropBindings count) = code := by
  induction count generalizing code with
  | zero => rfl
  | succ n ih => cases code <;> simp [Code.prefixBindings, Code.dropBindings, ih]

theorem Code.finite_enableLoops (code : Code Ty Prim Ref) :
    code.enableLoops.finite? = some code := by
  induction code <;> simp_all [Code.enableLoops, Code.finite?]
  all_goals contradiction

theorem Code.finite_sound (code : Code Ty Prim Ref true) (result : Code Ty Prim Ref)
    (success : code.finite? = some result) : result.enableLoops = code := by
  induction code generalizing result with
  | bind id ty prim next ih =>
    cases found : next.finite? with
    | none => simp [Code.finite?, found] at success
    | some child =>
      simp [Code.finite?, found] at success
      subst result
      simp only [Code.enableLoops, ih child found]
  | branch ref yes no ihYes ihNo =>
    cases left : yes.finite? <;> cases right : no.finite? <;>
      simp [Code.finite?, left, right] at success
    subst result
    simp only [Code.enableLoops, ihYes _ left, ihNo _ right]
  | block id ty body next ihBody ihNext =>
    cases left : body.finite? <;> cases right : next.finite? <;>
      simp [Code.finite?, left, right] at success
    subst result
    simp only [Code.enableLoops, ihBody _ left, ihNext _ right]
  | jump target ref | ret ref => simp [Code.finite?] at success; subst result; rfl
  | loop | «repeat» => simp [Code.finite?] at success

end Compiler.ZigAir.Control
