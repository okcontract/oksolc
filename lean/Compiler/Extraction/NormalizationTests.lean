/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.RecursiveTests

namespace Compiler.Extraction.Cache.NormalizationTests
open Compiler.Algebraic Compiler.Extraction.Interner Contract.Yul
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

-- Reversal witnesses that semantic preservation needs only permutation, not
-- canonical order. This test primitive is not Zig's in-place insertion sort.
def sortIds (ids : List NodeId) := ids.reverse
theorem sort_permutation (ids : List NodeId) : (sortIds ids).Perm ids := List.reverse_perm _
def normalize (request : Request) : Except Error (List NodeId) :=
  match normalizeCode.run sortIds request.item request.arguments with
  | none => .error .invalidOptional
  | some ids => .ok ids

def primitives : Primitives := { Recursive.Tests.primitives with normalize := fun request => Local.fromExcept (normalize request) }
theorem refines : NormalizationRefines sortIds primitives := by
  intro request ids cursor after actual
  have actual : normalize request = .ok ids := congrArg Prod.fst actual
  cases ran : normalizeCode.run sortIds request.item request.arguments with
  | none => simp [normalize, ran] at actual
  | some result =>
    have same : result = ids := by simpa [normalize, ran] using actual
    subst result
    rfl

theorem normalizes : Normalizes Recursive.Tests.model primitives :=
  normalizes_of_source _ sortIds sort_permutation primitives refines

theorem recursive_safe (depth : Nat) :
    Recursive.FindSound Recursive.Tests.model (Recursive.unfold primitives Recursive.Tests.reads 64 depth) :=
  Recursive.unfold_normalized_safe Recursive.Tests.env Recursive.Tests.base Recursive.Tests.pushes
    primitives sortIds sort_permutation refines
    (fun key _ before value valid evaluated => Recursive.Tests.allocate_safe key before value valid evaluated)
    (publish_safe _ true) Recursive.Tests.reads (fun heap _ => Recursive.Tests.reads_sound heap) 64 depth

def request : Request := ⟨⟨1, some 1, 0⟩, [1, 0], 77⟩
def result := Recursive.unfold primitives Recursive.Tests.reads 64 2 request Recursive.Tests.initial
example : normalize request = .ok [0, 1] := by rfl
example : result.1 = .ok 7 := by rfl
example : result.2.read 7 = some 42 := by rfl
example : result.2.table ⟨1, 1, 0, [0, 1], 77⟩ = some 7 := by rfl
example : result.2.table ⟨1, 1, 0, [1, 0], 77⟩ = none := by rfl

theorem preserved : Invariant Recursive.Tests.model result.2 ∧ Stable Recursive.Tests.initial result.2 ∧
    result.2.read 7 = some 42 :=
  recursive_safe 2 request Recursive.Tests.initial 42 ⟨(by intro key id found; cases found), trivial⟩ rfl (.ok 7) result.2 rfl

-- The theorem keeps arbitrary epoch-sensitive meanings for other operations
-- and atoms. Partial reads and undefined arities cannot become valid values.
def other : Meaning where
  operation := fun _ sequence values => some (BitVec.ofNat 256 sequence.toNat + values.headD 0)
  atom := fun _ data sequence values => some (data + BitVec.ofNat 256 sequence.toNat + values.headD 0)
def read : Read := fun id => if id == 0 then some 10 else if id == 1 then some 32 else none
def evaluate (item : Item) (ids : List NodeId) (sequence : BitVec 32 := 77) :=
  (normalizeCode.run sortIds item ids).bind (fun args => item.eval (Folding.wordMeaning other) read args sequence)
example : evaluate ⟨1, some 1, 0⟩ [1, 0] = some 42 := by rfl
example : evaluate ⟨1, some 2, 0⟩ [1, 0] = some 320 := by rfl
example : evaluate ⟨1, some 20, 0⟩ [1, 1] = some 1 := by rfl
example : evaluate ⟨1, some 22, 0⟩ [1, 0] = some 0 := by rfl
example : evaluate ⟨1, some 23, 0⟩ [1, 0] = some 42 := by rfl
example : evaluate ⟨1, some 24, 0⟩ [1, 0] = some 42 := by rfl
example : evaluate ⟨1, some 1, 0⟩ [] = none := by rfl
example : evaluate ⟨1, some 1, 0⟩ [0] = none := by rfl
example : evaluate ⟨1, some 1, 0⟩ [1, 0, 0] = none := by rfl
example : evaluate ⟨1, some 1, 0⟩ [1, 2] = none := by rfl
example : evaluate ⟨1, some 1, 0⟩ [2, 1] = none := by rfl
example : evaluate ⟨1, some 1, 0⟩ [2, 3] = none := by rfl
example : evaluate ⟨1, some 1, 0⟩ [1, 1] = some 64 := by rfl
example : evaluate ⟨1, some 3, 0⟩ [1, 0] = some 22 := by rfl
example : evaluate ⟨1, some 49, 0⟩ [1, 0] = some 109 := by rfl
example : evaluate ⟨2, some 1, 5⟩ [1, 0] = some 114 := by rfl
example : normalize ⟨⟨1, none, 0⟩, [], 77⟩ = .error .invalidOptional := by rfl
example : normalize ⟨⟨1, none, 0⟩, [1, 0], 77⟩ = .error .invalidOptional := by rfl
example : normalizeCode.run sortIds ⟨1, some 1, 0⟩ [1, 0, 0] = some [0, 0, 1] := by rfl

-- Dropping an operand is not a permutation. It can turn a malformed request
-- into a value, so the sort contract cannot be omitted from the theorem.
def lostOperand := (normalizeCode.run (List.drop 1) ⟨1, some 1, 0⟩ [1, 1, 0]).bind
  (fun ids => (⟨1, some 1, 0⟩ : Item).eval (Folding.wordMeaning other) read ids 77)
example : lostOperand = some 42 := by rfl
example : (⟨1, some 1, 0⟩ : Item).eval (Folding.wordMeaning other) read [1, 1, 0] 77 = none := by rfl

-- A failing native primitive supplies no successful normalization result.
def failure : Primitives := { primitives with normalize := fun _ => Local.fromExcept (.error .outOfMemory) }
theorem failure_refines : NormalizationRefines sortIds failure := by
  intro request ids cursor after actual
  cases actual
example : (Recursive.unfold failure Recursive.Tests.reads 64 2 request Recursive.Tests.initial).1 =
    .error .outOfMemory := by rfl

end Compiler.Extraction.Cache.NormalizationTests
