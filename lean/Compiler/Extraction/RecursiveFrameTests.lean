/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.RecursiveFrames
import Compiler.Extraction.ObservedHeapTests

namespace Compiler.Extraction.Recursive.FrameTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner Contract.Yul
set_option maxRecDepth 8192

def cells : List Storage.Cell := [ObservedTests.caller,
  { item := ⟨2, none, 10⟩, otherValue := 0, itemAddress := 30 },
  { item := ⟨2, none, 32⟩, otherValue := 0, itemAddress := 40 }]
def initial := observedHeap cells (fun _ => none)

/-- An executable constructor witness for structural preservation. Its graph
adapter is source-bound; addresses and unobserved word denotations here are test
data, not a physical allocation or general semantic-insertion proof. -/
def cellFor (key : Key) (before : Heap) : Storage.Cell := {
  item := ⟨key.kind, if key.kind = 1 then some key.instruction else none, key.data⟩,
  otherValue := 0, itemAddress := (before.representatives.getD []).length * 10 + 50,
  arguments := key.arguments, sequence := key.sequence,
  argumentsAddress := (before.representatives.getD []).length * 10 + 60
}
def insert (succeeds : Bool) (key : Key) (deterministic : Bool) : Action NodeId := fun before =>
  observedInsert (cellFor key before) key deterministic (fun _ => succeeds) before
def primitives (allocation publication : Bool) : Primitives := {
  NormalizationTests.primitives with insert := insert allocation, publish := publish publication
}

theorem primitive_frames (allocation publication : Bool) : PrimitiveFrames (primitives allocation publication) where
  insert := fun key deterministic before => Frames.insert (cellFor key before) key deterministic (fun _ => allocation) before
  publish := Frames.publish publication

def request : Request := ⟨⟨1, some 1, 0⟩, [2, 1], 77⟩
def result := unfold (primitives true true) representativeReads 64 2 request initial
def publicationFailure := unfold (primitives true false) representativeReads 64 2 request initial
def allocationFailure := unfold (primitives false true) representativeReads 64 2 request initial
def cutoff := unfold (primitives true true) representativeReads 64 1 request initial
def newCell := cellFor ⟨2, 0, 42, [], 0⟩ initial

theorem all_depths (allocation publication : Bool) (depth : Nat) :
    FindFrames (unfold (primitives allocation publication) representativeReads 64 depth) :=
  unfold_frames _ (primitive_frames allocation publication) _ _ depth

theorem success_retains : Extends initial result.2 := all_depths true true 2 request initial
theorem failure_retains : Extends initial publicationFailure.2 := all_depths true false 2 request initial

example : result.1 = .ok 3 := by rfl
example : result.2.representatives = some (cells ++ [newCell]) := by rfl
example : result.2.read 3 = some 42 := by rfl
example : result.2.table ⟨1, 1, 0, [1, 2], 77⟩ = some 3 := by rfl
example : result.2.table ⟨2, 0, 42, [], 0⟩ = some 3 := by rfl
example : (representativeReads result.2).operation 0 0x33 = .ok (some ⟨0, []⟩) := by rfl
example : (representativeReads result.2).constant 1 = .ok (some 10) := by rfl
example : publicationFailure.1 = .error .outOfMemory := by rfl
example : publicationFailure.2.representatives = some (cells ++ [newCell]) := by rfl
example : publicationFailure.2.table ⟨1, 1, 0, [1, 2], 77⟩ = none := by rfl
example : publicationFailure.2.table ⟨2, 0, 42, [], 0⟩ = some 3 := by rfl
example : allocationFailure = (.error .outOfMemory, initial) := by rfl
example : cutoff = (.error .unsupported, initial) := by rfl

theorem executed : Executes (primitives true true) representativeReads 64 request initial (.ok 3) result.2 :=
  ⟨2, rfl, by intro impossible; cases impossible⟩

theorem old_operation_retained :
    (representativeReads publicationFailure.2).operation 0 0x33 = (representativeReads initial).operation 0 0x33 :=
  Extends.operation initial publicationFailure.2 failure_retains cells rfl 0 (by decide) 0x33

theorem old_constant_retained :
    (representativeReads result.2).constant 1 = (representativeReads initial).constant 1 :=
  Extends.constant initial result.2 success_retains cells rfl 1 (by decide)

-- Equal word observations are insufficient: changing a Push into a CALLER
-- changes its structural observation despite the equal word and empty cache.
theorem changed_kind_rejected : ¬Extends ObservedTests.constantHeap ObservedTests.callerHeap := by
  intro changed
  have same := Extends.constant _ _ changed [ObservedTests.constant] rfl 0 (by decide)
  change (Except.ok none : Except Storage.ReadError (Option Word)) = .ok (some 3) at same
  cases same

theorem detached_rejected : ¬Extends initial { initial with representatives := none } := by
  intro detached
  obtain ⟨suffix, impossible⟩ := detached cells rfl
  cases impossible

end Compiler.Extraction.Recursive.FrameTests
