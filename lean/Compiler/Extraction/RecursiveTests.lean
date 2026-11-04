/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Recursive
import Compiler.Extraction.AddressMaskTests

namespace Compiler.Extraction.Recursive.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

-- A concrete semantic witness discharges every non-recursive premise. This
-- small allocator is a test model, not a refinement of native allocation.
def base : Meaning where
  operation := fun _ _ _ => none
  atom := fun kind data _ _ => if kind == 2 then some data else none
def env := AddressMask.Tests.env
def model := Dispatch.wordDispatchMeaning env base
theorem pushes : Pushes base := by intro value; rfl

def reads (heap : Heap) : Reads where
  constant := fun id => .ok (heap.read id)
  operation := fun _ _ => .ok none
theorem reads_sound (heap : Heap) : Sound model heap.read (reads heap) := by
  constructor
  · intro id value found; exact Except.ok.inj found
  · intro id opcode slice found; cases found
  · intro left right a b equal lhs rhs
    simp only [sameExpression, reads, beq_iff_eq] at equal
    subst right
    exact Option.some.inj (lhs.symm.trans rhs)

def allocate (key : Key) : Action NodeId := fun before =>
  if before.read 7 != none then (.error .capacity, before) else
  match key.eval model before.read with
  | none => (.error .unsupported, before)
  | some value => (.ok 7, ⟨fun id => if id == 7 then some value else before.read id,
      put equalityFields before.table key 7, none, before.allocationCursor⟩)

theorem allocate_safe (key : Key) (before : Heap) (value : Word) (valid : Invariant model before)
    (evaluated : key.eval model before.read = some value) :
    Safe model (allocate key) before (fun id after => after.read id = some value) := by
  by_cases vacant : before.read 7 = none
  · let newRead : Read := fun id => if id == 7 then some value else before.read id
    have stable : Preserves (fun read : Read => read) before.read newRead := by
      intro id word actual
      by_cases same : id = 7
      · subst id; have impossible := vacant.symm.trans actual; cases impossible
      · simpa only [newRead, beq_iff_eq, same, ↓reduceIte] using actual
    have cache := valid_stable model before.read newRead before.table valid.cache stable
    have denotation := key_stable model before.read newRead stable key value evaluated
    have resultRead : newRead 7 = some value := by rfl
    intro result after ran
    change (if before.read 7 != none then _ else _) = _ at ran
    simp only [vacant, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, evaluated] at ran
    cases ran
    exact ⟨⟨put_valid model newRead before.table cache key 7 value denotation resultRead, trivial⟩, stable, resultRead⟩
  · have full : (before.read 7 != none) = true := by simpa using vacant
    intro result after ran
    simp only [allocate, full, ↓reduceIte] at ran
    cases ran
    exact ⟨valid, fun _ _ actual => actual, trivial⟩

def primitives : Primitives where
  atCapacity := fun _ => false
  normalize := fun request => Local.fromExcept (.ok request.arguments)
  deterministic := fun _ => .ok true
  takeOwned := fun _ => Local.fromExcept (.ok ())
  simplify := fun _ => fail .safetyFault
  insert := fun key _ => allocate key
  publish := publish true

theorem primitive_contracts : PrimitiveContracts model primitives where
  normalize := by
    intro request args read cursor after actual
    have same := Except.ok.inj (congrArg Prod.fst actual)
    cases same
    rfl
  insert := by intro key deterministic before value valid evaluated; exact allocate_safe key before value valid evaluated
  publish := publish_safe model true

def initial : Heap := ⟨fun id => if id == 0 then some 10 else if id == 1 then some 32 else none, fun _ => none, none, 0⟩
def request : Request := ⟨⟨1, some 1, 0⟩, [0, 1], 77⟩
def result (depth : Nat) := unfold primitives reads 64 depth request initial
example : (result 0).1 = .error .unsupported := by rfl
example : (result 1).1 = .error .unsupported := by rfl
example : (result 2).1 = .ok 7 := by rfl
example : (result 5).1 = .ok 7 := by rfl
example : (result 2).2.read 7 = some 42 := by rfl
example : (result 2).2.table ⟨1, 1, 0, [0, 1], 77⟩ = some 7 := by rfl
example : (result 2).2.table ⟨2, 0, 42, [], 0⟩ = some 7 := by rfl
example : (result 2).2.read 0 = some 10 ∧ (result 2).2.read 1 = some 32 := by exact ⟨rfl, rfl⟩

theorem completed : Executes primitives reads 64 request initial (.ok 7) (result 2).2 :=
  ⟨2, rfl, by intro impossible; cases impossible⟩

theorem preserved : Invariant model (result 2).2 ∧ Stable initial (result 2).2 ∧ (result 2).2.read 7 = some 42 := by
  exact executes_safe env base pushes primitives primitive_contracts reads (fun heap _ => reads_sound heap)
    64 request initial (result 2).2 (.ok 7) 42 ⟨(by intro key id found; cases found), trivial⟩ rfl completed

-- Publication failure keeps the value constructed recursively, but not its
-- parent cache entry. The seed's arbitrary simplify callback is never used.
def publishFailure (depth : Nat := 2) := unfold { primitives with publish := publish false } reads 64 depth request initial
example : (publishFailure 2).1 = .error .outOfMemory := by rfl
example : (publishFailure 2).2.read 7 = some 42 := by rfl
example : (publishFailure 2).2.table ⟨1, 1, 0, [0, 1], 77⟩ = none := by rfl
example : Executes { primitives with publish := publish false } reads 64 request initial
    (.error .outOfMemory) (publishFailure 2).2 := ⟨2, rfl, by intro impossible; cases Except.error.inj impossible⟩
example : ¬Executes primitives reads 64 request initial (.error .unsupported) initial :=
  unsupported_not_execution _ _ _ _ _ _

def cacheHit := unfold primitives reads 64 1 request (result 2).2
example : cacheHit.1 = .ok 7 := by rfl
def constantRoot := unfold primitives reads 64 1 (constructorCode.constantRequest 9) initial
example : constantRoot.1 = .ok 7 := by rfl
example : constantRoot.2.read 7 = some 9 := by rfl
def capacityFirst := unfold { primitives with
    atCapacity := fun _ => true
    normalize := fun _ => Local.fromExcept (.error .outOfMemory) } reads 64 1 request initial
example : capacityFirst.1 = .error .capacity := by rfl

end Compiler.Extraction.Recursive.Tests
