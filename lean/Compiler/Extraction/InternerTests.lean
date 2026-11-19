/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerProgram
import Compiler.Extraction.InternerFixtures

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache Fixtures

example : (findCode.run primitives request cached).1 = .ok 3 := by rfl
example : (findCode.run primitives request empty).1 = .ok 7 := by rfl
example : (findCode.run primitives request empty).2.table key = some 7 := by rfl
example : (findCode.run { primitives with simplify := fun _ => pure none } request empty).1 = .ok 9 := by rfl
example : (findCode.run { primitives with deterministic := fun _ => .ok false } request cached).1 = .ok 9 := by rfl

-- Capacity is checked before local allocation; no rewriting occurs after a
-- failed owned-buffer allocation. Errors after graph growth retain that growth.
example : (findCode.run { primitives with
    atCapacity := fun _ => true
    normalize := fun _ => Local.fromExcept (.error .outOfMemory) } request empty).1 = .error .capacity := by rfl
example : (findCode.run { primitives with takeOwned := fun _ => Local.fromExcept (.error .outOfMemory) } request empty).2.read 7 = none := by rfl
example : let result := findCode.run { primitives with publish := publish false } request empty
    result.1 = .error .outOfMemory ∧ result.2.read 0 = some 10 ∧
    result.2.read 7 = some 42 ∧ result.2.table key = none := by exact ⟨rfl, rfl, rfl, rfl⟩
example : let result := findCode.run { primitives with simplify := fun _ heap => (.error .unsupported, grown heap) } request empty
    result.1 = .error .unsupported ∧ result.2.read 7 = some 42 := by exact ⟨rfl, rfl⟩

example : (forceCode.run primitives (fun _ _ => .ok ()) 7 request.item request.arguments empty).2.table key = some 7 := by rfl
example : (forceCode.run primitives (fun _ _ => .ok ()) 7 request.item request.arguments cached).2.table key = some 3 := by rfl
example : (forceCode.run primitives (fun _ _ => .error .invalidId) 7 request.item request.arguments cached).1 = .error .invalidId := by rfl

end Compiler.Extraction.Interner
