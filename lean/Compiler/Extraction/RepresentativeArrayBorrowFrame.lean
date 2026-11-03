/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayAppend
import Compiler.ZigAir.MemoryWordArrayWrites

namespace Compiler.Extraction.RepresentativeArray.Append
open Compiler.ZigAir.Memory
open Compiler.Algebraic

/-- Ready typed append preserves an independent live argument allocation
exactly, whether readonly, stack or persistent. The declared word-array type
derives separation from both mutated containers. Actual append, the parent
frame and its initialized offset contents are conclusions; native growth and
recursive child executions are outside this scope. -/
theorem append_parent_borrow (state : State) (header lifetime capacity length : Nat)
    (headerCell backing : Allocation) (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (source : WordArray.View) (values : List NodeId) (extent : Nat) (parent : Allocation)
    (initial : state.valid = true)
    (headerFound : state.heap.lookup header = some headerCell) (headerTyped : headerCell.type = allocationType)
    (headerWritable : headerCell.writable = true)
    (backingFound : state.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (itemsRead : readItems state ⟨header, 0⟩ = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (capacityRead : readField state ⟨header, 0⟩ capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : length < capacity) (argumentsValid : argumentsLength < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true)
    (parentFound : state.heap.lookup source.allocation = some parent) (parentTyped : parent.type = .array extent WordArray.word)
    (represented : WordArray.Represents state source values) :
    ∃ after, appendWithoutGrowth state ⟨header, 0⟩ itemAddress argumentsAddress argumentsLength id sequence = .ok after ∧
      after.valid = true ∧ after.heap.lookup source.allocation = some parent ∧ WordArray.Represents after source values ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ writable many type offset, load after (.pointer (.pointer writable many type) ⟨source.allocation, offset⟩) =
        load state (.pointer (.pointer writable many type) ⟨source.allocation, offset⟩)) := by
  have outsideHeader := state.heap.lookup_ne_of_type_ne source.allocation header parent headerCell parentFound headerFound
    (by simp [parentTyped, headerTyped, allocationType, WordArray.word])
  have outsideBacking := state.heap.lookup_ne_of_type_ne source.allocation lifetime parent backing parentFound backingFound
    (by simp [parentTyped, backingTyped, Expression.allocationType, WordArray.word])
  obtain ⟨after, executed, valid, _, _, _, nextId, nextAddress, frame⟩ := appendWithoutGrowth_framed state header lifetime capacity length
    headerCell backing itemAddress argumentsAddress argumentsLength id sequence initial headerFound headerTyped headerWritable
    backingFound backingTyped backingWritable itemsRead capacityRead spare argumentsValid idValid sequenceValid
  have same := frame source.allocation outsideHeader outsideBacking
  refine ⟨after, executed, valid, same.trans parentFound, ?_, nextId, nextAddress, ?_⟩
  · refine ⟨represented.1, ?_⟩
    intro index inside
    exact (load_eq_of_lookup state after true false WordArray.word (source.address index) same).trans (represented.2 index inside)
  · intro writable many type offset
    exact load_eq_of_lookup state after writable many type ⟨source.allocation, offset⟩ same

end Compiler.Extraction.RepresentativeArray.Append
