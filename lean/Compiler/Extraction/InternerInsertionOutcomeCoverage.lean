/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendCoverage
import Compiler.Extraction.InternerNativeBackingFailure
import Compiler.Extraction.InternerNativePublishedCompletion
import Compiler.Extraction.InternerNativePublicationRollback
import Compiler.Extraction.InternerNativeUnrelocatedTransferred

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The existing native insertion cases exhaust every ordinary source
completion in the admitted item domain. This is source coverage, independent
of the preservation conclusions subsequently supplied by those case proofs. -/
theorem execution_insertion_coverage (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety deterministic : Bool) (allocator container : Nat) (source : View)
    (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (meaning : Meaning)
    (growth : Option (Growth.Registered.Callbacks σ)) (before : World (Publication.Effects σ))
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety allocator container data capacity before rows)
    (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (admitted : deterministic = true → Admitted ops.arguments) (room : rows.length < 2 ^ 32 - 1)
    (outcome : Option Storage.Outcome)
    (completed : (execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth).1.1 =
      .ok outcome) :
    PreparationOOMAt ops allocator input normalized deterministic before.memory ∨
    BackingAllocationOOMAt ops allocate allocator container input normalized deterministic growth before ∨
    (deterministic = true ∧
      (PublishedObservation ops allocate safety allocator container meaning input key normalized growth before ∨
        RefusedObservation ops allocate safety allocator container meaning input key normalized growth before)) ∨
    (deterministic = false ∧ TransferredObservation ops allocate allocator container input growth before) := by
  rcases execution_preparation_coverage ops allocate safety allocator container source address input key normalized rows growth
      meaning deterministic before outcome room completed with failed | prepared
  · exact Or.inl failed
  · right
    obtain ⟨operands, remaining, duplicated, object, allocated, copied, middle, duplicateCall, createCall, cloneCall⟩ := prepared
    obtain ⟨installed, accepted, installedValid, assigned, native, backing⟩ :=
      execution_backing_coverage ops allocate safety deterministic allocator container object source address input copied key normalized operands remaining
        rows meaning growth before duplicated allocated middle data capacity facts live represented admitted room duplicateCall createCall cloneCall
        outcome completed
    have unique : ∀ other, AssemblyClone.NativeFields.install copied object middle = .ok other → other = installed := by
      intro other assignedOther
      exact Except.ok.inj (assignedOther.symm.trans assigned)
    have count := readHeader_capacity _ _ _ _ facts.header
    have rowCount : (before.graph.representatives.getD []).length = rows.length := by rw [facts.projected]; rfl
    obtain ⟨ownerCell, ownerFound, ownerType, _⟩ := facts.ownerLive
    have lock := Owner.NativeLock.checkHeader_eq_of_lookup safety before.memory.memory installed.memory container ownerCell
      installedValid.memory ownerFound ownerType ((native container ownerCell ownerFound).trans ownerFound.symm)
    have unlocked : Owner.NativeLock.checkHeader installed.memory (Owner.headerAddress ⟨container, 0⟩) = .ok () →
        Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok () := fun checked => lock.symm.trans checked
    cases accepted with
    | false =>
      left
      rcases backing with ⟨_, impossible⟩ | ⟨checked, first | relocated⟩
      · cases impossible
      · obtain ⟨empty, effects, response⟩ := first
        refine ⟨operands, remaining, duplicated, object, allocated, copied, middle, effects,
          duplicateCall, createCall, cloneCall, unlocked checked, Or.inl ⟨?_, ?_⟩⟩
        · simpa only [empty] using count
        · intro other assignedOther
          rw [unique other assignedOther]
          exact response
      · obtain ⟨nonempty, short, context, returnAddress, release, selected, effects, response⟩ := relocated
        refine ⟨operands, remaining, duplicated, object, allocated, copied, middle, effects,
          duplicateCall, createCall, cloneCall, unlocked checked, Or.inr ⟨capacity,
            Capacity.grow (Append.nextLength rows.length), context, returnAddress, release, count, nonempty,
            ?_, ?_, Capacity.grow_count_bytes rows.length room, selected, ?_⟩⟩
        · simpa only [rowCount] using short
        · rw [rowCount]
        · intro other assignedOther
          rw [unique other assignedOther]
          exact response
    | true =>
      right
      cases deterministic with
      | false =>
        right
        refine ⟨rfl, ?_⟩
        obtain ⟨operandsEq, duplicatedEq⟩ := duplicateCall
        subst operands
        subst duplicated
        rcases backing with ⟨spare, _⟩ | ⟨checked, first | relocated⟩
        · left
          refine ⟨domain, capacity, count, Or.inr ?_, object, allocated, copied, middle, createCall, cloneCall, ?_⟩
          · simpa only [rowCount] using spare
          · intro empty
            omega
        · left
          obtain ⟨empty, base, effects, response, fits⟩ := first
          refine ⟨domain, capacity, count, Or.inl empty, object, allocated, copied, middle, createCall, cloneCall,
            fun _ => ⟨base, effects, ?_, unlocked checked⟩⟩
          intro other assignedOther
          rw [unique other assignedOther]
          exact ⟨response, fits⟩
        · right
          obtain ⟨nonempty, short, context, returnAddress, release, selected, base, effects, response, fits⟩ := relocated
          refine ⟨domain, capacity, Capacity.grow (Append.nextLength rows.length), count, nonempty, ?_, ?_,
            Capacity.grow_count_bytes rows.length room, context, returnAddress, release, selected,
            object, allocated, copied, middle, base, effects, createCall, cloneCall, ?_, unlocked checked⟩
          · simpa only [rowCount] using short
          · rw [rowCount]
          · intro other assignedOther
            rw [unique other assignedOther]
            exact ⟨response, fits⟩
      | true =>
        left
        refine ⟨rfl, ?_⟩
        rcases backing with ⟨spare, _⟩ | ⟨checked, first | relocated⟩
        · let probe := ops.probe key (Publication.forget (memory (append safety allocate allocator container
            (before.graph.representatives.getD []) input key normalized ((key.eval meaning before.graph.read).getD 0)
            preparationOwnership (preparedFrame object copied operands installed)).2))
          have observed : SparePublication ops allocate safety allocator container meaning input key normalized probe.1 before := by
            refine ⟨capacity, count, ?_, operands, remaining, duplicated, object, allocated, copied, middle, probe.2,
              duplicateCall, createCall, cloneCall, ?_⟩
            · simpa only [rowCount] using spare
            · intro other assignedOther
              rw [unique other assignedOther]
          cases decision : probe.1 with
          | false => exact Or.inr (Or.inr (Or.inl (decision ▸ observed)))
          | true => exact Or.inl (Or.inr (Or.inl ⟨domain, decision ▸ observed⟩))
        · obtain ⟨empty, base, effects, response, fits⟩ := first
          let probe := ops.probe key (Publication.forget (memory (append safety allocate allocator container []
            input key normalized ((key.eval meaning before.graph.read).getD 0)
            preparationOwnership (preparedFrame object copied operands installed)).2))
          have observed : FirstPublication ops allocate safety allocator container meaning input key normalized probe.1 before := by
            refine ⟨?_, operands, remaining, duplicated, object, allocated, copied, middle, base, effects, probe.2,
              duplicateCall, createCall, cloneCall, ?_, ?_, unlocked checked⟩
            · simpa only [empty] using count
            · intro other assignedOther
              rw [unique other assignedOther]
              exact ⟨response, fits⟩
            · intro other assignedOther
              rw [unique other assignedOther]
          cases decision : probe.1 with
          | false => exact Or.inr (Or.inl (decision ▸ observed))
          | true => exact Or.inl (Or.inl ⟨domain, decision ▸ observed⟩)
        · obtain ⟨nonempty, short, context, returnAddress, release, selected, base, effects, response, fits⟩ := relocated
          let probe := ops.probe key (Publication.forget (memory (append safety allocate allocator container
            (before.graph.representatives.getD []) input key normalized ((key.eval meaning before.graph.read).getD 0)
            preparationOwnership (preparedFrame object copied operands installed) (some ⟨.noRemap context returnAddress, release⟩)).2))
          have observed : RelocatedPublication ops allocate safety allocator container meaning input key normalized growth probe.1 before := by
            refine ⟨capacity, Capacity.grow (Append.nextLength rows.length), count, nonempty, ?_, ?_,
              Capacity.grow_count_bytes rows.length room, context, returnAddress, release, selected,
              operands, remaining, duplicated, object, allocated, copied, middle, base, effects, probe.2,
              duplicateCall, createCall, cloneCall, ?_, ?_, unlocked checked⟩
            · simpa only [rowCount] using short
            · rw [rowCount]
            · intro other assignedOther
              rw [unique other assignedOther]
              exact ⟨response, fits⟩
            · intro other assignedOther
              rw [unique other assignedOther]
          cases decision : probe.1 with
          | false => exact Or.inr (Or.inr (Or.inr (decision ▸ observed)))
          | true => exact Or.inl (Or.inr (Or.inr ⟨domain, decision ▸ observed⟩))

/-- Lift exhaustive source cases through the native count reader and result
adapter. Ordinary completion remains explicit; validation rejection is never
reclassified as a compiler return. -/
theorem insert_insertion_coverage (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety deterministic : Bool) (allocator container : Nat) (source : View)
    (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (meaning : Meaning)
    (growth : Option (Growth.Registered.Callbacks σ)) (before : World (Publication.Effects σ))
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety allocator container data capacity before rows)
    (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (admitted : deterministic = true → Admitted ops.arguments) (room : rows.length < 2 ^ 32 - 1)
    (completed : ordinary (insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before).1 = true) :
    PreparationOOMAt ops allocator input normalized deterministic before.memory ∨
    BackingAllocationOOMAt ops allocate allocator container input normalized deterministic growth before ∨
    (deterministic = true ∧
      (PublishedObservation ops allocate safety allocator container meaning input key normalized growth before ∨
        RefusedObservation ops allocate safety allocator container meaning input key normalized growth before)) ∨
    (deterministic = false ∧ TransferredObservation ops allocate allocator container input growth before) := by
  have checked := checkedExecution_read ops allocate safety allocator container source address meaning input key normalized
    deterministic rows before growth data (readHeader_items _ _ _ _ facts.header)
  cases ran : execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth with
  | mk result reached =>
    obtain ⟨result, owner⟩ := result
    cases result with
    | error fault =>
      simp only [insert, facts.projected, body, checked, ran, ordinary, OwnedCall.Fault.recoverable, Bool.false_eq_true] at completed
    | ok outcome =>
      exact execution_insertion_coverage ops allocate safety deterministic allocator container source address input key normalized rows meaning growth
        before data capacity facts live represented domain admitted room outcome (by rw [ran])

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
