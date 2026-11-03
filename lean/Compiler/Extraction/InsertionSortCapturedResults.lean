/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortCapturedProofs

namespace Compiler.Extraction.InsertionSort.Captured
open Compiler.Algebraic Compiler.ZigAir Compiler.ZigAir.Memory Compiler.ZigAir.MemoryAir
open Compiler.ZigAir.Memory.WordArray

theorem exchange_stable (budget fuel : Nat) (view : View) (state after : State) (left right : Nat)
    (result : Except Heap.Fault Unit) (enough : budget ≤ fuel)
    (done : exchange budget view state left right = (result, after)) (terminal : result ≠ .error .incomplete) :
    exchange fuel view state left right = (result, after) := by
  by_cases bounds : left < view.length ∧ right < view.length
  · simp only [exchange, if_pos bounds] at done ⊢
    cases first : elementPointer state view.buffer left with
    | error reason => simpa only [first] using done
    | ok a =>
      simp only [first] at done ⊢
      cases second : elementPointer state view.buffer right with
      | error reason => simpa only [second] using done
      | ok b =>
        simp only [second] at done ⊢
        cases call : GeneratedMemory.fn_swap_u32.runFuel budget [a, b] state with
        | finished value final =>
          rw [invocation_settles _ _ _ _ budget value call fuel enough]
          simpa only [call] using done
        | suspended returnType mark args config =>
          simp only [call, outcome] at done
          exact False.elim (terminal (Prod.mk.inj done).1.symm)
  · simpa only [exchange, if_neg bounds] using done

theorem insert_stable (budget fuel : Nat) (view : View) (j : Nat) (state after : State)
    (result : Except Heap.Fault Unit) (enough : budget ≤ fuel)
    (done : insertUsing (operations budget view) j state = (result, after)) (terminal : result ≠ .error .incomplete) :
    insertUsing (operations fuel view) j state = (result, after) := by
  induction j generalizing state with
  | zero => exact done
  | succ j ih =>
    simp only [insertUsing, operations] at done ⊢
    cases current : Heap.read view state (j + 1) with
    | error reason => simpa only [current] using done
    | ok a =>
      simp only [current] at done ⊢
      cases previous : Heap.read view state j with
      | error reason => simpa only [previous] using done
      | ok b =>
        simp only [previous] at done ⊢
        by_cases compared : less a b = true
        · simp only [if_pos compared] at done ⊢
          cases called : exchange budget view state (j + 1) j with
          | mk value middle =>
            cases value with
            | error reason =>
              simp only [called] at done
              have complete : (Except.error reason : Except Heap.Fault Unit) ≠ .error .incomplete := by
                rw [(Prod.mk.inj done).1]
                exact terminal
              rw [exchange_stable budget fuel view state middle (j + 1) j _ enough called complete]
              exact done
            | ok returned =>
              cases returned
              simp only [called] at done
              rw [exchange_stable budget fuel view state middle (j + 1) j _ enough called (by intro h; cases h)]
              exact ih middle done
        · simpa only [if_neg compared] using done

theorem passes_stable (budget limit : Nat) (view : View) (fuel stop i : Nat) (state after : State)
    (result : Except Heap.Fault Unit) (enough : budget ≤ limit)
    (done : passesUsing (operations budget view) fuel stop i state = (result, after)) (terminal : result ≠ .error .incomplete) :
    passesUsing (operations limit view) fuel stop i state = (result, after) := by
  induction fuel generalizing i state with
  | zero => exact done
  | succ fuel ih =>
    simp only [passesUsing] at done ⊢
    by_cases guard : i < stop
    · simp only [if_pos guard] at done ⊢
      cases inserted : insertUsing (operations budget view) i state with
      | mk value middle =>
        cases value with
        | error reason =>
          simp only [inserted] at done
          have complete : (Except.error reason : Except Heap.Fault Unit) ≠ .error .incomplete := by
            rw [(Prod.mk.inj done).1]
            exact terminal
          rw [insert_stable budget limit view i state middle _ enough inserted complete]
          exact done
        | ok returned =>
          cases returned
          simp only [inserted] at done
          rw [insert_stable budget limit view i state middle _ enough inserted (by intro h; cases h)]
          exact ih (i + 1) middle done
    · simpa only [if_neg guard] using done

theorem run_stable (budget fuel : Nat) (view : View) (state after : State) (result : Except Heap.Fault Unit)
    (enough : budget ≤ fuel) (done : run budget state view = (result, after)) (terminal : result ≠ .error .incomplete) :
    run fuel state view = (result, after) := by
  by_cases width : view.length < addressLimit
  · simp only [run, if_pos width, runUsing] at done ⊢
    exact passes_stable budget fuel view _ _ _ state after result enough done terminal
  · simpa only [run, if_neg width] using done

/-- Every observed result is covered, not only the existentially constructed
large-budget run. Incomplete observations retain their exact executable state
but deliberately carry no permutation claim about a partly written word. -/
theorem run_result (budget : Nat) (view : View) (state after : State) (items : List NodeId)
    (result : Except Heap.Fault Unit) (related : Heap.Related view state items)
    (done : run budget state view = (result, after)) :
    result = .error .incomplete ∨ ∃ values,
      Heap.Related view after values ∧ values.Perm items ∧ HeapFrame view state after ∧
      ((result = .ok () ∧ values = sortIds items) ∨ result = .error (.memory .outOfMemory)) := by
  by_cases terminal : result = .error .incomplete
  · exact Or.inl terminal
  · obtain ⟨expected, final, values, ⟨limit, settled⟩, connected, permutation, frame, effect⟩ :=
      run_refines view state items related
    have observed := run_stable budget (budget + limit) view state after result (by omega) done terminal
    have same := observed.symm.trans (settled (budget + limit) (by omega))
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact Or.inr ⟨values, connected, permutation, frame, effect⟩

end Compiler.Extraction.InsertionSort.Captured
