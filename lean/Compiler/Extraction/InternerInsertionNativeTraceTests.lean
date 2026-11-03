/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNativeReplay
import Compiler.Extraction.InsertionExecutionActionTests
import Compiler.Extraction.InternerNativeSpareInsertionTests
import Compiler.Extraction.StorageExecutionTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.TraceTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input)
open CallerInputTests (key)
open CallerSpareSuccessTests

def captured (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :=
  recordExecution ops CallerSpareSuccessTests.allocate safety 7 6 (argumentView empty) itemSource Insertion.Tests.model input
    (key empty) (CallerSpareSuccessTests.normalized empty) true [old safety empty] (taken safety empty).2.world growth []

def replayed (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat))
    (leading trailing : List (Trace.Event Fault)) :=
  insertProgram.execute ⟨true, true, fun _ => false⟩
    (Trace.replay (leading ++ (captured safety empty growth).2.events ++ trailing) (.base .missingArguments)) {} leading.length

/-- Share the native count read established by the existing input geometry. -/
theorem spare_header (safety empty : Bool) :
    readItems (taken safety empty).2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨lifetime empty, 0⟩ 1) := by
  have entry := derived_input safety empty
  have fields := initial_geometry safety empty
  have nativeFrame := entry.native_frame 6 (owner safety empty) fields.1
  unfold readItems
  rw [readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) itemsOffset nativeFrame]
  exact fields.2.2.2.1

/-- The existing spare insertion, in both layouts and with empty/nonempty
arguments, now obtains its caller graph and result from exact protocol replay.
Arbitrary optional growth callbacks are the existing regression's parameter. -/
theorem spare_body (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat))
    (leading trailing : List (Trace.Event Fault)) :
    let observed := replayed safety empty growth leading trailing
    NativeSpareTests.actual safety empty growth =
      ((match observed.1.1 with
        | .error _ => .error (.language .safetyFault)
        | .ok outcome => (Interner.insertionOutcome [old safety empty] outcome).mapError OwnedCall.Fault.language),
        Insertion.projected [old safety empty] (taken safety empty).2.world (key empty)
          (cell input (key empty) (CallerSpareSuccessTests.normalized empty)
            (((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0)
            observed.1.2 (captured safety empty growth).2.effects)
          observed.1.2 (captured safety empty growth).2.effects) ∧
    observed.2 = leading.length + (captured safety empty growth).2.events.length := by
  have entry := derived_input safety empty
  have checked := body_recorded ops CallerSpareSuccessTests.allocate safety 7 6 (argumentView empty) itemSource
    Insertion.Tests.model input (key empty) (CallerSpareSuccessTests.normalized empty) true [old safety empty]
    (taken safety empty).2.world growth (.base .missingArguments) leading trailing ⟨lifetime empty, 0⟩ (spare_header safety empty)
  simpa only [NativeSpareTests.actual, insert, entry.origin.graph, (NativeSpareTests.initial_facts safety empty).projected,
    captured, replayed] using checked


/-- The same actual spare call enters the scoped graph action with its derived
cursor, preserving any live caller scope. No local ending-cursor premise is used. -/
theorem spare_scoped_replay (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat))
    (leading trailing : List (Trace.Event Fault)) (scope : Interner.Scoped.Scope) :
    let candidate := cell input (key empty) (CallerSpareSuccessTests.normalized empty)
      (((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0)
      (captured safety empty growth).1.2 (captured safety empty growth).2.effects
    let action := Interner.InsertionExecution.action candidate (key empty) true
      (Trace.replay (leading ++ (captured safety empty growth).2.events ++ trailing) (.base .missingArguments))
    let logical := Interner.Scoped.liftGraph action
      ⟨scope, { (taken safety empty).2.world.graph with allocationCursor := leading.length }⟩
    (NativeSpareTests.actual safety empty growth).1 = logical.1.mapError OwnedCall.Fault.language ∧
      logical.2 = ⟨scope, { (NativeSpareTests.actual safety empty growth).2.graph with
        allocationCursor := leading.length + (captured safety empty growth).2.events.length }⟩ ∧
      (NativeSpareTests.actual safety empty growth).2.memory = memory (captured safety empty growth).2.effects := by
  have entry := derived_input safety empty
  have rows : (taken safety empty).2.world.graph.representatives = some [old safety empty] := by
    rw [entry.origin.graph, (NativeSpareTests.initial_facts safety empty).projected]
  exact scoped_insert_replayed ops CallerSpareSuccessTests.allocate safety 7 6 (argumentView empty) itemSource
    Insertion.Tests.model input (key empty) (CallerSpareSuccessTests.normalized empty) true [old safety empty]
    (taken safety empty).2.world growth (.base .missingArguments) leading trailing ⟨lifetime empty, 0⟩
    (spare_header safety empty) rows scope

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.TraceTests
