/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFirstInsertionTests
import Compiler.Extraction.InternerNativeSpareInsertionTests
import Compiler.Extraction.InternerEnclosingRollbackFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.UnrelocatedTransferredTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)
open ConstructorItem.NativeRecursion

/-- Reuse both initialized callers; spare storage keeps its refusing allocator. -/
def before (spare safety empty : Bool) := if spare then CallerSpareSuccessTests.before safety empty else CallerInputTests.world safety
def taken (spare safety empty : Bool) := if spare then CallerSpareSuccessTests.taken safety empty else CallerInputTests.taken safety empty
def argumentView (spare empty : Bool) := if spare then CallerSpareSuccessTests.argumentView empty else CallerInputTests.argumentView empty
def normalized (spare empty : Bool) := if spare then CallerSpareSuccessTests.normalized empty else CallerInputTests.normalized empty
def lookup (spare empty : Bool) := if spare then CallerSpareSuccessTests.lookup empty else CallerInputTests.remaining empty
def rows (spare safety empty : Bool) := if spare then [CallerSpareSuccessTests.old safety empty] else []
def allocate (spare : Bool) := if spare then CallerSpareSuccessTests.allocate else CallerInputTests.allocate
abbrev ops := CallerFirstSuccessTests.ops

theorem entry (spare safety empty : Bool) :
    CallerInput 7 (argumentView spare empty) source (request empty) (values empty) input (key empty)
      (before spare safety empty) (taken spare safety empty).2 (normalized spare empty) (lookup spare empty) := by
  cases spare
  · exact CallerInputTests.derived_input safety empty
  · exact CallerSpareSuccessTests.derived_input safety empty

theorem reached (spare safety empty : Bool) :
    CallFrame safety 7 6 (rows spare safety empty) (argumentView spare empty) (request empty).arguments
      (normalized spare empty) source input (fun _ => True) (taken spare safety empty).2.world := by
  cases spare
  · exact NativeFirstTests.reached_frame safety empty
  · exact NativeSpareTests.reached_frame safety empty

def made (spare safety empty : Bool) := AssemblyItem.Creation.create (observe ops.create) 7 input.item (taken spare safety empty).2.world.memory
def cloned (spare safety empty : Bool) := AssemblyClone.Physical.run (observe ops.copy) 7 input (made spare safety empty).2
def object (spare safety empty : Bool) := (taken spare safety empty).2.world.memory.memory.nextId
def copied (spare safety empty : Bool) : AssemblyClone.NativeFields.ItemValue :=
  { input with verbatim := some ⟨2, 3, ⟨object spare safety empty + 1, [8, 9], 0⟩⟩ }
def ready (spare safety empty : Bool) :=
  (AssemblyClone.NativeFields.install (copied spare safety empty) (object spare safety empty) (cloned spare safety empty).2).toOption.getD
    (cloned spare safety empty).2

set_option maxHeartbeats 2000000 in
/-- Only source callback and capacity observations are evaluated. The shared
proof derives all final native graph and ownership facts. -/
theorem observed (spare safety empty : Bool) :
    UnrelocatedTransferred ops (allocate spare) 7 6 input (taken spare safety empty).2.world := by
  refine ⟨by decide, (if spare then 5 else 0), ?_, ?_, object spare safety empty, (made spare safety empty).2,
    copied spare safety empty, (cloned spare safety empty).2, ?_, ?_, ?_⟩
  · cases spare <;> cases safety <;> cases empty <;> insertion_kernel_rfl
  · cases spare <;> cases safety <;> cases empty <;> decide +kernel
  · cases spare <;> cases safety <;> cases empty <;> insertion_kernel_rfl
  · cases spare <;> cases safety <;> cases empty <;> insertion_kernel_rfl
  · intro zero
    cases spare with
    | true => contradiction
    | false =>
      refine ⟨4096, (ready false safety empty).effects.allocator * 10 + 7, ?_, ?_⟩
      · intro installed assigned
        have same : ready false safety empty = installed := by
          simp only [ready, assigned, Except.toOption, Option.getD_some]
        rw [← same]
        refine ⟨rfl, by decide, by decide, by decide, ?_⟩
        have bound : (ready false safety empty).memory.heap.all (fun entry =>
            decide (entry.2.base + (entry.2.type.layout.getD ⟨0, 1⟩).bytes ≤ 4096)) = true := by
          cases safety <;> cases empty <;> decide +kernel
        intro entry present layout shaped
        have checked := (List.all_eq_true.mp bound) entry present
        simp only [shaped, Option.getD_some, decide_eq_true_eq] at checked
        exact Or.inr checked
      · cases safety <;> cases empty <;> insertion_kernel_rfl

/-- Both existing executions instantiate the same reducer used by the general
proper-child step, for either layout, either buffer and any growth callback. -/
theorem shared_completion (spare safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops (allocate spare) safety 7 6
      (argumentView spare empty) source Insertion.Tests.model input (key empty) slice false growth) : Action (Publication.Effects Nat) NodeId)
      ⟨(taken spare safety empty).2.world, ⟨some (lookup spare empty), some (normalized spare empty), false⟩⟩
    FramePost (GraphFrame safety 7 6 (rows spare safety empty) (fun _ => True))
      (OwnedCall.finish (Publication.external ops.arguments) 7 ran.1 ran.2) := by
  have caller := entry spare safety empty
  let stack : Enclosing (σ := Nat) safety 7 6 (fun _ => True) := .root
  exact stack.insertion_rollback_derived trivial caller.origin (reached spare safety empty) ops (allocate spare) growth
    Insertion.Tests.model (key empty) false (Normalization.Tests.external_admitted _) caller.publication.aligned
    (fun _ _ _ _ _ absent => False.elim (absent rfl (Or.inl (observed spare safety empty))))

set_option maxHeartbeats 2000000 in
/-- The result is actual success (the return-frame test alone also permits a
clean rejection), with unchanged keys and the original buffer in the new row. -/
theorem success (spare safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    let world := (taken spare safety empty).2.world
    let actual := Insertion.Native.insert ops (allocate spare) safety 7 6 (argumentView spare empty) source
      Insertion.Tests.model input (key empty) (normalized spare empty) false growth world
    TransferredReturn safety 7 6 (rows spare safety empty) (normalized spare empty) world actual := by
  exact (reached spare safety empty).transferred ops (allocate spare) growth Insertion.Tests.model (key empty)
    (by cases spare <;> cases safety <;> cases empty <;> decide +kernel) (Or.inl (observed spare safety empty))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.UnrelocatedTransferredTests
