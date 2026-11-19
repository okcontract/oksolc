/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowingSuccess
import Compiler.Extraction.InternerCallerInsertionSpareSuccessTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

abbrev ops := CallerFirstSuccessTests.ops
def parent (empty : Bool) := view (CallerInputTests.operands empty)
def lifetime (empty : Bool) := CallerInputTests.object empty + 2
def releaseBacking : Backing.Release.External Nat := fun allocator base bytes alignment effects =>
  effects * 10 + (if allocator = 7 && base = 4096 && bytes = 160 && alignment = 8 then 9 else 0)
def allocate : Backing.Registry.Allocate Nat := fun allocator bytes alignment effects =>
  (if allocator = 7 && bytes = 416 && alignment = 8 then some 8192 else none, effects * 10 + 7)
def growth : Growth.Registered.Callbacks Nat := ⟨.noRemap 17 23, releaseBacking⟩
def selectedGrowth (cells : List Storage.Cell) := if cells.length = 5 then some growth else none

/-- The existing native execution and graph projection, with their explicit
outcomes. The fixture selects the captured refusing-remap callback for growth. -/
def insertWith (actions : Operations Nat) (safety empty : Bool) (slice : ArgumentSlice)
    (reserve : Backing.Registry.Allocate Nat := allocate) (deterministic : Bool := true) : GraphAction (Publication.Effects Nat) NodeId := fun before =>
  let cells := before.graph.representatives.getD []
  let ran := execution actions reserve safety 7 6 (parent empty) source Insertion.Tests.model input (key empty) slice deterministic cells before (selectedGrowth cells)
  let value := ((key empty).eval Insertion.Tests.model before.graph.read).getD 0
  let after := Insertion.projected cells before (key empty) (cell input (key empty) slice value ran.1.2 ran.2) ran.1.2 ran.2
  let result := match ran.1.1 with
    | .error _ => .error (.language .safetyFault)
    | .ok outcome => (Interner.insertionOutcome cells outcome).mapError OwnedCall.Fault.language
  (result, after)

def insert (safety empty : Bool) (slice : ArgumentSlice) : GraphAction (Publication.Effects Nat) NodeId :=
  insertWith ops safety empty slice

/-- Actual allocation, normalization, take, handoff and defers. The monadic
sequence does not run later calls after an earlier failure. This is the selected
insertion continuation, not a certificate for find's cache or recursive routing. -/
def invokeWith (actions : Operations Nat) (safety empty : Bool) (before : World (Publication.Effects Nat))
    (reserve : Backing.Registry.Allocate Nat := allocate) (deterministic : Bool := true) : Except OwnedCall.Fault NodeId × OwnedCall.State (Publication.Effects Nat) :=
  match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | .error _ => (.error (.language .safetyFault), ⟨before, { lookup := none }⟩)
  | .ok (_, native) =>
    Caller.invoke (Publication.external actions.arguments) 7 (do
      let _ ← Caller.initLookup (Publication.external actions.arguments) 160 7 (parent empty) ⟨before.memory.memory.nextId, 0, 2⟩ (request empty)
      take (Publication.external actions.arguments) 7
      handoff
      graph (fun slice => insertWith actions safety empty slice reserve deterministic)) { before with memory := { before.memory with memory := native } }

def invoke (safety empty : Bool) (before : World (Publication.Effects Nat)) := invokeWith ops safety empty before

def first (safety empty : Bool) :=
  let reached := (do handoff; graph (CallerFirstSuccessTests.insert safety empty) : Action (Publication.Effects Nat) NodeId) (CallerInputTests.taken safety empty).2
  finish (Publication.external ops.arguments) 7 reached.1 reached.2

/-- The sequence stops at the first failure, retaining its reached state. -/
def run (safety empty : Bool) : Nat → Except OwnedCall.Fault NodeId × OwnedCall.State (Publication.Effects Nat)
  | 0 => first safety empty
  | n + 1 =>
    let prior := run safety empty n
    match prior.1 with
    | .error _ => prior
    | .ok _ => invoke safety empty prior.2.world

def before (safety empty : Bool) (n : Nat) := (run safety empty n).2.world
def cells (safety empty : Bool) (n : Nat) := (before safety empty n).graph.representatives.getD []
def stack (safety empty : Bool) (n : Nat) :=
  ((Compiler.ZigAir.Memory.allocate (before safety empty n).memory.memory (.array 2 word)).toOption.map Prod.snd).getD (before safety empty n).memory.memory
def prepared (safety empty : Bool) (n : Nat) := Caller.initLookup (Publication.external ops.arguments) 160 7 (parent empty)
  ⟨(before safety empty n).memory.memory.nextId, 0, 2⟩ (request empty)
  ⟨{ before safety empty n with memory := { (before safety empty n).memory with memory := stack safety empty n } }, { lookup := none }⟩
def taken (safety empty : Bool) (n : Nat) := take (Publication.external ops.arguments) 7 (prepared safety empty n).2
def startId (empty : Bool) (n : Nat) := if empty then 12 + 3 * n else 14 + 5 * n
def normalized (_safety empty : Bool) (n : Nat) : ArgumentSlice := ⟨startId empty n + 1, values empty⟩
def lookup (empty : Bool) : Handle := ⟨parent empty, values empty, none⟩
def handle (safety empty : Bool) (n : Nat) : Handle := ⟨view (normalized safety empty n), values empty, none⟩
def operands (_safety empty : Bool) (n : Nat) : ArgumentSlice :=
  ⟨startId empty n + (if empty then 1 else 2), values empty⟩
def object (_safety empty : Bool) (n : Nat) := startId empty n + (if empty then 1 else 3)
def copied (safety empty : Bool) (n : Nat) : AssemblyClone.NativeFields.ItemValue :=
  { input with verbatim := some ⟨2, 3, ⟨object safety empty n + 1, [8, 9], 0⟩⟩ }
def duplicated (safety empty : Bool) (n : Nat) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
  (handle safety empty n) (taken safety empty n).2.world.memory
def made (safety empty : Bool) (n : Nat) := AssemblyItem.Creation.create (observe ops.create) 7 input.item (duplicated safety empty n).2
def cloned (safety empty : Bool) (n : Nat) := AssemblyClone.Physical.run (observe ops.copy) 7 input (made safety empty n).2
def ready (safety empty : Bool) (n : Nat) :=
  (AssemblyClone.NativeFields.install (copied safety empty n) (object safety empty n) (cloned safety empty n).2).toOption.getD (cloned safety empty n).2
def value (safety empty : Bool) (n : Nat) := ((key empty).eval Insertion.Tests.model (taken safety empty n).2.world.graph.read).getD 0
def row (safety empty : Bool) (n : Nat) : Storage.Cell :=
  ⟨(copied safety empty n).item, value safety empty n, object safety empty n, values empty, (key empty).sequence, (operands safety empty n).address⟩
def execute (safety empty : Bool) (n : Nat) := execution ops allocate safety 7 6 (parent empty) source Insertion.Tests.model
  input (key empty) (normalized safety empty n) true (cells safety empty n) (taken safety empty n).2.world (selectedGrowth (cells safety empty n))

theorem first_result (safety empty : Bool) : first safety empty =
    (.ok 0, ⟨CallerFirstSuccessTests.reached safety empty, ⟨none, some (CallerInputTests.normalized empty), true⟩⟩) :=
  CallerFirstSuccessTests.handoff_and_outer_cleanup safety empty

/-- A single observation bundle avoids repeatedly elaborating the same closed
execution. Expected descriptors are checked against the actual fresh identifier. -/
def observations (safety empty : Bool) (n : Nat) :=
  ((before safety empty n).memory.memory.nextId,
   (Compiler.ZigAir.Memory.allocate (before safety empty n).memory.memory (.array 2 word)).map Prod.fst,
   (prepared safety empty n).1, (taken safety empty n).1, (taken safety empty n).2.scope,
   (duplicated safety empty n).1, (made safety empty n).1, (cloned safety empty n).1)
def expected (safety empty : Bool) (n : Nat) :=
  (startId empty n,
   Except.ok (ε := Compiler.ZigAir.Memory.Fault) (Compiler.ZigAir.Memory.Value.pointer (.pointer true false (.array 2 word)) ⟨startId empty n, 0⟩),
   Except.ok (ε := OwnedCall.Fault) (values empty), Except.ok (ε := OwnedCall.Fault) (),
   (⟨some (lookup empty), some (normalized safety empty n), false⟩ : Local),
   Except.ok (ε := Normalization.Failure) (operands safety empty n, handle safety empty n),
   Except.ok (ε := AssemblyItem.Creation.Fault) (object safety empty n),
   Except.ok (ε := AssemblyClone.Physical.Fault) (copied safety empty n))

/-- The lock read at the actual sixth-call entry follows from the complete
initialized execution prefix, including the five preceding publications. -/
theorem growth_entry_unlocked (safety empty : Bool) :
    Owner.NativeLock.checkHeader (before safety empty 4).memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok () := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem observations_0 (safety empty : Bool) : observations safety empty 0 = expected safety empty 0 := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem observations_1 (safety empty : Bool) : observations safety empty 1 = expected safety empty 1 := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem observations_2 (safety empty : Bool) : observations safety empty 2 = expected safety empty 2 := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem observations_3 (safety empty : Bool) : observations safety empty 3 = expected safety empty 3 := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem observations_4 (safety empty : Bool) : observations safety empty 4 = expected safety empty 4 := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem reached_observations (safety empty : Bool) (n : Nat) (bounded : n < 5) :
    observations safety empty n = expected safety empty n := by
  have alternatives : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl | rfl
  · exact observations_0 safety empty
  · exact observations_1 safety empty
  · exact observations_2 safety empty
  · exact observations_3 safety empty
  · exact observations_4 safety empty

theorem prefix_results (safety empty : Bool) (n : Nat) (bounded : n < 5) :
    Compiler.ZigAir.Memory.allocate (before safety empty n).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨startId empty n, 0⟩, stack safety empty n) ∧
    (prepared safety empty n).1 = .ok (values empty) ∧ (taken safety empty n).1 = .ok () ∧
    (taken safety empty n).2.scope = ⟨some (lookup empty), some (normalized safety empty n), false⟩ := by
  have observed := reached_observations safety empty n bounded
  simp only [observations, expected, Prod.mk.injEq] at observed
  refine ⟨?_, observed.2.2.1, observed.2.2.2.1, observed.2.2.2.2.1⟩
  have allocated := observed.2.1
  cases call : Compiler.ZigAir.Memory.allocate (before safety empty n).memory.memory (.array 2 word) with
  | error fault => simp only [call, Except.map] at allocated; contradiction
  | ok result =>
    obtain ⟨pointer, native⟩ := result
    simp only [call, Except.map, Except.ok.injEq] at allocated
    simp only [stack, call, Except.toOption, Option.map_some, Option.getD_some, allocated]

theorem preparation_results (safety empty : Bool) (n : Nat) (bounded : n < 5) :
    duplicated safety empty n = (.ok (operands safety empty n, handle safety empty n), (duplicated safety empty n).2) ∧
    made safety empty n = (.ok (object safety empty n), (made safety empty n).2) ∧
    cloned safety empty n = (.ok (copied safety empty n), (cloned safety empty n).2) := by
  have observed := reached_observations safety empty n bounded
  simp only [observations, expected, Prod.mk.injEq] at observed
  exact ⟨Prod.ext observed.2.2.2.2.2.1 rfl, Prod.ext observed.2.2.2.2.2.2.1 rfl, Prod.ext observed.2.2.2.2.2.2.2 rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests
