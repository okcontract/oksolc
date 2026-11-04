/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorItemTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)

abbrev debug := AssemblyItem.Initializers.Tests.debug

/-- Fixture coordinates only: every prefix component below is the existing
constructor allocation/assignment or caller allocation/init/take operation. -/
structure Call where
  request : Interner.Request
  source : View
  before : World (Publication.Effects Nat)

namespace Call
def native (call : Call) := input call.request.item debug
def address (call : Call) : Compiler.ZigAir.Memory.Address := ⟨call.before.memory.memory.nextId, 0⟩
def constructed (call : Call) := (prepare call.request.item debug call.before).2
def stack (call : Call) :=
  ((Compiler.ZigAir.Memory.allocate call.constructed.memory.memory (.array 2 word)).toOption.map Prod.snd).getD call.constructed.memory.memory
def prepared (call : Call) := Caller.initLookup (Publication.external ops.arguments) 160 7 call.source
  ⟨call.before.memory.memory.nextId + 1, 0, 2⟩ call.request
  ⟨{ call.constructed with memory := { call.constructed.memory with memory := call.stack } }, { lookup := none }⟩
@[irreducible] def taken (call : Call) := take (Publication.external ops.arguments) 7 call.prepared.2
def normalized (call : Call) : ArgumentSlice := ⟨call.before.memory.memory.nextId + 2, call.request.arguments⟩
def lookup (call : Call) : Handle :=
  ⟨match Interner.Scoped.commutative call.request.item with
    | .ok true => ⟨call.before.memory.memory.nextId + 1, 0, call.request.arguments.length⟩
    | _ => call.source, call.request.arguments, none⟩
def key (call : Call) : Key := ⟨call.request.item.kind, call.request.item.instruction.getD 0,
  call.request.item.data, call.request.arguments, call.request.sequence⟩
def observations (call : Call) :=
  ((prepare call.request.item debug call.before).1, call.constructed.memory.memory.nextId,
    Compiler.ZigAir.Memory.allocate call.constructed.memory.memory (.array 2 word),
    call.prepared.1, call.taken.1, call.taken.2.scope, call.before.graph.table call.key,
    Interner.makeKey call.request call.request.arguments)
def expected (call : Call) :=
  ((Except.ok call.address : Except Fault Compiler.ZigAir.Memory.Address), call.before.memory.memory.nextId + 1,
    (Except.ok (.pointer (.pointer true false (.array 2 word)) ⟨call.before.memory.memory.nextId + 1, 0⟩, call.stack) :
      Except Compiler.ZigAir.Memory.Fault (Compiler.ZigAir.Memory.Value × Compiler.ZigAir.Memory.State)),
    (Except.ok call.request.arguments : Except Fault (List NodeId)), (Except.ok () : Except Fault Unit),
    Local.mk (some call.lookup) (some call.normalized) false, (none : Option NodeId),
    (Except.ok call.key : Except Interner.Error Key))

/-- Transport capacity witnesses through the actual item assignment and scratch allocation.
Only address bounds come from the witnesses; all reached cells remain native. -/
theorem prepared_allocations (call : Call) (witness middle last : Compiler.ZigAir.Memory.State)
    (firstPointer secondPointer : Compiler.ZigAir.Memory.Value)
    (valid : Valid call.before.memory) (witnessValid : witness.valid = true)
    (address : call.before.memory.memory.nextAddress = witness.nextAddress)
    (domain : (call.request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (first : Compiler.ZigAir.Memory.allocate witness AssemblyItem.viewType = .ok (firstPointer, middle))
    (second : Compiler.ZigAir.Memory.allocate middle (.array 2 word) = .ok (secondPointer, last)) :
    prepare call.request.item debug call.before = (.ok call.address, call.constructed) ∧
    Prepared call.request.item debug call.before call.constructed ∧
    Compiler.ZigAir.Memory.allocate call.constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨call.before.memory.memory.nextId + 1, 0⟩, call.stack) ∧
    call.stack.nextAddress = last.nextAddress := by
  obtain ⟨after, scratch, made, post, scratchRan, scratchCounter⟩ := prepare_with_scratch call.request.item debug call.before
    witness middle last firstPointer secondPointer valid witnessValid address domain
    AssemblyItem.Initializers.Tests.debug_valid first second
  have same : after = call.constructed := (congrArg Prod.snd made).symm
  rw [same] at made post scratchRan
  have sameStack : call.stack = scratch := by unfold stack; rw [scratchRan]; rfl
  rw [post.nextId, ← sameStack] at scratchRan
  exact ⟨made, post, scratchRan, (congrArg Compiler.ZigAir.Memory.State.nextAddress sameStack).trans scratchCounter⟩

/-- An actual empty borrowed input takes no allocation and retains the reached heap. -/
theorem normalized_empty (call : Call) (arguments : call.request.arguments = [])
    (source : call.source.length = 0) (commutative : Interner.Scoped.commutative call.request.item = .ok false)
    (current : Prepared call.request.item debug call.before call.constructed)
    (allocated : Compiler.ZigAir.Memory.allocate call.constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨call.before.memory.memory.nextId + 1, 0⟩, call.stack)) :
    call.prepared.1 = .ok [] ∧ call.taken.1 = .ok () ∧
    call.taken.2.scope = ⟨some call.lookup, some call.normalized, false⟩ ∧
    call.taken.2.world = { call.constructed with memory := { call.constructed.memory with memory := call.stack } } := by
  have initialized : call.prepared =
      (.ok [], ⟨{ call.constructed with memory := { call.constructed.memory with memory := call.stack } },
        { lookup := some ⟨call.source, [], none⟩ }⟩) := by
    simp only [prepared, Caller.initLookup, commutative, init, Bool.not_false, Bool.true_or, ↓reduceIte, arguments]
  have counter := (Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ allocated).2
  rw [current.nextId] at counter
  refine ⟨congrArg Prod.fst initialized, ?_⟩
  simp only [taken, initialized, take, takeOwned]
  rw [Duplication.run_empty _ _ _ _ _ _ source]
  simp only [lookup, commutative, normalized, counter, arguments]
  exact ⟨trivial, trivial, trivial⟩

theorem prefix_results (call : Call) (observed : call.observations = call.expected) :
    prepare call.request.item debug call.before = (.ok call.address, call.constructed) ∧
    call.constructed.memory.memory.nextId = call.before.memory.memory.nextId + 1 ∧
    Compiler.ZigAir.Memory.allocate call.constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨call.before.memory.memory.nextId + 1, 0⟩, call.stack) ∧
    call.prepared.1 = .ok call.request.arguments ∧ call.taken.1 = .ok () ∧
    call.taken.2.scope = ⟨some call.lookup, some call.normalized, false⟩ ∧
    call.before.graph.table call.key = none ∧ Interner.makeKey call.request call.request.arguments = .ok call.key := by
  simp only [observations, expected, Prod.mk.injEq] at observed
  exact ⟨Prod.ext observed.1 rfl, observed.2⟩
end Call

structure Call.Established (call : Call) (safety : Bool) (backing capacity : Nat) (rows : List Storage.Cell) : Prop where
  item : Prepared call.request.item debug call.before call.constructed
  entry : CallerInput 7 call.source call.address call.request call.request.arguments call.native call.key
    call.constructed call.taken.2 call.normalized call.lookup
  constructed : GraphFacts safety backing capacity call.constructed rows
  taken : GraphFacts safety backing capacity call.taken.2.world rows

/-- The actual item and caller prefix is independent of whether native graph
storage is empty or already allocated. -/
theorem Call.entry (call : Call)
    (good : Good call.source call.request.arguments call.before)
    (linked : call.before.graph.table = OwnedKeys.view call.before.memory.effects.keys)
    (live : OwnedKeys.Live 7 ⟨call.before.memory.effects.keys, call.before.memory.heap⟩)
    (unique : OwnedKeys.Unique call.before.memory.effects.keys)
    (domain : (call.request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (observed : call.observations = call.expected) :
    Prepared call.request.item debug call.before call.constructed ∧
    CallerInput 7 call.source call.address call.request call.request.arguments call.native call.key
      call.constructed call.taken.2 call.normalized call.lookup := by
  obtain ⟨made, count, allocated, initialized, transferred, scope, missed, keyed⟩ := call.prefix_results observed
  have post := (prepare_success _ _ _ _ _ good.1 domain AssemblyItem.Initializers.Tests.debug_valid made).2
  have initializedCall : Caller.initLookup (Publication.external ops.arguments) 160 7 call.source
      ⟨call.constructed.memory.memory.nextId, 0, 2⟩ call.request
      ⟨{ call.constructed with memory := { call.constructed.memory with memory := call.stack } }, { lookup := none }⟩ =
        (.ok call.request.arguments, call.prepared.2) := by
    rw [count]; exact Prod.ext initialized rfl
  obtain ⟨slice, remaining, entry⟩ := caller_input ops.arguments 160 7 call.source call.request debug call.before
    call.constructed call.address call.stack _ call.request.arguments call.prepared.2 call.taken.2 call.key good domain
    AssemblyItem.Initializers.Tests.debug_valid (Normalization.Tests.external_admitted _) made allocated initializedCall
    (by simpa only [Call.taken] using (Prod.ext transferred rfl : call.taken = (.ok (), call.taken.2))) keyed live unique (by
      intro old found _ _
      rw [linked, OwnedKeys.view, found] at missed
      cases missed)
  have same := Local.mk.inj (entry.origin.scope.symm.trans scope)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact ⟨post, entry⟩

/-- Both levels derive native item reads, normalized ownership and the reached
graph from their own production prefixes. No final graph or source contents
are assumed at either recursive boundary. -/
theorem Call.establish (call : Call) (safety : Bool) (backing capacity : Nat) (rows : List Storage.Cell)
    (facts : GraphFacts safety backing capacity call.before rows) (bounded : rows.length ≤ capacity)
    (good : Good call.source call.request.arguments call.before)
    (domain : (call.request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (observed : call.observations = call.expected) : call.Established safety backing capacity rows := by
  obtain ⟨post, entry⟩ := call.entry good facts.linked facts.live facts.unique domain observed
  have constructed := facts.frame bounded post.valid
    ((congrArg Interner.Heap.representatives post.graph).trans facts.projected)
    (congrArg Interner.Heap.table post.graph) (congrArg Publication.Effects.keys post.effects)
    post.memory (by intro id block found; rw [post.heap]; exact found)
  refine ⟨post, entry, constructed, constructed.frame bounded entry.origin.held.1.1 ?_ ?_ entry.keys
    entry.origin.memory entry.origin.registry⟩
  · exact (congrArg Interner.Heap.representatives entry.origin.graph).trans constructed.projected
  · exact congrArg Interner.Heap.table entry.origin.graph

theorem empty_good (world : World (Publication.Effects Nat)) (valid : Valid world.memory) :
    Good ⟨0, 0, 0⟩ [] world :=
  ⟨valid, rfl, fun index inside => False.elim (Nat.not_lt_zero index inside)⟩

namespace Call

/-- A noncommutative source view is borrowed by lookup, then duplicated by the
actual take operation. All returned coordinates come from those allocations. -/
theorem borrowed_taken (call : Call)
    (good : Good call.source call.request.arguments call.before)
    (current : Prepared call.request.item debug call.before call.constructed)
    (allocated : Compiler.ZigAir.Memory.allocate call.constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨call.before.memory.memory.nextId + 1, 0⟩, call.stack))
    (commutative : Interner.Scoped.commutative call.request.item = .ok false)
    (nonempty : call.request.arguments ≠ [])
    (width : (call.stack.nextAddress / 4 + 1) * 4 + call.request.arguments.length * 4 ≤ Compiler.ZigAir.Memory.addressLimit) :
    call.prepared.1 = .ok call.request.arguments ∧
    call.taken.1 = .ok () ∧
    call.taken.2.scope = ⟨some call.lookup, some call.normalized, false⟩ ∧
    call.taken.2.world.memory.memory.nextId = call.before.memory.memory.nextId + 3 ∧
    call.taken.2.world.memory.memory.nextAddress =
      max call.stack.nextAddress ((call.stack.nextAddress / 4 + 1) * 4 + call.request.arguments.length * 4) := by
  let entered : World (Publication.Effects Nat) := { call.constructed with memory :=
    { call.constructed.memory with memory := call.stack } }
  let base := (call.stack.nextAddress / 4 + 1) * 4
  let effects : Publication.Effects Nat := { entered.memory.effects with
    allocator := entered.memory.effects.allocator + call.request.arguments.length * 4 }
  have initialized : call.prepared =
      (.ok call.request.arguments, ⟨entered, { lookup := some call.lookup }⟩) := by
    simp only [Call.prepared, Caller.initLookup, commutative, init, Bool.not_false, Bool.true_or, ↓reduceIte, Call.lookup]
    rfl
  have input : Good call.source call.request.arguments entered := by
    have kept := good_frame _ _ _ _ good current.valid current.memory
    have buffer := caller_buffer call.constructed.memory call.stack _ call.source call.request.arguments
      current.valid kept.2 allocated
    exact ⟨buffer.1, buffer.2.1⟩
  have response : (Publication.external ops.arguments).allocate .duplicate entered.memory
      (call.request.arguments.length * 4) entered.memory.effects = (some base, effects) := by
    change (if false || decide (Compiler.ZigAir.Memory.addressLimit <
        (call.stack.nextAddress / 4 + 1) * 4 + call.request.arguments.length * 4) then none else some _, _) = _
    simp only [Nat.not_lt.mpr width, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rfl
  have fits := (Normalization.Tests.external_admitted (fun _ => false)) .duplicate
    (Publication.forget entered.memory) call.request.arguments base effects.allocator input.1.memory nonempty
    (congrArg (fun result => (result.1, result.2.allocator)) response)
  obtain ⟨after, ran, post⟩ := Duplication.run_admitted entered.memory.heap entered.memory.memory 7 base call.source
    call.request.arguments ((Publication.external ops.arguments).allocate .duplicate entered.memory)
    entered.memory.effects effects input.1.memory input.1.related input.2 nonempty
    (input.1.injected.fresh input.1.memory) response fits
  have reserved := Allocation.reserve_admitted entered.memory.heap entered.memory.memory 7 base call.request.arguments
    ((Publication.external ops.arguments).allocate .duplicate entered.memory) entered.memory.effects effects input.1.memory
    nonempty call.source input.2 (input.1.injected.fresh input.1.memory) response fits
  have advanced := Duplication.run_address _ _ _ _ _ _ _ _ _ _ _ input.2.1.symm reserved
  rw [ran] at advanced
  have counter := (Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ allocated).2
  rw [current.nextId] at counter
  have nextId : after.nextId = call.before.memory.memory.nextId + 3 := by
    simpa only [List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, ↓reduceIte, entered, counter, Nat.add_assoc] using post.nextId
  have nextAddress : after.nextAddress = max call.stack.nextAddress
      ((call.stack.nextAddress / 4 + 1) * 4 + call.request.arguments.length * 4) := advanced
  simp only [Call.taken, initialized, take, takeOwned, Call.lookup, commutative]
  rw [ran]
  simp only [Call.normalized, show entered.memory.memory.nextId = call.before.memory.memory.nextId + 2 from counter]
  exact ⟨trivial, trivial, trivial, nextId, nextAddress⟩

end Call
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
