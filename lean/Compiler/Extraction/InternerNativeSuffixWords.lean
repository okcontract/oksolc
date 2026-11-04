/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeInvocation
import Compiler.Extraction.InternerInsertionNativeReplay
import Compiler.Extraction.InternerCallerRecursionEffects
import Compiler.Extraction.InternerInsertionNativeFields
import Compiler.Extraction.InternerInsertionAllocationReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- These local cleanup actions change memory and scope, never the reached graph.
This includes rejected cleanup; no allocation, lifetime or success is assumed. -/
theorem deinit_graph (external : External σ) (allocator : Nat) (before : State σ) :
    (deinit external allocator before).2.world.graph = before.world.graph := by
  cases found : before.scope.lookup with
  | none => simp only [deinit, found]
  | some handle =>
    cases ran : deinitialize normalizationOwnershipCode external allocator handle before.world.memory with
    | mk result memory => cases result <;> simp only [deinit, found, ran]

theorem cleanup_graph (external : External σ) (allocator : Nat) (before : State σ) :
    (cleanup external allocator before).2.world.graph = before.world.graph := by
  unfold cleanup
  split
  · exact deinit_graph external allocator before
  · cases found : before.scope.slice with
    | none => exact deinit_graph external allocator before
    | some slice =>
      cases ran : free external allocator slice before.world.memory with
      | mk result memory =>
        cases result with
        | error fault => simp only [ran]
        | ok value =>
          cases value
          simp only [ran]
          exact deinit_graph external allocator _

/-- Transport words through the actual cleanup outcome. A cleanup error keeps
the reached graph and replaces the result only as the native finish specifies. -/
theorem Semantic.Ensures.finish (meaning : Meaning) (initial : Interner.Heap)
    (external : External σ) (allocator : Nat) (result : Except Fault α) (before : State σ)
    (post : α → Interner.Heap → Prop)
    (checked : Semantic.Ensures meaning initial result before.world.graph post) :
    let actual := finish external allocator result before
    Semantic.Ensures meaning initial actual.1 actual.2.world.graph post := by
  dsimp only
  cases ordinaryResult : ordinary result with
  | false => simpa only [OwnedCall.finish, ordinaryResult, Bool.false_eq_true, ↓reduceIte] using checked
  | true =>
    have frame := cleanup_graph external allocator before
    cases closed : cleanup external allocator before with
    | mk outcome after =>
      simp only [closed] at frame
      cases outcome with
      | error fault =>
        simp only [OwnedCall.finish, ordinaryResult, ↓reduceIte, closed]
        intro _
        rw [frame]
        exact ⟨(checked ordinaryResult).1, (checked ordinaryResult).2.1, trivial⟩
      | ok value =>
        cases value
        simpa only [OwnedCall.finish, ordinaryResult, ↓reduceIte, closed, frame] using checked

namespace Insertion.Native

/-- A specification law: defined PUSH observations denote their literal word.
This imposes no totality or operand-shape assumption and no native preservation
contract. Arbitrary interpretations of atoms need not satisfy it. -/
def PushValues (meaning : Meaning) : Prop :=
  ∀ value sequence values expected, meaning.atom 2#32 value sequence values = some expected → expected = value

theorem constructor_push_values (other : Meaning) : PushValues (Interner.constructorMeaning other) := by
  intro value sequence values expected evaluated
  simp only [Interner.constructorMeaning] at evaluated
  change (if values.isEmpty then some value else none) = some expected at evaluated
  split at evaluated
  · exact (Option.some.inj evaluated).symm
  · cases evaluated

/-- The candidate's stored word agrees with the evaluated key, including PUSH's
literal representation. Allocation identity has no role in this value law. -/
theorem candidate_value (meaning : Meaning) (read : Read) (item : Item)
    (arguments : List NodeId) (sequence : BitVec 32) (expected : Word)
    (pushes : item.kind = 2#32 → PushValues meaning)
    (evaluated : item.eval meaning read arguments sequence = some expected) :
    (if item.kind == 2#32 then item.data else expected) = expected := by
  by_cases constant : item.kind = 2#32
  · simp [Item.eval, constant] at evaluated
    cases found : readArguments read arguments with
    | none => simp [found] at evaluated
    | some values =>
      simp only [found, Option.bind] at evaluated
      simpa only [constant, beq_self_eq_true, ↓reduceIte] using (pushes constant _ _ _ _ evaluated).symm
  · simp [constant]

/-- Every replay outcome preserves words, even a stream mismatch during partial
cleanup. The input key and the literal law determine the candidate's value;
there is no successful-execution or native-result premise. -/
theorem allocationReplay_safe (input : AssemblyClone.NativeFields.ItemValue) (key : Key)
    (normalized : ArgumentSlice) (meaning : Meaning) (deterministic : Bool) (nextId : Nat)
    (stream : List (Trace.Event Fault)) (mismatch : Fault) (sequence : BitVec 32)
    (before : Interner.Heap) (expected : Word)
    (valid : Interner.Invariant meaning before)
    (pushes : input.item.kind = 2#32 → PushValues meaning)
    (bound : keyCode.run input.item normalized.items sequence = some key)
    (evaluated : key.eval meaning before.read = some expected) :
    Interner.Safe meaning (allocationReplay input key normalized meaning deterministic nextId stream mismatch)
      before (fun id after => after.read id = some expected) := by
  have word := candidate_value meaning before.read input.item normalized.items sequence expected pushes
    ((key_sound meaning before.read input.item normalized.items sequence key bound).symm.trans evaluated)
  have sequenceSame := (key_inputs input.item normalized.items sequence key bound).2
  let candidate := allocationCandidate input key normalized
    ((key.eval meaning before.read).getD 0) deterministic nextId
  have valueSame : candidate.value = expected := by
    simpa only [candidate, allocationCandidate, Storage.Cell.value, evaluated, Option.getD_some] using word
  have checked := Interner.InsertionExecution.action_safe meaning candidate key deterministic
    (Trace.replay stream mismatch) before valid
    (by simpa only [candidate, allocationCandidate, sequenceSame] using bound)
    (by rw [valueSame]; exact evaluated)
  rw [valueSame] at checked
  exact checked

variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator owner : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (slice : ArgumentSlice)
    (deterministic : Bool) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))

/-- Candidate key/value correspondence for this recorded execution and every
ordinary internal outcome. `candidate_words` derives it from the input key and
actual callback descriptors; native memory correspondence remains separate. -/
def CandidateWords (expected : Word) : Prop :=
  ∀ outcome, (execution ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth).1.1 = .ok outcome →
    let captured := recordExecution ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth []
    let candidate := cell input key slice ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects
    keyCode.run candidate.item candidate.arguments candidate.sequence = some key ∧ candidate.value = expected

/-- The actual native callbacks supply the candidate fields on every ordinary
internal outcome. The input key, evaluation and PUSH interpretation supply the
meaning; recording, clone/argument descriptors and candidate words are derived. -/
theorem candidate_words (sequence : BitVec 32) (expected : Word)
    (pushes : input.item.kind = 2#32 → PushValues meaning)
    (bound : keyCode.run input.item slice.items sequence = some key)
    (evaluated : key.eval meaning before.graph.read = some expected) :
    CandidateWords ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth expected := by
  intro outcome completed
  have fields := execution_field_values ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth outcome completed
  have recorded := execution_recorded ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth
    (.base .missingValue) [] [] []
  rw [← congrArg Prod.snd recorded.1] at fields
  let captured := recordExecution ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth []
  have binding := cell_value_binding input key slice ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects fields
  have sequenceSame := (key_inputs input.item slice.items sequence key bound).2
  constructor
  · rw [binding.1, sequenceSame]
    exact bound
  · rw [binding.2, evaluated]
    exact candidate_value meaning before.graph.read input.item slice.items sequence expected pushes
      ((key_sound meaning before.graph.read input.item slice.items sequence key bound).symm.trans evaluated)

/-- The actual native result supplies the replay theorem's execution outcome.
Native rejection remains nonordinary; ordinary allocation failure is retained. -/
theorem insert_ordinary_execution (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType backing rows.length))
    (represented : before.graph.representatives = some rows)
    (completed : ordinary (insert ops allocate safety allocator owner source address meaning input key slice deterministic growth before).1 = true) :
    ∃ outcome, (execution ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth).1.1 = .ok outcome := by
  have selected := checkedExecution_read ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth backing header
  cases ran : execution ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth with
  | mk pair after =>
    cases pair with
    | mk result owned =>
      cases result with
      | error fault =>
        simp only [insert, represented, body, selected, ran] at completed
        cases completed
      | ok outcome => exact ⟨outcome, rfl⟩

/-- Consume the actual transcript's word proof on every ordinary native result.
Only the reached candidate's key/value fields remain local obligations; no
successful-execution, final graph or semantic preservation premise is supplied. -/
theorem insert_replayed_ensures (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType backing rows.length))
    (represented : before.graph.representatives = some rows) (expected : Word)
    (valid : Interner.Invariant meaning before.graph) (evaluated : key.eval meaning before.graph.read = some expected)
    (binding : CandidateWords ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth expected) :
    let actual := insert ops allocate safety allocator owner source address meaning input key slice deterministic growth before
    Semantic.Ensures meaning before.graph actual.1 actual.2.graph (fun id after => after.read id = some expected) := by
  intro actual completed
  obtain ⟨outcome, executed⟩ := insert_ordinary_execution ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth
    backing header represented completed
  have fields := binding outcome executed
  have checked := insert_replayed_verified ops allocate safety allocator owner source address meaning input key slice deterministic rows before growth
    (.base .missingValue) [] [] backing header represented valid outcome executed fields.1 (by rw [fields.2]; exact evaluated)
  refine ⟨checked.1, checked.2.1, ?_⟩
  have word := checked.2.2
  change (match actual.1 with | .error _ => True | .ok id => actual.2.graph.read id = some _) at word
  cases returned : actual.1 with
  | error fault => trivial
  | ok id => simpa only [returned, fields.2] using word

end Insertion.Native

namespace ConstructorItem.NativeRecursion
open Recursive

/-- Derive all completed suffix words from actual native insertion/publication.
The reached frame supplies the native header and publication ownership. The
input key supplies the actual candidate through descriptor preservation; execution
outcome, probe selection, child-failure semantics and cleanup are derived. -/
theorem native_miss_words (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (rows : List Storage.Cell) (values : List NodeId) (slice : ArgumentSlice)
    (parent : World (Publication.Effects σ) → Prop) (key : Key) (lookup : Handle)
    (deterministic simplifying : Bool) (expected : Word) (aligned : key.arguments = slice.items)
    (sequence : BitVec 32) (bound : keyCode.run input.item slice.items sequence = some key)
    (pushes : input.item.kind = 2#32 → Insertion.Native.PushValues meaning) :
    MissWords (Publication.external ops.arguments) base.allocator
      ((context (callerContext ops allocate safety owner meaning base growth) owner usizeBits children debug).primitives source address input)
      (CallFrame safety base.allocator owner rows source values slice address input parent)
      meaning expected key slice lookup deterministic simplifying where
  insertion := by
    intro world frame valid evaluated
    obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
    have words := Insertion.Native.insert_replayed_ensures ops allocate safety base.allocator owner source address meaning input key slice
      deterministic (rows ++ added) world growth data (readHeader_items _ _ _ _ facts.header) facts.projected expected valid evaluated
      (Insertion.Native.candidate_words ops allocate safety base.allocator owner source address meaning input key slice deterministic
        (rows ++ added) world growth sequence expected pushes bound evaluated)
    exact words.finish meaning world.graph (Publication.external ops.arguments) base.allocator _ _ _
  publication := by
    intro _ world id frame valid evaluated actual
    obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1.1
    let ran := Publication.publish ops.probe ops.arguments base.allocator source key slice (Interner.findCode.published.run id) world
    have projected := Publication.publish_projection ops.probe ops.arguments base.allocator source key slice id world
      (ops.probe key (Publication.forget world.memory)).1 (ops.probe key (Publication.forget world.memory)).2 facts.valid
      (custody.publication source key aligned privateSource facts.live) frame.1.2.2.1 rfl
    have words : Semantic.Ensures meaning world.graph ran.1 ran.2.graph (fun _ _ => True) :=
      safe_at meaning world.graph _ _ (Interner.publish (ops.probe key (Publication.forget world.memory)).1 key id) _
        (fun _ => ⟨congrArg Prod.fst projected, congrArg Prod.snd projected⟩)
        (Interner.publish_safe meaning _ key id world.graph expected valid evaluated actual)
    apply Semantic.Ensures.finish
    simpa only [context_publishes, Interner.findCode, Interner.ResultId.run] using
      Semantic.publish_return_safe_at (Publication.callbacks ops.probe ops.arguments base.allocator source
        ((context (callerContext ops allocate safety owner meaning base growth) owner usizeBits children debug).primitives source address input))
        meaning key slice lookup id world expected actual words
  failure := by
    intro _ world fault _ valid
    exact (Semantic.Ensures.error meaning world.graph fault _ valid).finish meaning world.graph
      (Publication.external ops.arguments) base.allocator _ _ _

section
variable {σ : Type} (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (env : AddressMask.Environment) (other : Meaning) (growth : Option (Growth.Registered.Callbacks σ)) (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (modelChildren : Associative.Constructors AssemblyItem.Fields.Values)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared taken : State (Publication.Effects σ))
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle) (rows : List Storage.Cell)
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity constructed rows)
    (entry : Insertion.Native.CallerInput base.allocator source address request values
      (input request.item debug) key constructed taken normalized lookup)
    (privateSource : Caller.SourcePrivate source constructed.memory.effects.keys)
    (array : ArraySource source constructed.memory.memory)
    (parent frame : World (Publication.Effects σ) → Prop) (kept : parent taken.world)
    (locals : ∀ world, frame world → frame
      (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world))
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : base.queries.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (keyed : Interner.makeKey request values = .ok key)
    (transferred : take (Publication.external ops.arguments) base.allocator prepared = (.ok (), taken))

include facts entry privateSource array kept locals made room allocated initialized keyed transferred

/-- The actual native invocation consumes derived suffix semantics. Callers
supply native frame laws; the input key derives candidate and suffix semantics;
proper-child correspondence and word contracts remain guarded by the source. -/
theorem invoke_step_native_verified (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other) (cursor : World (Publication.Effects σ) → Nat) (deterministic : Bool)
    (dispatchCoupled : (deterministic && (request.item.kind == 1)) = true →
      (projectionAt (cursorGraph cursor) (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)
    (expected : Word)
    (frames : MissFrames (Publication.external ops.arguments) base.allocator
      ((context (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits children debug).primitives source address (input request.item debug))
      (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) frame key normalized lookup deterministic
          (deterministic && (request.item.kind == 1)))
    (classifiedAs : base.queries.deterministic request.item = .ok deterministic)
    (missedIf : deterministic = true → constructed.graph.table key = none)
    (item : Prepared request.item debug before constructed)
    (correct : (deterministic && (request.item.kind == 1)) = true →
      Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren)
    (addresses : (deterministic && (request.item.kind == 1)) = true →
      AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation)
    (shifts : (deterministic && (request.item.kind == 1)) = true →
      ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected) :
    let actual := invoke (Publication.external ops.arguments) base.budget base.allocator
      ((context (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits children debug).primitives source) base.queries source request debug before
    FramePost frame actual ∧
      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) := by
  exact invoke_step_verified_cursor safety owner usizeBits (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children modelChildren source request debug
    before constructed address pointer memory values prepared taken key normalized lookup rows facts entry
    privateSource array parent frame kept locals made room allocated initialized keyed transferred cursor deterministic dispatchCoupled
    env other expected frames
    (native_miss_words ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits children debug
      source address (input request.item debug) rows request.arguments normalized parent key lookup deterministic
      (deterministic && (request.item.kind == 1)) expected entry.publication.aligned request.sequence entry.keyed pushes)
    classifiedAs missedIf item correct addresses shifts valid evaluated

end

end ConstructorItem.NativeRecursion

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
