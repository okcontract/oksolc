/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorJointReturn
import Compiler.Extraction.InternerRecursiveProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (env : AddressMask.Environment) (other : Meaning) (model : Interner.Primitives) (debug : AssemblyItem.Fields.Values)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (rows : List Storage.Cell)
    (parent : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (leading trailing : List ProtocolEvent)

/-- The same five-field recorded step used by finite recursion, with the
child-history layer needed by the joint item proof. -/
abbrev jointStep := NativeRecursion.ProtocolTrace.step ops allocate safety owner
  (Dispatch.wordDispatchMeaning env other) base growth usizeBits (ChildTrace.constructors children observations)
  (ChildTrace.liftObservations observations)

variable {capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
include facts admitted typed valid capacityQuery

theorem step_borrowed_joint (slice : ArgumentSlice) (opcode : Opcode) (expected : Word)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (privateSource : Caller.SourcePrivate (view slice) before.memory.effects.keys)
    (array : ArraySource (view slice) before.memory.memory)
    (evaluated : (Interner.constructorCode.operationRequest opcode slice.items).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read slice.items Interner.constructorCode.sequence = some expected)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode slice.items).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode slice.items).item)
    (joint : JointEntry ops allocate safety owner usizeBits base growth children observations env other debug (view slice)
      (Interner.constructorCode.operationRequest opcode slice.items) rows parent model before leading trailing) :
    JointPost model (Interner.constructorCode.operationRequest opcode slice.items) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((jointStep ops allocate safety owner usizeBits base growth children observations env other).borrowedOperation
        slice.address opcode slice.items debug before leading) expected :=
  item_joint_verified ops allocate safety owner usizeBits base growth children observations env other debug (view slice)
    (Interner.constructorCode.operationRequest opcode slice.items) rows parent joint facts represented privateSource array admitted
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery expected valid evaluated
    (by intro impossible; have wrong : (1#32 : BitVec 32) = 2#32 := impossible; contradiction)

theorem step_constant_joint (value : Word) (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other)
    (classificationQuery : model.deterministic (Interner.constructorCode.constantRequest value).item =
      base.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (joint : JointEntry ops allocate safety owner usizeBits base growth children observations env other debug ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) rows parent model before leading trailing) :
    JointPost model (Interner.constructorCode.constantRequest value) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((jointStep ops allocate safety owner usizeBits base growth children observations env other).constant value debug before leading) value := by
  have represented : Represents before.memory.memory ⟨0, 0, 0⟩ [] := ⟨rfl, by intro index inside; simp at inside⟩
  have privateSource : Caller.SourcePrivate ⟨0, 0, 0⟩ before.memory.effects.keys := by
    intro key old found nonempty impossible
    exact (impossible rfl).elim
  have evaluated : (Interner.constructorCode.constantRequest value).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read [] Interner.constructorCode.sequence = some value := by
    simpa [Interner.constructorCode, Interner.ConstructorCode.constantRequest, Scalar.run, Item.eval,
      readArguments, Dispatch.wordDispatchMeaning, Dispatch.wordBaseMeaning, Folding.wordMeaning,
      ArithmeticShift.shiftMeaning, AddressMask.addressMeaning] using pushes value
  exact item_joint_verified ops allocate safety owner usizeBits base growth children observations env other debug ⟨0, 0, 0⟩
    (Interner.constructorCode.constantRequest value) rows parent joint facts represented privateSource (ArraySource.empty rfl) admitted
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery value valid evaluated (fun _ => literals)

theorem step_materialize_joint (id : NodeId) (value : Word) (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other)
    (classificationQuery : model.deterministic (Interner.constructorCode.constantRequest value).item =
      base.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (joint : JointEntry ops allocate safety owner usizeBits base growth children observations env other debug ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) rows parent model before leading trailing) :
    JointPost model (Interner.constructorCode.constantRequest value) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((jointStep ops allocate safety owner usizeBits base growth children observations env other).materialize id value debug before leading) value :=
  step_constant_joint ops allocate safety owner usizeBits base growth children observations env other model debug before rows parent leading trailing
    facts admitted typed valid capacityQuery value pushes literals classificationQuery joint

theorem step_operation_joint (opcode : Opcode) (values : List NodeId) (expected : Word)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read values Interner.constructorCode.sequence = some expected)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (joint : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) → Arguments.Prepared values before source prepared →
      JointEntry ops allocate safety owner usizeBits base growth children observations env other debug source
        (Interner.constructorCode.operationRequest opcode values) rows parent model prepared leading trailing)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    JointPost model (Interner.constructorCode.operationRequest opcode values) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((jointStep ops allocate safety owner usizeBits base growth children observations env other).operation opcode values debug before leading) expected := by
  apply prepared_constructor_joint ops allocate safety owner usizeBits base growth children observations env other debug model
    (Interner.constructorCode.operationRequest opcode values) before rows parent leading trailing
    (Arguments.prepare values) _ (!values.isEmpty) ?_
    (fun source prepared ran => Arguments.prepare_success values before prepared source facts.valid ran)
    (fun fault reached ran => Arguments.error_nonordinary values facts.valid reached fault ran)
    joint facts admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery expected valid evaluated
    (by intro impossible; have wrong : (1#32 : BitVec 32) = 2#32 := impossible; contradiction) (fun _ => localParent)
  dsimp only [jointStep, NativeRecursion.ProtocolTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors, literal]
  cases Arguments.prepare values before with
  | mk result prepared => cases result with
    | error fault => rfl
    | ok source => cases values <;> rfl

theorem step_local_joint (opcode : Opcode) (slice : ArgumentSlice) (selected : Nat) (repeated : NodeId) (first : Bool) (expected : Word)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (inside : first = true → selected < slice.items.length)
    (evaluated : (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read
      (if first then slice.items.set selected repeated else slice.items) Interner.constructorCode.sequence = some expected)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then slice.items.set selected repeated else slice.items)).item)
    (joint : ∀ source prepared, LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) →
      Arguments.Prepared (if first then slice.items.set selected repeated else slice.items) before source prepared →
      JointEntry ops allocate safety owner usizeBits base growth children observations env other debug source
        (Interner.constructorCode.operationRequest opcode (if first then slice.items.set selected repeated else slice.items))
        rows parent model prepared leading trailing)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    JointPost model (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((jointStep ops allocate safety owner usizeBits base growth children observations env other).localOperation
        opcode slice selected repeated first debug before leading) expected := by
  rcases items : slice.items with _ | ⟨left, _ | ⟨right, _ | ⟨extra, tail⟩⟩⟩
  · apply JointPost.rejected
    simp only [jointStep, NativeRecursion.ProtocolTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors, items]
    rfl
  · apply JointPost.rejected
    simp only [jointStep, NativeRecursion.ProtocolTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors, items]
    rfl
  · have good : Good (view slice) [left, right] before := ⟨facts.valid, by simpa only [items] using represented⟩
    have bound : first = true → selected < 2 := by simpa only [items] using inside
    rw [items] at evaluated classificationQuery joint
    apply prepared_constructor_joint ops allocate safety owner usizeBits base growth children observations env other debug model
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
      before rows parent leading trailing (LocalArguments.zigLocal (view slice) selected repeated first) _ true ?_
      (fun source prepared ran => ViewInput.local_input_optional (view slice) source left right repeated selected first before prepared good bound ran)
      (fun fault reached ran => LocalArguments.error_nonordinary left right repeated selected first good bound reached fault ran)
      joint facts admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery expected valid evaluated
      (by intro impossible; have wrong : (1#32 : BitVec 32) = 2#32 := impossible; contradiction) (fun _ => localParent)
    simp only [jointStep, NativeRecursion.ProtocolTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors, items, namedLocal, ↓reduceIte]
    cases LocalArguments.zigLocal (view slice) selected repeated first before with
    | mk result prepared => cases result <;> rfl
  · apply JointPost.rejected
    simp only [jointStep, NativeRecursion.ProtocolTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors, items]
    rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
