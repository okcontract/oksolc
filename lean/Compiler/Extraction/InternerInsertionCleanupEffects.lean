/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Cleanup adapters expose allocator-private effects only. These equalities
cover rejected and partially completed operations as well as successful frees;
they neither roll back effects nor assert that the remaining keys are live. -/
theorem free_keys (external : External σ) (allocator : Nat) (slice : ArgumentSlice)
    (before : Session (Publication.Effects σ)) :
    (free (Publication.external external) allocator slice before).2.effects.keys = before.effects.keys := by
  unfold free
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem destroy_keys (objects : AssemblyItem.Release σ) (allocator object : Nat)
    (before : Session (Publication.Effects σ)) :
    (AssemblyItem.destroy (release objects) allocator object before).2.effects.keys = before.effects.keys := by
  unfold AssemblyItem.destroy
  dsimp only
  split <;> rfl

theorem payload_free_keys (bytes : AssemblyItemDeinit.Release σ) (allocator : Nat) (slice : AssemblyItemDeinit.Bytes)
    (before : Session (Publication.Effects σ)) :
    (AssemblyItemDeinit.free (release bytes) allocator slice before).2.effects.keys = before.effects.keys := by
  unfold AssemblyItemDeinit.free
  split
  · rfl
  · split
    · rfl
    · dsimp only
      split <;> rfl

theorem payload_stage_keys (bytes : AssemblyItemDeinit.Release σ) (allocator : Nat)
    (payload : Option AssemblyItemDeinit.Bytes) (stage : AssemblyItemDeinit.Stage)
    (before : AssemblyItemDeinit.State (Publication.Effects σ)) :
    (stage.execute (release bytes) allocator payload before).2.memory.effects.keys = before.memory.effects.keys := by
  unfold AssemblyItemDeinit.Stage.execute
  split
  · rfl
  · cases stage with
    | invalidate => rfl
    | payload =>
      cases payload with
      | none => rfl
      | some slice =>
        have kept := payload_free_keys bytes allocator slice before.memory
        cases ran : AssemblyItemDeinit.free (release bytes) allocator slice before.memory with
        | mk result reached => simpa only [ran] using kept

theorem payload_execute_keys (bytes : AssemblyItemDeinit.Release σ) (allocator : Nat)
    (payload : Option AssemblyItemDeinit.Bytes) (stages : List AssemblyItemDeinit.Stage)
    (before : AssemblyItemDeinit.State (Publication.Effects σ)) :
    (AssemblyItemDeinit.execute (release bytes) allocator payload stages before).2.memory.effects.keys = before.memory.effects.keys := by
  induction stages generalizing before with
  | nil => rfl
  | cons stage rest ih =>
    have kept := payload_stage_keys bytes allocator payload stage before
    cases ran : stage.execute (release bytes) allocator payload before with
    | mk result reached =>
      simp only [ran] at kept
      cases result with
      | error fault => simpa only [AssemblyItemDeinit.execute, ran] using kept
      | ok value => cases value; simpa only [AssemblyItemDeinit.execute, ran] using (ih reached).trans kept

theorem item_deinit_keys (bytes : AssemblyItemDeinit.Release σ) (allocator : Nat)
    (object : Compiler.ZigAir.Memory.Address) (before : Session (Publication.Effects σ)) :
    (AssemblyItemDeinit.Native.run (release bytes) allocator object before).2.memory.effects.keys = before.effects.keys := by
  unfold AssemblyItemDeinit.Native.run
  split
  · rfl
  · rename_i payload read
    have kept := payload_execute_keys bytes allocator payload AssemblyItemDeinit.assemblyItemDeinitCode ⟨before, false⟩
    change (AssemblyItemDeinit.run (release bytes) allocator payload before).2.memory.effects.keys = before.effects.keys at kept
    cases ran : AssemblyItemDeinit.run (release bytes) allocator payload before with
    | mk result reached =>
      simp only [ran] at kept
      cases result with
      | error fault => exact kept
      | ok value =>
        cases value
        exact (congrArg Publication.Effects.keys (AssemblyItemDeinit.Native.finish_retains object reached.memory).2).trans kept

theorem expression_stage_keys (ops : Operations σ) (allocator : Nat) (descriptor : Compiler.ZigAir.Memory.Address)
    (stage : ExpressionDeinit.Stage) (before : ExpressionDeinit.State (Publication.Effects σ)) :
    (ExpressionDeinit.Native.step (release ops.bytes) (release ops.objects) (Publication.external ops.arguments)
      allocator descriptor stage before).2.memory.effects.keys = before.memory.effects.keys := by
  unfold ExpressionDeinit.Native.step
  split
  · rfl
  · cases stage with
    | itemValue =>
      dsimp only
      split
      · rfl
      · rename_i object read
        have kept := item_deinit_keys ops.bytes allocator object before.memory
        cases ran : AssemblyItemDeinit.Native.run (release ops.bytes) allocator object before.memory with
        | mk result reached => simpa only [ran] using kept
    | itemAllocation =>
      dsimp only
      split
      · rfl
      · rename_i object read
        split
        · rfl
        · have kept := destroy_keys ops.objects allocator object.allocation before.memory
          cases ran : AssemblyItem.destroy (release ops.objects) allocator object.allocation before.memory with
          | mk result reached => simpa only [ran] using kept
    | arguments =>
      dsimp only
      split
      · rfl
      · rename_i slice read
        have kept := free_keys ops.arguments allocator slice before.memory
        cases ran : free (Publication.external ops.arguments) allocator slice before.memory with
        | mk result reached => simpa only [ran] using kept
    | invalidate => dsimp only; split <;> rfl

theorem expression_execute_keys (ops : Operations σ) (allocator : Nat) (descriptor : Compiler.ZigAir.Memory.Address)
    (stages : List ExpressionDeinit.Stage) (before : ExpressionDeinit.State (Publication.Effects σ)) :
    (ExpressionDeinit.executeStages (ExpressionDeinit.Native.step (release ops.bytes) (release ops.objects)
      (Publication.external ops.arguments) allocator descriptor) stages before).2.memory.effects.keys = before.memory.effects.keys := by
  induction stages generalizing before with
  | nil => rfl
  | cons stage rest ih =>
    have kept := expression_stage_keys ops allocator descriptor stage before
    cases ran : ExpressionDeinit.Native.step (release ops.bytes) (release ops.objects)
        (Publication.external ops.arguments) allocator descriptor stage before with
    | mk result reached =>
      simp only [ran] at kept
      cases result with
      | error fault => simpa only [ExpressionDeinit.executeStages, ran] using kept
      | ok value => cases value; simpa only [ExpressionDeinit.executeStages, ran] using (ih reached).trans kept

theorem releaseValue_keys (ops : Operations σ) (allocator : Nat) (before : Frame σ) :
    (memory (releaseValue ops allocator before).2).effects.keys = (memory before).effects.keys := by
  unfold releaseValue
  split
  · rfl
  · rename_i object present
    have kept := item_deinit_keys ops.bytes allocator ⟨object, 0⟩ (memory before)
    cases ran : AssemblyItemDeinit.Native.run (release ops.bytes) allocator ⟨object, 0⟩ (memory before) with
    | mk result reached =>
      simp only [ran] at kept
      cases result <;> exact kept

theorem releaseLast_keys (ops : Operations σ) (allocator container : Nat) (before : Frame σ) :
    (memory (releaseLast ops allocator container before).2).effects.keys = (memory before).effects.keys := by
  unfold releaseLast
  split
  · rfl
  · rename_i descriptor selected
    have kept := expression_execute_keys ops allocator descriptor ExpressionDeinit.expressionDeinitCode ⟨memory before, false⟩
    change (ExpressionDeinit.Native.run (release ops.bytes) (release ops.objects) (Publication.external ops.arguments)
      allocator descriptor (memory before)).2.memory.effects.keys = (memory before).effects.keys at kept
    cases ran : ExpressionDeinit.Native.run (release ops.bytes) (release ops.objects) (Publication.external ops.arguments)
        allocator descriptor (memory before) with
    | mk result reached =>
      simp only [ran] at kept
      cases result <;> exact kept

theorem pop_keys (allocator container : Nat) (before : Frame σ) :
    (memory (pop allocator container before).2).effects.keys = (memory before).effects.keys := by
  rw [pop_memory]
  unfold Pop.Registered.run
  split
  · rfl
  · exact congrArg Publication.Effects.keys (Pop.Registered.finish_reached _ _ _).2

/-- Every native insertion cleanup action retains the actual key table. No
success, valid-memory, ownership, or no-alias premise hides partial failures. -/
theorem cleanup_action_keys (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ)) (action : Storage.Release) (owner : Storage.State) (before : Frame σ) :
    (memory ((callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).release
      action owner before).2).effects.keys = (memory before).effects.keys := by
  cases action with
  | value => exact releaseValue_keys ops allocator before
  | lastValue => exact releaseLast_keys ops allocator container before
  | pop => exact pop_keys allocator container before
  | normalized =>
    have kept := free_keys ops.arguments allocator normalized (memory before)
    cases ran : free (Publication.external ops.arguments) allocator normalized (memory before) with
    | mk result reached => simpa only [callbacks, Insertion.callbacks, ran] using kept
  | arguments =>
    simp only [callbacks, Insertion.callbacks]
    split
    · rfl
    · rename_i slice present
      have kept := free_keys ops.arguments allocator slice (memory before)
      cases ran : free (Publication.external ops.arguments) allocator slice (memory before) with
      | mk result reached => simpa only [ran] using kept
  | allocation =>
    simp only [callbacks, Insertion.callbacks, itemOperations, AssemblyItem.Creation.Insertion.operations]
    split
    · rfl
    · rename_i object present
      have kept := destroy_keys ops.objects allocator object (memory before)
      cases ran : AssemblyItem.destroy (release ops.objects) allocator object (memory before) with
      | mk result reached => simpa only [memory, ran] using kept

/-- Source-order unwinding retains the table even if an intermediate release
rejects. In particular the normalized owner release is included, not inferred
from the inner last-value/pop sequence. -/
theorem cleanup_sequence_keys (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ)) (actions : List Storage.Release) (owner : Storage.State) (before : Frame σ) :
    (memory (Storage.releaseAll
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth)
      actions owner before).2).effects.keys = (memory before).effects.keys := by
  induction actions generalizing owner before with
  | nil => rfl
  | cons action rest ih =>
    have kept := cleanup_action_keys ops allocate runtimeSafety allocator container source itemSource input key normalized
      cells value graph growth action owner before
    cases ran : (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).release
        action owner before with
    | mk result reached =>
      simp only [ran] at kept
      cases result with
      | error reason => simpa only [Storage.releaseAll, Storage.Release.execute, ran] using kept
      | ok result =>
        cases result
        simpa only [Storage.releaseAll, Storage.Release.execute, ran] using (ih (action.run owner) reached).trans kept

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
