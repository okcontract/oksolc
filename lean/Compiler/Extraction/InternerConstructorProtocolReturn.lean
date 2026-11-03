/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolTrace
import Compiler.Extraction.InternerConstructorNativeReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace

/-- The existing result, scoped session and caller-local protocol metadata.
This is an observation of the native execution, not a second native state. -/
def outcome (ran : Except Fault NodeId × Recorded σ) :=
  (ran.1, scopeView ran.2, ran.2.events, ran.2.tokens.incomplete)

/-- Ordinary retirement and semantic rejection preserve the same complete
observation. The native stack change remains explicit in `retire_native`. -/
theorem retire_outcome (mark : Nat) (ran : Except Fault NodeId × Recorded σ) :
    outcome (retire mark ran) = outcome ran := by
  have result : (retire mark ran).1 = ran.1 := by
    unfold retire TemporaryArguments.unwind
    split <;> rfl
  simp only [outcome, result, retire_scope, (retire_metadata mark ran).1, (retire_metadata mark ran).2]

/-- The actual item and scratch wrappers return in native nesting order, with
both original marks. Their complete scoped/protocol observation is the caller's
observation, without a caller preservation or cleanup-success premise. -/
theorem item_returned (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State) (leading : List ProtocolEvent)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : context.queries.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory)) :
    let called := Caller.ProtocolTrace.find context.external context.budget context.allocator
      (context.primitives source address (input request.item debug)) context.queries
      (ports source address (input request.item debug)) source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      (start { constructed with memory := { constructed.memory with memory } } leading)
    let actual := item context ports source request debug before leading
    actual = retire before.memory.memory.nextId (retire constructed.memory.memory.nextId called) ∧
      outcome actual = outcome called ∧
      (actual.1, actual.2.native) =
        (if ordinary called.1 then
          (called.1, { called.2.native with world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId called.2.native.world })
         else (called.1, called.2.native)) := by
  intro called actual
  have captured : actual = retire before.memory.memory.nextId (retire constructed.memory.memory.nextId called) := by
    simp only [actual, item, made, frame, room, Bool.false_eq_true, ↓reduceIte, allocated]
    rfl
  refine ⟨captured, ?_, ?_⟩
  · rw [captured, retire_outcome, retire_outcome]
  · have native := invoke_after_scratch context.external context.budget context.allocator (context.primitives source)
      context.queries source request debug before constructed address pointer memory made room allocated
    have erased := item_erases context ports source request debug before leading
    have caller := Caller.ProtocolTrace.find_erases context.external context.budget context.allocator
      (context.primitives source address (input request.item debug)) context.queries
      (ports source address (input request.item debug)) source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } leading
    rw [caller] at native
    exact erased.symm.trans native

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
