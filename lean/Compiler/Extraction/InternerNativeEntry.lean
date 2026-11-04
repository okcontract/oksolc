/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStep
import Compiler.Extraction.InternerNativeEntryLeaf
import Compiler.Extraction.InternerNativeEntryFailure
import Compiler.Extraction.InternerNativeClassificationFailure
import Compiler.Extraction.InternerNativeTakeFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray Recursive

/-- Decompose every ordinary native invocation using its actual entry prefix.
It either returns with unchanged graph and retained native allocations, or
reaches a taken miss. Preparation and initialization rejection remain
nonordinary. No child, word, or final-frame contract is assumed. -/
theorem invocation_entry (safety : Bool) (owner usizeBits capacity : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (host : External σ)
    (children : Constructors (Publication.Effects σ))
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    ordinary actual.1 = true →
      EntryLeaf safety base.allocator owner rows before request actual ∨
        ∃ site : ProtocolTrace.TakenSite σ, site.Reached base source request debug before := by
  dsimp only
  let p := (context base owner usizeBits children debug).primitives source
  let actual := invoke base.external base.budget base.allocator p base.queries source request debug before
  intro completed
  cases made : prepare request.item debug before with
  | mk result constructed =>
    cases result with
    | error fault =>
      have rejected := prepare_error_nonordinary request.item debug before constructed fault made
      have ran := invoke_rejected base.external base.budget base.allocator p base.queries source request debug
        before constructed fault made
      rw [ran] at completed
      simp only [rejected, Bool.false_eq_true] at completed
    | ok address =>
      have item := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
      cases room : base.queries.atCapacity constructed.graph with
      | true =>
        have checked := invoke_entry_failed_native host base.budget base.allocator owner capacity safety data rows
          p base.queries source request debug before constructed address (.language .capacity)
          facts represented admitted domain typed made rfl (Or.inl ⟨room, rfl⟩)
        rw [← external] at checked
        obtain ⟨result, native, _, closed, graph, keys, memory, registry⟩ := checked
        exact Or.inl (EntryLeaf.of_native result native closed graph keys memory registry
          (by intro _ impossible; cases impossible))
      | false =>
        obtain ⟨memory, allocated⟩ := prepare_scratch request.item debug before constructed address facts.valid domain typed made
        let pointer := Compiler.ZigAir.Memory.Value.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩
        cases initialized : Caller.initLookup base.external base.budget base.allocator source
            ⟨constructed.memory.memory.nextId, 0, 2⟩ request
            ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ with
        | mk result prepared =>
          cases result with
          | error fault =>
            cases ordinaryFault : ordinary (.error fault : Except Fault NodeId) with
            | false =>
              have rejected := invoke_init_rejected base.external base.budget base.allocator p base.queries source request debug
                before constructed address pointer memory fault prepared made room allocated initialized ordinaryFault
              rw [rejected] at completed
              simp only [ordinaryFault, Bool.false_eq_true] at completed
            | true =>
              have checked := invoke_entry_failed_native host base.budget base.allocator owner capacity safety data rows
                p base.queries source request debug before constructed address fault facts represented admitted domain typed made
                ordinaryFault (Or.inr ⟨room, by
                  intro otherMemory otherAllocated
                  have same := (Prod.mk.inj (Except.ok.inj (otherAllocated.symm.trans allocated))).2
                  subst otherMemory
                  exact ⟨prepared, by simpa only [external] using initialized⟩⟩)
              rw [← external] at checked
              obtain ⟨result, native, _, closed, graph, keys, memory, registry⟩ := checked
              exact Or.inl (EntryLeaf.of_native result native closed graph keys memory registry
                (by intro _ impossible; cases impossible))
          | ok values =>
            obtain ⟨key, keyed⟩ := Caller.initialized_key base.external base.budget base.allocator source
              ⟨constructed.memory.memory.nextId, 0, 2⟩ request _ prepared values initialized
            cases classified : base.queries.deterministic request.item with
            | error error =>
              cases ordinaryError : ordinary (.error (.language error) : Except Fault NodeId) with
              | false =>
                have rejected := invoke_classification_rejected base.external base.budget base.allocator p base.queries source request debug
                  before constructed address pointer memory values prepared error made room allocated initialized classified ordinaryError
                rw [rejected] at completed
                simp only [ordinaryError, Bool.false_eq_true] at completed
              | true =>
                have routed := Caller.find_classification_failed base.external base.budget base.allocator
                  (p address (input request.item debug)) base.queries source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
                  { constructed with memory := { constructed.memory with memory } } values prepared error room initialized classified
                have checked := invoke_initialized_native host base.budget base.allocator owner capacity safety data rows
                  p base.queries source request debug before constructed address pointer memory values prepared (.error (.language error))
                  facts represented admitted domain typed made room allocated (by simpa only [external] using initialized)
                  ordinaryError (by simpa only [external] using routed)
                rw [← external] at checked
                obtain ⟨result, native, _, closed, graph, keys, memory, registry, _⟩ := checked
                exact Or.inl (EntryLeaf.of_native result native closed graph keys memory registry
                  (by intro _ impossible; cases impossible))
            | ok deterministic =>
              have miss (missed : deterministic = true → constructed.graph.table key = none) :
                  EntryLeaf safety base.allocator owner rows before request actual ∨
                    ∃ site : ProtocolTrace.TakenSite σ, site.Reached base source request debug before := by
                cases transferred : take base.external base.allocator prepared with
                | mk result taken =>
                  cases result with
                  | error fault =>
                    have checked := invoke_take_failed_native host base.budget base.allocator owner capacity safety data rows
                      p base.queries source request debug before constructed address pointer memory values prepared taken fault key deterministic
                      facts represented admitted domain typed made room allocated (by simpa only [external] using initialized)
                      classified keyed missed (by simpa only [external] using transferred)
                    rw [← external] at checked
                    obtain ⟨_, result, _, native, _, closed, graph, keys, memory, registry, _⟩ := checked
                    exact Or.inl (EntryLeaf.of_native result native closed graph keys memory registry
                      (by intro _ impossible; cases impossible))
                  | ok ignored =>
                    cases ignored
                    obtain ⟨normalized, lookup, entry⟩ := caller_input host base.budget base.allocator source request debug before constructed
                      address memory pointer values prepared taken key ⟨facts.valid, represented⟩ domain typed admitted made allocated
                      (by simpa only [external] using initialized) (by simpa only [external] using transferred) keyed
                      facts.live facts.unique (privateSource key)
                    exact Or.inr ⟨⟨constructed, address, pointer, memory, values, prepared, taken, key, normalized, lookup, deterministic⟩,
                      made, room, allocated, initialized, classified, keyed, missed, transferred, entry⟩
              cases deterministic with
              | false => exact miss (by intro impossible; cases impossible)
              | true =>
                cases found : constructed.graph.table key with
                | none => exact miss (fun _ => found)
                | some id =>
                  have checked := invoke_cached_native host base.budget base.allocator owner capacity safety data rows
                    p base.queries source request debug before constructed address pointer memory values prepared key id
                    facts represented admitted domain typed made room allocated (by simpa only [external] using initialized)
                    classified keyed found
                  rw [← external] at checked
                  obtain ⟨result, native, _, closed, graph, keys, memory, registry, normalized⟩ := checked
                  exact Or.inl (EntryLeaf.of_native result native closed graph keys memory registry (by
                    intro result same
                    cases same
                    exact ⟨values, key, normalized, keyed, by simpa only [item.graph] using found⟩))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
