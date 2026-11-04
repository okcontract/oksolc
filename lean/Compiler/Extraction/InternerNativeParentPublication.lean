/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeParentRelease

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Actual key replacement retains a live enclosing call. Current custody
protects the old key owner; the child's original normalization provenance
separates the new key from the parent's source and normalized allocation.
Typed item reads rule out aliasing any retired argument word array. -/
theorem CallFrame.publication_completed
    {safety : Bool} {allocator owner : Nat} {rows currentRows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before world : World (Publication.Effects σ)}
    {childSource : View} {childRequest : Interner.Request} {childValues : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator childSource childRequest childValues before taken owned lookup)
    (initial : CallFrame safety allocator owner rows source values normalized address native parent before)
    (reached : CallFrame safety allocator owner rows source values normalized address native parent world)
    (host : External σ) (key : Key) (id : NodeId) (effects : σ)
    (after : OwnedKeys.Physical.State (Publication.Effects σ))
    (aligned : key.arguments = owned.items)
    (projected : world.graph.representatives = some currentRows)
    (custody : Caller.GraphCustody allocator owned currentRows world.memory)
    (completed : OwnedKeys.Physical.Completed (Publication.external host) key ⟨owned.address, id⟩
      ⟨world.memory.effects.keys, { world.memory with effects := ⟨world.memory.effects.keys, effects⟩ }⟩ after)
    (outer : parent (Publication.commit key id world (.ok (), after)).2) :
    CallFrame safety allocator owner rows source values normalized address native parent
      (Publication.commit key id world (.ok (), after)).2 := by
  obtain ⟨added, data, capacity, facts, parentCustody, privateSource⟩ := reached.1.1
  have sameRows := Option.some.inj (facts.projected.symm.trans projected)
  have privateOwned : Caller.GraphCustody allocator owned (rows ++ added) world.memory := sameRows.symm ▸ custody
  have kept := facts.publication_completed host key owned id effects after aligned privateOwned completed
  let published := (Publication.commit key id world (.ok (), after)).2
  have keys : published.memory.effects.keys = OwnedKeys.store world.memory.effects.keys key ⟨owned.address, id⟩ :=
    congrArg OwnedKeys.State.table completed.logical
  have parentLive : SliceValid allocator published.memory.heap normalized := by
    rcases parentCustody.live with empty | stored
    · exact Or.inl empty
    · by_cases empty : normalized.items = []
      · exact Or.inl empty
      · exact Or.inr ((completed.registry_frame _ _ _ _ _ normalized.address (by
          intro old found nonempty alias
          exact parentCustody.apart key old found nonempty ⟨empty, alias.symm⟩)).trans stored)
  have custodyKept := origin.custody_after_publication normalized initial.1.2.2.1
    parentCustody.toCustody published.memory parentLive keys
  have held : Held allocator source values owned world := by
    refine ⟨reached.1.2.1, privateOwned.live, ?_⟩
    intro nonempty
    have length : source.length ≠ 0 := by
      rw [← initial.1.2.1.2.1]; exact Nat.ne_of_gt (List.length_pos_iff.mpr nonempty)
    obtain ⟨cell, found⟩ := initial.1.2.1.backed length
    exact (origin.freshNative _ cell found).symm
  have sourceKept := (Publication.completion_held host allocator source values key owned id world _ after
    (privateOwned.publication source key aligned privateSource facts.live) held completed).1
  have itemKept := reached.2.1.frame (completed.frame address.allocation (by
    intro old found nonempty
    obtain ⟨⟨cell, located, typed, _⟩, _⟩ :=
      facts.valid.related allocator old.address key.arguments nonempty ((facts.live key old found).resolve_left nonempty)
    exact reached.2.1.apart_words old.address key.arguments.length cell located typed))
  exact ⟨⟨⟨added, data, capacity, kept, ⟨custodyKept, parentCustody.operands⟩,
    origin.source_private_after_publication source values initial.1.2.1 privateSource keys⟩,
    sourceKept, parentLive, reached.1.2.2.2⟩, itemKept, outer,
    reached.arraySource.frame (fun nonempty _ found =>
      (completed.frame _ (fun old stored length => privateSource key old stored length nonempty)).trans found)⟩

/-- Both actual probe outcomes preserve the live parent. Refusal reuses the
private frame; successful insertion/replacement uses the existing physical
completion. Only the next outer predicate retains its publication law. -/
theorem CallFrame.publish_parent
    {safety : Bool} {allocator owner : Nat} {rows parentRows : List Storage.Cell}
    {source parentSource : View} {request : Interner.Request} {values parentValues : List NodeId}
    {normalized parentNormalized : ArgumentSlice} {lookup : Handle}
    {address parentAddress : Compiler.ZigAir.Memory.Address}
    {native parentNative : AssemblyClone.NativeFields.ItemValue}
    {outer : World (Publication.Effects σ) → Prop} {before world : World (Publication.Effects σ)}
    {taken : State (Publication.Effects σ)}
    (origin : Caller.Origin allocator source request values before taken normalized lookup)
    (initial : CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized
      parentAddress parentNative outer before)
    (frame : CallFrame safety allocator owner rows source request.arguments normalized address native
      (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer) world)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (key : Key) (id : NodeId)
    (aligned : key.arguments = normalized.items)
    (publicationOuter : outer (Publication.publish hostProbe host allocator source key normalized id world).2) :
    CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer
      (Publication.publish hostProbe host allocator source key normalized id world).2 := by
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1.1
  have input := custody.publication source key aligned privateSource facts.live
  cases response : hostProbe key (Publication.forget world.memory) with
  | mk accepted effects =>
    cases accepted with
    | false =>
      have called := Publication.publish_oom hostProbe host allocator source key normalized id world effects
        (Publication.admit_complete _ _ _ _ _ input) response
      rw [called] at publicationOuter ⊢
      exact CallFrame.private_frame origin initial frame.parent facts.projected custody
        ⟨facts.valid.memory, facts.valid.related, facts.valid.injected⟩
        ⟨rfl, fun _ _ found _ => ⟨found, rfl⟩⟩ publicationOuter
    | true =>
      obtain ⟨after, called, completed, _⟩ := Publication.publish_success hostProbe host allocator source key normalized id world effects
        facts.valid input custody.live response
      rw [called] at publicationOuter ⊢
      exact CallFrame.publication_completed origin initial frame.parent host key id effects after aligned
        facts.projected custody completed publicationOuter

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
