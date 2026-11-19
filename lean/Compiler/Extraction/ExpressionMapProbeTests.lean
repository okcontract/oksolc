/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbeMemory
import Compiler.Extraction.ExpressionMapCandidateTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapProbeTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ExpressionMap.Buckets ExpressionMap
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)
open MapTableTests (prepared firstKey secondKey empty_custody)

/-- Every key collides, including its fingerprint, and the first probe wraps
from slot seven to zero. No hash injectivity is available to these proofs. -/
def collision (_ : Key) : BitVec 64 := (93 <<< 57) ||| 7

theorem masked_wrap : Probe.advance 8 7 = 0 := by decide +kernel
theorem source_hash_parts : Probe.start 8 (collision firstKey) = 7 ∧
    Probe.fingerprint (collision firstKey) = 93 := by decide +kernel

def first (safety : Bool) : World (Publication.Effects Nat) :=
  (publishSelectedNew .localMap safety 4 8 5 7 93 firstKey ⟨0, []⟩ 37 (prepared safety)).2

def second (safety : Bool) : World (Publication.Effects Nat) :=
  (publishSelectedNew .localMap safety 4 8 5 0 93 secondKey ⟨0, []⟩ 53 (first safety)).2

theorem first_probe (safety : Bool) :
    Probe.run (prepared safety).memory.memory 8 5 (collision firstKey) firstKey (view ⟨0, []⟩) = .ok (.miss 7 8) := by
  cases safety <;> decide +kernel

theorem second_probe (safety : Bool) :
    Probe.run (first safety).memory.memory 8 5 (collision secondKey) secondKey (view ⟨0, []⟩) = .ok (.miss 0 8) := by
  cases safety <;> decide +kernel

/-- Hash-independent preparation shared by collision and computed-hash clients. -/
theorem initialized_owner (hashes : Key → BitVec 64) (safety : Bool) (meaning : Meaning) :
    Facts safety 7 3 sentinel 0 (prepared safety) [] ∧
    Probe.Invariant hashes .localMap safety 4 5 8 6 (prepared safety).memory.memory (prepared safety).memory.effects.keys ∧
    (prepared safety).memory.effects.keys = (fun _ => none) := by
  obtain ⟨world, ran, facts, ready, _, _, _⟩ := MapCapacityTests.from_initialized_owner safety meaning
  have same : prepared safety = world := congrArg Prod.snd ran
  rw [← same] at facts ready
  have keys : (prepared safety).memory.effects.keys = fun _ => none :=
    prepareGrowth_keys .embedded safety 3 1 _ (owned safety)
  have inv : Probe.Invariant hashes .localMap safety 4 5 8 6 (prepared safety).memory.memory (prepared safety).memory.effects.keys := by
    rw [keys]; exact Probe.Invariant.of_ready hashes ready ⟨3, rfl⟩
  exact ⟨facts, inv, keys⟩

/-- Existing initialized-owner preparation now feeds the complete scan and
publication twice. Neither destination, absence, vacancy nor post-state binding
is an input to the production theorem. Both later lookups consume its result. -/
theorem repeated_from_initialized_owner (safety : Bool) (meaning : Meaning) :
    Facts safety 7 3 sentinel 0 (second safety) [] ∧
    Probe.Invariant collision .localMap safety 4 5 8 4 (second safety).memory.memory (second safety).memory.effects.keys ∧
    Probe.getHashed (second safety).memory.memory 8 5 (collision firstKey) firstKey (view ⟨0, []⟩) = .ok (some 37) ∧
    Probe.getHashed (second safety).memory.memory 8 5 (collision secondKey) secondKey (view ⟨0, []⟩) = .ok (some 53) := by
  obtain ⟨facts, inv, keys⟩ := initialized_owner collision safety meaning
  obtain ⟨outcome, probed, post⟩ := facts.probe_then_publish collision .localMap 4 5 8 6 (by intro impossible; cases impossible)
    inv (by decide) firstKey ⟨0, []⟩ 37 rfl (empty_custody _)
  have selected : outcome = .miss 7 8 := Except.ok.inj (probed.symm.trans (first_probe safety))
  subst outcome
  obtain ⟨a, published, aFacts, aInv, aKeys, _⟩ := post
  have firstSame : first safety = a := congrArg Prod.snd published
  rw [← firstSame] at aFacts aInv aKeys
  obtain ⟨outcome, probed, post⟩ := aFacts.probe_then_publish collision .localMap 4 5 8 5 (by intro impossible; cases impossible)
    aInv (by decide) secondKey ⟨0, []⟩ 53 rfl (empty_custody _)
  have selected : outcome = .miss 0 8 := Except.ok.inj (probed.symm.trans (second_probe safety))
  subst outcome
  obtain ⟨b, published, bFacts, bInv, bKeys, _⟩ := post
  have secondSame : second safety = b := congrArg Prod.snd published
  rw [← secondSame] at bFacts bInv bKeys
  refine ⟨bFacts, bInv, ?_, ?_⟩
  · rw [bFacts.lookup_hashed collision .localMap 4 5 8 4 bInv firstKey ⟨0, []⟩ rfl (empty_custody _), bKeys, aKeys, keys]
    decide +kernel
  · rw [bFacts.lookup_hashed collision .localMap 4 5 8 4 bInv secondKey ⟨0, []⟩ rfl (empty_custody _), bKeys]
    simp [OwnedKeys.store]

open Compiler.ZigAir.Memory

def setByte (state : Compiler.ZigAir.Memory.State) (index : Nat) (bits : BitVec 8) : Compiler.ZigAir.Memory.State :=
  (store state (Metadata.pointer 1 index) (Metadata.value bits)).toOption.getD state

/-- A raw probe fixture covers a complete cycle of tombstones, including the
terminal metadata read after the limit reaches zero. This does not certify remove. -/
def allTombstones : Compiler.ZigAir.Memory.State := (List.range 8).foldl (fun state index => setByte state index 1) MapNewTests.initialized

theorem exhausted_remembers_first :
    Probe.run allTombstones 8 1 (collision firstKey) firstKey ⟨0, 0, 0⟩ = .ok (.miss 7 7) := by decide +kernel

theorem exhausted_lookup_absent :
    Probe.getHashed allTombstones 8 1 (collision firstKey) firstKey ⟨0, 0, 0⟩ = .ok none := by decide +kernel

theorem earliest_tombstone_selected : Probe.select 8 3 7 = 7 := by decide +kernel

theorem free_before_tombstone_stops :
    Probe.run (setByte allTombstones 7 0) 8 1 (collision firstKey) firstKey ⟨0, 0, 0⟩ = .ok (.miss 7 8) := by decide +kernel

theorem invalid_unused_byte_rejected : ¬Probe.Canonical (setByte allTombstones 7 2) 8 1 := by
  intro canonical
  have impossible := canonical 7 (by decide) 2 (by decide +kernel)
  rcases impossible with zero | one | used <;> contradiction

theorem non_power_capacity_rejected : ¬Probe.Power 7 := by
  rintro ⟨shift, equal⟩
  have bound : shift < 3 := by
    by_cases small : shift < 3
    · exact small
    · have power := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ shift by omega)
      change 7 = 2 ^ shift at equal
      omega
  have cases : shift = 0 ∨ shift = 1 ∨ shift = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> contradiction

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapProbeTests
