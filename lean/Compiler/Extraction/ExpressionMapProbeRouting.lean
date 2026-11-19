/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbeLoop

namespace Compiler.Extraction.ExpressionMap.Probe
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Buckets
open Compiler.Extraction.Cache (Key)

def NonFree (state : State) (bucket index : Nat) : Prop :=
  ∃ bits, Metadata.readByte state bucket index = .ok bits ∧ Metadata.isFree bits = false

/-- The original placement invariant for an arbitrary hash function. It makes
no collision-freedom assumption. Connecting that function to the native Wyhash
execution remains a separate source obligation, not a newly trusted callback. -/
structure Routing (hashes : Key → BitVec 64) (state : State) (capacity : BitVec 32)
    (bucket : Nat) (table : OwnedKeys.Table) : Prop where
  entries : ∀ key entry, table key = some entry → ∃ distance, distance < capacity.toNat ∧
    Table.EntryView capacity bucket (slot capacity (hashes key) distance) state key entry ∧
    Metadata.readByte state bucket (slot capacity (hashes key) distance) = .ok (Metadata.occupied (fingerprint (hashes key))) ∧
    ∀ j, j < distance → NonFree state bucket (slot capacity (hashes key) j)

theorem Routing.empty (hashes : Key → BitVec 64) (state : State) (capacity : BitVec 32) (bucket : Nat) :
    Routing hashes state capacity bucket (fun _ => none) :=
  ⟨by intro key entry impossible; cases impossible⟩

theorem fingerprint_byte (fp : BitVec 7) : (Metadata.occupied fp).toNat % 128 = fp.toNat := by
  rw [(Metadata.packed_exact 0 fp).2.2.1]
  have := fp.isLt
  omega

variable {state : State} {capacity : BitVec 32} {bucket : Nat} {hash : BitVec 64} {hashes : Key → BitVec 64}
    {query : Key} {table : OwnedKeys.Table} {distance index first : Nat}

theorem Passed.nonfree (passed : Passed state capacity bucket hash query table distance)
    (inside : j < distance) : NonFree state bucket (slot capacity hash j) := by
  obtain ⟨bits, read, correct⟩ := passed j inside
  exact ⟨bits, read, correct.1⟩

theorem Completed.absent (routing : Routing hashes state capacity bucket table)
    (completed : Completed state capacity bucket (hashes query) query table (.miss index first)) : table query = none := by
  obtain ⟨distance, bounded, selected, passed, _, stopped⟩ := completed
  cases found : table query with
  | none => rfl
  | some entry =>
    obtain ⟨target, inside, view, read, earlier⟩ := routing.entries query entry found
    by_cases visited : target < distance
    · obtain ⟨bits, inspected, correct⟩ := passed target visited
      have equal := Except.ok.inj (inspected.symm.trans read)
      subst bits
      rcases correct.2.2 with unused | wrongFingerprint | notHere
      · have used := (Metadata.packed_exact 0 (fingerprint (hashes query))).2.2.2.1
        rw [used] at unused
        cases unused
      · exact False.elim (wrongFingerprint (fingerprint_byte _))
      · exact False.elim (notHere entry view)
    · have free : Metadata.observe state bucket index = .ok (true, false) := stopped.resolve_right (by omega)
      have zero := Metadata.read_byte_free state bucket index free
      have nonfree : NonFree state bucket index := by
        rw [selected]
        by_cases before : distance < target
        · exact earlier distance before
        · have same : distance = target := by omega
          subst distance
          exact ⟨_, read, (Metadata.packed_exact 0 (fingerprint (hashes query))).2.2.2.2⟩
      obtain ⟨bits, native, notFree⟩ := nonfree
      have equal := Except.ok.inj (native.symm.trans zero)
      subst bits
      cases notFree

/-- getAdapted's value read follows the complete probe. Hash production and
the preceding size-zero fast path are outside this post-hash boundary. -/
def getHashed (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (source : View) : Except Fault (Option (BitVec 32)) := do
  let selected ← lookupLoop state capacity bucket hash query source capacity.toNat (start capacity hash)
  match selected with
  | none => .ok none
  | some index =>
    let .scalar (.int false 32 id) ← Values.read state capacity bucket index | .error .unsupported
    .ok (some (BitVec.ofInt 32 id))

theorem get_hashed_verified (state : State) (capacity : BitVec 32) (bucket : Nat) (hashes : Key → BitVec 64)
    (query : Key) (source : View) (table : OwnedKeys.Table)
    (binding : Table.Binding place safety receiver bucket capacity state table) (power : Power capacity)
    (routing : Routing hashes state capacity bucket table)
    (queryRead : Represents state source query.arguments) (bounded : source.length * 4 < addressLimit) :
    getHashed state capacity bucket (hashes query) query source = .ok ((table query).map OwnedKeys.Entry.id) := by
  obtain ⟨outcome, ran, completed⟩ := run_verified state capacity bucket (hashes query) query source table binding power queryRead bounded
  have lookup : lookupLoop state capacity bucket (hashes query) query source capacity.toNat (start capacity (hashes query)) = .ok outcome.index := by
    rw [← loop_lookup state capacity bucket (hashes query) query source capacity.toNat (start capacity (hashes query)) capacity.toNat]
    change (run state capacity bucket (hashes query) query source).map Outcome.index = _
    rw [ran]; rfl
  cases outcome with
  | hit index =>
    obtain ⟨_, _, entry, found, view⟩ := completed
    simp [getHashed, lookup, Outcome.index, found, view.stored.value, number, bind, Except.bind]
  | miss index first =>
    simp [getHashed, lookup, Outcome.index, completed.absent routing, bind, Except.bind]

end Compiler.Extraction.ExpressionMap.Probe
