/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Std

namespace Compiler.Extraction.WyhashHash.Tests

/-- Same five-update byte stream as the native capture, including compiler
input shapes and retained/full-block boundaries. Digests are checked by the
kernel; the independent native capture must match all intermediate states. -/
def chunks (index position : Nat) : List Nat → List (List (BitVec 8))
  | [] => []
  | size :: rest => (List.range size).map (fun i => BitVec.ofNat 8 ((position + i) * 17 + index * 29 + 3)) ::
      chunks index (position + size) rest

def vectors : List (List Nat × BitVec 64) := [([4, 1, 32, 0, 4], 8117307482490114054),
  ([4, 1, 32, 4, 4], 4441275272849908170),
  ([4, 1, 32, 8, 4], 7658002488562928146),
  ([4, 1, 32, 12, 4], 13922326373079010),
  ([4, 1, 32, 60, 4], 11142354095984066416),
  ([0, 0, 0, 48, 0], 735990948783633014),
  ([48, 1, 0, 0, 0], 134512398204705221),
  ([47, 2, 0, 0, 0], 8835899605229634335),
  ([1, 47, 1, 0, 0], 17957029602079439078),
  ([0, 0, 0, 49, 0], 7389850134038840683),
  ([0, 0, 0, 96, 0], 17525240512086330133),
  ([0, 0, 0, 97, 0], 15006476242636456917),
  ([16, 16, 16, 16, 16], 10423393905889123604),
  ([49, 15, 1, 47, 2], 9011202463201722888)]

end Compiler.Extraction.WyhashHash.Tests
