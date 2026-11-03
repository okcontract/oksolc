/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.IR

namespace Compiler.Extraction.IR
open Compiler.Algebraic Contract.Yul

-- Generated typed program data; manual proofs live in Correspondence.lean.
-- Source SHA-256: d2c488ec16a8dcd03b89c992a1f4e0a21c998184a84d94aef65d0cd0781ee3fa
def matcher : Expr [.guard, .facts] .boolean :=
  (.guardSwitch (.var .here) (fun | .left_zero => (.eq (.optional .word) (.left (.var (.there .here))) (.some (.word 0))) | .right_zero => (.eq (.optional .word) (.right (.var (.there .here))) (.some (.word 0))) | .left_one => (.eq (.optional .word) (.left (.var (.there .here))) (.some (.word 1))) | .right_one => (.eq (.optional .word) (.right (.var (.there .here))) (.some (.word 1))) | .left_max => (.eq (.optional .word) (.left (.var (.there .here))) (.some (.word (BitVec.allOnes 256)))) | .right_max => (.eq (.optional .word) (.right (.var (.there .here))) (.some (.word (BitVec.allOnes 256)))) | .equal => (.equal (.var (.there .here)))))

def selection : Block [.opcode, .stage, .facts, .array .rule] :=
  (.letE (.var .here) (.loop (.var (.there (.there (.there (.there .here))))) (.branch (.eq .opcode (.ruleOpcode (.var .here)) (.var (.there .here))) (.letE (.ite (.eq .guard (.ruleGuard (.var .here)) (.guard .equal)) (.stage .equal) (.stage .constants)) (.branch (.and (.eq .stage (.var (.there (.there (.there (.there .here))))) (.var .here)) (.matches (.ruleGuard (.var (.there .here))) (.var (.there (.there (.there (.there (.there .here)))))))) (.ret (.some (.ruleReplacement (.var (.there .here))))) .done .done)) .done .done) (.ret .none)))

def construction : Build [.replacement, .node, .node] :=
  (.switch (.var .here) (fun | .left => (.ret (.var (.there .here))) | .right => (.ret (.var (.there (.there .here)))) | .zero => (.constant (.word 0)) | .one => (.constant (.word 1)) | .max => (.constant (.word (BitVec.allOnes 256))) | .not_right => (.operation .NOT (.cons (.var (.there (.there .here))) .nil)) | .neg_left => (.bind (.constant (.word 0)) (.branch (.eq .replacement (.var (.there .here)) (.replacement .neg_left)) (.operation .SUB (.cons (.var .here) (.cons (.var (.there (.there .here))) .nil))) (.operation .SUB (.cons (.var .here) (.cons (.var (.there (.there (.there .here)))) .nil))))) | .neg_right => (.bind (.constant (.word 0)) (.branch (.eq .replacement (.var (.there .here)) (.replacement .neg_left)) (.operation .SUB (.cons (.var .here) (.cons (.var (.there (.there .here))) .nil))) (.operation .SUB (.cons (.var .here) (.cons (.var (.there (.there (.there .here)))) .nil))))) | .iszero_left => (.branch (.eq .replacement (.var .here) (.replacement .iszero_left)) (.operation .ISZERO (.cons (.var (.there .here)) .nil)) (.operation .ISZERO (.cons (.var (.there (.there .here))) .nil))) | .iszero_right => (.branch (.eq .replacement (.var .here) (.replacement .iszero_left)) (.operation .ISZERO (.cons (.var (.there .here)) .nil)) (.operation .ISZERO (.cons (.var (.there (.there .here))) .nil))) | .bool_left => (.branch (.eq .replacement (.var .here) (.replacement .bool_left)) (.bind (.operation .ISZERO (.cons (.var (.there .here)) .nil)) (.operation .ISZERO (.cons (.var .here) .nil))) (.bind (.operation .ISZERO (.cons (.var (.there (.there .here))) .nil)) (.operation .ISZERO (.cons (.var .here) .nil)))) | .bool_right => (.branch (.eq .replacement (.var .here) (.replacement .bool_left)) (.bind (.operation .ISZERO (.cons (.var (.there .here)) .nil)) (.operation .ISZERO (.cons (.var .here) .nil))) (.bind (.operation .ISZERO (.cons (.var (.there (.there .here))) .nil)) (.operation .ISZERO (.cons (.var .here) .nil))))))

end Compiler.Extraction.IR
