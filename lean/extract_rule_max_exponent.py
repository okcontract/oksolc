#!/usr/bin/env python3
"""Bind the four constructors of the admitted max-base EXP branch.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import extract_rule_unary as owner
from extract_compiler import ROOT

OUTPUT = ROOT / "lean/Compiler/Extraction/RuleMaxExponentProgram.lean"

PROGRAM = '''
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.MaxExponent
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

/-- Only the two remaining operation sites of this branch are admitted. The
constant constructor is supplied by the retained production prefix. -/
def constructors (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) :
    Compiler.Extraction.Associative.Constructors Unit (GraphAction σ) where
  constant := fun value _ => constant value
  operation := fun opcode values _ => match values with
    | [odd] => if opcode == Compiler.Extraction.Dispatch.opISZERO then
        TemporaryUnary.invoke external budget allocator p q opcode odd
      else fun before => (.error .outsideOwnedContinuation, before)
    | [even, odd] => if opcode == Compiler.Extraction.Dispatch.opSUB then
        invoke external budget allocator p q opcode even odd
      else fun before => (.error .outsideOwnedContinuation, before)
    | _ => fun before => (.error .outsideOwnedContinuation, before)
  materialize := fun _ _ _ before => (.error .outsideOwnedContinuation, before)

/-- The parity callback reads arguments[1] in the world returned by constant.
It then allocates and initializes the actual pair, never a final-ID snapshot. -/
def parity (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (one : NodeId) : GraphAction σ NodeId :=
  borrowedFirst external budget allocator p q Compiler.Extraction.Dispatch.opAND source 1 one

def zigChain (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View) :
    GraphAction σ (Option NodeId) :=
  Compiler.Extraction.Dispatch.maxExponent (constructors constant external budget allocator p q)
    (fun one _ => parity external budget allocator p q source one) ()

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.MaxExponent
'''


def extract(source, opcodes, storage, versions):
    owner.dispatch.extract(source, opcodes, storage, versions)
    hashes = "".join("-- " + name + " SHA-256: " + hashlib.sha256(value).hexdigest() + "\n"
        for name, value in zip(("Source", "Opcodes", "Expression classes", "EVM versions"),
                              (source, opcodes, storage, versions)))
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.Extraction.InternerTemporaryUnary\nimport Compiler.Extraction.DispatchProgram\n\n"
        "-- Generated constructor segment of the complete simplifyWithOptions owner.\n"
        "-- Query/condition admission and native graph correspondence remain open.\n" + hashes + PROGRAM).encode()


def check():
    values = owner.inputs()
    if extract(*values) != OUTPUT.read_bytes():
        raise ValueError("max-base EXP constructor admission is stale; review and regenerate")
    return {**dict(zip(("sourceSha256", "opcodesSha256", "expressionClassesSha256", "versionsSha256"),
                       (hashlib.sha256(value).hexdigest() for value in values))),
        "programSha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(), "pairLiteralSites": 2,
        "scope": "four constructor calls of the max-base EXP branch",
        "completeExponentRuleVerified": False, "nativeQueryCorrespondenceVerified": False,
        "completeRecursiveConstructorsVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    if parser.parse_args().check:
        check()
    else:
        OUTPUT.write_bytes(extract(*owner.inputs()))
