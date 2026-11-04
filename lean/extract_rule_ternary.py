#!/usr/bin/env python3
"""Bind both three-word modular literals in the complete RuleList dispatcher.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import extract_rule_unary as owner
from extract_compiler import ROOT

OUTPUT = ROOT / "lean/Compiler/Extraction/RuleTernaryProgram.lean"


def extract(source, opcodes, storage, versions):
    owner.dispatch.extract(source, opcodes, storage, versions)
    hashes = "".join("-- " + name + " SHA-256: " + hashlib.sha256(value).hexdigest() + "\n"
        for name, value in zip(("Source", "Opcodes", "Expression classes", "EVM versions"),
                              (source, opcodes, storage, versions)))
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.Extraction.InternerTemporaryTernary\nimport Compiler.Extraction.DispatchProgram\n\n"
        "namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral\n"
        "open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray\n\n"
        "-- Generated literal segments of the complete admitted simplifyWithOptions owner.\n"
        "-- The retained constant/query/option prefix remains a compiler obligation.\n" + hashes +
        "inductive Site where\n  | multiplication | addition\n  deriving DecidableEq, Repr\n\n"
        "def opcode : Site → Opcode\n  | .multiplication => Compiler.Extraction.Dispatch.opMULMOD\n"
        "  | .addition => Compiler.Extraction.Dispatch.opADDMOD\n\n"
        "def zigLiteral (site : Site) (external : External σ) (budget allocator : Nat) (p : Primitives σ)\n"
        "    (q : Caller.Queries) (source : View) (right : NodeId) : GraphAction σ NodeId :=\n"
        "  borrowed external budget allocator p q (opcode site) source right\n\n"
        "end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral\n").encode()


def check():
    values = owner.inputs()
    if extract(*values) != OUTPUT.read_bytes():
        raise ValueError("RuleList ternary-literal admission is stale; review and regenerate")
    return {"sourceSha256": hashlib.sha256(values[0]).hexdigest(), "opcodesSha256": hashlib.sha256(values[1]).hexdigest(),
        "expressionClassesSha256": hashlib.sha256(values[2]).hexdigest(), "versionsSha256": hashlib.sha256(values[3]).hexdigest(),
        "programSha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(), "liveLiteralSites": 2,
        "scope": "the two three-word modular literals of simplifyWithOptions",
        "completeModularRuleVerified": False, "nativeQueryCorrespondenceVerified": False,
        "completeRecursiveConstructorsVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    if parser.parse_args().check:
        check()
    else:
        OUTPUT.write_bytes(extract(*owner.inputs()))
