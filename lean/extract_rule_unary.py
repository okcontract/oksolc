#!/usr/bin/env python3
"""Bind all three live one-word literals in the complete RuleList dispatcher.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Readonly prefixes and the parity-producing constructor remain explicit compiler
obligations. This admission models their actual loaded or returned operand.
"""
import argparse
import hashlib
import extract_dispatch as dispatch
from extract_compiler import ROOT

OUTPUT = ROOT / "lean/Compiler/Extraction/RuleUnaryProgram.lean"


def extract(source, opcodes, storage, versions):
    dispatch.extract(source, opcodes, storage, versions)
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.Extraction.InternerBorrowedUnary\n\n"
        "namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral\n"
        "open Compiler.Algebraic Compiler.ZigAir.Memory.WordArray\n\n"
        "-- Generated literal segments from the complete admitted simplifyWithOptions owner.\n"
        "-- Retained query/condition prefixes and parity construction are separate obligations.\n"
        "-- Source SHA-256: " + hashlib.sha256(source).hexdigest() + "\n"
        "-- Opcodes SHA-256: " + hashlib.sha256(opcodes).hexdigest() + "\n"
        "-- Expression classes SHA-256: " + hashlib.sha256(storage).hexdigest() + "\n"
        "-- EVM versions SHA-256: " + hashlib.sha256(versions).hexdigest() + "\n"
        "inductive Site where\n  | nestedIszero | zeroBaseExponent | parity\n  deriving DecidableEq, Repr\n\n"
        "def zigLiteral (site : Site) (external : External σ) (budget allocator : Nat) (p : Primitives σ)\n"
        "    (q : Caller.Queries) (source : View) (parity : NodeId) : GraphAction σ NodeId :=\n"
        "  match site with\n"
        "  | .nestedIszero => BorrowedInput.invoke external budget allocator p q (Interner.buildOpcode .ISZERO) source 0\n"
        "  | .zeroBaseExponent => BorrowedInput.invoke external budget allocator p q (Interner.buildOpcode .ISZERO) source 1\n"
        "  | .parity => invoke external budget allocator p q (Interner.buildOpcode .ISZERO) parity\n\n"
        "def afterParity (child : GraphAction σ NodeId) (external : External σ) (budget allocator : Nat)\n"
        "    (p : Primitives σ) (q : Caller.Queries) : GraphAction σ NodeId := do\n"
        "  let parity ← child\n"
        "  zigLiteral .parity external budget allocator p q ⟨0, 0, 0⟩ parity\n\n"
        "end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral\n").encode()


def inputs():
    nested = dispatch.nested
    return nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes(), dispatch.VERSIONS.read_bytes()


def check():
    values = inputs()
    if extract(*values) != OUTPUT.read_bytes():
        raise ValueError("RuleList unary-literal admission is stale; review and regenerate")
    return {"sourceSha256": hashlib.sha256(values[0]).hexdigest(), "opcodesSha256": hashlib.sha256(values[1]).hexdigest(),
        "expressionClassesSha256": hashlib.sha256(values[2]).hexdigest(), "versionsSha256": hashlib.sha256(values[3]).hexdigest(),
        "programSha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(), "liveLiteralSites": 3,
        "scope": "three live one-word literal segments of simplifyWithOptions",
        "completeExponentRuleVerified": False, "nativeQueryCorrespondenceVerified": False,
        "completeRecursiveConstructorsVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    if parser.parse_args().check:
        check()
    else:
        OUTPUT.write_bytes(extract(*inputs()))
