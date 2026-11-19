#!/usr/bin/env python3
"""Bind every unary temporary initializer in the admitted algebraic apply body.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib

import extract_temporary_arguments as negation
from extract_compiler import Parser, SOURCE, ROOT, Unsupported, construction_expression, parse_module

OUTPUT = ROOT / "lean/Compiler/Extraction/TemporaryUnaryProgram.lean"
FAMILIES = {
    ("not_right",): "try classes.makeOperation(.NOT, &.{right}, debug_data)",
    ("iszero_left", "iszero_right"): """try classes.makeOperation(.ISZERO, &.{
        if (replacement == .iszero_left) left else right,
    }, debug_data)""",
    ("bool_left", "bool_right"): """blk: {
        const first = try classes.makeOperation(.ISZERO, &.{
            if (replacement == .bool_left) left else right,
        }, debug_data);
        break :blk try classes.makeOperation(.ISZERO, &.{first}, debug_data);
    }""",
}


def extract(data):
    _, _, root = parse_module(data)
    construction_expression(root)
    # The complete owner still contains the already admitted negation family.
    # Its source binding is retained rather than copied into this adapter.
    negation.extract(data)
    arms = dict(root.args[1])
    for names, initializer in FAMILIES.items():
        if arms.get(names) != Parser(initializer).expression():
            raise Unsupported("unary initializer selection, order, contents or call boundary changed: " + ",".join(names))
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.Extraction.InternerTemporaryUnary\n\n"
        "namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary\n"
        "open Compiler.Algebraic Contract.Yul\n\n"
        "-- Generated from every unary literal in the production Algebraic.apply body.\n"
        "-- Source SHA-256: " + hashlib.sha256(data).hexdigest() + "\n"
        "-- Boolean rewriting returns from the first invocation before preparing the second array.\n"
        "def zigUnary (replacement : Replacement) (external : External σ) (budget allocator : Nat)\n"
        "    (p : Primitives σ) (q : Caller.Queries) (left right : NodeId) : GraphAction σ NodeId :=\n"
        "  match replacement with\n"
        "  | .not_right => invoke external budget allocator p q (Interner.buildOpcode .NOT) right\n"
        "  | .iszero_left | .iszero_right => invoke external budget allocator p q (Interner.buildOpcode .ISZERO)\n"
        "      (if replacement == .iszero_left then left else right)\n"
        "  | .bool_left | .bool_right => do\n"
        "    let first ← invoke external budget allocator p q (Interner.buildOpcode .ISZERO)\n"
        "      (if replacement == .bool_left then left else right)\n"
        "    invoke external budget allocator p q (Interner.buildOpcode .ISZERO) first\n"
        "  | _ => fun before => (.error .outsideOwnedContinuation, before)\n\n"
        "end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary\n").encode()


def check():
    data = SOURCE.read_bytes()
    if extract(data) != OUTPUT.read_bytes():
        raise ValueError("unary argument source admission is stale; review and regenerate")
    return {"sourceSha256": hashlib.sha256(data).hexdigest(),
        "programSha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
        "admittedBranches": [name for names in FAMILIES for name in names], "temporarySites": 4,
        "completeRecursiveConstructorsVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    if parser.parse_args().check:
        check()
    else:
        OUTPUT.write_bytes(extract(SOURCE.read_bytes()))
