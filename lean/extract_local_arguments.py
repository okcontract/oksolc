#!/usr/bin/env python3
"""Bind the named operand array segment in the complete RuleList helper.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

The readonly query/equality prefix remains a compiler correspondence obligation.
This admission retains it and binds only the local initializer/overwrite segment.
"""
import argparse
import hashlib
import extract_nested_construction as construction
from extract_compiler import ROOT

OUTPUT = ROOT / "lean/Compiler/Extraction/LocalArgumentsProgram.lean"


def extract(data, opcodes, storage):
    # The existing complete helper admission already fixes length guarding,
    # last-slot precedence, source loads, conditional overwrite and call boundary.
    construction.extract(data, opcodes, storage)
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.Extraction.InternerLocalArguments\n\n"
        "namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments\n"
        "open Compiler.Algebraic Compiler.ZigAir.Memory.WordArray\n\n"
        "-- Generated initializer/overwrite segment of admitted RuleList.dropRepeatedNested.\n"
        "-- The selected index is computed by the retained readonly prefix before this segment.\n"
        "-- Source SHA-256: " + hashlib.sha256(data).hexdigest() + "\n"
        "-- Opcodes SHA-256: " + hashlib.sha256(opcodes).hexdigest() + "\n"
        "-- Expression classes SHA-256: " + hashlib.sha256(storage).hexdigest() + "\n"
        "def zigLocal (source : View) (selected : Nat) (repeated : NodeId) (repeatedIsFirst : Bool) : GraphAction σ View :=\n"
        "  fun before => match copy source before with\n"
        "  | (.error fault, reached) => (.error fault, reached)\n"
        "  | (.ok target, initialized) => if repeatedIsFirst then overwrite target selected repeated initialized\n"
        "      else (.ok target, initialized)\n\n"
        "end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments\n").encode()


def check():
    nested = construction.nested
    source, opcodes, storage = nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes()
    if extract(source, opcodes, storage) != OUTPUT.read_bytes():
        raise ValueError("named local-array admission is stale; review and regenerate")
    return {"sourceSha256": hashlib.sha256(source).hexdigest(), "opcodesSha256": hashlib.sha256(opcodes).hexdigest(),
        "expressionClassesSha256": hashlib.sha256(storage).hexdigest(), "programSha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
        "scope": "dropRepeatedNested initializer and optional overwrite after the retained readonly prefix",
        "allocationBeforeInitializerReads": True, "aggregateInitialization": True,
        "completeHelperNativeCorrespondenceVerified": False, "completeRecursiveConstructorsVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    if parser.parse_args().check:
        check()
    else:
        nested = construction.nested
        OUTPUT.write_bytes(extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes()))
