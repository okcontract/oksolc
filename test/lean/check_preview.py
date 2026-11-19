#!/usr/bin/env python3
"""Certify the public preview example and reject its corrupted runtime.
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Reuses the ordinary function gate, including fresh packages, compiled audits,
negative controls and imported kernel replay. No alternative acceptance path.
"""
import json
from types import SimpleNamespace

import check_compiler_functions as functions
import compiler_artifacts as artifacts

EXAMPLE = artifacts.ROOT / "examples/verification"
FILES = ("Function.sol", "request.json", "response.json", "corrupted-response.json")


def fixture():
    request = functions.request((EXAMPLE / "request.json").read_bytes())
    if request["sources"]["Function.sol"]["content"] != (EXAMPLE / "Function.sol").read_text():
        raise ValueError("preview request differs from Function.sol")
    response = functions.response((EXAMPLE / "response.json").read_bytes(),
                                  (EXAMPLE / "request.json").read_bytes())
    return request, response


def corrupted(pair):
    """Replace RETURN with REVERT in both runtime and its installed image."""
    parsed, code, _ = functions.artifact(*pair)
    returns = [pc for pc, opcode, _ in functions.instructions(code) if opcode == 0xf3]
    if len(returns) != 1:
        raise ValueError("preview requires exactly one runtime RETURN")
    pc = returns[0]
    return functions.replace_runtime(pair, parsed["contract"], code[:pc] + b"\xfd" + code[pc + 1:])


def write_cases(output):
    fixture()
    output.mkdir(parents=True, exist_ok=False)
    request = output / "identity.json"
    request.write_bytes((EXAMPLE / "request.json").read_bytes())
    return [request]


def negative_pairs(pairs):
    if len(pairs) != 1:
        raise ValueError("preview requires exactly one artifact")
    retained = fixture()
    # Diagnostics can change independently of the certified bytes. Bind every
    # creation/runtime/selector field, not only the selected RETURN instruction.
    if pairs[0][0] != retained[0] or pairs[0][1]["contracts"] != retained[1]["contracts"]:
        raise ValueError("preview compiler artifacts changed; regenerate and review the fixture")
    changed = corrupted(pairs[0])
    stored = json.loads((EXAMPLE / "corrupted-response.json").read_bytes())
    if changed[1]["contracts"] != stored["contracts"]:
        raise ValueError("committed preview corruption differs from the checked control")
    return [("preview_return_changed_to_revert", [changed])]


def profile():
    result = SimpleNamespace(**vars(functions))
    result.write_cases = write_cases
    result.negative_pairs = negative_pairs
    result.EXTRA_INPUTS = (*functions.EXTRA_INPUTS,
                          *("examples/verification/" + name for name in FILES))
    result.REPORT_METADATA = {**functions.REPORT_METADATA, "example": "publicPreviewIdentity"}
    return result


if __name__ == "__main__":
    raise SystemExit(artifacts.main(profile()))
