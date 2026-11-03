#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Semantic address/target corruptions with matching installed runtime images.
"""
import copy
import compiler_contract_corpus as corpus


def push_position(functions, code, value):
    positions = [pc for pc, op, width in functions.instructions(code)
        if op == 0x60 and width == 1 and code[pc + 1] == value]
    if len(positions) != 1:
        raise ValueError("address corruption push anchor changed; review the ordinary artifact")
    return positions[0]


def negative_pairs(profile, pairs):
    functions = profile.functions
    beacon = next(pair for pair in pairs if
        corpus.sha(pair[0]["sources"]["Function.sol"]["content"].encode()) == corpus.BEACON_SHA256)
    parsed, code, _ = profile.artifact(*beacon)
    result = []
    req, res = copy.deepcopy(beacon)
    content = req["sources"]["Function.sol"]["content"]
    if content.count("address(0x1)") != 1:
        raise ValueError("retained address source anchor changed")
    req["sources"]["Function.sol"]["content"] = content.replace("address(0x1)", "address(0x2)")
    result.append(("corpus_wrong_address_literal", [(req, res)]))
    for label, old, new in (("corpus_wrong_address_value", 1, 2),
            ("corpus_wrong_address_width", 32, 20)):
        pc = push_position(functions, code, old)
        changed = code[:pc + 1] + bytes([new]) + code[pc + 2:]
        result.append((label, [functions.replace_runtime(beacon, parsed["contract"], changed)]))

    selected = next(pair for pair in pairs if profile.model(pair[0])["sourceUnitContracts"] == ["A", "B"])
    req, res = copy.deepcopy(selected)
    outputs = req["settings"]["outputSelection"]["Function.sol"].pop("A")
    req["settings"]["outputSelection"]["Function.sol"]["B"] = outputs
    contracts = res["contracts"]["Function.sol"]
    contracts["B"] = contracts.pop("A")
    # Both declarations are valid and share a selector. The complete certificate
    # must reject A's result against B's independently selected source body.
    result.append(("wrong_selected_contract", [(req, res)]))

    maximum = next(pair for pair in pairs if any(f["returnType"] == "address" and
        f["nodes"] == [{"literal": str(2**160 - 1)}] for f in profile.model(pair[0])["functions"]))
    parsed, code, _ = profile.artifact(*maximum)
    pc = push_position(functions, code, 160)
    changed = code[:pc + 1] + bytes([161]) + code[pc + 2:]
    result.append(("address_nonzero_upper_bits", [functions.replace_runtime(maximum, parsed["contract"], changed)]))
    return result
