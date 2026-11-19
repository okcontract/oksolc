"""Reject success, exceptional runtime and wrong installation for empty contracts.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import compiler_contract_corpus as corpus


def negative_pairs(profile, pairs):
    pair = next(pair for pair in pairs if profile.model(pair[0])['contract'] == corpus.EMPTY_BEACON_TARGET)
    parsed, code, selectors = profile.artifact(*pair)
    if parsed['functions'] or selectors:
        raise ValueError('empty-contract control has declared functions')
    # Only the executable prefix is selected; metadata is still bound and
    # installed as part of the complete image by the creation certificate.
    prefix = []
    for pc, op, width in profile.functions.instructions(code):
        if op == 0xfe:
            break
        prefix.append((pc, op, width))
    reverts = [pc for pc, op, _ in prefix if op == 0xfd]
    if len(reverts) != 1:
        raise ValueError('empty runtime revert changed; review corruption control')
    pc = reverts[0]
    result = []
    for name, opcode in (('empty_returns', 0xf3), ('empty_exceptional', 0xfe)):
        changed = code[:pc] + bytes([opcode]) + code[pc + 1:]
        result.append((name, [profile.functions.replace_runtime(pair, parsed['contract'], changed)]))
    req, res = copy.deepcopy(pair)
    creation = profile.functions.creation_code(parsed, res)
    if not creation.endswith(code):
        raise ValueError('empty creation runtime placement changed')
    offset = len(creation) - len(code) + pc
    changed = creation[:offset] + b'\xf3' + creation[offset + 1:]
    res['contracts']['Function.sol'][parsed['contract']]['evm']['bytecode']['object'] = changed.hex()
    result.append(('empty_wrong_installation', [(req, res)]))
    return result
