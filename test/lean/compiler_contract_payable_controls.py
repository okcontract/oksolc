#!/usr/bin/env python3
"""Payability controls retain complete source and installed artifact images.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import compiler_contract_corpus as corpus


def negative_pairs(profile, pairs):
    pair = next(pair for pair in pairs if
        corpus.sha(pair[0]['sources']['Function.sol']['content'].encode()) == corpus.PAYABLE_SHA256)
    result = []
    for name, before, after in (
            ('payable_rejected', 'external payable', 'external pure'),
            ('nonpayable_accepted', 'external pure', 'external payable')):
        req, res = copy.deepcopy(pair)
        content = req['sources']['Function.sol']['content']
        if content.count(before) != 1:
            raise ValueError('retained payability source anchor changed')
        req['sources']['Function.sol']['content'] = content.replace(before, after)
        result.append((name, [(req, res)]))
    parsed, code, _ = profile.artifact(*pair)
    guards = [pc for pc, op, _ in profile.functions.instructions(code) if op == 0x34]
    if len(guards) != 1:
        raise ValueError('native mixed-contract value guard changed; review corruption control')
    pc = guards[0]
    changed = code[:pc] + b'\x5f' + code[pc + 1:]
    result.append(('mixed_accept_value', [profile.functions.replace_runtime(pair, parsed['contract'], changed)]))
    pair = next(pair for pair in pairs if any(f['payable'] and f['checked'] and f['parameters']
        for f in profile.model(pair[0])['functions']))
    req, res = copy.deepcopy(pair)
    content = req['sources']['Function.sol']['content']
    if content.count('{ return x + y; }') != 1:
        raise ValueError('payable arithmetic source anchor changed')
    req['sources']['Function.sol']['content'] = content.replace(
        '{ return x + y; }', '{ unchecked { return x + y; } }')
    result.append(('payable_erase_panic', [(req, res)]))
    return result
