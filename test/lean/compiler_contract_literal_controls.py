#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Literal source/ABI corruptions keep creation and installed runtime together.
"""
import copy
import compiler_contract_corpus as corpus
from compiler_contract_address_controls import push_position


def negative_pairs(profile, pairs):
    pair = next(pair for pair in pairs if
        corpus.sha(pair[0]['sources']['Function.sol']['content'].encode()) == corpus.CLASHING_SHA256)
    parsed, code, _ = profile.artifact(*pair)
    result = []
    for name, before, after in (
            ('corpus_wrong_boolean_literal', 'return true;', 'return false;'),
            ('corpus_wrong_bare_address', '0x0000000000000000000000000000000011111142',
             '0x0000000000000000000000000000000011111143')):
        req, res = copy.deepcopy(pair)
        content = req['sources']['Function.sol']['content']
        if content.count(before) != 1:
            raise ValueError('retained literal source anchor changed: ' + name)
        req['sources']['Function.sol']['content'] = content.replace(before, after)
        result.append((name, [(req, res)]))
    pc = push_position(profile.functions, code, 1)
    if code[pc + 2:pc + 4] != bytes.fromhex('6020'):
        raise ValueError('native boolean return-width anchor changed; review the ordinary artifact')
    for name, at, value in (('corpus_noncanonical_boolean', pc + 1, 2),
            ('corpus_short_boolean_abi', pc + 3, 1)):
        changed = code[:at] + bytes([value]) + code[at + 1:]
        result.append((name, [profile.functions.replace_runtime(pair, parsed['contract'], changed)]))
    pair = next(pair for pair in pairs if any(f['returnType'] == 'bool' and
        f['nodes'] == [{'literal': '0'}] for f in profile.model(pair[0])['functions']))
    req, res = copy.deepcopy(pair)
    content = req['sources']['Function.sol']['content']
    if content.count('return false;') != 1:
        raise ValueError('false literal source anchor changed')
    req['sources']['Function.sol']['content'] = content.replace('return false;', 'return true;')
    result.append(('boolean_false_literal', [(req, res)]))
    return result
