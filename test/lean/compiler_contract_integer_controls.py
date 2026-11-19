#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Corrupt contextual word returns while preserving paired creation/runtime images.
"""
import copy
import compiler_contract_corpus as corpus


def negative_pairs(profile, pairs):
    pair = next(pair for pair in pairs if
        corpus.sha(pair[0]['sources']['Function.sol']['content'].encode()) == corpus.INTEGER_SHA256 and
        pair[0]['settings']['metadata'] == profile.SETTINGS['metadata'])
    parsed, code, _ = profile.artifact(*pair)
    anchors = [pc for pc, op, _ in profile.functions.instructions(code)
               if op == 0x80 and code[pc:pc + 7] == bytes.fromhex('805f60209252f3')]
    if len(anchors) != 1:
        raise ValueError('native integer return word/width anchor changed')
    pc = anchors[0]
    result = []
    # DUP1 replaces the zero with the nonzero output-memory pointer. Each
    # mutation preserves instruction widths, jump targets and the installed image.
    for name, offset, replacement in (('integer_return_wrong_word', pc + 1, 0x80),
                                      ('integer_return_short_abi', pc + 3, 0x1f)):
        changed = code[:offset] + bytes([replacement]) + code[offset + 1:]
        result.append((name, [profile.functions.replace_runtime(pair, parsed['contract'], changed)]))
    req, res = copy.deepcopy(pair)
    content = req['sources']['Function.sol']['content']
    if content.count('return 0;') != 1:
        raise ValueError('retained integer return source anchor changed')
    req['sources']['Function.sol']['content'] = content.replace('return 0;', 'return 1;')
    result.append(('integer_return_source_literal', [(req, res)]))
    return result
