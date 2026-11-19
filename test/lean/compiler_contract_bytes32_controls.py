#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Fixed-byte literal corruptions preserve the paired creation/runtime image.
"""
import copy
import compiler_contract_corpus as corpus


def negative_pairs(profile, pairs):
    pair = next(pair for pair in pairs if
        corpus.sha(pair[0]['sources']['Function.sol']['content'].encode()) == corpus.BYTES32_SHA256 and
        pair[0]['settings']['metadata'] == profile.SETTINGS['metadata'])
    parsed, code, _ = profile.artifact(*pair)
    # The optimizer also removes four trailing zero bits from "ERC20". Bind the
    # actual PUSH5/SHL representation and check its value, not an assumed shape.
    anchors = [(pc, size) for pc, op, size in profile.functions.instructions(code)
               if op == 0x64 and code[pc + 1:pc + 1 + size] == bytes.fromhex('0455243323')]
    if len(anchors) != 1:
        raise ValueError('native bytes32 literal anchor changed')
    pc, _ = anchors[0]
    if (code[pc + 6:pc + 9] != bytes.fromhex('60dc1b') or
            int.from_bytes(code[pc + 1:pc + 6], 'big') << code[pc + 7] !=
            int.from_bytes(b'ERC20'.ljust(32, b'\0'), 'big')):
        raise ValueError('native bytes32 right-padding anchor changed')
    returns = [(at, size) for at, op, size in profile.functions.instructions(code)
               if op == 0x60 and code[at + 1:at + 4] == bytes.fromhex('2090f3')]
    if len(returns) != 1:
        raise ValueError('native bytes32 return-width anchor changed')
    width, _ = returns[0]
    result = []
    for name, offset, replacement in (
            ('bytes32_left_padded', pc + 1, b'ERC20\x60\x00'),
            ('bytes32_shift_off_by_one', pc + 7, b'\xd4'),
            ('bytes32_reversed_bytes', pc + 1, b'02CRE\x60\xd8'),
            ('bytes32_short_abi', width + 1, b'\x1f')):
        changed = code[:offset] + replacement + code[offset + len(replacement):]
        result.append((name, [profile.functions.replace_runtime(pair, parsed['contract'], changed)]))
    req, res = copy.deepcopy(pair)
    content = req['sources']['Function.sol']['content']
    if content.count('bytes32("ERC20")') != 1:
        raise ValueError('retained bytes32 source anchor changed')
    req['sources']['Function.sol']['content'] = content.replace('bytes32("ERC20")', 'bytes32("ERC21")')
    result.append(('bytes32_source_literal', [(req, res)]))
    return result
