"""Semantic corruptions of exact raw-word returns and typed call admission.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import compiler_contract_corpus as corpus


def negative_pairs(profile, pairs):
    pair = next(pair for pair in pairs if
        corpus.sha(pair[0]['sources']['Function.sol']['content'].encode()) == corpus.RAW_RETURN_SHA256 and
        pair[0]['settings']['metadata'] == profile.SETTINGS['metadata'])
    parsed, code, _ = profile.artifact(*pair)
    result = []
    edits = (
        ('raw_return_boolean_normalized', b'\x5f\x19\x5f\x52', b'\x5f\x15\x5f\x52'),
        ('raw_return_missing_store', b'\x5f\x19\x5f\x52', b'\x5f\x19\x5f\x50'),
        ('raw_return_wrong_length', b'\x60\x20\x5f\xf3', b'\x60\x1f\x5f\xf3'),
        ('raw_return_wrong_offset', b'\x60\x20\x5f\xf3', b'\x60\x20\x80\xf3'),
        ('raw_return_success_reverts', b'\x60\x20\x5f\xf3', b'\x60\x20\x5f\xfd'),
        ('raw_return_padding_erased', b'\x60\x01\x60\x01\x60\xe0\x1b\x03\x19', b'\x60\x01\x60\x01\x60\x00\x1b\x03\x19'),
        ('raw_return_wrong_argument_offset', b'\x60\x04\x35', b'\x60\x05\x35'),
    )
    for name, before, after in edits:
        if code.count(before) != 1:
            raise ValueError('native raw-return control anchor changed: ' + name)
        result.append((name, [profile.functions.replace_runtime(pair, parsed['contract'], code.replace(before, after))]))
    positions = [pc for pc, op, _ in profile.functions.instructions(code) if op == 0x34]
    if len(positions) != 1:
        raise ValueError('native raw-return callvalue guard changed')
    pc = positions[0]
    result.append(('raw_return_accept_value', [profile.functions.replace_runtime(
        pair, parsed['contract'], code[:pc] + b'\x5f' + code[pc + 1:])]))
    req, res = copy.deepcopy(pair)
    before = '0x' + 'f' * 64
    if req['sources']['Function.sol']['content'].count(before) != 1:
        raise ValueError('raw-return source literal changed')
    req['sources']['Function.sol']['content'] = req['sources']['Function.sol']['content'].replace(before, '7')
    result.append(('raw_return_source_word', [(req, res)]))
    pair = next(pair for pair in pairs if 'function bytesInOrder(' in pair[0]['sources']['Function.sol']['content'])
    req, res = copy.deepcopy(pair)
    before, after = '0x' + bytes(range(32)).hex(), '0x' + bytes(reversed(range(32))).hex()
    if req['sources']['Function.sol']['content'].count(before) != 1:
        raise ValueError('raw-return byte-order source changed')
    req['sources']['Function.sol']['content'] = req['sources']['Function.sol']['content'].replace(before, after)
    result.append(('raw_return_byte_order', [(req, res)]))
    return result
