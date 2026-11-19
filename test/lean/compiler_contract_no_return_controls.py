"""Semantic corruptions for typed empty functions and their installed images.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import compiler_contract_corpus as corpus


def negative_pairs(profile, pairs):
    pair = next(pair for pair in pairs if
        corpus.sha(pair[0]['sources']['Function.sol']['content'].encode()) == corpus.NO_RETURN_SHA256 and
        pair[0]['settings']['metadata'] == profile.SETTINGS['metadata'])
    parsed, code, _ = profile.artifact(*pair)
    result = []
    # Each matched instruction sequence belongs to the executable prefix of the
    # metadata-free ordinary artifact. Unfamiliar code requires explicit review.
    edits = (
        ('no_return_padding_erased', b'\x60\x01\x60\x01\x60\xe0\x1b\x03\x19', b'\x60\x01\x60\x01\x60\x00\x1b\x03\x19'),
        ('no_return_fourth_byte_rejected', b'\x60\x01\x60\x01\x60\xe0\x1b\x03\x19', b'\x60\x01\x60\x01\x60\xe8\x1b\x03\x19'),
        ('no_return_wrong_argument_offset', b'\x60\x04\x35', b'\x60\x05\x35'),
        ('no_return_short_argument_accepted', b'\x60\x20\x36', b'\x60\x00\x36'),
    )
    for name, before, after in edits:
        if code.count(before) != 1:
            raise ValueError('native no-return control anchor changed: ' + name)
        result.append((name, [profile.functions.replace_runtime(pair, parsed['contract'], code.replace(before, after))]))
    instructions = list(profile.functions.instructions(code))
    for name, opcode, replacement in (('no_return_accept_value', 0x34, 0x5f),
                                      ('no_return_success_reverts', 0x00, 0x5b)):
        positions = [pc for pc, op, _ in instructions if op == opcode]
        if len(positions) != 1:
            raise ValueError('native no-return opcode changed: ' + name)
        pc = positions[0]
        changed = code[:pc] + bytes([replacement]) + code[pc + 1:]
        result.append((name, [profile.functions.replace_runtime(pair, parsed['contract'], changed)]))
    pair = next(pair for pair in pairs if
        'function ignore(uint256 ignored) public pure {}' in pair[0]['sources']['Function.sol']['content'])
    req, res = copy.deepcopy(pair)
    content = req['sources']['Function.sol']['content']
    req['sources']['Function.sol']['content'] = content.replace(
        'function ignore(uint256 ignored) public pure {}',
        'function ignore(uint256 ignored) public pure returns(uint256) { return ignored; }')
    # Return types do not enter the selector: the complete unchanged native
    # image must still be rejected for returning zero bytes instead of a word.
    result.append(('no_return_wrong_return_bytes', [(req, res)]))
    return result
