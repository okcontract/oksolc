"""Targeted literal mutations that preserve all unrelated source tokens.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from constructor_inventory import PAIRS, end
from extract_storage import lex


def spans(tokens, start, stop):
    result, first, index = [], start, start
    while index < stop:
        if tokens[index] in PAIRS:
            index = end(tokens, index)
        elif tokens[index] == ',':
            if first < index:
                result.append((first, index))
            first = index + 1
        index += 1
    if first < stop:
        result.append((first, stop))
    return result


def canonical(data):
    return ' '.join(lex(data.decode())).encode()


def variants(data):
    tokens = lex(data.decode())
    call = spans(tokens, 4, len(tokens) - 1)
    assert len(call) == 3
    start, stop = call[1]
    assert tokens[start:start + 3] == ['&', '.', '{'] and tokens[stop - 1] == '}'
    elements = spans(tokens, start + 3, stop - 1)
    assert elements

    def replace(name, span, replacement):
        changed = tokens[:span[0]] + replacement + tokens[span[1]:]
        assert changed != tokens, name
        return name, ' '.join(changed).encode()

    result = [replace('opcode', call[0], ['.', 'INVALID']), replace('debug', call[2], ['null'])]
    for index, span in enumerate(elements):
        value = ['1'] if tokens[span[0]:span[1]] == ['0'] else ['0']
        result.append(replace('element-' + str(index), span, value))
    if len(elements) > 1:
        reversed_elements = []
        for span in reversed(elements):
            if reversed_elements:
                reversed_elements.append(',')
            reversed_elements.extend(tokens[span[0]:span[1]])
        result.append(replace('order', (elements[0][0], elements[-1][1]), reversed_elements))
    for index in range(start, stop):
        if tokens[index] == '[':
            result.append(replace('index-' + str(index), (index + 1, end(tokens, index)), ['3']))
        if tokens[index] == 'try':
            result.append(replace('try-' + str(index), (index, index + 1), []))
    return result
