"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Named callback-boundary fixtures for every dispatcher rule family. Expressions
are probes, not assertions that production interning would retain these shapes.
"""
MAX = (1 << 256) - 1
ADDRESS_MASK = (1 << 160) - 1


def case(name, expression, calls, *, yul=False, version=None, fail=0):
    nodes, ids = [], {}

    def node(expr):
        if expr in ids:
            return ids[expr]
        if isinstance(expr, int):
            value = {'constant': expr}
        elif isinstance(expr, str):
            value = {}
        else:
            value = {'instruction': expr[0], 'arguments': [node(arg) for arg in expr[1:]]}
        result = len(nodes)
        nodes.append(value)
        ids[expr] = result
        return result

    args = [node(arg) for arg in expression[1:]]
    return {'name': name, 'nodes': nodes, 'instruction': expression[0], 'arguments': args,
            'forYul': yul, 'version': version, 'failAt': fail}, calls


def fixtures():
    cases = [
        case('fold_before_table', ('MUL', MAX, 2), [0]),
        case('fold_ternary', ('ADDMOD', MAX, 8, 9), [0]),
        case('arity_zero', ('ADD',), []),
        case('arity_four', ('ADD', 1, 2, 3, 4), []),
        case('unknown_opcode', ('STOP', 1, 2), []),
        case('table_constant', ('ADD', 'x', 0), []),
        case('signed_zero', ('SDIV', 'x', 0), [0]),
        case('signed_left_zero', ('SDIV', 0, 'x'), [0]),
        case('signed_one', ('SDIV', 'x', 1), []),
        case('byte_mask', ('AND', ('BYTE', 'x', 'y'), 255), [26]),
        case('byte_last', ('BYTE', 31, 'x'), [0, 22]),
        case('table_equal', ('SUB', 'x', 'x'), [0]),
        case('signed_equal', ('SLT', 'x', 'x'), [0]),
        case('xor_nested_right', ('XOR', 'x', ('XOR', 'y', 'x')), []),
        case('xor_nested_left', ('XOR', ('XOR', 'x', 'y'), 'x'), []),
        case('or_absorb_right', ('OR', 'x', ('AND', 'y', 'x')), []),
        case('or_absorb_left', ('OR', ('AND', 'x', 'y'), 'y'), []),
        case('and_absorb_right', ('AND', 'x', ('OR', 'y', 'x')), []),
        case('and_absorb_left', ('AND', ('OR', 'x', 'y'), 'y'), []),
        case('or_negation', ('OR', 'x', ('NOT', 'x')), [0]),
        case('and_negation', ('AND', ('NOT', 'x'), 'x'), [0]),
        case('and_repeat', ('AND', ('AND', 'x', 'y'), 'x'), [22]),
        case('or_repeat', ('OR', 'y', ('OR', 'x', 'y')), [23]),
        case('signextend_repeat', ('SIGNEXTEND', 'i', ('SIGNEXTEND', 'i', 'x')), [11]),
        case('signextend_min', ('SIGNEXTEND', 7, ('SIGNEXTEND', 2, 'x')), [0, 11]),
        case('mod_mul_yul', ('MOD', ('MUL', 'x', 'y'), 8), [9], yul=True),
        case('mod_add_yul', ('MOD', ('ADD', 'x', 'y'), 8), [8], yul=True),
        case('mod_mul_native', ('MOD', ('MUL', 'x', 'y'), 8), [0, 22]),
        case('mod_nonpower', ('MOD', 'x', 7), []),
        case('shift_large', ('SHL', 256, 'x'), [0]),
        case('byte_large', ('BYTE', 32, 'x'), [0]),
        case('signextend_large', ('SIGNEXTEND', 31, 'x'), []),
        case('signextend_mask_left', ('AND', 255, ('SIGNEXTEND', 0, 'x')), [0, 22]),
        case('signextend_mask_right', ('AND', ('SIGNEXTEND', 0, 'x'), 255), [0, 22]),
        case('address_mask_left', ('AND', ADDRESS_MASK, ('CALLER',)), [51]),
        case('address_mask_right', ('AND', ('ADDRESS',), ADDRESS_MASK), [48]),
        case('shift_same', ('SHL', 3, ('SHL', 5, 'x')), [0, 27]),
        case('shift_same_overflow', ('SHR', 128, ('SHR', 128, 'x')), [0]),
        case('shift_opposite_left', ('SHL', 3, ('SHR', 5, 'x')), [0, 28, 0, 22]),
        case('shift_opposite_right', ('SHR', 7, ('SHL', 2, 'x')), [0, 28, 0, 22]),
        case('shift_mask', ('SHL', 3, ('AND', 'x', 255)), [27, 0, 22]),
        case('alternating_mask', ('AND', ('OR', ('AND', 'x', 3), 'y'), 6), [0, 22, 0, 22, 23]),
        case('covered_mask', ('AND', MAX >> 7, ('SHR', 7, 'x')), [28]),
        case('merged_shifts', ('AND', ('SHL', 'i', 'x'), ('SHL', 'i', 'y')), [22, 27]),
        case('shift_product', ('MUL', 'x', ('SHL', 'i', 1)), [27]),
        case('shift_divisor', ('DIV', 'x', ('SHL', 'i', 1)), [28]),
        case('byte_left_shift', ('BYTE', 2, ('SHL', 8, 'x')), [0, 26]),
        case('byte_right_zero', ('BYTE', 0, ('SHR', 9, 'x')), [0]),
        case('byte_right_shift', ('BYTE', 2, ('SHR', 8, 'x')), [0, 26]),
        case('shift_signextend', ('SHL', 8, ('SIGNEXTEND', 2, 'x')), [27, 0, 11]),
        case('signextend_shift_sar', ('SIGNEXTEND', 2, ('SHR', 232, 'x')), [29]),
        case('sub_constant', ('SUB', 'x', 7), [0, 1]),
        case('sub_left_add', ('SUB', ('ADD', 'x', 7), 'y'), [3, 0, 1]),
        case('sub_right_add', ('SUB', 'x', ('ADD', 7, 'y')), [3, 0, 1]),
        case('sub_left_sub_right', ('SUB', ('SUB', 'x', 7), 'y'), [3, 0, 3]),
        case('sub_left_sub_left', ('SUB', ('SUB', 7, 'x'), 'y'), [1, 0, 3]),
        case('sub_right_sub_right', ('SUB', 'x', ('SUB', 'y', 7)), [3, 0, 1]),
        case('sub_right_sub_left', ('SUB', 'x', ('SUB', 7, 'y')), [1, 0, 1]),
        case('unary_not', ('NOT', ('NOT', 'x')), []),
        case('unary_triple_zero', ('ISZERO', ('ISZERO', ('ISZERO', 'x'))), [21]),
        case('unary_xor_eq', ('ISZERO', ('XOR', 'x', 'y')), [20]),
        case('unary_sub_eq', ('ISZERO', ('SUB', 'x', 'y')), [20]),
        case('unary_arity_rejected', ('NOT', ('NOT', 'x', 'y')), []),
        case('unary_forwarded_arity', ('ISZERO', ('XOR', 'x')), [20]),
        case('selfbalance_disabled', ('BALANCE', ('ADDRESS',)), []),
        case('exp_zero', ('EXP', 0, 'x'), [21], version='Homestead'),
        case('exp_one', ('EXP', 1, 'x'), [0], version='Homestead'),
        case('exp_minus_one', ('EXP', MAX, 'x'), [0, 22, 21, 3], version='Homestead'),
        case('exp_two_disabled', ('EXP', 2, 'x'), [], version='Byzantium'),
        case('exp_two_enabled', ('EXP', 2, 'x'), [0, 27], version='Constantinople'),
        case('mul_power_left', ('MUL', 8, 'x'), [0, 27], version='Osaka'),
        case('mul_power_right', ('MUL', 'x', 8), [0, 27], version='Osaka'),
        case('div_power_right', ('DIV', 'x', 8), [0, 28], version='Osaka'),
        case('mul_power_disabled', ('MUL', 'x', 8), [], version='Byzantium'),
    ]
    for op in ['STOP', 'SAR', 'CLZ', 'ADDRESS', 'BALANCE', 'ORIGIN', 'CALLER', 'COINBASE',
               'SELFBALANCE', 'KECCAK256', 'SLOAD', 'MLOAD', 'TLOAD', 'CALL', 'INVALID']:
        for arity in range(5):
            for version in [None, 'Osaka']:
                cases.append(case('nonword_' + op + '_' + str(arity) + '_' + str(version),
                                  (op, *[7, 3, 5, 9][:arity]), [], version=version))
    for op in ['ADD', 'MUL', 'SUB', 'DIV', 'SDIV', 'MOD', 'SMOD', 'EXP', 'NOT',
               'LT', 'GT', 'SLT', 'SGT', 'EQ', 'ISZERO', 'AND', 'OR', 'XOR', 'BYTE',
               'ADDMOD', 'MULMOD', 'SIGNEXTEND', 'SHL', 'SHR']:
        arity = 1 if op in ['NOT', 'ISZERO'] else 3 if op in ['ADDMOD', 'MULMOD'] else 2
        cases.append(case('word_vocabulary_' + op, (op, *[7, 3, 5][:arity]), [0]))
    for args in [(), ('i',), ('i', 'x'), ('i', 'x', 'y')]:
        cases.append(case('and_byte_forward_' + str(len(args)), ('AND', ('BYTE', *args), 255), [26]))
    for mask, calls in [(0, [0]), (255, [26]), (256, []), (MAX, [])]:
        cases.append(case('and_byte_mask_' + str(mask), ('AND', ('BYTE', 'i', 'x'), mask), calls))
    cases.append(case('and_byte_reversed', ('AND', 255, ('BYTE', 'i', 'x')), []))
    for reverse in [False, True]:
        def pair(left, right):
            return ('AND', right, left) if reverse else ('AND', left, right)
        for nested_args in [('x', 'y'), ('y', 'x')]:
            cases.append(case('and_absorb_' + str(reverse) + str(nested_args), pair('x', ('OR', *nested_args)), []))
            cases.append(case('and_repeat_' + str(reverse) + str(nested_args), pair('x', ('AND', *nested_args)), [22]))
        cases.append(case('and_negation_' + str(reverse), pair('x', ('NOT', 'x')), [0]))
        for mask, index, calls in [(255, 0, [0, 22]), (256, 0, []), (0xff00, 1, [0, 22]),
                                   (ADDRESS_MASK, 19, [0, 22]), (255, 31, []), (255, MAX, []), (0, 0, [0]), (MAX, 0, [])]:
            cases.append(case('and_signextend_' + str(reverse) + '_' + str(mask) + '_' + str(index),
                              pair(mask, ('SIGNEXTEND', index, 'x')), calls))
        for address in ['ADDRESS', 'CALLER', 'ORIGIN', 'COINBASE']:
            opcode = dict(ADDRESS=48, CALLER=51, ORIGIN=50, COINBASE=65)[address]
            cases.append(case('and_address_' + address + str(reverse), pair(ADDRESS_MASK, (address,)), [opcode]))
            cases.append(case('and_address_mask_miss_' + address + str(reverse), pair(ADDRESS_MASK - 1, (address,)), []))
            cases.append(case('and_address_arity_' + address + str(reverse), pair(ADDRESS_MASK, (address, 'i')), []))
        for constant in [0, 7, MAX]:
            for first in [False, True]:
                nested = ('AND', constant, 'x') if first else ('AND', 'x', constant)
                label = str(reverse) + '_' + str(first) + '_' + str(constant)
                cases.append(case('and_reassociate_word_' + label, pair(nested, 'y'), [22, 0, 22]))
                cases.append(case('and_reassociate_constant_' + label, pair(nested, 6), [0, 22]))
        for inner_second in [False, True]:
            for constant_first in [False, True]:
                inner = ('AND', 3, 'x') if constant_first else ('AND', 'x', 3)
                alternatives = ('OR', 'y', inner) if inner_second else ('OR', inner, 'y')
                cases.append(case('and_alternating_' + str(reverse) + '_' + str(inner_second) + '_' + str(constant_first),
                                  pair(alternatives, 6), [0, 22, 0, 22, 23]))
        for amount, mask, calls in [(7, MAX >> 7, [28]), (255, 1, [28]), (256, 1, [28]),
                                    (257, 1, []), (MAX, 1, []), (7, 1, []), (256, 0, [0]), (7, MAX, [])]:
            cases.append(case('and_covered_' + str(reverse) + '_' + str(amount) + '_' + str(mask),
                              pair(mask, ('SHR', amount, 'x')), calls))
    for amount in ['i', 0, 1, 255, 256, MAX]:
        cases.append(case('and_merged_' + str(amount), ('AND', ('SHL', amount, 'x'), ('SHL', amount, 'y')), [22, 27]))
    cases.append(case('and_merged_distinct', ('AND', ('SHL', 7, 'x'), ('SHL', 8, 'y')), []))
    for args in [(), ('i',), ('i', 'x', 'y')]:
        cases.append(case('and_merged_arity_' + str(len(args)), ('AND', ('SHL', *args), ('SHL', 'i', 'y')), []))
    cases.extend([
        case('and_equal_unknown', ('AND', 'x', 'x'), []),
        case('and_distinct_unknown', ('AND', 'x', 'y'), []),
        case('and_fold_mask', ('AND', MAX, 255), [0]),
    ])
    for outer, inner, calls in [
        (7, 2, [0, 11]), (2, 7, [0, 11]), (2, 2, [11]), (0, 30, [0, 11]),
        (30, 0, [0, 11]), (31, 0, [0, 11]), (32, 0, [0, 11]), (MAX, 0, [0, 11]),
        (1, MAX, [0, 11]), (31, 31, [11]), (MAX, MAX, [11]),
    ]:
        cases.append(case('signextend_nested_' + str(outer) + '_' + str(inner),
                          ('SIGNEXTEND', outer, ('SIGNEXTEND', inner, 'x')), calls))
    for index in [0, 1, 2, 15, 30]:
        correct_amount = 256 - 8 * (index + 1)
        for amount in [correct_amount, correct_amount - 1, correct_amount + 1, correct_amount - 8, 256, 264, MAX]:
            cases.append(case('signextend_shr_' + str(index) + '_' + str(amount),
                              ('SIGNEXTEND', index, ('SHR', amount, 'x')),
                              [29] if amount == correct_amount else [], yul=True, version='Homestead'))
    for index in [31, 32, 256, MAX]:
        cases.append(case('signextend_large_' + str(index), ('SIGNEXTEND', index, ('SHR', 0, 'x')), []))
    for nested in ['SIGNEXTEND', 'SHR']:
        for args in [(), ('i',), ('i', 'x'), ('i', 'x', 'y')]:
            cases.append(case('signextend_arity_' + nested + str(len(args)), ('SIGNEXTEND', 2, (nested, *args)), []))
    cases.extend([
        case('signextend_repeat_unknown', ('SIGNEXTEND', 'i', ('SIGNEXTEND', 'i', 'x')), [11]),
        case('signextend_distinct_unknown', ('SIGNEXTEND', 'i', ('SIGNEXTEND', 'j', 'x')), []),
        case('signextend_unknown_outer', ('SIGNEXTEND', 'i', ('SIGNEXTEND', 2, 'x')), []),
        case('signextend_unknown_shift', ('SIGNEXTEND', 'i', ('SHR', 232, 'x')), []),
        case('signextend_large_unknown_inner', ('SIGNEXTEND', 31, ('SIGNEXTEND', 'i', 'x')), []),
        case('signextend_equal_arguments', ('SIGNEXTEND', 'x', 'x'), []),
        case('signextend_zero_unknown_index', ('SIGNEXTEND', 'i', 0), []),
        case('signextend_fold_negative', ('SIGNEXTEND', 0, 128), [0]),
        case('signextend_fold_positive', ('SIGNEXTEND', 0, 127), [0]),
        case('signextend_fold_large', ('SIGNEXTEND', 31, 128), [0]),
        case('signextend_fold_max_index', ('SIGNEXTEND', MAX, MAX), [0]),
    ])
    for shift, opposite, shift_opcode, opposite_opcode in [('SHR', 'SHL', 28, 27), ('SHL', 'SHR', 27, 28)]:
        prefix = shift.lower()
        for nested, boundaries in [
            (shift, [(7, 9, [0, shift_opcode]), (1, 254, [0, shift_opcode]), (1, 255, [0]),
                     (255, 0, [0, shift_opcode]), (1, 256, [0]), (1, MAX, [0]), (255, 255, [0]),
                     (256, 1, [0]), (MAX, MAX, [0]), (0, MAX, [])]),
            (opposite, [(7, 2, [0, shift_opcode, 0, 22]), (2, 7, [0, opposite_opcode, 0, 22]), (8, 8, [0, 22]),
                     (255, 1, [0, shift_opcode, 0, 22]), (1, 255, [0, opposite_opcode, 0, 22]),
                     (7, 0, [0, shift_opcode, 0, 22]), (0, 7, []), (1, 256, []), (1, MAX, []), (256, 1, [0])]),
        ]:
            for outer, inner, calls in boundaries:
                cases.append(case(prefix + '_nested_' + nested + '_' + str(outer) + '_' + str(inner),
                                  (shift, outer, (nested, inner, 'x')), calls, yul=True, version='Osaka'))
        for amount, mask in [(1, 0), (8, 0xff00), (255, MAX), (256, MAX)]:
            for first in [False, True]:
                masked = ('AND', mask, 'x') if first else ('AND', 'x', mask)
                cases.append(case(prefix + '_mask_' + str(amount) + '_' + str(first), (shift, amount, masked),
                                  [0] if amount >= 256 else [shift_opcode, 0, 22]))
        for nested in [shift, opposite, 'AND']:
            for args in [(), ('i',), ('i', 'x'), ('i', 'x', 'y')]:
                cases.append(case(prefix + '_nested_miss_' + nested + str(len(args)), (shift, 7, (nested, *args)), []))
        cases.extend([
            case(prefix + '_unknown_amount', (shift, 'i', (shift, 7, 'x')), []),
            case(prefix + '_equal_unknown', (shift, 'x', 'x'), []),
            case(prefix + '_right_zero', (shift, 'x', 0), [0]),
            case(prefix + '_mask_both_constants', (shift, 8, ('AND', 0xff00, 0x7f00)), [shift_opcode, 0, 22]),
            case(prefix + '_fold_255', (shift, 255, MAX), [0]),
            case(prefix + '_fold_256', (shift, 256, MAX), [0]),
            case(prefix + '_fold_zero', (shift, 0, MAX), [0]),
        ])
    for amount, index, calls in [
        (8, 0, [27, 0, 11]), (8, 30, [27, 0, 11]), (8, 31, [27, 0, 11]), (8, 32, [27, 0, 11]),
        (248, 0, [27, 0, 11]), (16, 30, [27, 0, 11]), (248, 32, [27, 0, 11]),
        (0, MAX, []), (1, 0, []), (7, 0, []), (9, 0, []), (255, 0, []),
        (8, 33, []), (8, MAX, []), (256, 0, [0]), (264, 0, [0]), (MAX, MAX, [0]),
    ]:
        cases.append(case('shl_signextend_' + str(amount) + '_' + str(index),
                          ('SHL', amount, ('SIGNEXTEND', index, 'x')), calls))
    for args in [(), ('i',), ('i', 'x'), ('i', 'x', 'y')]:
        cases.append(case('shl_signextend_miss_' + str(len(args)), ('SHL', 8, ('SIGNEXTEND', *args)), []))
    for shift, boundaries in [
        ('SHL', [(0, 0, [0, 26]), (0, 8, [0, 26]), (30, 8, [0, 26]),
                 (30, 16, [0, 26]), (0, 256, [0, 26]), (30, 256, [0, 26]),
                 (0, 1, []), (2, 9, []), (30, 255, []), (0, 264, []), (0, MAX, []),
                 (31, 0, [0, 22]), (31, 9, [0, 22]), (31, 256, [0, 22]),
                 (32, 8, [0]), (MAX, MAX, [0])]),
        ('SHR', [(0, 0, [0, 26]), (1, 8, [0, 26]), (30, 240, [0, 26]),
                 (30, 248, [0]), (0, 8, [0]), (0, 9, [0]), (1, 9, []), (30, 7, []),
                 (0, 256, [0]), (30, 257, [0]), (30, MAX, [0]),
                 (31, 256, [0, 22]), (31, MAX, [0, 22]), (32, 0, [0]), (MAX, 8, [0])]),
    ]:
        for index, amount, calls in boundaries:
            cases.append(case('byte_boundary_' + shift + '_' + str(index) + '_' + str(amount),
                              ('BYTE', index, (shift, amount, 'x')), calls, yul=True, version='Osaka'))
        for args in [(), ('i',), ('i', 'x'), ('i', 'x', 'y')]:
            cases.append(case('byte_nested_miss_' + shift + str(len(args)), ('BYTE', 2, (shift, *args)), []))
    cases.extend([
        case('byte_plain_unknown', ('BYTE', 'i', 'x'), []),
        case('byte_plain_equal', ('BYTE', 'x', 'x'), []),
        case('byte_unknown_index_shift', ('BYTE', 'i', ('SHL', 8, 'x')), []),
        case('byte_fold_first', ('BYTE', 0, MAX), [0]),
        case('byte_fold_last', ('BYTE', 31, 0x1234), [0]),
        case('byte_fold_outside', ('BYTE', 32, MAX), [0]),
        case('byte_large_plain', ('BYTE', MAX, 'x'), [0]),
        case('byte_last_plain', ('BYTE', 31, 'x'), [0, 22]),
    ])
    for label, value in [('zero', 0), ('max', MAX), ('high', 1 << 255)]:
        cases.append(case('sub_constant_' + label, ('SUB', 'x', value), [] if value == 0 else [0, 1]))
        for name, expression, calls in [
            ('left_add', ('SUB', ('ADD', value, 'x'), 'y'), [3, 0, 1]),
            ('right_add', ('SUB', 'x', ('ADD', 'y', value)), [3, 0, 1]),
            ('left_sub_right', ('SUB', ('SUB', 'x', value), 'y'), [3, 0, 3]),
            ('left_sub_left', ('SUB', ('SUB', value, 'x'), 'y'), [1, 0, 3]),
            ('right_sub_right', ('SUB', 'x', ('SUB', 'y', value)), [3, 0, 1]),
            ('right_sub_left', ('SUB', 'x', ('SUB', value, 'y')), [1, 0, 1]),
        ]:
            cases.append(case('sub_' + name + '_' + label, expression, calls, yul=True, version='Osaka'))
    cases.extend([
        case('sub_fold_wrap', ('SUB', 0, 1), [0]),
        case('sub_fold_equal', ('SUB', MAX, MAX), [0]),
        case('sub_plain_miss', ('SUB', 'x', 'y'), [], yul=True, version='Homestead'),
        case('sub_zero_priority', ('SUB', ('ADD', 'x', 7), 0), []),
        case('sub_constant_priority', ('SUB', ('ADD', 'x', 7), 9), [0, 1]),
        case('sub_equal_priority', ('SUB', ('SUB', 'x', 7), ('SUB', 'x', 7)), [0]),
        case('sub_left_add_first', ('SUB', ('ADD', 'x', 7), ('ADD', 'y', 9)), [3, 0, 1]),
        case('sub_right_add_before_left_sub', ('SUB', ('SUB', 'x', 7), ('ADD', 'y', 9)), [3, 0, 1]),
        case('sub_left_sub_first', ('SUB', ('SUB', 'x', 7), ('SUB', 'y', 9)), [3, 0, 3]),
        case('sub_left_both_constants', ('SUB', ('SUB', 7, 9), 'x'), [3, 0, 3]),
        case('sub_right_both_constants', ('SUB', 'x', ('SUB', 7, 9)), [3, 0, 1]),
        case('sub_add_both_constants', ('SUB', ('ADD', 7, 9), 'x'), [3, 0, 1]),
        case('sub_malformed_left_fallback', ('SUB', ('ADD', 'x'), ('SUB', 'y', 7)), [3, 0, 1]),
        case('sub_nonconstant_left_fallback', ('SUB', ('SUB', 'x', 'y'), ('SUB', 7, 'z')), [1, 0, 1]),
    ])
    for nested in ['ADD', 'SUB']:
        for args in [(), ('x',), ('x', 'y'), ('x', 'y', 7)]:
            expression = (nested, *args)
            cases.append(case('sub_malformed_left_' + nested + str(len(args)), ('SUB', expression, 'z'), []))
            cases.append(case('sub_malformed_right_' + nested + str(len(args)), ('SUB', 'z', expression), []))
    for op, opcode in [('ADD', 1), ('MUL', 2), ('AND', 22), ('OR', 23), ('XOR', 24)]:
        cases.append(case('assoc_' + op, (op, (op, 'x', 7), 3), [0, opcode]))
        cases.append(case('assoc_move_' + op, (op, 'y', (op, 'x', 7)), [opcode, 0, opcode]))
    for op, opcode in [('ADD', 1), ('OR', 23), ('XOR', 24)]:
        cases.append(case('assoc_both_candidates_' + op, (op, (op, 'x', 7), (op, 'y', 3)), [opcode, 0, opcode]))
        cases.append(case('assoc_constant_first_' + op, (op, (op, 7, 'x'), 3), [0, opcode]))
        cases.append(case('assoc_plain_miss_' + op, (op, 'x', 'y'), [], yul=True, version='Osaka'))
    cases.extend([
        case('assoc_add_table_priority', ('ADD', ('ADD', 'x', 7), 0), []),
        case('assoc_or_equal_priority', ('OR', ('OR', 'x', 7), ('OR', 'x', 7)), []),
        case('assoc_xor_equal_priority', ('XOR', ('XOR', 'x', 7), ('XOR', 'x', 7)), [0]),
        case('or_negation_left', ('OR', ('NOT', 'x'), 'x'), [0]),
        case('assoc_add_wrapping_fold', ('ADD', MAX, 1), [0]),
    ])
    for amount in [0, 255, 256, MAX]:
        for side in ['left', 'right']:
            shifted = ('SHL', amount, 1)
            expression = ('MUL', shifted, 'x') if side == 'left' else ('MUL', 'x', shifted)
            cases.append(case('mul_shift_product_' + side + '_' + str(amount), expression, [27], version='Osaka'))
    for side in ['left', 'right']:
        for power in [1, 127, 128, 255]:
            expression = ('MUL', 1 << power, 'x') if side == 'left' else ('MUL', 'x', 1 << power)
            cases.append(case('mul_revision_power_' + side + '_' + str(power), expression, [0, 27], version='Osaka'))
    cases.extend([
        case('mul_revision_nonpower', ('MUL', 'x', 3), [], version='Osaka'),
        case('mul_revision_zero_priority', ('MUL', 'x', 0), [0], version='Osaka'),
        case('mul_revision_one_priority', ('MUL', 'x', 1), [], version='Osaka'),
        case('mul_revision_fold_priority', ('MUL', 8, 3), [0], version='Osaka'),
        case('mul_revision_disabled_high', ('MUL', 1 << 255, 'x'), [], version='Byzantium'),
        case('mul_revision_first_shift_fork', ('MUL', 'x', 8), [0, 27], version='Constantinople'),
        case('mul_reassociation_before_shift', ('MUL', ('MUL', 'x', 7), ('SHL', 'y', 1)), [2, 0, 2], yul=True, version='Osaka'),
        case('mul_reassociation_before_revision', ('MUL', ('MUL', 'x', 7), 8), [0, 2], version='Osaka'),
    ])
    for amount in [0, 255, 256, MAX]:
        cases.append(case('div_shift_divisor_' + str(amount), ('DIV', 'x', ('SHL', amount, 1)), [28], version='Osaka'))
    for power in [1, 127, 128, 255]:
        cases.append(case('div_revision_power_' + str(power), ('DIV', 'x', 1 << power), [0, 28], version='Osaka'))
    cases.extend([
        case('div_revision_nonpower', ('DIV', 'x', 3), [], version='Osaka'),
        case('div_revision_zero_priority', ('DIV', 'x', 0), [0], version='Osaka'),
        case('div_revision_one_priority', ('DIV', 'x', 1), [], version='Osaka'),
        case('div_revision_fold_priority', ('DIV', 17, 8), [0], version='Osaka'),
        case('div_revision_disabled_high', ('DIV', 'x', 1 << 255), [], version='Byzantium'),
        case('div_revision_first_shift_fork', ('DIV', 'x', 8), [0, 28], version='Constantinople'),
        case('div_revision_numerator_only', ('DIV', 8, 'x'), [], version='Osaka'),
        case('div_equal_miss', ('DIV', 'x', 'x'), [], version='Osaka'),
        case('div_shift_disabled_fork', ('DIV', 'x', ('SHL', 'i', 1)), [28], version='Byzantium'),
        case('div_shift_wrong_base', ('DIV', 'x', ('SHL', 'i', 2)), [], version='Osaka'),
        case('div_shift_wrong_arity', ('DIV', 'x', ('SHL', 'i')), [], version='Osaka'),
        case('div_shift_numerator_only', ('DIV', ('SHL', 'i', 1), 'x'), [], version='Osaka'),
        case('div_fold_zero', ('DIV', MAX, 0), [0], version='Osaka'),
    ])
    for op, opcode in [('MUL', 9), ('ADD', 8)]:
        for yul in [False, True]:
            for power in [0, 7, 255]:
                cases.append(case('mod_nested_' + op + '_' + str(yul) + '_' + str(power),
                    ('MOD', (op, 'x', 'y'), 1 << power), [opcode] if yul else [0, 22], yul=yul, version='Osaka'))
        cases.append(case('mod_nested_nonpower_' + op, ('MOD', (op, 'x', 'y'), 3), [], yul=True))
        cases.append(case('mod_nested_malformed_' + op, ('MOD', (op, 'x'), 8), [0, 22], yul=True))
    for power in [1, 128]:
        cases.append(case('mod_plain_power_' + str(power), ('MOD', 'x', 1 << power), [0, 22], yul=True))
    cases.extend([
        case('mod_zero_priority', ('MOD', ('MUL', 'x', 'y'), 0), [0], yul=True),
        case('mod_equal_priority', ('MOD', 'x', 'x'), [0], yul=True),
        case('mod_fold_priority', ('MOD', MAX, 8), [0], yul=True),
        case('mod_unknown_modulus', ('MOD', ('MUL', 'x', 'y'), 'z'), [], yul=True),
        case('mod_wrapped_add_counterexample', ('MOD', (MAX + 2) & MAX, 3), [0], yul=True),
        case('mod_wrapped_mul_counterexample', ('MOD', (MAX * 2) & MAX, 3), [0], yul=True),
    ])
    for base, calls in [(0, [21]), (1, [0]), (2, [0, 27]), (MAX, [0, 22, 21, 3])]:
        for version in ['Byzantium', 'Constantinople', 'Osaka']:
            cases.append(case('exp_revision_' + str(base) + '_' + version, ('EXP', base, 'x'),
                [] if base == 2 and version == 'Byzantium' else calls, version=version))
        cases.append(case('exp_no_revision_' + str(base), ('EXP', base, 'x'), []))
    for name, base, exponent in [
        ('zero_zero', 0, 0), ('zero_max', 0, MAX), ('one_max', 1, MAX),
        ('two_255', 2, 255), ('two_256', 2, 256), ('two_max', 2, MAX),
        ('minus_even', MAX, 1 << 255), ('minus_odd', MAX, MAX),
    ]:
        cases.append(case('exp_fold_' + name, ('EXP', base, exponent), [0], yul=True, version='Osaka'))
    cases.extend([
        case('exp_unknown_exponent_zero', ('EXP', 'x', 0), [], version='Osaka'),
        case('exp_other_base', ('EXP', 3, 'x'), [], version='Osaka'),
        case('exp_equal_unknown', ('EXP', 'x', 'x'), [], version='Osaka'),
    ])
    for op in ['ADDMOD', 'MULMOD']:
        for name, a, b, modulus in [
            ('wide', MAX, 2, 3), ('zero', MAX, MAX, 0),
            ('one', MAX, MAX, 1), ('large', MAX, MAX, MAX),
        ]:
            cases.append(case('ternary_' + op + '_' + name, (op, a, b, modulus), [0], yul=True, version='Osaka'))
        cases.append(case('ternary_' + op + '_missing', (op, 'x', 2, 3), [], version='Osaka'))
        for args in [(), (1,), (1, 2), (1, 2, 3, 4)]:
            cases.append(case('ternary_' + op + '_arity_' + str(len(args)), (op, *args), [], version='Osaka'))
    for op in ['STOP', 'EXP', 'ADD', 'ISZERO']:
        cases.append(case('arity_three_' + op, (op, 0, 1, 2), [], version='Osaka'))
    for op in ['NOT', 'ISZERO']:
        for name, value in [('zero', 0), ('one', 1), ('high_bit', 1 << 255), ('max', MAX)]:
            cases.append(case('unary_fold_' + op + '_' + name, (op, value), [0]))
        cases.append(case('unary_plain_miss_' + op, (op, 'x'), [], yul=True, version='Osaka'))
    for op in ['SDIV', 'SMOD']:
        for name, a, b in [
            ('negative_left', MAX - 6, 2), ('negative_right', 7, MAX - 1),
            ('negative_both', MAX - 6, MAX - 1), ('overflow', 1 << 255, MAX),
            ('equal_minimum', 1 << 255, 1 << 255), ('minimum_one', 1 << 255, 1),
            ('constant_one_priority', 7, 1), ('constant_zero', MAX, 0),
        ]:
            cases.append(case('signed_' + op + '_' + name, (op, a, b), [0]))
        zero_calls = [0] if op == 'SDIV' else []
        cases.append(case('signed_' + op + '_zero_right', (op, 'x', 0), zero_calls))
        cases.append(case('signed_' + op + '_zero_left', (op, 0, 'x'), zero_calls))
        cases.append(case('signed_' + op + '_one_right', (op, 'x', 1), []))
        cases.append(case('signed_' + op + '_equal_unknown', (op, 'x', 'x'), [], yul=True, version='Osaka'))
        cases.append(case('signed_' + op + '_distinct_unknown', (op, 'x', 'y'), []))
    for op in ['EQ', 'LT', 'SLT', 'GT', 'SGT']:
        opcode = dict(EQ=20, LT=16, SLT=18, GT=17, SGT=19)[op]
        cases.append(case('unary_bool_' + op, ('ISZERO', ('ISZERO', (op, 'x', 'y'))), [opcode]))
        cases.append(case('comparison_equal_' + op, (op, 'x', 'x'), [0]))
        cases.append(case('comparison_distinct_' + op, (op, 'x', 'y'), [], yul=True, version='Osaka'))
        cases.append(case('comparison_fold_sign_' + op, (op, 1 << 255, MAX), [0]))
        cases.append(case('comparison_fold_max_zero_' + op, (op, MAX, 0), [0], yul=True, version='Osaka'))
    for name, expression, calls in [
        ('eq_left_zero', ('EQ', 0, 'x'), [21]),
        ('eq_right_zero', ('EQ', 'x', 0), [21]),
        ('lt_left_zero', ('LT', 0, 'x'), [21, 21]),
        ('lt_left_max', ('LT', MAX, 'x'), [0]),
        ('lt_right_zero', ('LT', 'x', 0), [0]),
        ('gt_right_zero', ('GT', 'x', 0), [21, 21]),
        ('gt_right_max', ('GT', 'x', MAX), [0]),
        ('gt_left_zero', ('GT', 0, 'x'), [0]),
        ('slt_zero_is_not_unsigned', ('SLT', 0, 'x'), []),
        ('sgt_max_is_not_unsigned', ('SGT', 'x', MAX), []),
    ]:
        cases.append(case('comparison_' + name, expression, calls))
    for version, enabled in [('Petersburg', False), ('Istanbul', True), ('Osaka', True)]:
        cases.append(case('selfbalance_' + version, ('BALANCE', ('ADDRESS',)), [71] if enabled else [], version=version))
    # Inject at every construction point; retained partial traces are compared.
    return cases + [(dict(item, name=item['name'] + '_oom_' + str(i), failAt=i), calls[:i])
                    for item, calls in cases for i in range(1, len(calls) + 1)]
