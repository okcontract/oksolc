"""Generate an explicitly scoped three-instruction cut of the native hash caller.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

The complete caller stays captured. Unsupported key admission and the suffix are
reported, never erased into a purported whole-function translation. The capture
gate binds source/configuration identities and regenerates the concrete callee.
"""
from generate import fields
from generate_aggregate import Decoder, constant, type_of


def render(caller, initializer):
    if (caller.get('name') != 'src.libevmasm.expression_classes.ExpressionKeyContext.hash' or
            caller.get('sourceFile') != 'src/libevmasm/expression_classes.zig' or
            initializer.get('name') != 'hash.wyhash.Wyhash.init' or
            initializer.get('sourceFile') != 'hash/wyhash.zig'):
        raise ValueError('initialization fragment has an unexpected source identity')
    decoder = Decoder(initializer)
    decoder.program(initializer)
    if (caller['configuration'] != initializer['configuration'] or
            caller['schema'] != initializer['schema'] or
            caller['capturePoint'] != initializer['capturePoint'] or
            caller['bodyTraversal'] != initializer['bodyTraversal']):
        raise ValueError('caller/callee capture configuration differs')
    body, instructions = caller['body'], caller['instructions']
    if (len(body) != 30 or body[4:7] != [4, 5, 6] or
            [i['index'] for i in instructions if i.get('payloadVisited') is True] != body):
        raise ValueError('initialization cut is not the captured consecutive body fragment')
    allocated, called, stored = [instructions[index] for index in body[4:7]]
    fields(allocated, 'index tag type payloadVisited allocationKind')
    fields(called, 'index tag type payloadVisited callee arguments')
    fields(stored, 'index tag type payloadVisited lhs rhs')
    fields(called['callee'], 'kind identity')
    identity = {key: initializer[key] for key in ('name', 'sourceFile', 'sourceSha256')}
    if (allocated['tag'] != 'alloc' or allocated['allocationKind'] != 'stack' or
            called['tag'] != 'call' or called['callee'] != {'kind': 'function', 'identity': identity} or
            stored['tag'] != 'store' or stored['lhs'] != {'kind': 'instruction', 'index': 4} or
            stored['rhs'] != {'kind': 'instruction', 'index': 5}):
        raise ValueError('initialization allocation/call/store changed')
    if (type_of(allocated['type']) != ('ptr', True, False, decoder.result) or
            type_of(called['type']) != decoder.result or type_of(stored['type']) != ('void',) or
            decoder.parameters != [('int', False, 64)] or len(called['arguments']) != 1):
        raise ValueError('initialization type or argument mismatch')
    argument = called['arguments'][0]
    argument_type, reference = constant(argument)
    if argument_type != decoder.parameters[0] or argument.get('value') != 0:
        raise ValueError('production initializer seed changed')
    text = '\n'.join([
        '/-', '// Copyright (C) 2026 OKcontract Pte. Ltd.', '// SPDX-License-Identifier: GPL-3.0',
        'Generated from captured AIR instructions 4, 5, 6; do not edit.',
        'This is a caller fragment, not a complete hash-function translation.', '-/',
        'import Compiler.ZigAir.AggregateCall', 'import Compiler.ZigAir.GeneratedWyhashInit', '',
        'namespace Compiler.ZigAir.GeneratedExpressionHashInit', '',
        'def fragment (next : AggregateCall.Code) : AggregateCall.Code :=',
        '  AggregateCall.allocateCallStore 4 5 6 GeneratedWyhashInit.fn_init',
        f'    [{reference}] next', '', 'end Compiler.ZigAir.GeneratedExpressionHashInit', '',
    ])
    scope = {'selectedInstructions': body[4:7], 'remainingPrefix': body[:4], 'remainingSuffix': body[7:],
             'visitedInstructions': 3, 'callerVisitedInstructions': len(body),
             'completeCallerTranslated': False, 'sourceAdapterFormallyVerified': False}
    return text, scope
