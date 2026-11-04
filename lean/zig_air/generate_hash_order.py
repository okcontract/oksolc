"""Bind source caller order to the scoped hasher execution.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

This emits the view/update schedule, not update/finalization AIR. The actual
view programs and initializer are regenerated separately by the same gate.
"""
from generate import fields
from generate_hash_byte_views import CALLER, PRODUCTION, expect, pointer, require

WYHASH = 'hash.wyhash.Wyhash.'


def ref(inst):
    return {'kind': 'instruction', 'index': inst['index']}


def target(inst):
    callee = inst.get('callee', {})
    require(inst['tag'] == 'call' and callee.get('kind') == 'function', 'expected direct ordinary call')
    return callee['identity']['name']


def caller_order(record, mode='ReleaseFast'):
    """Check each caller input edge, including array-to-slice operands."""
    instructions = record['instructions']
    require(all(type(index) is int and 0 <= index < len(instructions) for index in record['body']),
            'caller body has an invalid instruction index')
    body = [instructions[index] for index in record['body']]
    require([i['index'] for i in instructions if i.get('payloadVisited') is True] == record['body'],
            'caller has unreviewed nested or reordered instructions')
    require(len(body) == 30, 'caller instruction sequence changed')
    require(all(not i.get('unsupportedPayload', False) for i in body), 'caller has an unsupported payload')
    key, key_alloc, key_store, key_pointer, hasher, init, init_store = body[:7]
    require(mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'), 'unsupported caller build mode')
    safe = mode != 'ReleaseFast'
    require([i['tag'] for i in body[:7]] == ['arg', 'alloc', 'store_safe' if safe else 'store',
                                          'ptr_cast', 'alloc', 'call', 'store'],
            'caller initialization order changed')
    require(type(key['zirParameterIndex']) is int and key['zirParameterIndex'] == 1 and
            key_alloc['allocationKind'] == hasher['allocationKind'] == 'stack',
            'caller key argument or allocation kind changed')
    require(key_store['lhs'] == ref(key_alloc) and key_store['rhs'] == ref(key) and
            key_pointer['operand'] == ref(key_alloc) and init_store['lhs'] == ref(hasher) and
            init_store['rhs'] == ref(init), 'caller key/initializer materialization changed')
    require(target(init) == WYHASH + 'init' and init['arguments'] == [
        {'kind': 'constant', 'type': {'kind': 'int', 'bits': 64, 'signedness': 'unsigned'}, 'value': 0}],
        'caller initializer or seed changed')
    position, updates, views = 7, [], []
    for field in range(5):
        pointer = body[position]
        require(pointer['tag'] == ('struct_field_ptr_index_' + str(field) if field < 4 else 'struct_field_ptr') and
                pointer['operand'] == ref(key_pointer) and type(pointer['fieldIndex']) is int and pointer['fieldIndex'] == field,
                'caller hash field order changed')
        position += 1
        argument = pointer
        if field == 3:
            argument = body[position]
            require(argument['tag'] == 'load' and argument['operand'] == ref(pointer),
                    'caller argument slice load changed')
            position += 1
        view, conversion, update = body[position:position + 3]
        helper = 'mem.sliceAsBytes__func_' if field == 3 else 'mem.asBytes__func_'
        require(target(view).startswith(helper) and view['arguments'] == [ref(argument)],
                'caller byte-view helper changed')
        require(conversion['tag'] == ('ptr_cast' if field == 3 else 'array_to_slice'),
                'caller byte-view conversion changed')
        require(conversion.get('operand') == ref(view) and not conversion.get('unsupportedPayload', False),
                'caller byte-view conversion operand missing or changed')
        require(target(update) == WYHASH + 'update' and update['arguments'] == [ref(hasher), ref(conversion)],
                'caller update receiver or input changed')
        views.append({'fieldIndex': field, 'call': view['index'], 'callee': target(view),
                      'conversion': conversion['index'], 'conversionTag': conversion['tag']})
        updates.append(update['index'])
        position += 3
    finish, returned = body[position:]
    require(target(finish) == WYHASH + 'final' and finish['arguments'] == [ref(hasher)] and
            returned['tag'] == ('ret_safe' if safe else 'ret') and returned['operand'] == ref(finish),
            'caller final result changed')
    return {'keyAllocation': key_alloc['index'], 'hasherAllocation': hasher['index'],
            'initializerCall': init['index'], 'initializerStore': init_store['index'],
            'byteViews': views, 'updateCalls': updates, 'finalCall': finish['index'],
            'byteViewSemanticsVerified': False, 'callerExecutionVerified': False}


def render(caller, records, sources):
    expect({k: caller[k] for k in ('name', 'sourceFile', 'sourceSha256')},
        {'name': CALLER, 'sourceFile': PRODUCTION, 'sourceSha256': sources[PRODUCTION]}, 'caller order identity changed')
    require(caller['configuration']['optimize'] == 'ReleaseFast', 'ordered execution admits ReleaseFast only')
    order = caller_order(caller)
    owner = records[WYHASH + 'init']['signature']['returnType']
    expect(owner['identity'], {'name': WYHASH.rstrip('.'), 'sourceFile': 'hash/wyhash.zig',
        'sourceSha256': sources['hash/wyhash.zig']}, 'hasher storage identity changed')
    expect(owner['layout'], {'kind': 'abi', 'bytes': 104, 'alignment': 8}, 'hasher layout changed')
    receiver = pointer(owner, 104, 8)
    receiver['flags']['isConst'] = False
    byte_slice = pointer({'kind': 'int', 'bits': 8, 'signedness': 'unsigned'}, 1, 1, slice=True)
    word = {'kind': 'int', 'bits': 64, 'signedness': 'unsigned'}
    for name, indices, parameters, result in (
        ('update', order['updateCalls'], [receiver, byte_slice], {'kind': 'void'}),
        ('final', [order['finalCall']], [receiver], word),
    ):
        callee = records[WYHASH + name]
        identity = {'name': WYHASH + name, 'sourceFile': 'hash/wyhash.zig', 'sourceSha256': sources['hash/wyhash.zig']}
        expect({k: callee[k] for k in identity}, identity, 'ordered callee identity changed')
        for key in ('configuration', 'schema', 'capturePoint', 'bodyTraversal'):
            expect(callee[key], caller[key], 'ordered callee capture configuration changed')
        expect(callee['signature'], {'callingConvention': {'auto': {}}, 'genericInstance': False,
            'varArgs': False, 'noaliasBits': 0, 'parameters': parameters, 'returnType': result},
            'ordered callee signature changed')
        for index in indices:
            instruction = caller['instructions'][index]
            fields(instruction, 'index tag type payloadVisited callee arguments')
            expect(instruction['callee'], {'kind': 'function', 'identity': identity}, 'ordered call identity changed')
            expect(instruction['type'], result, 'ordered call result changed')
    expect(caller['signature']['returnType'], word, 'hash return type changed')
    choices = ('some .kind', 'some .instruction', 'some .data', 'none', 'some .sequence')
    entries = ', '.join(choices[view['fieldIndex']] for view in order['byteViews'])
    text = '\n'.join([
        '/-', '// Copyright (C) 2026 OKcontract Pte. Ltd.', '// SPDX-License-Identifier: GPL-3.0',
        'Generated from the complete captured caller call order.',
        'Key-copy admission and update/finalization AIR refinement remain open.', '-/',
        'import Compiler.Extraction.ExpressionMapHashOrder', '',
        'namespace Compiler.Extraction.ExpressionMap.GeneratedHashOrder',
        'open Compiler.ZigAir.Memory', '',
        f'def inputs : List HashBytes.Ordered.Input := [{entries}]', '',
        '/-- The captured initialization precedes every view/update pair; finalization follows them. -/',
        'def run (state : State) (keyId : Nat) : Except Fault (BitVec 64) × State :=',
        '  HashBytes.Ordered.run state keyId inputs', '',
        'end Compiler.Extraction.ExpressionMap.GeneratedHashOrder', '',
    ])
    return text, {'callerVisitedInstructions': len(caller['body']), 'schedule': order,
        'initializationBeforeViews': True, 'updatesInterleavedWithViews': True, 'finalizationAfterViews': True,
        'updateFinalizationBodiesTranslated': False, 'keyCopyTranslated': False,
        'completeCallerTranslated': False, 'sourceAdapterFormallyVerified': False}
