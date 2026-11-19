"""Caller-boundary ordering and scoped-callee signature controls.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

from test_hash_initialization import fixture as initialization_fixture
from generate_hash_order import render, CALLER, PRODUCTION, WYHASH, pointer


def fixture():
    caller, initializer = initialization_fixture()
    sources = {PRODUCTION: '1' * 64, 'hash/wyhash.zig': initializer['sourceSha256']}
    caller.update(sourceSha256=sources[PRODUCTION])
    word = {'kind': 'int', 'bits': 64, 'signedness': 'unsigned'}
    caller['signature'] = {'returnType': word}
    owner = initializer['signature']['returnType']
    owner['identity'] = {'name': WYHASH.rstrip('.'), 'sourceFile': 'hash/wyhash.zig',
                         'sourceSha256': sources['hash/wyhash.zig']}
    owner['layout'] = {'kind': 'abi', 'bytes': 104, 'alignment': 8}
    receiver = pointer(owner, 104, 8)
    receiver['flags']['isConst'] = False
    byte_slice = pointer({'kind': 'int', 'bits': 8, 'signedness': 'unsigned'}, 1, 1, slice=True)
    records = {initializer['name']: initializer}
    for name, indices, parameters, result in (
        ('update', [10, 14, 18, 23, 27], [receiver, byte_slice], {'kind': 'void'}),
        ('final', [28], [receiver], word),
    ):
        callee = {k: copy.deepcopy(caller[k]) for k in ('configuration', 'schema', 'capturePoint', 'bodyTraversal')}
        identity = {'name': WYHASH + name, 'sourceFile': 'hash/wyhash.zig', 'sourceSha256': sources['hash/wyhash.zig']}
        callee.update(identity)
        callee['signature'] = {'callingConvention': {'auto': {}}, 'genericInstance': False,
            'varArgs': False, 'noaliasBits': 0, 'parameters': parameters, 'returnType': result}
        for index in indices:
            caller['instructions'][index].update(type=result, callee={'kind': 'function', 'identity': identity})
        records[callee['name']] = callee
    return copy.deepcopy((caller, records, sources))


class HashOrderTests(unittest.TestCase):
    def test_order_is_executable_but_callee_refinement_stays_open(self):
        args = fixture()
        before = copy.deepcopy(args)
        text, scope = render(*args)
        self.assertEqual(args, before)
        self.assertIn('[some .kind, some .instruction, some .data, none, some .sequence]', text)
        self.assertIn('HashBytes.Ordered.run state keyId inputs', text)
        self.assertEqual(scope['callerVisitedInstructions'], 30)
        for flag in ('initializationBeforeViews', 'updatesInterleavedWithViews', 'finalizationAfterViews'):
            self.assertTrue(scope[flag])
        for flag in ('updateFinalizationBodiesTranslated', 'keyCopyTranslated', 'completeCallerTranslated',
                     'sourceAdapterFormallyVerified'):
            self.assertFalse(scope[flag])

    def test_caller_cannot_precollect_delay_omit_or_redirect_updates(self):
        edits = [lambda c: c['body'].__setitem__(slice(10, 12), [11, 10]),
            lambda c: c['body'].remove(10),
            lambda c: c['instructions'][10]['arguments'][0].update(index=1),
            lambda c: c['instructions'][10]['arguments'][1].update(index=8),
            lambda c: c['instructions'][27].update(tag='store'),
            lambda c: c['instructions'][29]['operand'].update(index=5),
            lambda c: c['instructions'][7].update(fieldIndex=False),
            lambda c: c['instructions'][0].update(zirParameterIndex=True),
            lambda c: c['instructions'][10].update(unsupportedPayload=True),
            lambda c: c.update(name=CALLER + '.other'),
            lambda c: c.update(sourceSha256='2' * 64),
            lambda c: c['configuration'].update(optimize='Debug'),
            lambda c: c['signature']['returnType'].update(bits=32)]
        for index, edit in enumerate(edits):
            args = fixture()
            edit(args[0])
            with self.subTest(index=index), self.assertRaises(ValueError):
                render(*args)

    def test_callee_prototypes_and_identities_remain_bound(self):
        edits = [lambda rs: rs[WYHASH + 'update']['signature']['parameters'][0]['flags'].update(isConst=True),
            lambda rs: rs[WYHASH + 'update']['signature']['parameters'][1]['flags'].update(isConst=False),
            lambda rs: rs[WYHASH + 'update']['signature'].update(varArgs=True),
            lambda rs: rs[WYHASH + 'update']['signature']['returnType'].update(kind='noreturn'),
            lambda rs: rs[WYHASH + 'final']['signature']['returnType'].update(bits=32),
            lambda rs: rs[WYHASH + 'final'].update(sourceSha256='2' * 64),
            lambda rs: rs[WYHASH + 'update']['configuration'].update(endianness='big'),
            lambda rs: rs[WYHASH + 'init']['signature']['returnType']['identity'].update(name='other.Hasher'),
            lambda rs: rs[WYHASH + 'init']['signature']['returnType']['layout'].update(bytes=112)]
        for index, edit in enumerate(edits):
            args = fixture()
            edit(args[1])
            with self.subTest(index=index), self.assertRaises(ValueError):
                render(*args)


if __name__ == '__main__':
    unittest.main()
