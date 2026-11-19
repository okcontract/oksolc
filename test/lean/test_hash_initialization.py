"""Check fragment boundaries, typed call bindings and explicit remaining scope.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

from test_expression_hash_air import fixture as caller_fixture
from test_zig_air_aggregate_generate import aggregate_fixture
from check_zig_air_memory import pointer
from generate_hash_initialization import render


def fixture():
    caller, callee = caller_fixture(), aggregate_fixture()
    caller.update(name='src.libevmasm.expression_classes.ExpressionKeyContext.hash',
                  sourceFile='src/libevmasm/expression_classes.zig')
    callee.update(name='hash.wyhash.Wyhash.init', sourceFile='hash/wyhash.zig')
    for key in ('configuration', 'schema', 'capturePoint', 'bodyTraversal'):
        caller[key] = copy.deepcopy(callee[key])
    owner = callee['signature']['returnType']
    caller['instructions'][4]['type'] = pointer(owner, owner['layout'])
    caller['instructions'][5]['type'] = owner
    caller['instructions'][5]['callee']['identity'] = {
        key: callee[key] for key in ('name', 'sourceFile', 'sourceSha256')}
    caller['instructions'][6]['type'] = {'kind': 'void'}
    return copy.deepcopy((caller, callee))


class HashInitializationTests(unittest.TestCase):
    def test_fragment_keeps_residual_scope(self):
        caller, callee = fixture()
        before = copy.deepcopy((caller, callee))
        text, scope = render(caller, callee)
        self.assertIn('allocateCallStore 4 5 6', text)
        self.assertEqual(scope['selectedInstructions'], [4, 5, 6])
        self.assertEqual(scope['remainingPrefix'] + scope['selectedInstructions'] + scope['remainingSuffix'], caller['body'])
        self.assertEqual(scope['callerVisitedInstructions'], 30)
        self.assertFalse(scope['completeCallerTranslated'])
        self.assertEqual(before, (caller, callee))

    def test_changed_order_receiver_seed_and_callee_reject(self):
        edits = [
            lambda c, f: c['body'].__setitem__(slice(4, 6), [5, 4]),
            lambda c, f: c['instructions'][4].update(allocationKind='heap'),
            lambda c, f: c['instructions'][5]['arguments'][0].update(value=1),
            lambda c, f: c['instructions'][5]['arguments'].clear(),
            lambda c, f: c['instructions'][5]['callee']['identity'].update(sourceSha256='b' * 64),
            lambda c, f: c['instructions'][6]['lhs'].update(index=1),
            lambda c, f: c['instructions'][6]['rhs'].update(index=4),
            lambda c, f: c['instructions'][5].update(payloadVisited=False),
            lambda c, f: c['instructions'][5].update(unsupportedPayload=True),
            lambda c, f: c['configuration'].update(optimize='Debug'),
            lambda c, f: c.update(name='another.hash'),
            lambda c, f: f.update(sourceFile='another/wyhash.zig'),
        ]
        for edit in edits:
            caller, callee = fixture()
            edit(caller, callee)
            with self.subTest(edit=edit), self.assertRaises(ValueError): render(caller, callee)

    def test_pointer_result_and_store_types_reject(self):
        edits = [
            lambda c: c['instructions'][4]['type']['flags'].update(isConst=True),
            lambda c: c['instructions'][4]['type']['flags'].update(size='many'),
            lambda c: c['instructions'][5].update(type={'kind': 'void'}),
            lambda c: c['instructions'][6].update(type={'kind': 'int', 'bits': 64, 'signedness': 'unsigned'}),
            lambda c: c['instructions'][5]['arguments'][0]['type'].update(bits=32),
        ]
        for edit in edits:
            caller, callee = fixture()
            edit(caller)
            with self.subTest(edit=edit), self.assertRaises(ValueError): render(caller, callee)


if __name__ == '__main__':
    unittest.main()
