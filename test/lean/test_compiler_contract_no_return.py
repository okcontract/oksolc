"""Closed admission and complete inventory for typed functions with no return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import cases, function, request, source_request
from test_compiler_contracts import fake_response


class NoReturnTests(unittest.TestCase):
    def test_resource_failure_cannot_pass_a_negative_control(self):
        rejected = checker.artifacts.is_semantic_rejection
        self.assertTrue(rejected(checker, 1, 'error: unsolved goals'))
        self.assertTrue(rejected(checker, 1, 'error: proposition is false'))
        for exit_code, diagnostic in (
            (0, 'unsolved goals'), (-6, 'unsolved goals'),
            (1, 'unsolved goals\nerror: (kernel) excessive memory consumption detected'),
            (1, 'unsolved goals\nOUT OF MEMORY'),
            (1, 'unsolved goals\nmaximum recursion depth has been reached'),
            (1, 'unknown identifier source')):
            with self.subTest(exit_code=exit_code, diagnostic=diagnostic):
                self.assertFalse(rejected(checker, exit_code, diagnostic))

    def test_unchanged_complete_corpus_source(self):
        source, origin = corpus.load(corpus.NO_RETURN_PATH)
        req = dict(cases())[corpus.NO_RETURN_CASE]
        self.assertEqual(req['sources']['Function.sol']['content'], source)
        self.assertEqual(origin['sourceSha256'], corpus.NO_RETURN_SHA256)
        self.assertEqual(origin['sourceBytes'], 168)
        self.assertFalse(origin['wholeOriginalRequestVerified'])
        self.assertFalse(origin['originalSettingsPreserved'])
        parsed = checker.model(req)['functions']
        self.assertEqual(len(parsed), 1)
        self.assertEqual(parsed[0]['signature'], 'supportsInterface(bytes4)')
        self.assertEqual(parsed[0]['returnType'], 'none')
        self.assertEqual(parsed[0]['parameterTypes'], ['bytes4'])
        self.assertEqual(parsed[0]['nodes'], [])
        self.assertIsNone(parsed[0]['root'])
        self.assertEqual(parsed[0]['mutability'], 'view')
        record = checker.case_metadata(req, fake_response(req))
        self.assertEqual(record['corpusSource'], origin)
        self.assertEqual(record['certificateKind'], 'mixedMethodContract')
        self.assertEqual(record['functions'][0]['bodyScope'], 'empty')

    def test_empty_is_exact_not_ignored_source(self):
        for body in ('{ return; }', '{ revert(); }', '{ assert(false); }', '{ ignored; }',
                     '{ uint256 local; }', '{ assembly {} }'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                checker.model(request(['function f(bytes4 ignored) external view ' + body]))
        for declaration in (
            'function f(bytes4 ignored) external pure returns(uint256) { return uint256(0); }',
            'function f(uint256 ignored) external view returns(uint256) { return ignored; }',
            'function f(bytes8 ignored) external view {}',
            'function f(bytes ignored) external view {}',
            'function f(bytes4 ignored) external {}',
            'function f(bytes4 x, bytes4 x) external view {}'):
            with self.subTest(declaration=declaration), self.assertRaises(ValueError):
                checker.model(request([declaration]))
        unsupported = 'pragma solidity *; contract A {} contract B { function f(bytes4 x) external view { x; } }'
        with self.assertRaises(ValueError): checker.model(source_request(unsupported, 'A'))

    def test_mixed_inventory_and_separate_admission_routes(self):
        req = request(['function ignore(bytes4 id, uint256 ignored) public view {}', function('f', 'x', ('x',))])
        parsed = checker.model(req)['functions']
        self.assertEqual([f['signature'] for f in parsed], ['ignore(bytes4,uint256)', 'f(uint256)'])
        res = fake_response(req)
        changed = copy.deepcopy(res)
        del changed['contracts']['Function.sol']['C']['evm']['methodIdentifiers']['ignore(bytes4,uint256)']
        with self.assertRaises(ValueError): checker.artifact(req, changed)
        for source in ('function f(bytes4 x) public pure {}', 'function f(uint256 x) public pure {}'):
            with self.subTest(source=source), self.assertRaises(ValueError): checker.functions.model(request([source]))
        with self.assertRaises(ValueError):
            checker.model(request(['function f(' + ','.join('bytes4 x' + str(i) for i in range(9)) + ') external view {}']))


if __name__ == '__main__':
    unittest.main()
