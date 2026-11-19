#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Contextual uint256 literal returns, corpus identity and conservative rejection.
"""
import unittest
from unittest.mock import patch

import check_compiler_contracts as contracts
import check_compiler_functions as functions
import check_compiler_storage as storage
import compiler_contract_corpus as corpus
import compiler_storage_cases as storage_cases
from compiler_contract_cases import cases, source_request
from compiler_function_cases import request
from test_compiler_contracts import fake_response


class IntegerReturnTests(unittest.TestCase):
    def test_complete_retained_source(self):
        content, origin = corpus.load(corpus.INTEGER_PATH)
        req = dict(cases())[corpus.INTEGER_CASE]
        self.assertEqual(req['sources']['Function.sol']['content'], content)
        self.assertEqual(corpus.sha(content.encode()), corpus.INTEGER_SHA256)
        self.assertEqual((origin['sourceBytes'], origin['originalSourceCount'], origin['omittedSourceCount']),
                         (159, 229, 228))
        self.assertEqual(origin['originalFork'], 'london')
        self.assertTrue(origin['completeSourceUnit'])
        self.assertTrue(origin['sourceContentUnchanged'])
        self.assertFalse(origin['wholeOriginalRequestVerified'])
        self.assertFalse(origin['originalSettingsPreserved'])
        self.assertEqual(origin['uncertifiedSiblingContracts'], [])
        self.assertIsNone(origin['upstreamCommit'])
        self.assertIsNone(origin['retainedCorpusTransforms'])
        self.assertEqual(contracts.case_metadata(req, fake_response(req))['corpusSource'], origin)
        f = contracts.model(req)['functions'][0]
        self.assertEqual((f['signature'], f['returnType'], f['nodes']),
                         ('foo()', 'uint256', [{'literal': '0'}]))
        for field in ('INTEGER_ARCHIVE_SHA256', 'INTEGER_REQUEST_SHA256', 'INTEGER_SHA256'):
            with self.subTest(field=field), patch.object(corpus, field, '0' * 64), self.assertRaises(ValueError):
                corpus.load(corpus.INTEGER_PATH)

    def test_return_context_matches_existing_explicit_conversion(self):
        for literal in ('0', '1', '42', str(2**256 - 1), '0x0', '0xff', '0x' + 'f' * 64):
            for checked in (False, True):
                req = request(literal, ('ignored',), checked=checked)
                explicit = request('uint256(' + literal + ')', ('ignored',), checked=checked)
                with self.subTest(literal=literal, checked=checked):
                    self.assertEqual(functions.model(req), functions.model(explicit))
                    self.assertEqual(contracts.model(req), contracts.model(explicit))
                    proof, _ = contracts.proof_source([(req, fake_response(req))], 8)
                    self.assertIn(b'SolidityContract.Preserves sources creation code', proof)
        req = request('42', (), checked=True)
        req['sources']['Function.sol']['content'] = req['sources']['Function.sol']['content'].replace(
            'return 42;', 'return /* conversion context */ 42 /* end */;')
        self.assertEqual(functions.model(req)['nodes'], [{'literal': '42'}])

    def test_only_standalone_bounded_literal_is_admitted(self):
        expressions = [str(2**256), '0x1' + '0' * 64, '00', '01', '-1', '+1', '1.0', '1e2',
            '1_000', '1 ether', '(1)', '~1', '1 + 2', '1 - 2', '1 << 1',
            '1 + uint256(2)', 'uint256(1) + 2', 'ignored + 1', '1 + ignored',
            'uint256(1 + 2)', '1; return 2', '1 return', '1 2']
        expressions += ['0x' + '1' * n for n in (39, 40, 41)]
        for expression in expressions:
            for profile in (functions, contracts):
                with self.subTest(expression=expression, profile=profile.__name__), self.assertRaises(ValueError):
                    profile.model(request(expression, ('ignored',), checked=True))

    def test_other_contexts_and_unsupported_siblings_reject(self):
        req = storage_cases.request(['cell'], [storage_cases.function('f', 'return 0;', mutability='pure')])
        with self.assertRaises(ValueError):
            storage.model(req)
        content, _ = corpus.load(corpus.INTEGER_PATH)
        for sibling in ('contract Other { uint256 state; }',
                        'contract Other { function f() external pure returns(uint256) { return 1 + 2; } }'):
            with self.assertRaises(ValueError):
                contracts.model(source_request(content + sibling, corpus.INTEGER_TARGET))


if __name__ == '__main__':
    unittest.main()
