#!/usr/bin/env python3
"""Payability admission is per method, with the existing body restrictions.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
from unittest.mock import patch
import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import cases, function, request, source_request
from test_compiler_contracts import fake_response


class PayableContractTests(unittest.TestCase):
    def test_retained_mixed_contract_and_scope(self):
        content, origin = corpus.load(corpus.PAYABLE_PATH)
        req = dict(cases())[corpus.PAYABLE_CASE]
        self.assertEqual(req['sources']['Function.sol']['content'], content)
        self.assertEqual(corpus.sha(content.encode()), corpus.PAYABLE_SHA256)
        self.assertEqual((origin['sourceBytes'], origin['originalSourceCount']), (490, 282))
        self.assertEqual(origin['uncertifiedSiblingContracts'], [])
        self.assertTrue(origin['completeSourceUnit'])
        self.assertFalse(origin['wholeOriginalRequestVerified'])
        self.assertFalse(origin['originalSettingsPreserved'])
        self.assertIsNone(origin['upstreamCommit'])
        self.assertIsNone(origin['retainedCorpusTransforms'])
        parsed = checker.model(req)
        self.assertEqual([(f['signature'], f['payable']) for f in parsed['functions']],
                         [('admin()', True), ('delegatedFunction()', False)])
        record = checker.case_metadata(req, fake_response(req))
        self.assertEqual(record['corpusSource'], origin)
        self.assertEqual([f['payable'] for f in record['functions']], [True, False])
        with patch.object(corpus, 'PAYABLE_SHA256', '0' * 64), self.assertRaisesRegex(ValueError, 'complete source unit'):
            corpus.load(corpus.PAYABLE_PATH)
        with patch.object(corpus, 'PAYABLE_ARCHIVE_SHA256', '0' * 64), self.assertRaisesRegex(ValueError, 'corpus identity'):
            corpus.load(corpus.PAYABLE_PATH)

    def test_payability_does_not_leak_between_methods(self):
        for flags in ((True, False), (False, True), (True, True)):
            req = request([function(name, 'x', ('x',), payable=flag) for name, flag in zip(('f', 'g'), flags)])
            self.assertEqual([f['payable'] for f in checker.model(req)['functions']], list(flags))
            # The legacy single-function route has not expanded its grammar.
            with self.assertRaises(ValueError):
                checker.functions.model(request([function('f', 'x', ('x',), payable=True)]))

    def test_expression_and_source_unit_boundaries(self):
        body = function('f', 'x', ('x',), payable=True)
        for changed in (body.replace('payable', 'view'), body.replace('payable', ''),
                body.replace('return x;', 'return msg.value;'), body.replace('return x;', 'return f(x);'),
                body.replace('payable', 'payable pure'), body.replace('uint256 x', 'address x')):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                checker.model(request([changed]))
        content, _ = corpus.load(corpus.PAYABLE_PATH)
        for suffix in ('contract Other { uint256 x; }', 'contract Other { receive() external payable {} }'):
            with self.assertRaises(ValueError):
                checker.model(source_request(content + suffix, corpus.CLASHING_TARGET))

    def test_payable_trace_quantifies_arbitrary_value(self):
        req = request([function('f', 'x', ('x',), payable=True)])
        proof, _ = checker.proof_source([(req, fake_response(req))], 8)
        text = proof.decode()
        self.assertIn('payable := true', text)
        self.assertNotIn('theorem trace_paid', text)
        self.assertNotIn('(value : input.value = 0#256)', text)
        self.assertIn('exact trace_returned input sized selected full', text)
        self.assertIn('SolidityContract.Preserves sources creation code', text)


if __name__ == '__main__':
    unittest.main()
