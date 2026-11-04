"""Empty targets require complete source admission and a universal runtime proof.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import cases, request, source_request
from test_compiler_contracts import fake_response


class EmptyContractTests(unittest.TestCase):
    def test_complete_retained_target_and_sibling_identity(self):
        content, origin = corpus.load(corpus.BEACON_PATH, corpus.EMPTY_BEACON_TARGET)
        req = dict(cases())[corpus.EMPTY_BEACON_CASE]
        self.assertEqual(req['sources']['Function.sol']['content'], content)
        self.assertEqual(origin['sourceSha256'], corpus.BEACON_SHA256)
        self.assertEqual(origin['certificateContract'], corpus.EMPTY_BEACON_TARGET)
        self.assertEqual(origin['uncertifiedSiblingContracts'], [corpus.BEACON_TARGET])
        self.assertFalse(origin['wholeOriginalRequestVerified'])
        parsed = checker.model(req)
        self.assertEqual(parsed['functions'], [])
        self.assertEqual(parsed['sourceUnitContracts'], [corpus.EMPTY_BEACON_TARGET, corpus.BEACON_TARGET])
        record = checker.case_metadata(req, fake_response(req))
        self.assertEqual(record['corpusSource'], origin)
        self.assertEqual(record['certificateKind'], 'emptyContract')
        self.assertEqual(record['callInputScope'], 'allFiniteCalldata')
        with self.assertRaises(ValueError): corpus.load(corpus.BEACON_PATH, 'Missing')

    def test_empty_is_not_absent_or_an_omitted_handler(self):
        for declaration in ('fallback() external {}', 'receive() external payable {}',
                'uint256 state;', 'constructor() {}', 'event E();'):
            with self.subTest(declaration=declaration), self.assertRaises(ValueError): checker.model(request([declaration]))
        for text, target in (('contract E {} contract X { fallback() external {} }', 'E'),
                             ('contract E {}', 'Missing'), ('contract E is X {}', 'E')):
            req = source_request('pragma solidity *; ' + text, target)
            with self.subTest(text=text), self.assertRaises(ValueError): checker.model(req)
        with self.assertRaises(ValueError): checker.functions.model(request([]))

    def test_exact_empty_method_inventory(self):
        req = request([])
        res = fake_response(req)
        self.assertEqual(checker.artifact(req, res)[2], [])
        for methods in ({'invented()': '12345678'}, None, []):
            changed = copy.deepcopy(res)
            changed['contracts']['Function.sol']['C']['evm']['methodIdentifiers'] = methods
            with self.subTest(methods=methods), self.assertRaises(ValueError): checker.artifact(req, changed)

    def test_certificate_has_unconditional_runtime_and_creation_obligations(self):
        req = request([])
        proof, claims = checker.proof_source([(req, fake_response(req))], 8)
        text = proof.decode()
        self.assertEqual(len(claims), 1)
        self.assertIn('theorem trace (input : Input) :', text)
        self.assertIn('.finished cost (.reverted [])', text)
        self.assertIn('theorem creation_trace (input : Input)', text)
        self.assertIn('SolidityEmptyContract.Preserves creation code', text)
        self.assertNotIn('Function0.', text)
        self.assertNotIn('member', text)


if __name__ == '__main__':
    unittest.main()
