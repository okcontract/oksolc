#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Complete retained contract and literal ABI admission boundaries.
"""
import copy
import unittest
from unittest.mock import patch
import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import cases, literal_function, request, source_request
from test_compiler_contracts import fake_response


class LiteralContractTests(unittest.TestCase):
    def test_complete_retained_contract(self):
        content, origin = corpus.load(corpus.CLASHING_PATH)
        req = dict(cases())[corpus.CLASHING_CASE]
        self.assertEqual(req['sources']['Function.sol']['content'], content)
        self.assertEqual(corpus.sha(content.encode()), corpus.CLASHING_SHA256)
        self.assertEqual((origin['sourceBytes'], origin['originalSourceCount']), (493, 270))
        self.assertEqual(origin['uncertifiedSiblingContracts'], [])
        self.assertTrue(origin['completeSourceUnit'])
        self.assertFalse(origin['wholeOriginalRequestVerified'])
        self.assertFalse(origin['originalSettingsPreserved'])
        self.assertIsNone(origin['upstreamCommit'])
        self.assertIsNone(origin['retainedCorpusTransforms'])
        parsed = checker.model(req)
        self.assertEqual(parsed['contract'], corpus.CLASHING_TARGET)
        self.assertEqual([(f['signature'], f['returnType'], f['nodes']) for f in parsed['functions']],
            [('admin()', 'address', [{'literal': '286331202'}]),
             ('delegatedFunction()', 'bool', [{'literal': '1'}])])
        self.assertEqual(checker.case_metadata(req, fake_response(req))['corpusSource'], origin)
        with patch.object(corpus, 'CLASHING_SHA256', '0' * 64), self.assertRaisesRegex(ValueError, 'complete source unit'):
            corpus.load(corpus.CLASHING_PATH)
        with patch.object(corpus, 'CLASHING_ARCHIVE_SHA256', '0' * 64), self.assertRaisesRegex(ValueError, 'corpus identity'):
            corpus.load(corpus.CLASHING_PATH)

    def test_boolean_values_and_arithmetic_modes(self):
        for value, number in (('false', '0'), ('true', '1')):
            for unchecked in (False, True):
                body = literal_function('f', 'bool', value, ('ignored',))
                if unchecked:
                    body = body.replace('{ return ' + value + '; }', '{ unchecked { return ' + value + '; } }')
                req = request([body]);f = checker.model(req)['functions'][0]
                self.assertEqual(f['nodes'], [{'literal': number}])
                self.assertEqual(f['checked'], not unchecked)
                proof, claims = checker.proof_source([(req, fake_response(req))], 8)
                self.assertIn(b'SolidityBoolLiteral.literal ' + value.encode(), proof)
                self.assertIn(b'rw [SolidityBoolLiteral.result source ' + value.encode(), proof)
                self.assertIn(b'SolidityContract.Preserves sources creation code', proof)
                self.assertEqual(len(claims), 1)
                with self.assertRaises(ValueError): checker.functions.model(req)

    def test_boolean_scope_fails_closed(self):
        for expression in ('0', '1', '2', 'bool(1)', '!false', 'true && false', 'true == true', 'x'):
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                checker.model(request([literal_function('f', 'bool', expression, ('x',))]))
        bad = literal_function('f', 'bool', 'true', ('x',)).replace('uint256 x', 'bool x')
        with self.assertRaises(ValueError): checker.model(request([bad]))
        f = checker.model(request([literal_function('f', 'bool', 'true')]))['functions'][0]
        for value in ('2', '-1', str(2**256)):
            changed = copy.deepcopy(f);changed['nodes'][0]['literal'] = value
            with self.assertRaises(ValueError): checker.functions.function_facts(changed, 0)

    def test_bare_address_exact_scope(self):
        for digits in ('0' * 40, '9' * 40, '0' * 32 + '11111142'):
            req = request([literal_function('f', 'address', '0x' + digits)])
            f = checker.model(req)['functions'][0]
            self.assertEqual(f['nodes'], [{'literal': str(int(digits, 16))}])
            with self.assertRaises(ValueError): checker.functions.model(req)
        for expression in ('0x1', '1', '0x' + '0' * 39, '0x' + '1' * 41,
                '0x' + 'a' * 40, '0x' + 'A' * 40, '0X' + '0' * 40,
                '0x' + '0' * 40 + ' + 1', '0x' + '0' * 39 + '_1'):
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                checker.model(request([literal_function('f', 'address', expression)]))

    def test_every_callable_and_sibling_remain_checked(self):
        content, _ = corpus.load(corpus.CLASHING_PATH)
        bad = content.replace('return true;', 'return !false;')
        with self.assertRaises(ValueError): checker.model(source_request(bad, corpus.CLASHING_TARGET))
        bad = content + 'contract Other { function g() external pure returns(bool) { return bool(1); } }'
        with self.assertRaises(ValueError): checker.model(source_request(bad, corpus.CLASHING_TARGET))
        req = source_request(content, corpus.CLASHING_TARGET);res = fake_response(req)
        del res['contracts']['Function.sol'][corpus.CLASHING_TARGET]['evm']['methodIdentifiers']['delegatedFunction()']
        with self.assertRaises(ValueError): checker.artifact(req, res)


if __name__ == '__main__':
    unittest.main()
