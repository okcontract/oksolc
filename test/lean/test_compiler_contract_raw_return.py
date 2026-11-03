"""Closed raw-return source admission and complete artifact inventory.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest
from unittest.mock import patch

import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import cases, function, raw_return, request, source_request
from test_compiler_contracts import fake_response


class RawReturnTests(unittest.TestCase):
    def test_complete_corpus_keeps_raw_result_and_unnamed_slot(self):
        content, origin = corpus.load(corpus.RAW_RETURN_PATH)
        req = dict(cases())[corpus.RAW_RETURN_CASE]
        self.assertEqual(req['sources']['Function.sol']['content'], content)
        self.assertEqual(origin['sourceSha256'], corpus.RAW_RETURN_SHA256)
        self.assertEqual(origin['sourceBytes'], 305)
        self.assertFalse(origin['wholeOriginalRequestVerified'])
        self.assertFalse(origin['originalSettingsPreserved'])
        parsed = checker.model(req)['functions'][0]
        self.assertEqual(parsed['parameters'], [None])
        self.assertEqual(parsed['signature'], 'supportsInterface(bytes4)')
        self.assertEqual(parsed['returnType'], 'bool')
        self.assertEqual(parsed['bodyScope'], 'rawWordReturn')
        self.assertEqual(parsed['rawReturnWord'], str(2**256 - 1))
        self.assertEqual(parsed['nodes'], [])
        self.assertIsNone(parsed['root'])
        metadata = checker.case_metadata(req, fake_response(req))
        self.assertEqual(metadata['corpusSource'], origin)
        self.assertEqual(metadata['functions'][0]['rawReturnWord'], str(2**256 - 1))
        self.assertEqual(metadata['certificateKind'], 'mixedMethodContract')
        with patch.object(corpus, 'RAW_RETURN_SHA256', '0' * 64), self.assertRaises(ValueError):
            corpus.load(corpus.RAW_RETURN_PATH)

    def test_only_complete_literal_scratch_write_and_return(self):
        good = raw_return('f', 7, 'bytes4 id', result='bool')
        edits = (
            ('mstore(0, 7)', 'mstore(32, 7)'),
            ('return(0, 32)', 'return(1, 32)'),
            ('return(0, 32)', 'return(0, 31)'),
            ('mstore(0, 7)', 'mstore(0, id)'),
            ('mstore(0, 7)', 'mstore(0, add(3, 4))'),
            ('mstore(0, 7)', 'mstore8(0, 7)'),
            ('mstore(0, 7)', ''),
            ('return(0, 32)', 'revert(0, 32)'),
            ('return(0, 32)', 'return(0, 32) mstore(0, 8)'),
            ('assembly {', 'assembly { let x := 0'),
            ('assembly {', 'assembly { sstore(0, 1)'),
            ('assembly {', 'uint256 x = 1; assembly {'),
            ('mstore(0, 7)', 'mstore(0, ' + str(2**256) + ')'),
            ('returns(bool)', 'returns(bytes32)'),
        )
        for before, after in edits:
            with self.subTest(after=after), self.assertRaises(ValueError):
                checker.model(request([good.replace(before, after)]))
        # Selecting A must not hide unsupported instructions in sibling B.
        bad = 'pragma solidity *; contract A {} contract B { ' + good.replace('return(0, 32)', 'return(0, 33)') + ' }'
        with self.assertRaises(ValueError): checker.model(source_request(bad, 'A'))

    def test_exact_values_and_positional_abi(self):
        for value in (0, 1, 7, 2**256 - 1):
            for result in ('uint256', 'bool', 'address'):
                with self.subTest(value=value, result=result):
                    parsed = checker.model(request([raw_return('f', value, 'bytes4,bytes4,uint256 x', result=result)]))['functions'][0]
                    self.assertEqual(parsed['parameters'], [None, None, 'x'])
                    self.assertEqual(parsed['parameterTypes'], ['bytes4', 'bytes4', 'uint256'])
                    self.assertEqual(parsed['rawReturnWord'], str(value))
                    self.assertEqual(parsed['signature'], 'f(bytes4,bytes4,uint256)')
        for parameters in ('bytes4 x, uint256 x', ',bytes4', 'bytes4,', 'bytes8', 'bytes calldata',
                           ','.join(['bytes4'] * 9)):
            with self.subTest(parameters=parameters), self.assertRaises(ValueError):
                checker.model(request([raw_return('f', 7, parameters)]))
        with self.assertRaises(ValueError):
            checker.model(request(['function f(uint256) external pure returns(uint256) { return uint256(7); }']))
        with self.assertRaises(ValueError):
            checker.functions.model(request([raw_return('f', 7)]))

    def test_mixed_inventory_and_raw_proof_obligation(self):
        req = request([raw_return('f', 2**256 - 1, 'bytes4', result='bool'),
                       'function ignore(bytes4) external view {}', function('word', 'x', ('x',))])
        res = fake_response(req)
        changed = copy.deepcopy(res)
        del changed['contracts']['Function.sol']['C']['evm']['methodIdentifiers']['f(bytes4)']
        with self.assertRaises(ValueError): checker.artifact(req, changed)
        text, claims = checker.proof_source([(req, res)], 8)
        self.assertEqual(claims, [checker.MODULE + '.Case0.checked'])
        self.assertIn(b'SolidityRawReturn.bytes_eq', text)
        self.assertIn(b'SolidityMethodContract.Method.rawWord Function0.source Function0.returnedWord', text)
        self.assertIn(b'SolidityNoReturn.selected_returning source', text)
        self.assertNotIn(b'SolidityBoolLiteral.result source true', text)


if __name__ == '__main__':
    unittest.main()
