#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Complete Sablier source identity and fail-closed fixed-byte literal admission.
"""
import copy
import unittest
from unittest.mock import patch

import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import cases, literal_function, request, source_request
from test_compiler_contracts import fake_response


class Bytes32ContractTests(unittest.TestCase):
    def test_complete_retained_source(self):
        content, origin = corpus.load(corpus.BYTES32_PATH)
        req = dict(cases())[corpus.BYTES32_CASE]
        self.assertEqual(req['sources']['Function.sol']['content'], content)
        self.assertEqual(corpus.sha(content.encode()), corpus.BYTES32_SHA256)
        self.assertEqual((origin['sourceBytes'], origin['originalSourceCount'], origin['omittedSourceCount']),
                         (186, 281, 280))
        self.assertTrue(origin['completeSourceUnit'])
        self.assertTrue(origin['sourceContentUnchanged'])
        self.assertFalse(origin['wholeOriginalRequestVerified'])
        self.assertFalse(origin['originalSettingsPreserved'])
        self.assertEqual(origin['uncertifiedSiblingContracts'], [])
        self.assertIsNone(origin['upstreamCommit'])
        self.assertIsNone(origin['retainedCorpusTransforms'])
        self.assertEqual(checker.case_metadata(req, fake_response(req))['corpusSource'], origin)
        f = checker.model(req)['functions'][0]
        self.assertEqual((f['signature'], f['returnType'], f['literalBytes']),
                         ('symbol()', 'bytes32', list(b'ERC20')))
        for field in ('BYTES32_ARCHIVE_SHA256', 'BYTES32_REQUEST_SHA256', 'BYTES32_SHA256'):
            with self.subTest(field=field), patch.object(corpus, field, '0' * 64), self.assertRaises(ValueError):
                corpus.load(corpus.BYTES32_PATH)

    def test_encoding_boundaries_and_modes(self):
        for text in ('', '!', '0123456789ABCDEFGHIJKLMNOPQRSTUV', 'a /* b */ // c', "a'b"):
            for unchecked in (False, True):
                body = literal_function('f', 'bytes32', 'bytes32("' + text + '")', ('ignored',))
                if unchecked:
                    body = body.replace('{ return ', '{ unchecked { return ').replace('; }', '; } }')
                req = request([body]); f = checker.model(req)['functions'][0]
                self.assertEqual(f['literalBytes'], list(text.encode()))
                self.assertEqual(int(f['nodes'][0]['literal']).to_bytes(32, 'big'), text.encode().ljust(32, b'\0'))
                self.assertEqual(f['checked'], not unchecked)
                proof, claims = checker.proof_source([(req, fake_response(req))], 8)
                self.assertIn(b'theorem literal_encoding : wordBytes literalWord = literalBytes ++', proof)
                self.assertIn(b'List.replicate (32 - literalBytes.length) 0 := by decide +kernel', proof)
                self.assertIn(b'rw [SolidityBytes32Literal.result source literalBytes', proof)
                self.assertIn(b'SolidityContract.Preserves sources creation code', proof)
                self.assertEqual(len(claims), 1)
                with self.assertRaises(ValueError): checker.functions.model(req)

    def test_unsupported_strings_and_types_reject(self):
        expressions = ['bytes32("' + 'x' * 33 + '")', 'bytes32("a\\n")', 'bytes32("a\\x00")',
            'bytes32("a\\\"b")', 'bytes32("a\nb")', 'bytes32("a\tb")', 'bytes32("a\x00b")',
            'bytes32("é")', 'bytes32(unicode"abc")', 'bytes32(hex"abcd")', 'bytes32("a" "b")',
            "bytes32('abc')", 'bytes32(1)', 'bytes32(x)', 'bytes32("a") | bytes32("b")', '"a"']
        for expression in expressions:
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                checker.model(request([literal_function('f', 'bytes32', expression, ('x',))]))
        for kind in ('bytes', 'bytes1', 'bytes31', 'string', 'uint256', 'address', 'bool'):
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                checker.model(request([literal_function('f', kind, 'bytes32("a")')]))
        for body in ('function f() external pure returns(bytes32) { assembly { mstore(0, 1) return(0, 32) } }',
                'function f(bytes32 x) external pure returns(bytes32) { return bytes32("a"); }'):
            with self.assertRaises(ValueError): checker.model(request([body]))

    def test_unsupported_sibling_cannot_be_skipped(self):
        content, _ = corpus.load(corpus.BYTES32_PATH)
        content += 'contract Other { function f() external pure returns(string memory) { return "a"; } }'
        with self.assertRaises(ValueError): checker.model(source_request(content, corpus.BYTES32_TARGET))

    def test_invalid_descriptors_reject(self):
        f = checker.model(dict(cases())[corpus.BYTES32_CASE])['functions'][0]
        for data in ([65] * 33, [True], [-1], [256], [0], [34], [92], [127], 'ERC20'):
            changed = copy.deepcopy(f); changed['literalBytes'] = data
            with self.subTest(data=data), self.assertRaises(ValueError): checker.functions.function_facts(changed, 0)
        # A different in-range proposed word reaches the kernel equality check.
        changed = copy.deepcopy(f); changed['nodes'][0]['literal'] = '0'
        lines, _ = checker.functions.function_facts(changed, 0)
        self.assertIn('def literalWord : BitVec 256 := 0', lines)
        self.assertIn('    List.replicate (32 - literalBytes.length) 0 := by decide +kernel', lines)


if __name__ == '__main__':
    unittest.main()
