#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Closed contract admission and complete source/artifact coverage regressions.
"""
import copy
import json
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import cases, function, request


def fake_response(req):
    parsed = checker.model(req)
    return {"contracts": {"Function.sol": {parsed["contract"]: {"evm": {
        "bytecode": {"object": "00"}, "deployedBytecode": {"object": "00"},
        "methodIdentifiers": {f["signature"]: f"{i:08x}"
            for i, f in enumerate(parsed["functions"])}}}}}}


class ContractTests(unittest.TestCase):
    def test_retained_source_and_explicit_corpus_scope(self):
        content, origin = corpus.load()
        req = dict(cases())[corpus.CASE]
        self.assertEqual(req["sources"]["Function.sol"]["content"], content)
        self.assertEqual(corpus.sha(content.encode()), corpus.SOURCE_SHA256)
        self.assertEqual(origin["originalSourcePath"], corpus.SOURCE_PATH)
        self.assertEqual(origin["originalFork"], "osaka")
        self.assertEqual((origin["sourceBytes"], origin["originalSourceCount"], origin["omittedSourceCount"]), (186, 338, 337))
        self.assertTrue(origin["sourceContentUnchanged"])
        self.assertFalse(origin["wholeOriginalRequestVerified"])
        self.assertFalse(origin["originalSettingsPreserved"])
        self.assertEqual(checker.case_metadata(req, fake_response(req))["corpusSource"], origin)
        parsed = checker.model(req)["functions"][0]
        self.assertEqual(parsed["signature"], "decimals()")
        self.assertEqual(parsed["visibility"], "public")
        self.assertEqual(parsed["nodes"], [{"literal": str(2**256 - 1)}])
        self.assertIsNone(corpus.matching_origin(content + "\n"))

    def test_corpus_identity_failures(self):
        with patch.object(corpus, "ARCHIVE_SHA256", "0" * 64), patch.object(corpus.subprocess, "run") as run:
            with self.assertRaisesRegex(ValueError, "corpus identity"):
                corpus.load()
            run.assert_not_called()
        with patch.object(corpus.subprocess, "run", return_value=SimpleNamespace(stdout=b"{}")):
            with self.assertRaisesRegex(ValueError, "request identity"):
                corpus.load()
        with patch.object(corpus, "SOURCE_SHA256", "0" * 64):
            with self.assertRaisesRegex(ValueError, "complete source unit"):
                corpus.load()

    def test_complete_function_scope(self):
        for _, req in cases():
            parsed = checker.model(req)
            self.assertTrue(0 <= len(parsed["functions"]) <= 8)
            self.assertEqual(checker.request(json.dumps(req).encode()), req)
        parsed = checker.model(request([function("f", "x", ("x",)), function("g", "y", ("y",))]))
        self.assertEqual([f["parameters"] for f in parsed["functions"]], [["x"], ["y"]])
        self.assertEqual([f["nodes"] for f in parsed["functions"]], [[{"input": "x"}], [{"input": "y"}]])
        with self.assertRaises(ValueError):
            checker.model(request([function("f", "x", ("x",)), function("g", "x", ("y",))]))

    def test_fail_closed_contract_admission(self):
        for functions in ([function("f", "x"), function("f", "y")],
                [function("f" + str(i), "x") for i in range(9)],
                [function("f", "x"), "receive() external payable {}"],
                [function("f", "x"), "fallback() external {}"],
                [function("f", "x"), "uint256 state;"],
                [function("f", "x"), "constructor() {}"]):
            with self.subTest(functions=functions), self.assertRaises(ValueError):
                checker.model(request(functions))
        req = request([function("f", "x"), function("g", "y")])
        with self.assertRaises(ValueError):
            checker.functions.model(req)

    def test_exact_methods_and_selectors(self):
        req = request([function("f", "x"), function("g", "y")])
        res = fake_response(req)
        self.assertEqual(checker.artifact(req, res)[2], [0, 1])
        for methods in ({"f(uint256,uint256)": "00000000"},
                {"f(uint256,uint256)": "00000000", "g(uint256,uint256)": "00000000"},
                {"f(uint256,uint256)": "00000000", "g(uint256,uint256)": "123456789"},
                {"f(uint256,uint256)": "00000000", "g(uint256,uint256)": "00000001", "h()": "00000002"}):
            changed = copy.deepcopy(res)
            changed["contracts"]["Function.sol"]["C"]["evm"]["methodIdentifiers"] = methods
            with self.subTest(methods=methods), self.assertRaises(ValueError):
                checker.artifact(req, changed)

    def test_all_functions_in_final_claim(self):
        pairs = [(req, fake_response(req)) for _, req in cases()]
        batches, claims = checker.artifacts.proof_batches(checker, pairs, 8)
        self.assertEqual([len(names) for _, names in batches], [4, 4, 4, 4, 4, 4, 4, 4, 4, 3])
        self.assertEqual(claims, [checker.MODULE + f".Case{i}.checked" for i in range(len(pairs))])
        eight = next(pair for pair in pairs if len(checker.model(pair[0])["functions"]) == 8)
        proof, _ = checker.proof_source([eight], 8)
        text = proof.decode()
        self.assertIn("SolidityContract.Preserves sources creation code", text)
        for index in range(8):
            self.assertIn(f"Function{index}.trace input sized header chosen", text)
            self.assertIn(f"Function{index}.inhabited", text)
            self.assertIn(f"Function{index}.selector", text)
        self.assertEqual(text.count("theorem trace_unknown"), 1)
        self.assertEqual(text.count("theorem trace_short"), 1)
        for offset in (-1, True, 128):
            with self.assertRaises(ValueError):
                checker.proof_source(pairs[:1], 8, case_offset=offset)


if __name__ == "__main__":
    unittest.main()
