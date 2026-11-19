#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Complete-source selection and bounded address-result admission regressions.
"""
import copy
import unittest
from unittest.mock import patch

import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import address_function, cases, request, selected_constants, source_request
from test_compiler_contracts import fake_response


class AddressContractTests(unittest.TestCase):
    def test_complete_retained_unit_and_selected_artifact(self):
        content, origin = corpus.load(corpus.BEACON_PATH)
        req = dict(cases())[corpus.BEACON_CASE]
        self.assertEqual(req["sources"]["Function.sol"]["content"], content)
        self.assertEqual(corpus.sha(content.encode()), corpus.BEACON_SHA256)
        self.assertEqual(origin["sourceBytes"], 215)
        self.assertEqual(origin["certificateContract"], corpus.BEACON_TARGET)
        self.assertEqual(origin["uncertifiedSiblingContracts"], ["BadBeaconNoImpl"])
        self.assertTrue(origin["completeSourceUnit"])
        self.assertFalse(origin["wholeOriginalRequestVerified"])
        self.assertFalse(origin["originalSettingsPreserved"])
        parsed = checker.model(req)
        self.assertEqual(parsed["sourceUnitContracts"], ["BadBeaconNoImpl", corpus.BEACON_TARGET])
        self.assertEqual(parsed["functions"][0]["returnType"], "address")
        self.assertEqual(parsed["functions"][0]["nodes"], [{"literal": "1"}])
        metadata = checker.case_metadata(req, fake_response(req))
        self.assertEqual(metadata["corpusSource"], origin)
        self.assertEqual(metadata["uncertifiedSiblingContracts"], ["BadBeaconNoImpl"])
        with patch.object(corpus, "BEACON_SHA256", "0" * 64), self.assertRaisesRegex(ValueError, "complete source unit"):
            corpus.load(corpus.BEACON_PATH)

    def test_address_boundaries_and_word_scope(self):
        for value in (0, 1, 2**160 - 1):
            req = request([address_function("f", value)])
            parsed = checker.model(req)["functions"][0]
            self.assertEqual(parsed["nodes"], [{"literal": str(value)}])
            with self.assertRaises(ValueError):
                checker.functions.model(req)
        parsed = checker.model(request([address_function("f", "0x1")]))["functions"][0]
        self.assertEqual(parsed["nodes"], [{"literal": "1"}])
        for value in (2**160, -1, "01", "0x" + "1" * 40, "uint160(1)", "1 + 2", "x", "true"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                checker.model(request([address_function("f", value, ("x",))]))
        base = request([address_function("f", 1)])
        content = base["sources"]["Function.sol"]["content"]
        for old, new in (("returns(address)", "returns(address payable)"),
                ("address(1)", "uint256(1)"), ("address(1)", "address(1) + address(1)"),
                ("f()", "f(address x)")):
            with self.subTest(new=new), self.assertRaises(ValueError):
                checker.model(source_request(content.replace(old, new)))

    def test_explicit_target_binds_full_source_and_response(self):
        req = selected_constants()
        content = req["sources"]["Function.sol"]["content"]
        for target, value in (("A", "1"), ("B", "2")):
            selected = source_request(content, target)
            parsed = checker.model(selected)
            self.assertEqual(parsed["contract"], target)
            self.assertEqual(parsed["functions"][0]["nodes"], [{"literal": value}])
        for target in (None, "Missing", "*", ""):
            with self.subTest(target=target), self.assertRaises(ValueError):
                checker.model(source_request(content, target))
        res = fake_response(req)
        changed = copy.deepcopy(res)
        changed["contracts"]["Function.sol"]["B"] = changed["contracts"]["Function.sol"].pop("A")
        with self.assertRaises(ValueError):
            checker.artifact(req, changed)
        changed = copy.deepcopy(res)
        changed["contracts"]["Function.sol"]["B"] = changed["contracts"]["Function.sol"]["A"]
        with self.assertRaises(ValueError):
            checker.artifact(req, changed)

    def test_selection_never_skips_unsupported_declarations(self):
        good = "pragma solidity *; contract A { " + address_function("f", 1) + " }"
        bad_siblings = ("contract A {}", "contract B { uint256 state; }", "contract B is A {}",
            "contract B { constructor() {} }", "contract B { function g() external pure returns(bool) { return !false; } }",
            "contract B { function g() external pure returns(uint256) { return f(); } }",
            "pragma solidity *;", "import X;", "interface B {}", "contract B {")
        for sibling in bad_siblings:
            with self.subTest(sibling=sibling), self.assertRaises(ValueError):
                checker.model(source_request(good + sibling, "A"))
        self.assertEqual(checker.model(source_request(good + "contract B {}", "B"))["functions"], [])
        for content, target in ((good + "contract B {}", "Missing"),
                (good + "".join("contract C" + str(i) + " {}" for i in range(8)), "A")):
            with self.assertRaises(ValueError):
                checker.model(source_request(content, target))
        parsed = checker.model(source_request("pragma solidity *; contract E {} contract A { " + address_function("f", 1) + " }", "A"))
        self.assertEqual(parsed["sourceUnitContracts"], ["E", "A"])

    def test_selected_settings_remain_fixed(self):
        req = selected_constants()
        for selection in ({"*": {"A": checker.SETTINGS["outputSelection"]["*"]["*"]}},
                {"Function.sol": {"A": [], "B": []}}, {"Function.sol": {"A": ["abi"]}}):
            changed = copy.deepcopy(req)
            changed["settings"]["outputSelection"] = selection
            with self.subTest(selection=selection), self.assertRaises(ValueError):
                checker.model(changed)
        changed = copy.deepcopy(req)
        changed["settings"]["evmVersion"] = "osaka"
        with self.assertRaises(ValueError):
            checker.model(changed)

    def test_certificate_consumes_range_and_address_result(self):
        req = request([address_function("f", 2**160 - 1)])
        code, _ = checker.proof_source([(req, fake_response(req))], 8)
        self.assertIn(b"SolidityAddressLiteral.literal", code)
        self.assertIn(b"rw [SolidityAddressLiteral.result source", code)
        self.assertIn(b"SolidityContract.Preserves sources creation code", code)

    def test_corruption_keeps_creation_and_runtime_together(self):
        req = request([address_function("f", 1)])
        res = fake_response(req)
        _, changed = checker.functions.replace_runtime((req, res), "C", b"\x01")
        original = res["contracts"]["Function.sol"]["C"]["evm"]
        corrupted = changed["contracts"]["Function.sol"]["C"]["evm"]
        self.assertEqual(original["bytecode"]["object"], "00")
        self.assertEqual(corrupted["bytecode"]["object"], corrupted["deployedBytecode"]["object"])
        self.assertEqual(corrupted["bytecode"]["object"], "01")
        with self.assertRaises(ValueError):
            checker.functions.replace_runtime((req, res), "C", b"\x01\x00")


if __name__ == "__main__":
    unittest.main()
