#!/usr/bin/env python3
"""Metadata policies preserve complete source, runtime and deployment binding.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
import subprocess
import unittest

import check_compiler_contracts as checker
import compiler_contract_corpus as corpus
from compiler_contract_cases import cases
from test_compiler_contracts import fake_response


class MetadataContractTests(unittest.TestCase):
    def request(self):
        return dict(cases())[corpus.CLASHING_CASE + "-metadata"]

    def test_policy_and_complete_source_match_retained_request(self):
        packed = (corpus.ROOT / corpus.CLASHING_ARCHIVE).read_bytes()
        self.assertEqual(corpus.sha(packed), corpus.CLASHING_ARCHIVE_SHA256)
        raw = subprocess.run(["zstd", "-qdc"], input=packed, capture_output=True, check=True, timeout=30).stdout
        self.assertEqual(corpus.sha(raw), corpus.CLASHING_REQUEST_SHA256)
        original = json.loads(raw)
        req = self.request()
        self.assertEqual(req["settings"]["metadata"], original["settings"]["metadata"])
        self.assertEqual(req["sources"]["Function.sol"], original["sources"][corpus.CLASHING_PATH])
        self.assertEqual(req["settings"]["evmVersion"], "cancun")
        self.assertEqual(len(checker.model(req)["functions"]), 2)
        metadata = checker.case_metadata(req, fake_response(req))
        self.assertEqual(metadata["metadataSettings"], checker.IPFS_METADATA)
        self.assertFalse(metadata["corpusSource"]["originalSettingsPreserved"])
        self.assertFalse(metadata["corpusSource"]["wholeOriginalRequestVerified"])

    def test_settings_fail_closed_for_selected_and_default_targets(self):
        for name in (corpus.CLASHING_CASE + "-metadata", "checked-metadata"):
            req = dict(cases())[name]
            for key, value in (("appendCBOR", False), ("appendCBOR", 1), ("useLiteralContent", 1),
                               ("useLiteralContent", False), ("bytecodeHash", "bzzr1"), ("extra", True)):
                changed = copy.deepcopy(req); changed["settings"]["metadata"][key] = value
                with self.subTest(name=name, key=key, value=value), self.assertRaises(ValueError):
                    checker.model(changed)
            for key, value in (("evmVersion", "osaka"), ("viaIR", False),
                               ("optimizer", {"enabled": False, "runs": 200})):
                changed = copy.deepcopy(req); changed["settings"][key] = value
                with self.subTest(key=key), self.assertRaises(ValueError): checker.model(changed)
            with self.assertRaises(ValueError): checker.functions.model(req)

    def test_full_bytes_feed_the_same_deployment_claim_and_controls(self):
        req = self.request(); res = fake_response(req)
        evm = res["contracts"]["Function.sol"][corpus.CLASHING_TARGET]["evm"]
        evm["deployedBytecode"]["object"] = "60006000fdfe0001"
        evm["bytecode"]["object"] = "00" + evm["deployedBytecode"]["object"]
        before = copy.deepcopy((req, res))
        metadata = checker.case_metadata(req, res)
        self.assertEqual(metadata["bytecodeBytes"], 8)
        self.assertEqual(metadata["creationBytecodeBytes"], 9)
        text, claims = checker.proof_source([(req, res)], 8)
        self.assertIn(b"padded creation 1 8 = code", text)
        self.assertIn(b"SolidityContract.Preserves sources creation code", text)
        self.assertEqual(len(claims), 1)
        controls = checker.metadata_controls([(req, res)])
        self.assertEqual([name for name, _ in controls], ["metadata_runtime_truncated",
            "metadata_runtime_changed", "metadata_wrong_boolean_source"])
        for _, [(changed_req, changed_res)] in controls:
            self.assertEqual(changed_res["contracts"]["Function.sol"][corpus.CLASHING_TARGET]["evm"]["bytecode"], evm["bytecode"])
            self.assertEqual(changed_req["settings"], req["settings"])
        self.assertEqual((req, res), before)


if __name__ == "__main__":
    unittest.main()
