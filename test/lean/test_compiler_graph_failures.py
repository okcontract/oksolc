#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Failure-artifact binding, complete sweep inventory and closed encoding tests.
"""
import copy
import json
import tempfile
from pathlib import Path
import unittest

import check_compiler_graph_failures as checker
from compiler_graph_cases import cases


def encode(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def fixture():
    req = copy.deepcopy(dict(cases())["associate_add_fold"])
    req["schema"] = "oksolc.compiler-graph-failure-request.v1"
    reached = copy.deepcopy(req["nodes"][:4]) + [{"literal": "8"}]
    complete = reached + [{"binary": {"op": "add", "left": 0, "right": 4}}]
    attempts = [
        {"outcome": "outOfMemory", "nodes": [], "resultIds": [], "cache": []},
        {"outcome": "outOfMemory", "nodes": reached, "resultIds": [0, 1, 2, 3],
            "cache": [{"key": {"literal": "8"}, "id": 4}]},
        {"outcome": "complete", "nodes": complete, "resultIds": [0, 1, 2, 3, 5],
            "cache": [{"key": copy.deepcopy(req["nodes"][4]), "id": 5}]}]
    res = {"schema": "oksolc.compiler-graph-failure-response.v1", "requestSha256": checker.gate.digest(encode(req)),
        "resizePolicy": "always-fail", "observations": [
            {"failureAt": i if i < 2 else None, "successfulAllocations": i, "inducedFailure": i < 2,
                "attempt": attempt} for i, attempt in enumerate(attempts)]}
    return req, res


class GraphFailureTests(unittest.TestCase):
    def test_exact_binding_and_closed_theorem(self):
        req, res = fixture()
        self.assertEqual(checker.request(encode(req)), req)
        self.assertEqual(checker.response(encode(res), encode(req)), res)
        code, names = checker.proof_source([(req, res)], 8)
        self.assertIn(b"Failure.certify 8 before_0 attempts_0 (by decide) locals", code)
        self.assertIn(b"Failure.Preserves before_0 attempt locals", code)
        self.assertEqual(names, ["Compiler.Validation.Artifact.checked_0"])
        self.assertEqual(checker.case_metadata(req, res)["failedAttemptsWithMoreRepresentativesThanResults"], 1)
        with self.assertRaises(ValueError):
            checker.response(encode(res), encode(req) + b" ")
        for fuel in (-1, 17, True):
            with self.assertRaises(ValueError):
                checker.proof_source([(req, res)], fuel)

    def test_no_omitted_reordered_or_fabricated_cuts(self):
        req, res = fixture()
        for field, value in (("failureAt", None), ("failureAt", True), ("successfulAllocations", True),
                ("successfulAllocations", 0), ("inducedFailure", False), ("inducedFailure", 1), ("attempt", [])):
            bad = copy.deepcopy(res)
            bad["observations"][1][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                checker.admit_response(bad, req)
        for observations in ([], res["observations"][:-1], res["observations"][1:],
                list(reversed(res["observations"])), res["observations"] * 65):
            with self.assertRaises(ValueError):
                checker.admit_response({**res, "observations": observations}, req)
        for field, value in (("failureAt", 2), ("inducedFailure", True), ("successfulAllocations", 9)):
            bad = copy.deepcopy(res)
            bad["observations"][-1][field] = value
            with self.assertRaises(ValueError):
                checker.admit_response(bad, req)

    def test_reached_graph_is_checked_even_without_results(self):
        req, res = fixture()
        for field, value in (("nodes", [{"unary": {"op": "iszero", "arg": 0}}]),
                ("resultIds", [0]), ("cache", [{"key": {"literal": "8"}, "id": 0}]),
                ("outcome", "unsupported")):
            bad = copy.deepcopy(res)
            bad["observations"][0]["attempt"][field] = value
            with self.assertRaises(ValueError):
                checker.admit_response(bad, req)
        for field, value in (("nodes", [{"input": "x"}] * 257),
                ("resultIds", [True]), ("cache", res["observations"][1]["attempt"]["cache"] * 2)):
            bad = copy.deepcopy(res)
            bad["observations"][1]["attempt"][field] = value
            with self.assertRaises(ValueError):
                checker.admit_response(bad, req)

    def test_negative_controls_require_kernel_rejection(self):
        pair = fixture()
        original = copy.deepcopy(pair)
        controls = checker.negative_pairs([pair])
        self.assertEqual({name for name, _ in controls}, {"old_result", "partial_cache",
            "missing_prefix_result", "incomplete_baseline"})
        for _, [(req, res)] in controls:
            checker.response(encode(res), encode(req))
            checker.proof_source([(req, res)], 8)
        self.assertEqual(pair, original)

    def test_closed_requests_and_responses(self):
        req, res = fixture()
        for field, value in (("schema", "wrong"), ("extra", None), ("nodes", [])):
            with self.assertRaises(ValueError):
                checker.admit_request({**req, field: value})
        for field, value in (("schema", "wrong"), ("extra", None), ("resizePolicy", "native"), ("requestSha256", "bad")):
            with self.assertRaises(ValueError):
                checker.admit_response({**res, field: value}, req)

    def test_corpus_and_distinct_batches(self):
        with tempfile.TemporaryDirectory(dir="/private/tmp") as tmp:
            paths = checker.write_cases(Path(tmp) / "requests")
            self.assertEqual(len(paths), 7)
            for path in paths:
                checker.request(path.read_bytes())
        batches = checker.proof_batches([fixture(), fixture()], 8)
        self.assertEqual([names for _, names in batches], [["Compiler.Validation.Artifact.checked_0"],
            ["Compiler.Validation.Artifact.checked_1"]])


if __name__ == "__main__":
    unittest.main()
