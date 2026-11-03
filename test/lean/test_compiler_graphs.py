#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission, exact-binding and closed-encoding regressions for graph artifacts.
"""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import check_compiler_graphs as checker
from common import BuildError


def encode(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def fixture():
    return {"schema": "oksolc.compiler-graph-request.v1",
        "nodes": [{"input": "x"}, {"literal": "0"}, {"binary": {"op": "add", "left": 0, "right": 1}}], "root": 2}


def response(req):
    return {"schema": "oksolc.compiler-graph-response.v2", "requestSha256": checker.gate.digest(encode(req)),
        "nodes": [{"input": "x"}, {"literal": "0"}], "root": 0, "resultIds": [0, 1, 0],
        "cache": [{"key": {"input": "x"}, "id": 0}, {"key": {"literal": "0"}, "id": 1},
                  {"key": {"binary": {"op": "add", "left": 0, "right": 1}}, "id": 0}]}


class GraphArtifactTests(unittest.TestCase):
    def test_binding_and_encoding(self):
        req = fixture()
        raw = encode(req)
        res = response(req)
        self.assertEqual(checker.request(raw), req)
        self.assertEqual(checker.response(encode(res), raw), res)
        code, claims = checker.proof_source([(req, res)], 8)
        self.assertIn(b'Inventory.certify 8 before_0 after_0 ids_0 cache_0 2 0 (by decide) (by decide) locals', code)
        self.assertIn(b'Inventory.Preserves before_0 after_0 ids_0 cache_0 locals', code)
        self.assertEqual(claims, ["Compiler.Validation.Artifact.checked_0"])
        with self.assertRaises(ValueError):
            checker.response(encode(res), raw + b" ")
        with self.assertRaises(ValueError):
            checker.proof_source([], 8)

    def test_complete_inventory_admission(self):
        req = fixture()
        good = response(req)
        for key, value in (("resultIds", [0, 1]), ("resultIds", [0, 2, 0]),
                ("resultIds", [0, True, 0]), ("resultIds", [0, 1, 1]),
                ("cache", good["cache"] * 2), ("cache", good["cache"] * 1025),
                ("cache", [{"key": {"unary": {"op": "iszero", "arg": 2}}, "id": 0}]),
                ("cache", [{"key": {"literal": "0"}, "id": 2}]),
                ("cache", [{"key": {"input": "x"}, "id": 0, "extra": True}]),
                ("schema", "oksolc.compiler-graph-response.v1")):
            bad = copy.deepcopy(good)
            bad[key] = value
            with self.subTest(key=key, value=value[:2] if isinstance(value, list) else value), self.assertRaises(ValueError):
                checker.response(encode(bad), encode(req))
        # These changes remain syntactically admitted. Only the Lean checker
        # can reject their incorrect word semantics.
        bad = copy.deepcopy(good)
        bad["resultIds"][1] = 0
        checker.response(encode(bad), encode(req))
        bad = copy.deepcopy(good)
        bad["cache"][2]["id"] = 1
        checker.response(encode(bad), encode(req))

    def test_invalid_nodes_roots_and_resources(self):
        cases = [([], 0), ([{"input": "x"}], 1), ([{"input": "x"}], True),
            ([{"unary": {"op": "bitnot", "arg": 0}}], 0),
            ([{"input": "x"}, {"unary": {"op": "bitnot", "arg": 1}}], 0),
            ([{"input": "x"}, {"binary": {"op": "add", "left": -1, "right": 0}}], 1),
            ([{"input": "x"}, {"binary": {"op": "add", "left": True, "right": 0}}], 1),
            ([{"input": "x"}, {"unary": {"op": "sload", "arg": 0}}], 1),
            ([{"input": "x"}, {"binary": {"op": "sdiv", "left": 0, "right": 0}}], 1),
            ([{"literal": "01"}], 0), ([{"literal": "+1"}], 0), ([{"literal": str(2**256)}], 0),
            ([{"literal": 0}], 0), ([{"literal": "0", "input": "x"}], 0),
            ([{"input": "x\"\naxiom bad : False"}], 0), ([{"unknown": "x"}], 0),
            ([{"input": "x"}] * 257, 0)]
        expanding = [{"input": "x"}]
        for i in range(13):
            expanding.append({"binary": {"op": "add", "left": i, "right": i}})
        cases.append((expanding, 0))
        for nodes, root in cases:
            with self.subTest(nodes=nodes[:2], root=root):
                with self.assertRaises(ValueError):
                    checker.graph(nodes, root)

    def test_inventory_controls_preserve_admission(self):
        from compiler_graph_cases import cases
        fixtures = dict(cases())
        alias = fixtures["inventory_alias"]
        unused = fixtures["inventory_unused"]
        alias_response = response(alias)
        unused_response = {"schema": "oksolc.compiler-graph-response.v2",
            "requestSha256": checker.gate.digest(encode(unused)), "nodes": copy.deepcopy(unused["nodes"]),
            "root": 0, "resultIds": [0, 1],
            "cache": [{"key": {"input": "x"}, "id": 0}, {"key": {"input": "y"}, "id": 1}]}
        recursive = fixtures["associate_add_fold"]
        nodes = copy.deepcopy(recursive["nodes"][:4]) + [{"literal": "8"},
            {"binary": {"op": "add", "left": 0, "right": 4}}]
        recursive_response = {"schema": "oksolc.compiler-graph-response.v2",
            "requestSha256": checker.gate.digest(encode(recursive)), "nodes": nodes,
            "root": 5, "resultIds": [0, 1, 2, 3, 5],
            "cache": [{"key": copy.deepcopy(node), "id": i} for i, node in enumerate(nodes)] +
                     [{"key": copy.deepcopy(recursive["nodes"][4]), "id": 5}]}
        pairs = [(alias, alias_response), (unused, unused_response), (recursive, recursive_response)]
        original = copy.deepcopy(pairs)
        controls = checker.negative_pairs(pairs)
        self.assertEqual({name for name, _ in controls}, {"unused_result", "unused_representative",
            "cache_value", "cache_operand", "cache_operator", "unused_cache_poison",
            "associate_wrong_constant", "associate_wrong_cache_operator"})
        for name, [(req, res)] in controls:
            with self.subTest(name=name):
                checker.response(encode(res), encode(req))
                if not name.startswith("associate_"):
                    self.assertEqual(req["root"], 0)
                    self.assertEqual(res["root"], 0)
                    self.assertEqual(res["nodes"][0], {"input": "x"})
        self.assertEqual(pairs, original)

    def test_closed_schema_and_duplicate_keys(self):
        req = fixture()
        for key, value in (("schema", "other"), ("extra", True)):
            changed = copy.deepcopy(req)
            changed[key] = value
            with self.assertRaises(ValueError):
                checker.request(encode(changed))
        duplicate = encode(req).replace(b'"root":2', b'"root":2,"root":0')
        with self.assertRaises(BuildError):
            checker.request(duplicate)
        changed = copy.deepcopy(req)
        changed["nodes"][2]["binary"]["extra"] = 0
        with self.assertRaises(ValueError):
            checker.request(encode(changed))
        with self.assertRaises(UnicodeError):
            checker.request(b"\xff")

    def test_encoder_revalidates_closed_input(self):
        bad = fixture()
        bad["nodes"][0]["input"] = 'x"; axiom bad : False'
        with self.assertRaises(ValueError):
            checker.proof_source([(bad, bad)], 8)
        with self.assertRaises(ValueError):
            checker.proof_source([(fixture(), fixture())], 17)

    def test_snapshot_ignores_only_project_local_cache(self):
        with tempfile.TemporaryDirectory(dir="/private/tmp") as temporary:
            root = Path(temporary) / ".lake" / "evidence" / "lean"
            (root / ".lake").mkdir(parents=True)
            for name in ("Model.lean", ".lake/Generated.lean", "lean-toolchain", "lake-manifest.json"):
                (root / name).write_text("retained input\n")
            self.assertEqual(set(checker.package_inputs(root)),
                             {"Model.lean", "lean-toolchain", "lake-manifest.json"})


if __name__ == "__main__":
    unittest.main()
