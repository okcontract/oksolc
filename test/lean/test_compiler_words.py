#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Source-profile, byte binding, closed proof encoding and corpus regressions.
"""
import copy
import json
import unittest

import check_compiler_words as checker
from compiler_word_cases import cases, request
from common import BuildError


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def pair():
    req = request([{"input": "x"}])
    res = {"schema": "oksolc.compiler-word-response.v1",
           "requestSha256": checker.artifacts.gate.digest(encoded(req)), "bytecode": "80"}
    return req, res


class WordArtifactTests(unittest.TestCase):
    def test_exact_binding(self):
        req, res = pair()
        self.assertEqual(checker.request(encoded(req)), req)
        self.assertEqual(checker.response(encoded(res), encoded(req)), res)
        with self.assertRaises(ValueError):
            checker.response(encoded(res), encoded(req) + b" ")
        for name, value in (("schema", "wrong"), ("extra", True), ("requestSha256", "0")):
            changed = {**res, name: value}
            with self.assertRaises(ValueError):
                checker.response(encoded(changed), encoded(req))
        with self.assertRaises(BuildError):
            checker.request(encoded(req).replace(b'"root":0', b'"root":0,"root":0'))

    def test_source_rejections_include_unused_nodes(self):
        req, _ = pair()
        for name, value in (("schema", "other"), ("arithmetic", "checked"), ("evmVersion", "osaka"),
                            ("parameters", ["x", "x"]), ("parameters", []),
                            ("parameters", ["x", "bad\"name"]), ("parameters", [False]),
                            ("parameters", [str(i) for i in range(17)]), ("extra", 0)):
            with self.subTest(name=name, value=value), self.assertRaises(ValueError):
                checker.admit_request({**req, name: value})
        for op in ("div", "mod", "lt", "gt", "eq"):
            changed = copy.deepcopy(req)
            changed["nodes"].append({"binary": {"op": op, "left": 0, "right": 0}})
            with self.subTest(op=op), self.assertRaises(ValueError):
                checker.admit_request(changed)
        changed = copy.deepcopy(req)
        changed["nodes"].append({"unary": {"op": "iszero", "arg": 0}})
        with self.assertRaises(ValueError):
            checker.admit_request(changed)

    def test_canonical_and_bounded_bytes(self):
        for value in ("", "0", "0X00", "0x80", "FF", "gg", "80\n", "80" * 4097, [128], False):
            with self.subTest(value=str(value)[:25]), self.assertRaises(ValueError):
                checker.bytecode(value)
        self.assertEqual(checker.bytecode("00ff"), b"\x00\xff")
        # Unsupported/truncated opcodes remain proof input, never host acceptance.
        self.assertEqual(checker.bytecode("60"), b"\x60")

    def test_closed_encoder_and_source_shift_order(self):
        req, res = pair()
        req["nodes"] = [{"input": "x"}, {"literal": "7"},
                        {"binary": {"op": "shl", "left": 0, "right": 1}}]
        req["root"] = 2
        code, claims = checker.proof_source([(req, res)], 8)
        self.assertIn(b'(.binary .shl (.input "x") (.literal 7))', code)
        self.assertIn(b'SolidityWord.metered_bytecode_sound 8', code)
        self.assertEqual(claims, [checker.MODULE + ".checked_0"])
        for bad in ([], [(request([{"input": 'x"; axiom bad : False'}]), res)]):
            with self.assertRaises(ValueError):
                checker.proof_source(bad, 8)
        with self.assertRaises(ValueError):
            checker.proof_source([(req, res)], True)

    def test_complete_corpus_and_native_corruption_controls(self):
        records = cases()
        self.assertEqual(len(records), 118)
        self.assertEqual(len({name for name, _ in records}), len(records))
        self.assertTrue({f"push_{i}" for i in range(1, 33)} <= {n for n, _ in records})
        pairs = []
        for _, req in records:
            checker.admit_request(req)
            res = {"schema": "oksolc.compiler-word-response.v1",
                   "requestSha256": checker.artifacts.gate.digest(encoded(req)), "bytecode": "80"}
            pairs.append((req, res))
        controls = checker.negative_pairs(pairs)
        self.assertEqual([n for n, _ in controls], ["wrong_value", "truncated_push", "lost_input_frame"])
        for _, negative in controls:
            req, res = negative[0]
            checker.response(encoded(res), encoded(req))
        self.assertTrue(all(res["bytecode"] == "80" for _, res in pairs))


if __name__ == "__main__":
    unittest.main()
