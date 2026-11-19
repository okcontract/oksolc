#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Typed control-flow and unsupported-case checks for the AIR translation boundary.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean/zig_air"))
from generate import Decoder, captured_path, constant, generate, type_of
from build_toolchain import digest


U8 = {"kind": "int", "signedness": "unsigned", "bits": 8}
VOID = {"kind": "void"}
NEVER = {"kind": "noreturn"}


def ref(index):
    return {"kind": "instruction", "index": index}


def const(value, ty=U8):
    return {"kind": "constant", "type": ty, "value": value}


def inst(index, tag, ty, **payload):
    return dict(index=index, tag=tag, type=ty, payloadVisited=True, **payload)


def fixture():
    return {
        "schema": "oksolc.fresh-air.v3", "capturePoint": "after-sema-before-legalize",
        "name": "fixture.choose", "sourceFile": "fixture.zig", "sourceSha256": "a" * 64,
        "configuration": {"optimize": "ReleaseFast", "useLlvm": True, "isTest": False},
        "signature": {"callingConvention": "auto", "genericInstance": False, "varArgs": False,
                      "noaliasBits": 0, "parameters": [U8], "returnType": U8},
        "sourceOperationTags": ["add", "ret_node"], "sourceValidityConditionsPreserved": False,
        "sourceValidity": {"schema": "oksolc.source-validity.v1", "coverage": "runtime-slice-results",
                           "complete": False, "slices": []},
        "bodyTraversal": "supported-structured-containers-only", "body": [0, 1, 7],
        "instructions": [
            inst(0, "arg", U8, zirParameterIndex=0),
            inst(1, "block", U8, body=[2, 3]),
            inst(2, "cmp_lt", {"kind": "bool"}, lhs=ref(0), rhs=const(128)),
            inst(3, "cond_br", NEVER, condition=ref(2), thenBody=[4, 5], elseBody=[6]),
            inst(4, "add", U8, lhs=ref(0), rhs=const(1)),
            inst(5, "br", NEVER, target=1, operand=ref(4)),
            inst(6, "br", NEVER, target=1, operand=ref(0)),
            inst(7, "ret", NEVER, operand=ref(1)),
        ],
    }


def decode(record):
    return Decoder(record).program(record)


class GenerationTests(unittest.TestCase):
    def rejects(self, edit, message):
        record = copy.deepcopy(fixture())
        edit(record)
        with self.assertRaisesRegex(ValueError, message):
            decode(record)

    def test_control_is_preserved_and_semantic_mutation_changes_output(self):
        record = fixture()
        original = decode(record)
        self.assertIn("(.block 1", original)
        self.assertIn("(.branch (.local 2)", original)
        self.assertIn("(.jump 1 (.local 4))", original)
        for tag in ("sub", "add_safe", "add_wrap"):
            changed = copy.deepcopy(record)
            changed["instructions"][4]["tag"] = tag
            self.assertNotEqual(decode(changed), original)

    def test_dominance_and_lexical_block_targets(self):
        for index, field, value in ((4, "lhs", ref(4)), (6, "operand", ref(4)),
                                    (7, "operand", ref(2))):
            self.rejects(lambda r: r["instructions"][index].update({field: value}), "dominated")
        for target in (0, 5, 7, True, -1, 8):
            self.rejects(lambda r: r["instructions"][5].update(target=target), "destination|integer")

    def test_control_ownership_and_termination(self):
        for body in ([0, 1, 7, 7], [0, 0, 1, 7], [0, 1], [], [True], [8]):
            self.rejects(lambda r: r.update(body=body), "ownership|terminator|body|integer")
        self.rejects(lambda r: r["instructions"][3].update(elseBody=[4, 5]), "ownership")

    def test_types_and_signature(self):
        edits = [
            lambda r: r["instructions"][4].update(type=VOID),
            lambda r: r["instructions"][5].update(operand={"kind": "unit"}),
            lambda r: r["instructions"][3].update(condition=ref(0)),
            lambda r: r["instructions"][7].update(operand={"kind": "unit"}),
            lambda r: r["signature"].update(parameters=[VOID]),
            lambda r: r["signature"].update(noaliasBits=True),
            lambda r: r["signature"].update(varArgs=True),
            lambda r: r["signature"].update(genericInstance=True),
            lambda r: r["instructions"][0].update(zirParameterIndex=1),
        ]
        for edit in edits:
            self.rejects(edit, "typed|result|signature|contract")

    def test_unknown_and_memory_operations_reject(self):
        for tag in ("future", "load", "store", "alloc", "call", "loop", "repeat", "unreach"):
            self.rejects(lambda r: r["instructions"][4].update(tag=tag), "unsupported AIR operation")
        self.rejects(lambda r: r["instructions"][4].update(extra=0), "fields")
        self.rejects(lambda r: r["instructions"][4].update(payloadVisited=False), "unvisited")
        self.rejects(lambda r: r.update(sourceValidityConditionsPreserved=True), "source-validity")
        self.rejects(lambda r: r["configuration"].update(optimize="Debug"), "configuration")
        self.rejects(lambda r: r["sourceValidity"]["slices"].append({"anchor": "dead-result"}), "source-validity obligations")
        self.rejects(lambda r: r["sourceValidity"].update(complete=True), "source-validity obligations")
        self.rejects(lambda r: r["sourceValidity"].update(complete=0), "source-validity obligations")
        self.rejects(lambda r: r.update(schema="oksolc.fresh-air.v1"), "schema")

    def test_unused_placeholder_has_no_payload_and_cannot_execute(self):
        record = fixture()
        record["instructions"].append({"index": 8, "tag": "block", "payloadVisited": False,
                                       "unsupportedPayload": True, "reason": "outside-decoded-body-closure"})
        self.assertEqual(decode(record), decode(fixture()))
        corrupt = copy.deepcopy(record)
        corrupt["instructions"][8]["body"] = [0]
        with self.assertRaisesRegex(ValueError, "fields"):
            decode(corrupt)
        record["body"].insert(1, 8)
        with self.assertRaisesRegex(ValueError, "unvisited"):
            decode(record)

    def test_dead_result_work_is_retained(self):
        record = fixture()
        record["instructions"][5]["operand"] = ref(0)
        self.assertIn("(.arithmetic .add .unchecked", decode(record))

    def test_constants_are_exact_and_bounded(self):
        for signed in (False, True):
            for width in (0, 1, 8, 256, 512):
                ty = {"kind": "int", "bits": width, "signedness": "signed" if signed else "unsigned"}
                lower, upper = (-(2 ** (width - 1)), 2 ** (width - 1)) if signed and width else (0, 2 ** width)
                for value in (lower, upper - 1):
                    self.assertIn(f"({value})", constant(const(value, ty))[1])
                for value in (lower - 1, upper, True, 0.0):
                    with self.assertRaises(ValueError):
                        constant(const(value, ty))
        for width in (-1, True, 513):
            with self.assertRaises(ValueError):
                type_of(dict(U8, bits=width))
        for value in (None, [], "u8"):
            with self.assertRaises(ValueError):
                type_of(value)

    def test_artifact_paths_cannot_escape_or_follow_links(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "air").mkdir()
            (root / "air/good.json").write_text("{}")
            (root / "air/link.json").symlink_to("good.json")
            for name in ("../good.json", "/good.json", "a/b.json", "link.json", "absent.json", "", True):
                with self.assertRaises(ValueError):
                    captured_path(root / "report.json", {"file": name})
            self.assertEqual(captured_path(root / "report.json", {"file": "good.json"}), root / "air/good.json")

    def test_generation_binds_record_and_source_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "air").mkdir()
            report = {"schema": "oksolc.fresh-air-numeric.v1", "status": "captured",
                      "numericSourceSha256": "a" * 64, "functions": {}}
            for name in ("numeric.u2s", "numeric.s2u"):
                record = fixture()
                record["name"] = name
                path = root / "air" / (name + ".json")
                path.write_text(json.dumps(record))
                report["functions"][name] = {"file": path.name, "sha256": digest(path), "requested": True}
            report_path = root / "report.json"
            report_path.write_text(json.dumps(report))
            manifest = generate(report_path, root / "valid.lean", root / "manifest.json")
            self.assertEqual(manifest["leanSha256"], digest(root / "valid.lean"))
            for mutation in ("hash", "source", "incomplete", "requested"):
                changed = copy.deepcopy(report)
                if mutation == "hash":
                    changed["functions"]["numeric.u2s"]["sha256"] = "b" * 64
                elif mutation == "source":
                    changed["numericSourceSha256"] = "b" * 64
                elif mutation == "incomplete":
                    changed["status"] = "failed"
                else:
                    changed["functions"]["numeric.u2s"]["requested"] = 1
                report_path.write_text(json.dumps(changed))
                with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                    generate(report_path, root / "invalid.lean", root / "invalid.json")
                self.assertFalse((root / "invalid.lean").exists())


if __name__ == "__main__":
    unittest.main()
