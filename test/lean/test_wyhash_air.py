#!/usr/bin/env python3
"""Keep captured Wyhash rejection evidence separate from proof acceptance.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import check_wyhash_air as gate
from test_zig_air_memory_generate import memory_fixture
from test_zig_air_byte_generate import fixture as byte_fixture


class WyhashAirTests(unittest.TestCase):
    def test_decoded_fixture_is_not_preservation(self):
        result = gate.inspect_body(byte_fixture())
        self.assertEqual(result["decoder"], {"status": "decoded", "preservationVerified": False})

    def test_rejection_keeps_body_and_bounded_omission_locations(self):
        record = memory_fixture()
        record["sourceOperationTags"].append("slice_length")
        record["signature"]["returnType"] = {"kind": "unsupported", "zigTypeTag": "struct"}
        for inst in record["instructions"]:
            inst["unsupportedPayload"] = True
            inst["type"] = {"kind": "unsupported", "zigTypeTag": "struct"}
        record["instructions"].append({"index": 4, "tag": "dead", "payloadVisited": False,
                                       "unsupportedPayload": True})
        before = copy.deepcopy(record)
        result = gate.inspect_body(record)
        self.assertEqual(record, before)
        self.assertEqual(result["decoder"]["status"], "rejected")
        self.assertIn("length-based slice", result["decoder"]["reason"])
        self.assertTrue(result["lengthBasedSliceObserved"])
        self.assertEqual(result["unvisitedInstructionCount"], 1)
        self.assertNotIn("dead", result["unsupportedPayloads"])
        self.assertEqual(result["unsupportedValues"]["struct"], {
            "count": 5, "locations": ["/signature/returnType", "/instructions/0/type"], "omittedLocations": 3})

    def fixture(self, directory, edit=None):
        records = {}
        for wrapper, method in gate.ENTRIES.items():
            target = memory_fixture()
            target.update(name="hash.wyhash.Wyhash." + method, sourceFile="hash/wyhash.zig", sourceSha256="b" * 64)
            target["sourceValidity"]["slices"] = []
            body = memory_fixture()
            body.update(name="wyhash_air." + wrapper, sourceFile="wyhash_air.zig")
            body["sourceValidity"]["slices"] = []
            body["instructions"][2] = {"index": 2, "tag": "call", "payloadVisited": True,
                "callee": {"kind": "function", "identity": {key: target[key] for key in ("name", "sourceFile", "sourceSha256")}},
                "arguments": [], "type": {"kind": "void"}}
            records[body["name"]] = body
            records[target["name"]] = target
        if edit:
            edit(records)
        (directory / "air").mkdir()
        report = {"schema": "oksolc.fresh-air-capture.v1", "status": "captured", "captureComplete": True,
                  "sourceSha256": "a" * 64, "objects": {"ordinary": "c" * 64, "captured": "c" * 64}, "functions": {}}
        for index, (name, record) in enumerate(records.items()):
            path = directory / "air" / (str(index) + ".json")
            gate.write_json(path, record)
            report["functions"][name] = {"file": path.name, "sha256": gate.digest(path),
                                          "requested": name.startswith("wyhash_air.")}
        path = directory / "report.json"
        gate.write_json(path, report)
        return path

    def test_all_three_public_bodies_are_required(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = self.fixture(Path(tmp))
            result = gate.inspect_capture(path, "b" * 64)
            self.assertEqual(set(result["entries"]), {"init", "update", "final"})
            report = json.loads(path.read_text())
            del report["functions"]["hash.wyhash.Wyhash.final"]
            gate.write_json(path, report)
            with self.assertRaisesRegex(ValueError, "pinned standard-library body"):
                gate.inspect_capture(path, "b" * 64)

    def test_hash_source_call_and_configuration_tampering_reject(self):
        edits = [
            lambda r: r["wyhash_air.finish"].update(sourceSha256="d" * 64),
            lambda r: r["hash.wyhash.Wyhash.final"].update(sourceSha256="d" * 64),
            lambda r: r["hash.wyhash.Wyhash.final"]["configuration"].update(optimize="Debug"),
            lambda r: r["wyhash_air.finish"]["instructions"][2]["callee"]["identity"].update(sourceFile="other.zig"),
            lambda r: r["wyhash_air.finish"]["instructions"][2].update(payloadVisited=False),
        ]
        for edit in edits:
            with self.subTest(edit=edit), tempfile.TemporaryDirectory() as tmp:
                path = self.fixture(Path(tmp), edit)
                with self.assertRaises(ValueError):
                    gate.inspect_capture(path, "b" * 64)
        with tempfile.TemporaryDirectory() as tmp:
            path = self.fixture(Path(tmp))
            raw = path.parent / "air/0.json"
            raw.write_text(raw.read_text() + " ")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                gate.inspect_capture(path, "b" * 64)

    def test_partial_capture_or_changed_native_object_reject(self):
        for edit in (lambda r: r.update(captureComplete=False), lambda r: r.update(status="failed"),
                     lambda r: r["objects"].update(ordinary="d" * 64)):
            with tempfile.TemporaryDirectory() as tmp:
                path = self.fixture(Path(tmp))
                report = json.loads(path.read_text())
                edit(report)
                gate.write_json(path, report)
                with self.assertRaisesRegex(ValueError, "did not complete"):
                    gate.inspect_capture(path, "b" * 64)


if __name__ == "__main__":
    unittest.main()
