#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture-completion and provenance rejection controls; no semantic oracle.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean/zig_air"))
from capture import inspect_records, read_json, source_files, module_bindings, module_arguments


RECORD = {
    "schema": "oksolc.fresh-air.v3", "capturePoint": "after-sema-before-legalize",
    "name": "fixture.add", "sourceSha256": "a" * 64,
    "sourceValidityConditionsPreserved": False,
    "sourceValidity": {"schema": "oksolc.source-validity.v1", "coverage": "runtime-slice-results",
                       "complete": False, "slices": []},
    "sourceOperationTags": ["addwrap", "ret_node"],
    "configuration": {"optimize": "ReleaseFast", "useLlvm": True, "isTest": False},
    "body": [0], "instructions": [{"index": 0, "tag": "future_opcode", "unsupportedPayload": True}],
}


class CaptureTests(unittest.TestCase):
    def test_named_leaf_module_is_bound_without_source_rewriting(self):
        data = {Path("fixture.zig"): b'const p = @import("src/production.zig");',
                Path("src/production.zig"): b'const n = @import("number");',
                Path("src/number.zig"): b'const s = @import("std"); pub const Word = u64;'}
        modules = module_bindings(["number=src/number.zig"])
        with patch.object(Path, "read_bytes", lambda path: data[path]):
            extra = [Path("src/production.zig"), Path("src/number.zig")]
            self.assertEqual(source_files(Path("fixture.zig"), extra, modules),
                             {str(path): value for path, value in data.items()})
            with self.assertRaisesRegex(ValueError, "module missing"):
                source_files(Path("fixture.zig"), extra[:1], modules)
            with self.assertRaisesRegex(ValueError, "missing from explicit closure"):
                source_files(Path("fixture.zig"), extra)
            data[Path("src/number.zig")] = b'const n = @import("number");'
            with self.assertRaisesRegex(ValueError, "self-contained leaves"):
                source_files(Path("fixture.zig"), extra, modules)
            data[Path("src/number.zig")] = b'pub const Word = u64;'
            data[Path("src/production.zig")] = b'const n = @import("number.zig");'
            with self.assertRaisesRegex(ValueError, "both name and path"):
                source_files(Path("fixture.zig"), extra, modules)

    def test_module_identity_and_per_module_mode(self):
        for entries in (["std=src/x.zig"], ["root=src/x.zig"], ["x"], ["x=/tmp/x.zig"],
                        ["x=../x.zig"], ["x=x.json"], ["x=src/x.zig", "x=src/y.zig"],
                        ["x=src/x.zig", "y=src/x.zig"]):
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                module_bindings(entries)
        self.assertEqual(module_arguments(Path("fixture.zig"), {}, "ReleaseFast"),
                         ["-OReleaseFast", Path("fixture.zig")])
        arguments = module_arguments(Path("run/fixture.zig"), {"number": "src/number.zig"}, "ReleaseSafe")
        # -M resets settings: every module must receive the requested mode.
        for index, value in enumerate(arguments):
            if str(value).startswith('-M'):
                previous = arguments[:index]
                self.assertIn('-OReleaseSafe', previous[1 + max(
                    (i for i, arg in enumerate(previous) if str(arg).startswith('-M')), default=-1):])
        self.assertIn('-Mnumber=run/src/number.zig', arguments)
        self.assertEqual(arguments[2:4], ['--dep', 'number'])

    def test_explicit_production_source_closure(self):
        data = {Path("fixture.zig"): b'const p = @import("src/production.zig");',
                Path("src/production.zig"): b'const s = @import("std"); const t = @import("../types.zig");',
                Path("types.zig"): b'const Id = u32;'}
        with patch.object(Path, "read_bytes", lambda path: data[path]):
            files = source_files(Path("fixture.zig"), [Path("src/production.zig"), Path("types.zig")])
            self.assertEqual(files, {str(path): value for path, value in data.items()})
            with self.assertRaisesRegex(ValueError, "missing from explicit closure"):
                source_files(Path("fixture.zig"), [Path("src/production.zig")])

    def test_capture_source_paths_and_indirect_imports_reject(self):
        data = {Path("fixture.zig"): b'const p = @import(module_name);', Path("types.zig"): b'const Id = u32;'}
        with patch.object(Path, "read_bytes", lambda path: data[path]):
            for paths in ([Path("../types.zig")], [Path("/types.zig")], [Path("fixture.zig")],
                          [Path("types.json")], [Path("types.zig"), Path("types.zig")]):
                with self.subTest(paths=paths), self.assertRaisesRegex(ValueError, "invalid or duplicate"):
                    source_files(Path("fixture.zig"), paths)
            with self.assertRaisesRegex(ValueError, "nonstatic"):
                source_files(Path("fixture.zig"), [Path("types.zig")])

    def inspect(self, record, roots=None):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory / "root.json").write_text(json.dumps(record))
            return inspect_records(directory, roots or ["fixture.add"], "a" * 64, "ReleaseFast")

    def test_retains_explicit_unsupported_payloads(self):
        summary = self.inspect(RECORD)["fixture.add"]
        self.assertEqual(summary["unsupportedPayloadCount"], 1)
        self.assertEqual(summary["sourceOperationTags"], RECORD["sourceOperationTags"])
        self.assertTrue(summary["requested"])

    def test_missing_and_duplicate_roots(self):
        with self.assertRaisesRegex(ValueError, "missing requested"):
            self.inspect(RECORD, ["fixture.missing"])
        with self.assertRaisesRegex(ValueError, "unique"):
            self.inspect(RECORD, ["fixture.add", "fixture.add"])

    def test_corrupted_capture_metadata_rejects(self):
        mutations = [
            ("schema", "future"), ("capturePoint", "after-legalize"),
            ("sourceSha256", "b" * 64), ("sourceValidityConditionsPreserved", True),
            ("sourceValidity", None), ("sourceValidity", {}),
            ("sourceValidity", dict(RECORD["sourceValidity"], complete=True)),
            ("sourceValidity", dict(RECORD["sourceValidity"], complete=0)),
            ("sourceOperationTags", []), ("sourceOperationTags", ["ret", "ret"]),
            ("body", [1]), ("body", [True]),
            ("instructions", [{"index": 1, "tag": "ret"}]),
            ("configuration", {"optimize": "Debug", "useLlvm": True, "isTest": False}),
            ("configuration", {"optimize": "ReleaseFast", "useLlvm": False, "isTest": False}),
            ("configuration", {"optimize": "ReleaseFast", "useLlvm": True, "isTest": True}),
        ]
        for key, value in mutations:
            with self.subTest(field=key, value=value), self.assertRaises(ValueError):
                record = copy.deepcopy(RECORD)
                record[key] = value
                self.inspect(record)

    def test_truncated_duplicate_and_nonfinite_json_reject(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "record.json"
            for text in ('{"name":', '{"name":"a","name":"b"}', '{"n":NaN}'):
                with self.subTest(text=text), self.assertRaises(ValueError):
                    path.write_text(text)
                    read_json(path)

    def test_duplicate_functions_and_symlinks_reject(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory / "one.json").write_text(json.dumps(RECORD))
            (directory / "two.json").write_text(json.dumps(RECORD))
            with self.assertRaisesRegex(ValueError, "duplicate captured"):
                inspect_records(directory, ["fixture.add"], "a" * 64, "ReleaseFast")
            (directory / "two.json").unlink()
            (directory / "two.json").symlink_to("one.json")
            with self.assertRaisesRegex(ValueError, "unexpected capture entry"):
                inspect_records(directory, ["fixture.add"], "a" * 64, "ReleaseFast")


if __name__ == "__main__":
    unittest.main()
