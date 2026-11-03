#!/usr/bin/env python3
"""Reject changed initializer defaults, incomplete owner profiles and provenance.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import tempfile
import unittest
import copy

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_graph_init as admission
from extract_storage import Unsupported
import check_graph_init as gate


class GraphInitTests(unittest.TestCase):
    def test_generated_initializer_is_bound(self):
        self.assertEqual(admission.extract(admission.storage.SOURCE.read_bytes()), admission.OUTPUT.read_bytes())
        self.assertFalse(admission.check()["nativeGraphMutationCorrespondenceVerified"])

    def test_owner_and_initializer_mutations_reject(self):
        source = admission.storage.SOURCE.read_text()
        for before, after in (
            ("return .{ .allocator = allocator };", "return .{ .allocator = undefined };"),
            ("representatives: std.ArrayList(Expression) = .empty,", "representatives: std.ArrayList(Expression) = undefined,"),
            ("expressions: ExpressionMap = .empty,", "expressions: ExpressionMap = undefined,"),
            ("expressions: ExpressionMap = .empty,", "expressions: ExpressionMap = .empty, extra: usize = 0,"),
            ("    pub fn deinit(self: *ExpressionClasses) void {", "    extra: usize = 0,\n    pub fn deinit(self: *ExpressionClasses) void {"),
            ("return .{ .allocator = allocator };", "allocator.free(&.{}); return .{ .allocator = allocator };"),
            ("return self.representatives.items.len;", "return self.expressions.size;"),
            ("std.HashMapUnmanaged(ExpressionKey, Id, ExpressionKeyContext, 80)", "std.AutoHashMapUnmanaged(ExpressionKey, Id)"),
            ("\n};\n\nfn makeKey", "\n    extra: usize = 0,\n};\n\nfn makeKey"),
        ):
            with self.subTest(mutation=after), self.assertRaises(Unsupported):
                self.assertEqual(source.count(before), 1)
                admission.extract(source.replace(before, after).encode())

    def test_comment_decoy_does_not_admit_changed_init(self):
        source = admission.storage.SOURCE.read_bytes()
        changed = source.replace(b"return .{ .allocator = allocator };", b"return .{ .allocator = undefined };")
        with self.assertRaises(Unsupported):
            admission.extract(b"// return .{ .allocator = allocator };\n" + changed)

    def test_every_pinned_std_input_is_required(self):
        with tempfile.TemporaryDirectory() as directory:
            lib = Path(directory)
            (lib / "std").mkdir()
            for name in admission.STD:
                (lib / "std" / name).write_bytes(b"unreviewed container default")
            for name in admission.STD:
                saved = admission.STD.copy()
                try:
                    for other in saved:
                        if other != name:
                            admission.STD[other] = admission.hashlib.sha256(b"unreviewed container default").hexdigest()
                    with self.subTest(name=name), self.assertRaisesRegex(ValueError, name.replace(".", r"\.")):
                        admission.check_std(lib)
                finally:
                    admission.STD.clear()
                    admission.STD.update(saved)

    def profile(self):
        fields = {"allocator_pointer": 64, "allocator_vtable": 128, "representative_length": 0,
            "representative_capacity": 0, "map_metadata_null": True, "map_size": 0,
            "map_available": 0, "map_lock_empty": True, "representative_lock_empty": True}
        cases = [{"input": {**fields, "allocator_pointer": pointer}, "actual": {**fields, "allocator_pointer": pointer},
            "before": trace.copy(), "after": trace.copy(), "size": 0, "cache_capacity": 0, "key_iterator_empty": True, "queries": gate.expected_queries()}
            for pointer, trace in zip((64, 256), gate.TRACES)]
        return {"schema": "oksolc.graph-init-observations.v4", "zigVersion": "0.17.0",
            "mode": "Debug", "backend": "stage2_llvm", "cases": cases}

    def test_native_profile_complete_fields_queries_and_types(self):
        original = self.profile()
        gate.check_profile(original, "Debug")
        for key, wrong in (("cache_capacity", 1), ("cache_capacity", False),
                ("key_iterator_empty", False), ("key_iterator_empty", 1)):
            changed = copy.deepcopy(original)
            changed["cases"][0][key] = wrong
            with self.subTest(key=key, wrong=wrong), self.assertRaises(ValueError):
                gate.check_profile(changed, "Debug")
        for key in ("cache_capacity", "key_iterator_empty"):
            changed = copy.deepcopy(original)
            del changed["cases"][0][key]
            with self.subTest(missing=key), self.assertRaises(ValueError):
                gate.check_profile(changed, "Debug")
        for label, key, value in (("actual", "representative_length", 1), ("actual", "map_available", 1),
                ("actual", "map_metadata_null", False), ("actual", "map_lock_empty", False),
                ("actual", "allocator_pointer", 999), ("actual", "allocator_vtable", 999),
                ("actual", "map_size", False), ("after", "alloc", 4)):
            changed = copy.deepcopy(original)
            changed["cases"][0][label][key] = value
            with self.subTest(label=label, key=key), self.assertRaises(ValueError):
                gate.check_profile(changed, "Debug")
        for key in original["cases"][0]["actual"]:
            changed = copy.deepcopy(original)
            del changed["cases"][0]["actual"][key]
            with self.subTest(omitted=key), self.assertRaises(ValueError):
                gate.check_profile(changed, "Debug")
        for kind in ("omitted-query", "wrong-query", "mistyped-query", "cache-hit", "cache-mistyped", "cache-omitted", "duplicate-context", "extra-case"):
            changed = copy.deepcopy(original)
            if kind == "omitted-query":
                changed["cases"][0]["queries"].pop()
            elif kind == "wrong-query":
                changed["cases"][0]["queries"][0]["operation_missing"] = False
            elif kind == "mistyped-query":
                changed["cases"][0]["queries"][0]["invalid_representative"] = 1
            elif kind == "cache-hit":
                changed["cases"][0]["queries"][0]["cache_missing"] = False
            elif kind == "cache-mistyped":
                changed["cases"][0]["queries"][0]["cache_missing"] = 1
            elif kind == "cache-omitted":
                del changed["cases"][0]["queries"][0]["cache_missing"]
            elif kind == "duplicate-context":
                for label in ("input", "actual"):
                    changed["cases"][1][label]["allocator_pointer"] = 64
            else:
                changed["cases"].append(changed["cases"][0])
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                gate.check_profile(changed, "Debug")


if __name__ == "__main__":
    unittest.main()
