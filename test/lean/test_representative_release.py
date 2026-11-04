#!/usr/bin/env python3
"""Reject malformed or incomplete native full-capacity free observations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from copy import deepcopy
import unittest

import check_representative_release as gate


def fixture(mode="Debug"):
    return {
        "schema": "oksolc.representative-release-native.v6",
        "target": {"arch": "aarch64", "os": "macos", "mode": mode, "pointer_bytes": 8},
        "descriptor": {"bytes": 32, "alignment": 8},
        "backing": {"base": 512, "length": 2, "capacity": 5},
        "allocation": {"calls": 1, "base": 512, "bytes": 160, "alignment": 8},
        "copy_allocation": {"calls": 1, "base": 800, "bytes": 224, "alignment": 8},
        "remap": {"calls": 1, "base": 512, "bytes": 160, "new_bytes": 224, "alignment": 8},
        "header": {"base": 800, "length": 2, "capacity": 7},
        "copy": {"base": 800, "capacity": 7, "rows": [
            {"item_base": 32, "arguments_base": 260, "arguments_length": 2, "id": 0, "sequence": 23},
            {"item_base": 32, "arguments_base": 260, "arguments_length": 2, "id": 1, "sequence": 29}]},
        "release": {"calls": 1, "base": 512, "bytes": 160, "alignment": 8},
        "order": 1312,
        "oom": {"failed": True, "calls": 1, "base": 0, "bytes": 160, "alignment": 8, "frees": 0, "order": 1},
        "growth_oom": {"failed": True, "calls": 2, "base": 0, "bytes": 224, "alignment": 8, "frees": 0, "order": 131,
            "remap": {"calls": 1, "base": 1056, "bytes": 160, "new_bytes": 224, "alignment": 8}, "old_base": 1056,
            "header": {"base": 1056, "length": 2, "capacity": 5}, "rows": [
                {"item_base": 32, "arguments_base": 260, "arguments_length": 2, "id": 0, "sequence": 23},
                {"item_base": 32, "arguments_base": 260, "arguments_length": 2, "id": 1, "sequence": 29}]},
        "empty_calls": 0,
        "empty_growth": {"sentinel_base": 1408, "source": 1440, "calls": 1, "base": 1536,
            "bytes": 160, "alignment": 8, "remaps": 0, "frees": 0, "order": 1,
            "header": {"base": 1536, "length": 0, "capacity": 5}},
        "item": {"base_before": 32, "base_after": 32, "instruction_after": "LT"},
        "parent": {"base": 256, "arguments_base": 260, "arguments_length": 2, "after": [777, 99, 1, 5]},
    }


class NativeRelease(unittest.TestCase):
    def test_all_build_modes(self):
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            gate.check_observation(fixture(mode), mode)

    def test_wrong_extent_effects_and_borrow(self):
        for path, value in (
                (("release", "bytes"), 64), (("release", "bytes"), 192),
                (("release", "base"), 520), (("release", "alignment"), 4),
                (("release", "calls"), 0), (("release", "calls"), 2),
                (("empty_calls",), 1), (("backing", "length"), 5),
                (("item", "base_after"), 40), (("item", "instruction_after"), "GT"),
                (("parent", "arguments_base"), 256), (("parent", "arguments_length"), 3),
                (("parent", "after"), [777, 1, 99, 5]), (("parent", "after"), [0, 99, 1, 5]),
                (("target", "arch"), "x86_64"), (("target", "mode"), "ReleaseFast"),
                (("schema",), "oksolc.representative-release-native.v1"),
                (("allocation", "base"), 520), (("allocation", "bytes"), 64), (("allocation", "calls"), 0),
                (("order",), 21), (("oom", "failed"), False), (("oom", "failed"), 1),
                (("oom", "calls"), 0), (("oom", "frees"), 1), (("oom", "base"), 512), (("oom", "order"), 12)):
            with self.subTest(path=path, value=value):
                profile = fixture()
                owner = profile
                for key in path[:-1]:
                    owner = owner[key]
                owner[path[-1]] = value
                with self.assertRaises(ValueError):
                    gate.check_observation(profile, "Debug")

    def test_empty_growth_requires_no_sentinel_access(self):
        for path, value in (
                (("calls",), 0), (("bytes",), 0), (("remaps",), 1), (("frees",), 1),
                (("order",), 1312), (("source",), 1408), (("base",), 1440),
                (("header", "base"), 1664), (("header", "length"), 1), (("header", "capacity"), 4)):
            profile = fixture()
            owner = profile["empty_growth"]
            for key in path[:-1]:
                owner = owner[key]
            owner[path[-1]] = value
            with self.subTest(path=path, value=value), self.assertRaises(ValueError):
                gate.check_observation(profile, "Debug")

    def test_no_integer_coercions(self):
        for path in (("release", "calls"), ("allocation", "calls"), ("allocation", "base"), ("backing", "base"), ("parent", "arguments_base")):
            for value in (True, False, -1, 0.0, "512", None, [], 2**64):
                profile = fixture()
                profile[path[0]][path[1]] = value
                with self.subTest(path=path, value=value), self.assertRaises(ValueError):
                    gate.check_observation(profile, "Debug")
        profile = fixture()
        profile["parent"]["after"][2] = True
        with self.assertRaises(ValueError):
            gate.check_observation(profile, "Debug")

    def test_exact_fields_and_list_shape(self):
        for key in fixture():
            missing = fixture()
            del missing[key]
            with self.subTest(key=key), self.assertRaises(ValueError):
                gate.check_observation(missing, "Debug")
        for key in (None, "allocation", "release", "parent", "target", "oom"):
            extra = fixture()
            (extra if key is None else extra[key])["extra"] = 0
            with self.subTest(key=key), self.assertRaises(ValueError):
                gate.check_observation(extra, "Debug")
        profile = fixture()
        profile["parent"]["after"] = tuple(profile["parent"]["after"])
        with self.assertRaises(ValueError):
            gate.check_observation(profile, "Debug")

    def test_full_ranges_and_separation(self):
        for base in (513, 2**64 - 8, 256):
            profile = fixture()
            profile["backing"]["base"] = profile["allocation"]["base"] = profile["release"]["base"] = base
            with self.subTest(base=base), self.assertRaises(ValueError):
                gate.check_observation(profile, "Debug")
        profile = fixture()
        profile["item"]["base_before"] = profile["item"]["base_after"] = 544
        with self.assertRaises(ValueError):
            gate.check_observation(profile, "Debug")

    def test_observation_is_not_rewritten(self):
        profile = fixture()
        original = deepcopy(profile)
        gate.check_observation(profile, "Debug")
        self.assertEqual(profile, original)

    def test_mutation_selectors_are_unique(self):
        source = gate.control_source()
        self.assertEqual(len(gate.MUTATIONS), len({name for name, _, _ in gate.MUTATIONS}))
        for name, original, replacement in gate.MUTATIONS:
            with self.subTest(name=name):
                self.assertEqual(source.count(original), 1)
                self.assertNotEqual(original, replacement)

    def test_copied_fields_and_allocation(self):
        for key, value in (("item_base", 40), ("arguments_base", 256), ("arguments_length", 3), ("id", 9), ("sequence", 0)):
            for row in range(2):
                profile = fixture()
                profile["copy"]["rows"][row][key] = value
                with self.subTest(row=row, key=key), self.assertRaises(ValueError):
                    gate.check_observation(profile, "Debug")
        for base in (512, 600, 256, 32, 801, 2**64 - 8):
            profile = fixture()
            profile["copy"]["base"] = profile["copy_allocation"]["base"] = base
            with self.subTest(base=base), self.assertRaises(ValueError):
                gate.check_observation(profile, "Debug")
        for key, value in (("calls", 2), ("bytes", 64), ("alignment", 4), ("base", 808)):
            profile = fixture()
            profile["copy_allocation"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                gate.check_observation(profile, "Debug")

    def test_relocation_header_and_remap_observations(self):
        for section, key, value in (("header", "base", 512), ("header", "length", 7), ("header", "capacity", 5),
                ("remap", "base", 800), ("remap", "calls", 0), ("remap", "bytes", 64), ("remap", "new_bytes", 160),
                ("remap", "alignment", 4)):
            profile = fixture()
            profile[section][key] = value
            with self.subTest(section=section, key=key), self.assertRaises(ValueError):
                gate.check_observation(profile, "Debug")

    def test_nonempty_growth_oom(self):
        for path, value in (
                (("failed",), False), (("calls",), 1), (("base",), 1056), (("bytes",), 160),
                (("alignment",), 4), (("frees",), 1), (("order",), 1312), (("old_base",), 1064),
                (("remap", "calls"), 0), (("remap", "base"), 800), (("remap", "bytes"), 64),
                (("remap", "new_bytes"), 160), (("header", "length"), 7), (("header", "capacity"), 7),
                (("header", "base"), 800), (("rows", 0, "item_base"), 40),
                (("rows", 1, "arguments_base"), 256), (("rows", 1, "id"), 0)):
            profile = fixture()
            owner = profile["growth_oom"]
            for key in path[:-1]:
                owner = owner[key]
            owner[path[-1]] = value
            with self.subTest(path=path, value=value), self.assertRaises(ValueError):
                gate.check_observation(profile, "Debug")
        for base in (1057, 2**64 - 8, 256, 32, 800):
            profile = fixture()
            failed = profile["growth_oom"]
            failed["old_base"] = failed["header"]["base"] = failed["remap"]["base"] = base
            with self.subTest(base=base), self.assertRaises(ValueError):
                gate.check_observation(profile, "Debug")


if __name__ == "__main__":
    unittest.main()
