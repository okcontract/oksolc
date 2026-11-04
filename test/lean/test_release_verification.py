"""Release packaging must reject partial, mixed-commit and modified evidence.
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import copy
import importlib
from pathlib import Path
import tempfile
import unittest

import release_verification as release


def report():
    return {"status": "passed", "accepted": True, "corpusComplete": True,
            "freshPackage": True, "freshKernelReplay": True, "wholeCompilerVerified": False,
            "requestedCases": 1, "unvalidatedCases": [], "cases": [{"case": 0, "accepted": True}],
            "negativeControls": [{"rejected": True}],
            "proofBatches": [{"cases": [0], "freshPackage": True, "freshKernelReplay": True}]}


class ReleaseTests(unittest.TestCase):
    def test_incomplete_or_vacuous_acceptance_rejects(self):
        mutations = {"freshKernelReplay": False, "corpusComplete": False, "cases": [],
                     "negativeControls": [], "unvalidatedCases": [0], "proofBatches": [],
                     "wholeCompilerVerified": True, "requestedCases": 2}
        for field, value in mutations.items():
            bad = report()
            bad[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                release.accepted(bad)
        bad = report()
        bad["proofBatches"] *= 2
        with self.assertRaisesRegex(ValueError, "batch coverage"):
            release.accepted(bad)

    def evidence(self, root):
        source = {"commit": "a" * 40, "tree": "b" * 40}
        for profile in release.REQUIRED:
            base = root / profile
            process = base / (profile + "-process/receipt.json")
            process.parent.mkdir(parents=True)
            release.write(process, {"status": "passed", "exitCode": 0})
            files = {process.relative_to(base).as_posix(): release.digest(process)}
            if profile != "models":
                result = base / profile / "report.json"
                result.parent.mkdir()
                value = report()
                module = importlib.import_module("check_compiler_functions" if profile == "preview" else "check_compiler_" + profile)
                value["schema"] = module.REPORT_SCHEMA
                if profile == "preview":
                    value["example"] = "publicPreviewIdentity"
                release.write(result, value)
                files[result.relative_to(base).as_posix()] = release.digest(result)
            record = base / "release-receipts" / (profile + ".json")
            record.parent.mkdir()
            release.write(record, {"schema": release.SCHEMA, "profile": profile, "source": source,
                                   "files": files, "summary": {}, "wholeCompilerVerified": False})
        return source

    def test_all_profiles_same_commit_are_required(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = self.evidence(root)
            self.assertEqual(set(release.collect(root, source)[0]), release.REQUIRED)
            path = root / "preview/release-receipts/preview.json"
            original = release.read(path)
            changed = copy.deepcopy(original)
            changed["source"]["commit"] = "c" * 40
            release.write(path, changed)
            with self.assertRaisesRegex(ValueError, "release commit"):
                release.collect(root, source)
            path.unlink()
            with self.assertRaisesRegex(ValueError, "missing release profiles"):
                release.collect(root, source)

    def test_changed_bytes_and_escaping_paths_reject(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = self.evidence(root)
            (root / "words/words/report.json").write_text("{}")
            with self.assertRaisesRegex(ValueError, "evidence changed"):
                release.collect(root, source)
            for name in ("../outside", "/etc/hosts"):
                with self.assertRaisesRegex(ValueError, "escapes"):
                    release.contained(root, name)

    def test_a_different_gate_cannot_supply_a_profile(self):
        bad = report()
        bad["schema"] = "oksolc.compiler-graph-verification.v2"
        with self.assertRaisesRegex(ValueError, "wrong artifact profile"):
            release.accepted(bad, "words")
