#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Regression checks for external request capture and the comparison gate."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import compare


def output(creation="6000", deployed="6001"):
    return {
        "contracts": {"test.sol": {"Test": {"evm": {
            "bytecode": {"object": creation},
            "deployedBytecode": {"object": deployed},
        }}}}
    }


class ComparisonGateTests(unittest.TestCase):
    def preflight(self, reference, oksolc):
        request = compare.Request("test", Path("test.json"), b"{}")
        responses = [(0, json.dumps(value).encode(), b"")
                     for value in (reference, oksolc)]
        with patch.object(compare, "run_capture", side_effect=responses):
            return compare.preflight_case(
                compare.Case("test", (request,)), ["solc"], ["oksolc"], {}, {}
            )

    def test_both_creation_and_deployed_bytecode_are_checked(self):
        self.assertTrue(self.preflight(output(), output()).bytecode_match)
        for changed in (output(creation="6002"), output(deployed="6002")):
            with self.subTest(changed=changed):
                self.assertFalse(self.preflight(output(), changed).bytecode_match)
        self.assertFalse(self.preflight(output(), output(deployed="")).bytecode_match)

    def test_other_standard_json_differences_remain_visible(self):
        changed = output()
        changed["sources"] = {"test.sol": {"id": 1}}
        result = self.preflight(output(), changed)
        self.assertTrue(result.bytecode_match)
        self.assertFalse(result.semantic_output_match)
        self.assertFalse(result.exact_output_match)

    def test_failure_paths_must_match_even_when_both_have_no_bytecode(self):
        failure = {"errors": [{"severity": "error", "message": "stack too deep"}]}
        other = {"errors": [{"severity": "error", "message": "unsupported input"}]}
        result = self.preflight(failure, failure)
        self.assertEqual(result.reference_errors, ("stack too deep",))
        for changed in (other, {}, output()):
            with self.subTest(changed=changed):
                with self.assertRaisesRegex(RuntimeError, "different compiler errors"):
                    self.preflight(failure, changed)

    def test_empty_success_is_not_bytecode_parity(self):
        with self.assertRaisesRegex(RuntimeError, "no contract bytecode"):
            self.preflight({}, {})


class LauncherTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.compiler = self.root / "compiler"
        self.compiler.write_text(
            f"#!{sys.executable}\n"
            "import json, sys\n"
            "if '--version' in sys.argv:\n"
            "    print('Version: 0.8.36+oksolc.0.1.4')\n"
            "else:\n"
            "    if 'standard-json' in sys.argv:\n"
            "        assert '--no-cache' in sys.argv\n"
            "    json.load(sys.stdin)\n"
            f"    print({json.dumps(output())!r})\n"
        )
        self.compiler.chmod(0o755)

    def test_capture_preserves_bytes_deduplicates_and_forwards_status(self):
        request = b'{ "language": "Solidity", "sources": {} }\n'
        capture_dir = self.root / "captures"
        env = {**os.environ, "SOLC_REFERENCE": str(self.compiler),
               "SOLC_CAPTURE_DIR": str(capture_dir)}
        wrapper = compare.REPO_ROOT / "test/benchmarks/capture_solc.py"
        for _ in range(2):
            result = subprocess.run([str(wrapper), "--standard-json"],
                                    input=request, capture_output=True, env=env)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout), output())
        captures = list(capture_dir.glob("*.json"))
        self.assertEqual(len(captures), 1)
        self.assertEqual(captures[0].stem, hashlib.sha256(request).hexdigest())
        self.assertEqual(captures[0].read_bytes(), request)
        version = subprocess.run([str(wrapper), "--version"],
                                 capture_output=True, env=env)
        self.assertEqual(version.returncode, 0, version.stderr)
        self.assertIn(b"Version: 0.8.36", version.stdout)
        self.assertEqual(len(list(capture_dir.glob("*.json"))), 1)
        self.compiler.write_text(f"#!{sys.executable}\nimport sys\nsys.exit(7)\n")
        failed = subprocess.run([str(wrapper), "--standard-json"], input=request,
                                capture_output=True, env=env)
        self.assertEqual(failed.returncode, 7)

    def test_replay_invokes_both_compilers_and_writes_reports(self):
        project = "uniswap-v4-2022-06-16"
        requests = self.root / "retained" / project / "requests"
        requests.mkdir(parents=True)
        request = b'{"language":"Solidity","sources":{}}'
        (requests / "input.json").write_bytes(request)
        report_dir = self.root / "reports"
        result = subprocess.run([
            "bash", str(compare.REPO_ROOT / "test/benchmarks/external-compare.sh"),
            "--reuse-captured-requests", str(self.root / "retained"),
            "--project", project, str(self.compiler), str(self.compiler), "1",
        ], env={**os.environ, "BENCHMARK_REPORT_DIR": str(report_dir),
                "BENCHMARK_WARMUPS": "0"}, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads((report_dir / f"{project}.json").read_text())
        benchmark = report["benchmarks"][project]
        self.assertTrue(benchmark["preflight"]["bytecode_match"])
        self.assertEqual(set(benchmark["compilers"]),
                         {"system-solc-via-ir", "zig-via-ir"})
        self.assertIn("--no-cache", report["configuration"]["zig_command"])
        self.assertEqual(report["provenance"]["requests"][0]["sha256"],
                         hashlib.sha256(request).hexdigest())
        self.assertTrue((report_dir / f"{project}-summary.json").is_file())


if __name__ == "__main__":
    unittest.main()
