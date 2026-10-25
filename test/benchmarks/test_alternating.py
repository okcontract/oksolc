#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Validate the exact measured output, including zero-exit compiler failures."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("alternating-compare.py")
SPEC = importlib.util.spec_from_file_location("alternating", SCRIPT)
alternating = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(alternating)


class AlternatingTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.request = self.root / "request.json"
        self.request.write_text(json.dumps({
            "language": "Solidity",
            "sources": {"A.sol": {"content": "contract A {}"}},
            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
        }))
        self.output = {"contracts": {"A.sol": {"A": {"abi": []}}}}
        self.counter = self.root / "invocations"

    def compiler(self, raw, name="compiler", exit_code=0):
        binary = self.root / name
        binary.write_text(
            f"#!{sys.executable}\n"
            f"# {name}\n"
            "import json, os, pathlib, sys\n"
            "assert '--no-cache' in sys.argv\n"
            "assert pathlib.Path(os.environ['XDG_CONFIG_HOME']).parent.resolve() == pathlib.Path.cwd()\n"
            "assert json.load(sys.stdin)['language'] == 'Solidity'\n"
            f"with open({str(self.counter)!r}, 'a') as log: log.write('run\\n')\n"
            f"sys.stdout.write({raw!r})\n"
            "sys.stderr.write('test diagnostic')\n"
            f"sys.exit({exit_code})\n"
        )
        binary.chmod(0o755)
        return binary

    def test_validates_one_measured_invocation_and_records_digest(self):
        self.output["errors"] = [{"severity": "warning", "message": "warning"}]
        raw = json.dumps(self.output)
        sample = alternating.run_compiler(self.compiler(raw), self.request, 2)
        self.assertEqual(self.counter.read_text(), "run\n")
        self.assertEqual(sample["output_sha256"], hashlib.sha256(raw.encode()).hexdigest())
        self.assertEqual(sample["artifact_manifest"], [("A.sol", "A", "abi")])
        self.assertGreater(sample["wall_seconds"], 0)

    def test_rejects_zero_exit_errors_empty_and_malformed_output(self):
        for raw, message in (
            ("", "invalid JSON"), ("not JSON", "invalid JSON"), ("[]", "non-object"),
            ("{}", "no artifacts"), ('{"contracts":{}}', "no artifacts"),
            ('{"errors":[{"severity":"error","type":"InternalCompilerError"}]}', "compiler errors"),
        ):
            with self.subTest(raw=raw), self.assertRaisesRegex(RuntimeError, message):
                alternating.run_compiler(self.compiler(raw), self.request, 1)

    def test_rejects_missing_requested_artifact(self):
        raw = json.dumps({"contracts": {"A.sol": {"A": {"metadata": "{}"}}}})
        with self.assertRaisesRegex(RuntimeError, "missing requested artifact"):
            alternating.run_compiler(self.compiler(raw), self.request, 1)

    def test_rejects_nonzero_exit_even_with_valid_artifacts(self):
        with self.assertRaisesRegex(RuntimeError, "test diagnostic"):
            alternating.run_compiler(self.compiler(json.dumps(self.output), exit_code=2), self.request, 1)

    def test_ast_only_requests_are_valid(self):
        request = {"sources": {"A.sol": {}}, "settings": {"outputSelection": {"*": {"": ["ast"]}}}}
        raw = json.dumps({"sources": {"A.sol": {"id": 0, "ast": {"nodeType": "SourceUnit"}}}}).encode()
        self.assertEqual(alternating.validate_output(raw, request), [("A.sol", "", "ast")])
        with self.assertRaisesRegex(RuntimeError, "missing requested artifact"):
            alternating.validate_output(b'{"sources":{"A.sol":{"id":0}}}', request)

    def test_yul_without_a_deployed_subobject_is_valid(self):
        request = {"language": "Yul", "sources": {"A.yul": {}}, "settings": {
            "outputSelection": {"*": {"*": ["evm.bytecode.object", "evm.deployedBytecode.object"]}},
        }}
        raw = json.dumps({"contracts": {"A.yul": {"A": {"evm": {"bytecode": {"object": "00"}}}}}}).encode()
        self.assertEqual(alternating.validate_output(raw, request), [("A.yul", "A", "evm.bytecode.object")])

    def test_complete_helper_rejects_failure_and_partial_contract_output(self):
        baseline_output = {"contracts": {"A.sol": {"A": {"abi": []}, "B": {"abi": []}}}}
        baseline = self.compiler(json.dumps(baseline_output), "baseline")
        cases = [
            ({"errors": [{"severity": "error", "message": "failure"}]}, b"compiler errors"),
            (self.output, b"artifact manifests differ"),
        ]
        for output, message in cases:
            candidate = self.compiler(json.dumps(output), "candidate")
            report = self.root / "report.json"
            result = subprocess.run([
                sys.executable, str(SCRIPT), "--baseline", str(baseline),
                "--candidate", str(candidate), "--request", "case", str(self.request),
                "--runs", "1", "--warmups", "0", "--output", str(report),
            ], capture_output=True, timeout=30)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn(message, result.stderr)
            self.assertFalse(report.exists())

    def test_complete_helper_records_valid_comparison(self):
        raw = json.dumps(self.output)
        baseline = self.compiler(raw, "baseline")
        candidate = self.compiler(raw, "candidate")
        report = self.root / "report.json"
        result = subprocess.run([
            sys.executable, str(SCRIPT), "--baseline", str(baseline),
            "--candidate", str(candidate), "--request", "case", str(self.request),
            "--runs", "2", "--warmups", "1", "--output", str(report),
        ], capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(report.read_text())
        self.assertEqual(data["schema"], 2)
        self.assertIn("--no-cache", data["protocol"]["persistent_compiler_cache"])
        workload = data["workloads"]["case"]
        self.assertEqual(workload["invocation_order"], ["baseline", "candidate", "candidate", "baseline"])
        for samples in workload["samples"].values():
            self.assertEqual(len(samples), 2)
            self.assertTrue(all(sample["output_sha256"] == hashlib.sha256(raw.encode()).hexdigest() for sample in samples))
        self.assertEqual(len(self.counter.read_text().splitlines()), 6)


if __name__ == "__main__":
    unittest.main()
