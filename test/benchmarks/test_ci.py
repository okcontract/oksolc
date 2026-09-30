#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Check single-invocation measurement and rejection of invalid compiler output."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

import ci
import compare
from test_external import output


class SingleInvocationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.request = self.root / "request.json"
        self.request.write_text('{"language":"Solidity"}')
        self.counter = self.root / "invocations"
        self.expected_hash = compare.contract_output_sha256(compare.contract_output(output()))

    def invoke(self, raw, exit_code=0):
        # A real child process exercises wait4, file capture, and exit handling.
        script = self.root / "compiler.py"
        script.write_text(
            "import json, sys\n"
            "assert json.load(sys.stdin) == {'language': 'Solidity'}\n"
            f"with open({str(self.counter)!r}, 'a') as counter: counter.write('run\\n')\n"
            f"sys.stdout.write({raw!r})\n"
            "sys.stderr.write('compiler diagnostic')\n"
            f"sys.exit({exit_code})\n"
        )
        self.counter.write_text("")
        result = ci.benchmark_request(
            [sys.executable, str(script)], self.request, self.expected_hash, self.root
        )
        self.assertEqual(self.counter.read_text(), "run\n")
        self.assertEqual(result["measurement"]["exit_code"], exit_code)
        self.assertGreater(result["measurement"]["wall_seconds"], 0)
        self.assertGreater(result["measurement"]["peak_rss_mib"], 0)
        return result

    def test_validates_the_only_measured_invocation(self):
        value = output()
        value["errors"] = [{"severity": "warning", "message": "a warning"}]
        result = self.invoke(json.dumps(value))
        self.assertEqual(result["status"], "passed")
        self.assertEqual(result["contract_output_sha256"], self.expected_hash)

    def test_rejects_bad_output_even_with_zero_exit_status(self):
        cases = [
            (json.dumps(output(creation="6002")), "SHA256 changed"),
            (json.dumps(output(deployed="6002")), "SHA256 changed"),
            (json.dumps({"errors": [{"severity": "error", "message": "stack too deep"}]}),
             "stack too deep"),
            ("{}", "no contract bytecode"),
            ("[]", "non-object"),
            ("not JSON", "invalid JSON"),
        ]
        for raw, message in cases:
            with self.subTest(message=message, raw=raw):
                result = self.invoke(raw)
                self.assertEqual(result["status"], "failed")
                self.assertIn(message, result["error"])

    def test_rejects_nonzero_exit_despite_valid_output(self):
        result = self.invoke(json.dumps(output()), exit_code=7)
        self.assertEqual(result["status"], "failed")
        self.assertIn("exited with 7: compiler diagnostic", result["error"])


if __name__ == "__main__":
    unittest.main()
