"""Exercise dispatch, resource failures and the development/acceptance boundary.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_compiler as command


class CompilerWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.args = command.parser().parse_args(["hash", "--output", str(self.root / "run")])

    def test_acceptance_dispatch_keeps_the_original_gate(self):
        self.args.phase = "accept"
        argv = command.worker_command(self.args, self.root / "check")
        self.assertEqual(argv[1], str(command.gate.ROOT / "test/lean/check_native_map_memory.py"))
        self.assertIn("--wyhash-hash", argv)
        self.assertNotIn("--preflight", argv)
        self.assertNotIn("--worker", argv)
        self.args.phase = "preflight"
        self.assertIn("--preflight", command.worker_command(self.args, self.root / "check"))
        self.args.target = "map-publication"
        self.assertIn("--receiver-search", command.worker_command(self.args, self.root / "check"))

    def test_hash_capture_toolchain_is_forwarded(self):
        self.args.phase = "accept"
        self.args.air_toolchain = self.root / "captured-toolchain.json"
        argv = command.worker_command(self.args, self.root / "check")
        self.assertEqual(argv[argv.index("--air-toolchain") + 1], str(self.args.air_toolchain))

    def test_development_does_not_dispatch_acceptance_or_replay(self):
        self.args.profile = True
        argv = command.worker_command(self.args, self.root / "check")
        self.assertIn("--worker", argv)
        self.assertIn("--profile", argv)
        self.assertNotIn("--fresh", argv)
        self.assertNotIn("--preflight", argv)

    def test_target_roots_have_the_full_existing_adapter(self):
        for target, (module, _) in command.TARGETS.items():
            adapter = command.importlib.import_module(module)
            with self.subTest(target=target):
                for method in ("audit", "audit_controls", "interfaces", "source_binding", "source_controls", "controls"):
                    self.assertTrue(callable(getattr(adapter, method)))
                source = command.gate.ROOT / "lean" / (adapter.MODULE.replace(".", "/") + ".lean")
                self.assertTrue(source.is_file())
                self.assertEqual(len(set(adapter.CLAIMS)), len(adapter.CLAIMS))

    def test_invocations_cannot_overlap(self):
        lock = self.root / "lock"
        with command.invocation_lock(lock):
            with self.assertRaisesRegex(ValueError, "another compiler proof check"):
                with command.invocation_lock(lock):
                    self.fail("overlap")
        with command.invocation_lock(lock):
            pass

    def execute(self, receipt_status="passed", exit_code=0, child_status="passed"):
        def bounded(argv, output, **limits):
            self.assertEqual(limits, {"rss_mib": 8192, "timeout": 3600})
            output.mkdir()
            receipt = {"status": receipt_status, "exitCode": exit_code}
            command.write(output / "receipt.json", receipt)
            if child_status is not None:
                check = self.args.output / "check"
                check.mkdir()
                command.write(check / "report.json", {"status": child_status})
            return receipt
        with patch.object(command.gate, "ROOT", self.root), \
                patch.object(command, "resolve_tools", return_value=({}, self.root, {}, self.root / "zig", self.root)), \
                patch.object(command.bounded_run, "run", side_effect=bounded):
            return command.run(self.args)

    def test_development_receipt_never_grants_acceptance(self):
        result = self.execute()
        self.assertEqual(result["status"], "passed")
        self.assertEqual(result["assurance"], "developmentOnly")
        self.assertFalse(result["accepted"])
        self.assertFalse(result["wholeCompilerVerified"])

    def test_preflight_has_its_own_terminal_status(self):
        self.args.phase = "preflight"
        result = self.execute(child_status="preflight-passed")
        self.assertEqual(result["assurance"], "developmentOnly")

    def test_resource_or_process_failure_cannot_be_hidden_by_child_report(self):
        for name, status, code in (("resource", "failed", -9), ("process", "failed", 1),
                                   ("inconsistent", "passed", 1)):
            self.args.output = self.root / name
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "bounded verification process failed"):
                self.execute(status, code)
            report = json.loads((self.args.output / "report.json").read_bytes())
            self.assertEqual(report["status"], "failed")
            self.assertFalse(report["accepted"])

    def test_zero_exit_with_incomplete_report_rejects(self):
        for status in ("failed", "preflight-passed", None):
            self.args.output = self.root / str(status)
            with self.subTest(status=status), self.assertRaises((ValueError, FileNotFoundError)):
                self.execute(child_status=status)
            report = json.loads((self.args.output / "report.json").read_bytes())
            self.assertEqual(report["status"], "failed")

    def test_failed_prerequisite_stops_before_audit_and_controls(self):
        tools = ({}, self.root, {}, self.root / "zig", self.root)
        with patch.object(command, "resolve_tools", return_value=tools), \
                patch.object(command.gate, "snapshot", return_value={}), \
                patch.object(command.native, "std_inputs", return_value={}), \
                patch.object(command.gate.source, "file_digest", return_value="digest"), \
                patch.object(command.gate.prove, "check_module", return_value=({"status": "failed"}, {})), \
                patch.object(command.physical, "audit") as audit:
            with self.assertRaisesRegex(ValueError, "build failed"):
                command.development(self.args)
            audit.assert_not_called()
        report = json.loads((self.args.output / "report.json").read_bytes())
        self.assertEqual(report["status"], "failed")
        self.assertFalse(report["freshKernelReplay"])


if __name__ == "__main__":
    unittest.main()
