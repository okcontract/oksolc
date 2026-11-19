"""Behavioral checks for the bounded proof-control scheduler.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
from pathlib import Path
import tempfile
import threading
import time
import unittest

from assembly_item_creation_checks import checked_controls
from benchmark_control_matrix import parity
from lean_control_matrix import ControlPlan


class ControlMatrixTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.output = Path(self.directory.name)
        self.env = {"LEAN_NUM_THREADS": "4", "TEST_INPUT": "unchanged"}

    def plan(self, execute, count=8):
        plan = ControlPlan(self.output, self.env, "lean")
        records = [plan.add(self.output, "case-" + str(i), "source-" + str(i), True, self.env, execute)
                   for i in range(count)]
        return plan, records

    def test_parallel_bound_order_environment_and_join(self):
        lock = threading.Lock()
        ready = threading.Barrier(4, timeout=5)
        active = peak = 0
        finished = []

        def execute(output, name, source, expected, env, lean):
            nonlocal active, peak
            index = int(name.split("-")[-1])
            self.assertEqual((source, expected, lean), ("source-" + str(index), True, "lean"))
            self.assertEqual(env, {"LEAN_NUM_THREADS": "1", "TEST_INPUT": "unchanged"})
            env["TEST_INPUT"] = "worker-local"
            with lock:
                active += 1
                peak = max(peak, active)
            if index < 4:
                ready.wait()
            time.sleep(0.03 if index == 0 else 0.002)
            with lock:
                active -= 1
                finished.append(name)
            return {"name": name, "status": "passed"}

        plan, pending = self.plan(execute)
        records, summary = plan.seal(pending).run(4)
        self.assertEqual([r["name"] for r in records], ["case-" + str(i) for i in range(8)])
        self.assertNotEqual(finished[0], "case-0")
        self.assertEqual((peak, active, summary["status"], summary["leanThreadsPerControl"]), (4, 0, "passed", 1))
        self.assertEqual(self.env, {"LEAN_NUM_THREADS": "4", "TEST_INPUT": "unchanged"})

    def test_serial_baseline_keeps_four_lean_threads(self):
        def execute(output, name, source, expected, env, lean):
            self.assertEqual(env["LEAN_NUM_THREADS"], "4")
            return {"name": name}
        plan, pending = self.plan(execute, 2)
        records, summary = plan.seal(pending).run(1)
        self.assertEqual([r["name"] for r in records], ["case-0", "case-1"])
        self.assertEqual(summary["leanThreadsPerControl"], 4)

    def test_first_failure_cancels_pending_and_joins_started_work(self):
        ready = threading.Barrier(4, timeout=5)
        lock = threading.Lock()
        active = 0

        def execute(output, name, source, expected, env, lean):
            nonlocal active
            index = int(name.split("-")[-1])
            with lock:
                active += 1
            try:
                if index < 4:
                    ready.wait()
                if index == 1:
                    raise ValueError("unexpected proof result")
                time.sleep(0.08)
                return {"name": name}
            finally:
                with lock:
                    active -= 1

        plan, pending = self.plan(execute, 100)
        with self.assertRaisesRegex(ValueError, "unexpected proof result"):
            plan.seal(pending).run(4)
        self.assertEqual(active, 0)
        report = json.loads((self.output / "control-matrix.json").read_text())
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["controls"][1]["status"], "failed")
        self.assertGreater(sum(r["status"] == "cancelled" for r in report["controls"]), 90)
        self.assertNotIn("running", [r["status"] for r in report["controls"]])

    def test_existing_diagnostic_validator_is_deferred_and_remains_strict(self):
        def execute(output, name, source, expected, env, lean):
            (output / (name + ".stdout")).write_text("error: Invalid field; unsolved goals\n")
            return {"name": name, "expectedAcceptance": False}
        plan = ControlPlan(self.output, self.env, "lean")
        pending = plan.add(self.output, "negative", "bad source", False, self.env, execute)
        records = checked_controls(self.output, [pending])
        self.assertFalse((self.output / "negative.stdout").exists())
        with self.assertRaisesRegex(ValueError, "resource, syntax or elaboration"):
            plan.seal(records).run(4)
        report = json.loads((self.output / "control-matrix.json").read_text())
        self.assertEqual(report["controls"][0]["status"], "failed")

    def test_physical_publication_controls_defer_their_existing_diagnostics(self):
        from check_owned_keys_physical import controls
        plan = ControlPlan(self.output, self.env, "lean")
        pending = controls(self.output, self.env, plan)
        self.assertEqual(len(pending), 8)
        manifest = plan.seal(pending).manifest()
        self.assertTrue(all(task["diagnosticChecks"] ==
            ["check_owned_keys_physical.check_control_diagnostic"] for task in manifest))
        self.assertEqual(list(self.output.iterdir()), [])

    def test_kernel_decision_failure_does_not_hide_resource_or_elaboration_errors(self):
        from unittest.mock import patch
        from types import SimpleNamespace
        from check_zig_air_proofs import mutation_check
        proof = 'error: Tactic `decide` failed for proposition\n'
        for suffix in ('', 'maximum recursion depth has been reached', 'unknown identifier x', 'timeout'):
            with self.subTest(suffix=suffix):
                def child(*args, **kwargs):
                    kwargs['stdout'].write((proof + suffix).encode())
                    return SimpleNamespace(returncode=1)
                with patch('check_zig_air_proofs.subprocess.run', side_effect=child):
                    result = mutation_check(self.output, 'decision', 'source', False, self.env, 'lean')
                if suffix:
                    with self.assertRaisesRegex(ValueError, 'resource, syntax or elaboration'):
                        checked_controls(self.output, [result])
                else:
                    self.assertEqual(checked_controls(self.output, [result]), [result])

    def test_collection_rejects_missing_or_duplicate_controls(self):
        for order in ((0,), (0, 0)):
            with self.subTest(order=order):
                plan, pending = self.plan(lambda *args: self.fail("collection executed Lean"), 2)
                with self.assertRaisesRegex(ValueError, "lost or duplicated"):
                    plan.seal([pending[i] for i in order])

    def test_builder_return_order_is_preserved(self):
        plan, pending = self.plan(lambda output, name, *_: {"name": name}, 2)
        records, _ = plan.seal(list(reversed(pending))).run(4)
        self.assertEqual([r["name"] for r in records], ["case-1", "case-0"])

    def test_invalid_budget_stale_outputs_and_second_execution_fail_closed(self):
        for workers in (0, 5, True):
            plan, pending = self.plan(lambda *args: self.fail("invalid budget executed Lean"), 1)
            with self.assertRaisesRegex(ValueError, "one to four"):
                plan.seal(pending).run(workers)
        plan, pending = self.plan(lambda *args: self.fail("stale output executed Lean"), 1)
        (self.output / "case-0.stdout").write_text("retained")
        with self.assertRaisesRegex(ValueError, "already exists"):
            plan.seal(pending).run(4)
        self.assertEqual((self.output / "case-0.stdout").read_text(), "retained")
        with self.assertRaisesRegex(ValueError, "runs once"):
            plan.run(4)

    def test_collection_preserves_unique_paths_and_environment(self):
        plan, pending = self.plan(lambda *args: None, 1)
        for name, output, env in (("case-0", self.output, self.env), ("../escape", self.output, self.env),
                                  ("new", self.output / "elsewhere", self.env),
                                  ("new", self.output, {"LEAN_NUM_THREADS": "8"})):
            with self.subTest(name=name, output=output, env=env):
                with self.assertRaises(ValueError):
                    plan.add(output, name, "source", True, env, lambda *args: None)
        plan.seal(pending)
        with self.assertRaises(ValueError):
            pending[0].checked_by(self.output, lambda *_: None)

    def test_benchmark_parity_requires_every_result_and_complete_diagnostic_bytes(self):
        reference = [{"name": "negative", "expectedAcceptance": False, "sourceSha256": "source",
                      "exitCode": 1, "stdoutSha256": "whole-diagnostic", "stderrSha256": "empty",
                      "status": "passed", "seconds": 1}]
        parity(reference, [{**reference[0], "seconds": 2}])
        for field, changed in (("name", "other"), ("expectedAcceptance", True),
                               ("sourceSha256", "different-source"), ("exitCode", 0),
                               ("stdoutSha256", "same-first-error-different-tail"),
                               ("stderrSha256", "warning"), ("status", "failed")):
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, field):
                parity(reference, [{**reference[0], field: changed}])
        for actual in ([], reference + reference):
            with self.assertRaisesRegex(ValueError, "missing or extra"):
                parity(reference, actual)


if __name__ == "__main__":
    unittest.main()
