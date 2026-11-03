"""Process-tree resource controls, including fresh-replay session boundaries.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import bounded_run as guard


class BoundedRunTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.output = Path(self.temp.name) / "run"

    def run_code(self, code, **limits):
        return guard.run([sys.executable, "-c", code], self.output, interval=0.02, **limits)

    def test_terminal_status_and_raw_streams(self):
        report = self.run_code("import sys; print('out'); print('err',file=sys.stderr); sys.exit(3)")
        self.assertEqual((report["status"], report["exitCode"]), ("failed", 3))
        self.assertEqual((self.output / "stdout.log").read_text(), "out\n")
        self.assertEqual((self.output / "stderr.log").read_text(), "err\n")

    def test_success_is_terminal_and_recorded(self):
        report = self.run_code("print('complete')")
        self.assertEqual((report["status"], report["exitCode"]), ("passed", 0))
        self.assertEqual(json.loads((self.output / "receipt.json").read_text()), report)

    def test_memory_counts_children_in_separate_sessions_and_stops_them(self):
        # Each child is below the limit; their sum crosses it. Real bytearrays
        # touch pages, so this measures resident memory, not a virtual mapping.
        code = """import subprocess, sys, time
children = [subprocess.Popen([sys.executable, '-c',
    'import time; data=bytearray(48*1024**2); time.sleep(30)'],
    start_new_session=True) for _ in range(2)]
print(*(p.pid for p in children), flush=True)
time.sleep(30)
"""
        report = self.run_code(code, rss_mib=90, timeout=10)
        self.assertEqual((report["status"], report["resourceLimit"]), ("failed", "aggregateRss"))
        self.assertGreater(report["peakSampledTreeRssBytes"], 90 * 1024**2)
        self.assertGreaterEqual(report["peakProcesses"], 3)
        pids = [int(p) for p in (self.output / "stdout.log").read_text().split()]
        rows = guard.snapshot()
        self.assertTrue(all(pid not in rows or rows[pid][1] == 0 for pid in pids))

    def test_timeout_is_not_success(self):
        report = self.run_code("import time; time.sleep(30)", timeout=0.15)
        self.assertEqual((report["status"], report["resourceLimit"]), ("failed", "timeout"))
        self.assertLess(report["exitCode"], 0)

    def test_unavailable_inspection_prevents_launch(self):
        with patch.object(guard, "snapshot", side_effect=RuntimeError("no inspection")), \
                patch.object(guard.subprocess, "Popen") as launch:
            with self.assertRaisesRegex(RuntimeError, "no inspection"):
                self.run_code("print('must not run')")
            launch.assert_not_called()
        report = json.loads((self.output / "receipt.json").read_text())
        self.assertEqual(report["status"], "failed")
        self.assertIsNone(report["exitCode"])

    def test_reparented_children_retained_and_reused_pids_excluded(self):
        rows = {10: (1, 100, "root"), 11: (10, 200, "child"), 12: (11, 300, "grandchild"),
                20: (1, 400, "unrelated")}
        selected = guard.descendants(rows, {10: "root"})
        self.assertEqual(set(selected), {10, 11, 12})
        known = {pid: row[2] for pid, row in selected.items()}
        rows = {11: (1, 200, "child"), 12: (1, 300, "reused")}
        self.assertEqual(set(guard.descendants(rows, known)), {11})


if __name__ == "__main__":
    unittest.main()
