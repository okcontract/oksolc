#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Compiler evidence size limits must reject explicitly and preserve raw outputs.
"""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
import check_compiler as check


class ArtifactReadTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.output = Path(self.directory.name)

    def invoke(self, script, **kwargs):
        return check.require_success(self.output, 'trial', [sys.executable, '-c', script],
                                     os.environ.copy(), 30, **kwargs)

    def test_larger_explicit_limit_retains_complete_output(self):
        size = 16 * 1024 * 1024 + 1
        result = self.invoke('import sys; sys.stdout.buffer.write(b"x" * ' + str(size) + ')',
                             stdout_limit=64 * 1024 * 1024)
        self.assertEqual(result, b'x' * size)
        self.assertEqual((self.output / 'trial.stdout').read_bytes(), result)

    def test_default_limit_still_rejects_and_retains(self):
        size = 16 * 1024 * 1024 + 1
        with self.assertRaisesRegex(ValueError, 'output limit exceeded: trial.stdout'):
            self.invoke('import sys; sys.stdout.buffer.write(b"x" * ' + str(size) + ')')
        self.assertEqual((self.output / 'trial.stdout').stat().st_size, size)
        record = json.loads((self.output / 'trial.process.json').read_text())
        self.assertEqual((record['status'], record['exitCode']), ('completed', 0))

    def test_explicit_limit_boundary_rejects_without_truncation(self):
        self.assertEqual(self.invoke('print("abc", end="")', stdout_limit=3), b'abc')
        with self.assertRaisesRegex(ValueError, 'output limit exceeded: trial.stdout'):
            self.invoke('print("abcd", end="")', stdout_limit=3)
        self.assertEqual((self.output / 'trial.stdout').read_bytes(), b'abcd')

    def test_failed_process_cannot_become_accepted_output(self):
        with self.assertRaisesRegex(ValueError, 'trial failed; inspect its retained stdout/stderr'):
            self.invoke('import sys; print("partial"); sys.exit(7)', stdout_limit=64 * 1024 * 1024)
        record = json.loads((self.output / 'trial.process.json').read_text())
        self.assertEqual(record['exitCode'], 7)
        self.assertEqual((self.output / 'trial.stdout').read_bytes(), b'partial\n')

    def test_input_and_working_directory_are_forwarded(self):
        (self.output / 'marker').write_bytes(b'ok')
        result = self.invoke('import pathlib,sys; assert pathlib.Path("marker").read_bytes() == b"ok"; '
                             'sys.stdout.buffer.write(sys.stdin.buffer.read())',
                             cwd=self.output, data=b'input', stdout_limit=5)
        self.assertEqual(result, b'input')


if __name__ == '__main__':
    unittest.main()
