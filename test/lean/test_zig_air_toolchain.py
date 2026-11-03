#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Failure-boundary tests for the isolated Zig toolchain builder.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import importlib.util
import io
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("zig_air_build", ROOT / "lean/zig_air/build_toolchain.py")
BUILD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILD)


class ToolchainTests(unittest.TestCase):
    def test_archive_rejects_paths_and_links_before_extracting(self):
        for name, kind in (("../escape", tarfile.REGTYPE), ("/escape", tarfile.REGTYPE),
                           ("link", tarfile.SYMTYPE), ("link", tarfile.LNKTYPE)):
            with self.subTest(name=name, kind=kind), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                archive = root / "source.tar"
                with tarfile.open(archive, "w") as stream:
                    valid = tarfile.TarInfo("valid")
                    valid.size = 2
                    stream.addfile(valid, io.BytesIO(b"ok"))
                    invalid = tarfile.TarInfo(name)
                    invalid.type = kind
                    invalid.linkname = "valid"
                    stream.addfile(invalid)
                with self.assertRaisesRegex(ValueError, "unsafe or unsupported"):
                    BUILD.unpack(archive, root / "out")
                self.assertFalse((root / "out").exists())
                self.assertFalse((root / "escape").exists())

    def test_regular_archive_and_content_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            archive = root / "source.tar"
            with tarfile.open(archive, "w") as stream:
                member = tarfile.TarInfo("dir/source.zig")
                member.size = 2
                stream.addfile(member, io.BytesIO(b"ok"))
            BUILD.unpack(archive, root / "out")
            before = BUILD.source_identity(root / "out")
            self.assertEqual(before["files"], 1)
            self.assertEqual((root / "out/dir/source.zig").read_bytes(), b"ok")
            (root / "out/dir/source.zig").write_bytes(b"no")
            self.assertNotEqual(before, BUILD.source_identity(root / "out"))
            (root / "out/link").symlink_to("dir/source.zig")
            with self.assertRaisesRegex(ValueError, "unexpected link"):
                BUILD.source_identity(root / "out")

    def test_failure_preserves_streams_status_and_literal_arguments(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            argument = "`never execute` $(anything)\nsecond line"
            with self.assertRaisesRegex(ValueError, "failed"):
                BUILD.run(root, "failure", [sys.executable, "-c",
                    "import sys; print(sys.argv[1]); print('diagnostic', file=sys.stderr); sys.exit(7)", argument])
            receipt = json.loads((root / "failure.process.json").read_text())
            self.assertEqual(receipt["exitCode"], 7)
            self.assertEqual(receipt["status"], "completed")
            self.assertEqual(receipt["command"][-1], argument)
            self.assertEqual((root / "failure.stdout").read_text(), argument + "\n")
            self.assertEqual((root / "failure.stderr").read_text(), "diagnostic\n")

    def test_timeout_retains_actual_terminal_status(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaises(BUILD.subprocess.TimeoutExpired):
                BUILD.run(root, "timeout", [sys.executable, "-c", "import time; time.sleep(60)"], timeout=0.1)
            receipt = json.loads((root / "timeout.process.json").read_text())
            self.assertLess(receipt["exitCode"], 0)
            self.assertEqual(receipt["status"], "failed")
            self.assertEqual(receipt["error"], "TimeoutExpired")

    def test_changed_build_patch_anchor_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build = root / "build.zig"
            build.write_text("unrelated build script\n")
            with self.assertRaisesRegex(ValueError, "configuration changed"):
                BUILD.link_system_libcpp(root, root / "libc++.tbd")
            self.assertEqual(build.read_text(), "unrelated build script\n")

    def test_zero_exit_does_not_hide_build_diagnostics(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            stream = root / "build.stderr"
            stream.write_text("error: memory usage peaked above the declared upper bound\n")
            report = {}
            with self.assertRaisesRegex(ValueError, "zero exit status"):
                BUILD.record_build_diagnostics(root, report)
            self.assertEqual(report["status"], "failed")
            self.assertEqual(report["buildDiagnostics"]["sha256"], BUILD.digest(stream))
            stream.write_text("warning: retained diagnostic\n")
            BUILD.record_build_diagnostics(root, report)
            self.assertEqual(report["status"], "built-with-diagnostics")
            stream.write_bytes(b"")
            BUILD.record_build_diagnostics(root, report)
            self.assertEqual(report["status"], "built")


if __name__ == "__main__":
    unittest.main()
