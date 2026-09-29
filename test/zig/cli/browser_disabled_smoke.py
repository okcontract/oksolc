#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Disabled browser commands fail before creating project or cache state."""

from pathlib import Path
import subprocess
import sys
import tempfile


def main(cli):
    with tempfile.TemporaryDirectory(prefix="oksolc-no-browser-") as directory:
        for arguments in (["browse"], ["serve", "--browse"]):
            result = subprocess.run(
                [cli, *arguments], cwd=directory, capture_output=True, timeout=10
            )
            assert result.returncode != 0, result
            assert not result.stdout, result.stdout
            assert b"web browser is disabled" in result.stderr, result.stderr
            assert b"zig build -Dbrowser=true" in result.stderr, result.stderr
            assert not list(Path(directory).iterdir()), "disabled browser created files"
    print("disabled browser: commands report the build option without creating state")


if __name__ == "__main__":
    main(str(Path(sys.argv[1]).resolve()))
