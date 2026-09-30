#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2014-2026 The Solidity Authors.
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Transparent solc wrapper that records Standard JSON requests from Forge."""

from __future__ import annotations

import hashlib
import os
import subprocess
import sys
from pathlib import Path


def write_capture(directory: Path, request: bytes) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256(request).hexdigest()
    destination = directory / f"{digest}.json"
    try:
        descriptor = os.open(
            destination,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL,
            0o644,
        )
    except FileExistsError:
        return
    with os.fdopen(descriptor, "wb") as output:
        output.write(request)


def main() -> int:
    reference = os.environ.get("SOLC_REFERENCE")
    capture_dir = os.environ.get("SOLC_CAPTURE_DIR")
    if not reference or not capture_dir:
        print(
            "capture_solc.py requires SOLC_REFERENCE and SOLC_CAPTURE_DIR",
            file=sys.stderr,
        )
        return 2

    arguments = sys.argv[1:]
    if "--standard-json" not in arguments:
        os.execv(reference, [reference, *arguments])
        raise AssertionError("execv unexpectedly returned")

    request = sys.stdin.buffer.read()
    write_capture(Path(capture_dir), request)
    completed = subprocess.run(
        [reference, *arguments],
        input=request,
        check=False,
        stdout=sys.stdout.buffer,
        stderr=sys.stderr.buffer,
    )
    return completed.returncode


if __name__ == "__main__":
    sys.exit(main())
