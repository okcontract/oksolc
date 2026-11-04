#!/usr/bin/env python3
"""Bounded JSON, process execution and artifact helpers for compiler verification.
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MAX_INPUT = 16 * 1024 * 1024
MAX_OUTPUT = 64 * 1024 * 1024
DRIVER_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class BuildError(Exception):
    def __init__(self, category, message):
        super().__init__(message)
        self.category = category


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
                       allow_nan=False) + "\n").encode()


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def identity(kind, data):
    return {"algorithm": "sha256", "domain": "oksolc.lean." + kind + ".v1",
            "digest": sha256(("oksolc.lean." + kind + ".v1\0").encode() + data)}


def decode_json(data):
    def object_pairs(pairs):
        obj = {}
        for key, value in pairs:
            if key in obj:
                raise BuildError("invalidJson", f"duplicate JSON key: {key}")
            obj[key] = value
        return obj

    def nonfinite(value):
        raise BuildError("invalidJson", f"non-finite JSON number: {value}")

    try:
        return json.loads(data, object_pairs_hook=object_pairs, parse_constant=nonfinite)
    except (ValueError, UnicodeError, RecursionError) as error:
        raise BuildError("invalidJson", str(error)) from error


def read_bounded(path, maximum):
    with path.open("rb") as source:
        data = source.read(maximum + 1)
    if len(data) > maximum:
        raise BuildError("resourceLimit", f"input exceeds {maximum} bytes: {path.name}")
    return data


def invoke(command, data, timeout, *, cwd=None, env=None):
    # File-backed output avoids unbounded buffering from a malformed child.
    with tempfile.TemporaryFile() as inp, tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        inp.write(data)
        inp.seek(0)
        child = subprocess.Popen(command, stdin=inp, stdout=out, stderr=err,
                                 start_new_session=True, cwd=cwd, env=env)
        try:
            child.wait(timeout=timeout)
        except BaseException:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            finally:
                child.wait()
            raise
        if out.tell() > MAX_OUTPUT or err.tell() > MAX_OUTPUT:
            raise BuildError("resourceLimit", "backend output limit exceeded")
        out.seek(0)
        err.seek(0)
        stdout, stderr = out.read(), err.read()
        if child.returncode:
            diagnostic = stderr + (b"\n" if stderr and stdout else b"") + stdout
            raise BuildError("backendFailure", diagnostic.decode(errors="replace")[:4000])
        return stdout, stderr


def publish(output, artifacts):
    if output.exists() or output.is_symlink():
        raise BuildError("outputExists", "output directory already exists; choose a new directory")
    output.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".lean-bundle-", dir=output.parent))
    try:
        for name, data in artifacts.items():
            (staging / name).write_bytes(data)
        # Same filesystem: readers see either no bundle or the complete directory.
        staging.rename(output)
    finally:
        if staging.exists():
            shutil.rmtree(staging)
