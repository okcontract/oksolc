#!/usr/bin/env python3
"""Pinned Lean tools and complete proof-input identities for compiler verification.
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil

from common import BuildError, ROOT, invoke, sha256

LEAN_ROOT = ROOT / "lean"
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")
DRIVER_SHA256 = sha256(Path(__file__).read_bytes())


def zig_library(zig=None):
    """Locate the installed pinned library without assuming a Zig source checkout."""
    zig = zig or shutil.which("zig")
    if zig is None:
        raise BuildError("missingToolchain", "Zig is required to locate its standard library")
    version, stderr = invoke([str(zig), "version"], b"", 30, cwd=ROOT)
    if stderr.strip() or version.decode().strip() != (ROOT / ".zigversion").read_text().strip():
        raise BuildError("unsupportedToolchain", "Zig version differs from .zigversion")
    observed, stderr = invoke([str(zig), "env"], b"", 30, cwd=ROOT)
    match = re.search(rb'^    \.lib_dir = ("(?:[^"\\]|\\.)*"),$', observed, re.M)
    if stderr.strip() or not match:
        raise BuildError("unsupportedToolchain", "cannot locate Zig's standard library")
    library = Path(json.loads(match[1])).resolve()
    if not (library / "std/sort.zig").is_file():
        raise BuildError("unsupportedToolchain", "invalid Zig standard-library directory")
    return library


def file_digest(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest() if hasattr(hashlib, "file_digest") else stream_digest(handle)


def stream_digest(handle):
    digest = hashlib.sha256()
    for block in iter(lambda: handle.read(1024 * 1024), b""):
        digest.update(block)
    return digest.hexdigest()


def source_inputs():
    paths = [p for p in LEAN_ROOT.rglob("*.lean") if ".lake" not in p.parts]
    paths += [LEAN_ROOT / "lean-toolchain", LEAN_ROOT / "lake-manifest.json"]
    return {str(p.relative_to(LEAN_ROOT)): file_digest(p) for p in sorted(paths)}


def toolchain(lean_bin, jobs):
    env = dict(os.environ)
    env.pop("LEAN_SYSROOT", None)
    if lean_bin:
        env["PATH"] = str(lean_bin.resolve()) + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = str(jobs)
    lean = shutil.which("lean", path=env["PATH"])
    lake = shutil.which("lake", path=env["PATH"])
    if not lean or not lake:
        raise BuildError("missingToolchain", "Lean and Lake must be installed before checking")
    version, stderr = invoke([lean, "--version"], b"", 30, cwd=LEAN_ROOT, env=env)
    if stderr.strip() or "version 4.29.0," not in version.decode():
        raise BuildError("unsupportedToolchain", "expected installed Lean 4.29.0")
    prefix, stderr = invoke([lean, "--print-prefix"], b"", 30, cwd=LEAN_ROOT, env=env)
    if stderr.strip():
        raise BuildError("unsupportedToolchain", "cannot locate Lean toolchain")
    sysroot = Path(prefix.decode().strip()).resolve()
    # Use the actual pinned binaries, not an elan proxy or a PATH replacement.
    binaries = {"lean": sysroot / "bin/lean", "lake": sysroot / "bin/lake"}
    env["PATH"] = str(sysroot / "bin") + os.pathsep + env["PATH"]
    env["LEAN_PATH"] = str(LEAN_ROOT / ".lake/build/lib/lean")
    env["LEAN_SRC_PATH"] = os.pathsep.join(map(str, [LEAN_ROOT, sysroot / "src/lean/lake", sysroot / "src/lean"]))
    return env, sysroot, {key: {"path": str(path), "sha256": file_digest(path)} for key, path in binaries.items()}
