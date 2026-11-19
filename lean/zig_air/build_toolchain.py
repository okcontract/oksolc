#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Build an isolated LLVM-enabled Zig 0.17 toolchain for semantic extraction.
// Copyright (C) 2026 OKcontract Pte. Ltd.

The original Zig checkout is read-only. Raw command results and a manifest stay
in the requested new output directory. A successful build is not a compiler
correctness claim or a complete external-toolchain reproducibility claim.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import signal
import subprocess
import tarfile
import time

REVISION = "7647adab80dd088f4de3610fd245915a912eb6ad"
VERSION = "0.17.0"


def digest(path):
    sha = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            sha.update(block)
    return sha.hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def run(output, name, command, *, cwd=None, timeout=1800, env=None):
    """Retain streams and terminal status even on cancellation or failure."""
    command = list(map(str, command))
    record = {"command": command, "cwd": str(cwd or Path.cwd()), "status": "failed"}
    started = time.monotonic()
    try:
        with (output / (name + ".stdout")).open("wb") as out, (output / (name + ".stderr")).open("wb") as err:
            child = subprocess.Popen(command, cwd=cwd, env=env, stdout=out, stderr=err, start_new_session=True)
            try:
                record["exitCode"] = child.wait(timeout=timeout)
            except BaseException as error:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                record["exitCode"] = child.wait()
                record["error"] = type(error).__name__
                raise
        record["status"] = "completed"
    finally:
        record["seconds"] = time.monotonic() - started
        write_json(output / (name + ".process.json"), record)
    if record["exitCode"] != 0:
        raise ValueError(name + " failed; inspect its retained stdout/stderr")


def text(output, name):
    path = output / (name + ".stdout")
    if path.stat().st_size > 1024 * 1024:
        raise ValueError(name + ": diagnostic output exceeds limit")
    return path.read_text().strip()


def record_build_diagnostics(output, report):
    # The pinned Step.make appends the peak-RSS diagnostic without returning
    # MakeFailed. A zero exit status therefore does not mean clean diagnostics.
    stderr = output / "build.stderr"
    report["buildDiagnostics"] = {"bytes": stderr.stat().st_size, "sha256": digest(stderr)}
    report["status"] = "built-with-diagnostics" if stderr.stat().st_size else "built"
    if b"error:" in stderr.read_bytes():
        report["status"] = "failed"
        raise ValueError("Zig build reported an error despite its zero exit status; inspect build.stderr")


def check_checkout(output, tree, label):
    run(output, label + "-revision", ["git", "-C", tree, "rev-parse", "HEAD"])
    if text(output, label + "-revision") != REVISION:
        raise ValueError("Zig checkout is not the pinned 0.17 revision")
    run(output, label + "-status", ["git", "-C", tree, "status", "--porcelain", "--untracked-files=normal"])
    if text(output, label + "-status"):
        raise ValueError("Zig checkout has local changes; original sources are never modified")


def unpack(archive, destination):
    """The pinned Git archive has regular files and directories, no links."""
    with tarfile.open(archive) as source:
        members = source.getmembers()
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or ".." in path.parts or not path.parts or not (member.isfile() or member.isdir()):
                raise ValueError("unsafe or unsupported source archive member: " + member.name)
        source.extractall(destination, members=members)


def source_identity(tree):
    entries = {}
    for path in sorted(tree.rglob("*")):
        if path.is_symlink():
            raise ValueError("unexpected link in isolated source tree: " + str(path))
        if path.is_file():
            entries[path.relative_to(tree).as_posix()] = digest(path)
    encoded = json.dumps(entries, sort_keys=True, separators=(",", ":")).encode()
    return {"files": len(entries), "sha256": hashlib.sha256(encoded).hexdigest()}


def link_system_libcpp(source, library):
    """Use the SDK C++ ABI used by system LLVM; never modify Zig semantics."""
    build_file = source / "build.zig"
    original = build_file.read_text()
    # The pinned macOS branch sets link_libcpp even when use-zig-libcxx is
    # false. That requests Zig's bundled C++ library, not the SDK library.
    old = """            .driverkit, .ios, .maccatalyst, .macos, .tvos, .visionos, .watchos => {
                mod.link_libcpp = true;
            },"""
    new = old.replace("mod.link_libcpp = true;", "mod.addObjectFile(.{ .cwd_relative = " +
                      json.dumps(str(library)) + " });")
    if original.count(old) != 1:
        raise ValueError("pinned system C++ build configuration changed")
    before = digest(build_file)
    build_file.write_text(original.replace(old, new))
    return {"file": "build.zig", "beforeSha256": before, "afterSha256": digest(build_file),
            "library": str(library), "librarySha256": digest(library)}


def build(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.zig-air-toolchain.v1", "status": "failed", "zigRevision": REVISION,
              "jobs": args.jobs, "buildMode": "ReleaseFast", "compilerVerified": False,
              "compilerDebugInfo": "stripped", "compilerBuildMemoryLimitBytes": 8_000_000_000,
              "externalToolchainClosureComplete": False, "semanticExportImplemented": False}
    try:
        tree, bootstrap = args.zig_tree.resolve(), args.bootstrap.resolve()
        llvm, lld = args.llvm_prefix.resolve(), args.lld_prefix.resolve()
        check_checkout(output, tree, "before")
        run(output, "bootstrap-version", [bootstrap, "version"])
        if text(output, "bootstrap-version") != VERSION:
            raise ValueError("bootstrap Zig must be exactly " + VERSION)
        report["bootstrap"] = {"path": str(bootstrap), "sha256": digest(bootstrap), "version": VERSION}
        run(output, "llvm-version", [llvm / "bin/llvm-config", "--version"])
        if not text(output, "llvm-version").startswith("22."):
            raise ValueError("pinned Zig requires LLVM 22.x")
        report["llvm"] = {"prefix": str(llvm), "version": text(output, "llvm-version"), "lldPrefix": str(lld)}
        archive, source = output / "source.tar", output / "source"
        run(output, "archive", ["git", "-C", tree, "archive", "--format=tar", "--output=" + str(archive), REVISION])
        report["sourceArchiveSha256"] = digest(archive)
        unpack(archive, source)
        report["upstreamSourceTree"] = source_identity(source)
        if args.system_libcpp:
            report["systemCppLinkPatch"] = link_system_libcpp(source, args.system_libcpp.resolve())
        if args.fresh_air:
            import patch_toolchain
            report["freshAirCapturePatch"] = patch_toolchain.apply(source)
            report["freshAirCaptureImplemented"] = True
        before = source_identity(source)
        report["sourceTree"] = before
        cmake_dir, install = output / "cmake", output / "install"
        run(output, "configure", [args.cmake, "-S", source, "-B", cmake_dir, "-G", args.cmake_generator,
            "-DCMAKE_BUILD_TYPE=Release", "-DZIG_SHARED_LLVM=ON",
            "-DCMAKE_PREFIX_PATH=" + str(llvm) + ";" + str(lld)])
        run(output, "zigcpp", [args.cmake, "--build", cmake_dir, "--target", "zigcpp", "--parallel", str(args.jobs)])
        config = cmake_dir / "config.h"
        report["configSha256"] = digest(config)
        build_env = dict(os.environ, ZIG_LIB_DIR=str(source / "lib"),
                         ZIG_GLOBAL_CACHE_DIR=str(output / "global-cache"))
        search_prefixes = [path.resolve(strict=True) for path in args.search_prefix]
        if any(not path.is_dir() for path in search_prefixes):
            raise ValueError("build search prefixes must be existing directories")
        report["buildSearchPrefixes"] = list(map(str, search_prefixes))
        run(output, "build", [bootstrap, "build", "-j" + str(args.jobs),
            # Debug information for the capture executable is unnecessary;
            # target source locations and AIR still follow each capture's mode.
            # Keep Zig's own 8 GB build limit rather than raising it.
            "-Doptimize=ReleaseFast", "-Dstrip=true", "-Dversion-string=" + VERSION, "-Denable-llvm",
            "-Dconfig_h=" + str(config), "-Dno-lib", "-Dno-langref",
            *[part for path in search_prefixes for part in ("--search-prefix", path)],
            "--cache-dir", output / "zig-cache", "--prefix", install], cwd=source, env=build_env)
        record_build_diagnostics(output, report)
        compiler = install / "bin/zig"
        run(output, "compiler-version", [compiler, "version"])
        if text(output, "compiler-version") != VERSION:
            raise ValueError("built Zig has an unexpected version")
        # Compiling through LLVM is necessary: an LLVM-disabled binary would
        # change builtin.zig_backend in the program we intend to extract.
        fixture = output / "smoke.zig"
        fixture.write_text("// Copyright (C) 2026 OKcontract Pte. Ltd.\n"
                           "export fn add_wrapping(x: u32, y: u32) u32 { return x +% y; }\n")
        for label, executable in (("baseline", bootstrap), ("rebuilt", compiler)):
            run(output, label + "-llvm-smoke", [executable, "build-obj", "--zig-lib-dir", source / "lib",
                "-fllvm", "-OReleaseFast", "-fstrip", fixture, "-femit-bin=" + str(output / (label + ".o")),
                "--cache-dir", output / (label + "-cache"), "--global-cache-dir", output / "global-cache"])
        smoke = {label: digest(output / (label + ".o")) for label in ("baseline", "rebuilt")}
        report["llvmSmokeObjects"] = smoke
        if smoke["baseline"] != smoke["rebuilt"]:
            raise ValueError("LLVM smoke object differs from the installed pinned compiler")
        check_checkout(output, tree, "after")
        if before != source_identity(source) or report["bootstrap"]["sha256"] != digest(bootstrap):
            raise ValueError("toolchain inputs changed during the build")
        if args.system_libcpp and report["systemCppLinkPatch"]["librarySha256"] != digest(args.system_libcpp.resolve()):
            raise ValueError("system C++ link input changed during the build")
        report["compiler"] = {"path": str(compiler), "sha256": digest(compiler), "version": VERSION,
                              "zigLibDir": str(source / "lib")}
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-tree", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True, help="new directory; never reuse a previous run")
    parser.add_argument("--bootstrap", type=Path, required=True)
    parser.add_argument("--llvm-prefix", type=Path, required=True)
    parser.add_argument("--lld-prefix", type=Path, required=True)
    parser.add_argument("--cmake", default="cmake")
    parser.add_argument("--cmake-generator", choices=("Ninja", "Unix Makefiles"), default="Ninja")
    parser.add_argument("--system-libcpp", type=Path,
                        help="optional macOS SDK libc++.tbd; records the isolated build-only link patch")
    parser.add_argument("--search-prefix", type=Path, action="append", default=[],
                        help="explicit Zig build dependency prefix (e.g. LLVM's zstd); repeat as needed")
    parser.add_argument("--fresh-air", action="store_true", help="include the opt-in fresh AIR capture hooks")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    build(args)


if __name__ == "__main__":
    main()
