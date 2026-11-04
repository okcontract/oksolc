#!/usr/bin/env python3
"""Named, memory-bounded compiler proof checks using the existing acceptance tools.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
from contextlib import contextmanager
import fcntl
import importlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

import bounded_run
import check_compiler as gate
import check_native_map_memory as native
import check_word_swap as physical
from lean_control_matrix import ControlPlan


# Each root includes its attachment tests and production-facing proof clients.
# The adapters own the declaration inventory, interface pins and control sources.
TARGETS = {
    "hash": ("native_wyhash_memory_checks", "--wyhash-hash"),
    "map-publication": ("native_map_search_checks", "--receiver-search"),
}
PINNED_BIN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.29.0/bin"


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def resolve_tools(args):
    lean_bin = args.lean_bin or (PINNED_BIN if PINNED_BIN.is_dir() else None)
    env, sysroot, tools = gate.source.toolchain(lean_bin, 4)
    zig = args.zig or shutil.which("zig")
    if zig is None:
        raise ValueError("Zig is required; supply --zig")
    zig = Path(zig).resolve()
    version = subprocess.run([str(zig), "version"], capture_output=True, check=True, timeout=30)
    if version.stdout.decode().strip() != (gate.ROOT / ".zigversion").read_text().strip():
        raise ValueError("Zig version differs from .zigversion")
    lib = args.zig_lib_dir
    if lib is None:
        lib = gate.source.zig_library(zig)
    lib = lib.resolve()
    if not (lib / "std/hash/wyhash.zig").is_file():
        raise ValueError("invalid Zig library directory")
    return env, sysroot, tools, zig, lib


@contextmanager
def invocation_lock(path):
    """Exclude overlapping invocations of this entry point in one checkout."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError("another compiler proof check owns this checkout") from error
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def development(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.compiler-proof-development.v1", "status": "failed",
              "target": args.target, "assurance": "developmentOnly", "accepted": False,
              "freshKernelReplay": False, "nativeObservations": False,
              "wholeCompilerVerified": False}
    try:
        adapter = importlib.import_module(TARGETS[args.target][0])
        env, sysroot, tools, zig, lib = resolve_tools(args)
        before, std = gate.snapshot(), native.std_inputs(lib)
        zig_hash = gate.source.file_digest(zig)
        report.update(module=adapter.MODULE, claims=adapter.CLAIMS, inputs=before,
                      tools=tools, zigSha256=zig_hash, stdInputs=std)
        proof, artifacts = gate.prove.check_module(adapter.MODULE, lean_bin=sysroot / "bin",
            jobs=4, timeout=args.proof_timeout, profile=args.profile)
        proof_dir = output / "proof"
        proof_dir.mkdir()
        for name, data in artifacts.items():
            (proof_dir / name).write_bytes(data)
        if proof["status"] != "passed":
            raise ValueError("selected proof/client build failed; see proof/report.json")
        # A clean checkout must build the audit prerequisite as well as clients.
        gate.require_success(output, "audit-prerequisite",
            [tools["lake"]["path"], "--quiet", "--rehash", "build", "Contract.Check.Declarations"],
            env, args.proof_timeout, cwd=gate.ROOT / "lean")
        report["audit"] = physical.audit(output, env, tools["lean"]["path"], adapter.MODULE, adapter.CLAIMS)
        rows = json.loads((output / "audit.json").read_bytes())["claims"]
        report["boundaryAudit"] = adapter.audit(rows)
        report["auditControls"] = adapter.audit_controls(rows)
        report["interfaces"] = adapter.interfaces(output, env, tools["lean"]["path"])
        report["sourceBinding"] = adapter.source_binding(lib)
        report["sourceControls"] = adapter.source_controls(lib)
        plan = ControlPlan(output, env, tools["lean"]["path"])
        plan.seal(adapter.controls(output, env, plan))
        report["controls"], report["controlMatrix"] = plan.run(args.control_workers)
        if (before != gate.snapshot() or std != native.std_inputs(lib) or
                zig_hash != gate.source.file_digest(zig) or any(
                    gate.source.file_digest(Path(t["path"])) != t["sha256"] for t in tools.values())):
            raise ValueError("development inputs changed during the check")
        report["status"] = "passed"
    except BaseException as error:
        report["failure"] = {"kind": type(error).__name__, "message": str(error)}
        raise
    finally:
        write(output / "report.json", report)


def worker_command(args, output):
    common = ["--output", str(output), "--control-workers", str(args.control_workers),
              "--proof-timeout", str(args.proof_timeout)]
    for name in ("lean_bin", "zig", "zig_lib_dir"):
        value = getattr(args, name)
        if value is not None:
            common += ["--" + name.replace("_", "-"), str(value)]
    if getattr(args, "air_toolchain", None) is not None:
        common += ["--air-toolchain", str(args.air_toolchain)]
    if args.phase == "dev":
        return [sys.executable, str(Path(__file__).resolve()), args.target, "--worker", *common,
                *(["--profile"] if args.profile else [])]
    return [sys.executable, str(gate.ROOT / "test/lean/check_native_map_memory.py"),
            TARGETS[args.target][1], *common, *(["--preflight"] if args.phase == "preflight" else [])]


def run(args):
    output = args.output.resolve()
    report = {"schema": "oksolc.compiler-proof-run.v1", "status": "failed", "target": args.target,
              "phase": args.phase, "accepted": False, "wholeCompilerVerified": False}
    with invocation_lock(gate.ROOT / "lean/.lake/compiler-verification.lock"):
        output.mkdir(parents=True, exist_ok=False)
        try:
            _, sysroot, _, zig, lib = resolve_tools(args)
            args.lean_bin, args.zig, args.zig_lib_dir = sysroot / "bin", zig, lib
            command = worker_command(args, output / "check")
            receipt = bounded_run.run(command, output / "process", rss_mib=args.rss_mib,
                                      timeout=args.timeout)
            report["processReceiptSha256"] = gate.source.file_digest(output / "process/receipt.json")
            if receipt["status"] != "passed" or receipt["exitCode"] != 0:
                raise ValueError("bounded verification process failed; see process/receipt.json and logs")
            checked = json.loads((output / "check/report.json").read_bytes())
            expected = "preflight-passed" if args.phase == "preflight" else "passed"
            if checked["status"] != expected:
                raise ValueError("verification process did not produce a complete report")
            report.update(status="passed", checkReportSha256=gate.source.file_digest(output / "check/report.json"),
                          assurance="existingAcceptanceGate" if args.phase == "accept" else "developmentOnly")
        except BaseException as error:
            report["failure"] = {"kind": type(error).__name__, "message": str(error)}
            raise
        finally:
            write(output / "report.json", report)
    return report


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("target", choices=TARGETS)
    result.add_argument("--phase", choices=("dev", "preflight", "accept"), default="dev")
    result.add_argument("--output", type=Path, required=True, help="new evidence directory")
    result.add_argument("--lean-bin", type=Path)
    result.add_argument("--zig", type=Path)
    result.add_argument("--zig-lib-dir", type=Path)
    result.add_argument("--air-toolchain", type=Path, help="captured Zig toolchain report; required for hash preflight/accept")
    result.add_argument("--control-workers", type=int, choices=range(1, 5), default=2)
    result.add_argument("--proof-timeout", type=int, default=600)
    result.add_argument("--rss-mib", type=int, default=8192)
    result.add_argument("--timeout", type=int, default=3600, help="aggregate wall-clock limit")
    result.add_argument("--profile", action="store_true", help="dev only: profile the entire selected module")
    result.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    return result


def main():
    options = parser()
    args = options.parse_args()
    if min(args.rss_mib, args.timeout, args.proof_timeout) <= 0 or (args.profile and args.phase != "dev"):
        options.error("positive limits required; profiling is development-only")
    try:
        if args.worker:
            development(args)
        else:
            run(args)
        print(f"{args.target}: {args.phase} passed; report: {args.output / 'report.json'}")
        return 0
    except (Exception, KeyboardInterrupt) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
