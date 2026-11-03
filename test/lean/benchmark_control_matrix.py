#!/usr/bin/env python3
"""Paired measurements of the complete native-constructor control matrix.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Run against an already built Lean library, with no other Lean jobs active.
This is a scheduling benchmark, not verification acceptance: the production
gate must still audit statements and perform fresh kernel replay separately.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys
import time

import check_native_invocation as gate
import native_constructor_checks as constructors
from build_toolchain import digest, write_json

ROOT = Path(__file__).resolve().parents[2]
PARITY_FIELDS = ("name", "expectedAcceptance", "sourceSha256", "exitCode",
                 "stdoutSha256", "stderrSha256", "status")


def interval(values):
    """Deterministic percentile bootstrap of a paired mean; raw pairs retained."""
    rng = random.Random(20260925)
    draws = sorted(statistics.mean(rng.choices(values, k=len(values))) for _ in range(10000))
    return {"mean": statistics.mean(values), "paired95PercentBootstrap": [draws[249], draws[9749]]}


def snapshot(tools):
    cache = ROOT / "lean/.lake/build/lib/lean"
    return {"python": gate.python_inputs.inputs(), "lean": gate.harness.lean_check.source_inputs(),
            "native": gate.source_gate.inputs(),
            "tools": {name: {"path": item["path"], "sha256": digest(Path(item["path"]))}
                      for name, item in tools.items()},
            "cachedLibrary": {str(p.relative_to(cache)): digest(p) for p in sorted(cache.rglob("*"))
                              if p.is_file() and p.suffix != ".trace"}}


def parity(reference, actual):
    """Compare complete ordered results; a matching first error is insufficient."""
    if len(reference) != len(actual):
        raise ValueError("control parity: missing or extra controls")
    for index, (before, after) in enumerate(zip(reference, actual)):
        for field in PARITY_FIELDS:
            if before[field] != after[field]:
                raise ValueError(f"control parity at {index} {before['name']}: {field}")


def worker(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env, _, tools = gate.harness.lean_check.toolchain(args.lean_bin, 4)
    frozen = json.loads(args.frozen.read_bytes())
    if snapshot(tools) != frozen:
        raise ValueError("benchmark inputs changed before sample")
    plan = gate.control_plan(output, env, tools["lean"]["path"], constructors)
    report = {"status": "failed", "freshKernelReplay": False}
    try:
        report["controls"], report["matrix"] = plan.run(args.worker_jobs)
        if snapshot(tools) != frozen:
            raise ValueError("benchmark inputs changed during sample")
        report["status"] = "passed"
    finally:
        write_json(output / "report.json", report)


def sample(args, name, workers):
    """One isolated worker; wait4 reaps it and records per-sample resources.

    maxrss is the OS-reported high-water statistic, not a sampled sum of
    concurrent resident sets. Keep that distinction in the evidence schema.
    All raw streams and the terminal receipt are retained before assertions.
    """
    output = args.output / name
    command = [sys.executable, str(Path(__file__).resolve()), "--lean-bin", str(args.lean_bin),
               "--output", str(output), "--worker-jobs", str(workers),
               "--frozen", str(args.output / "inputs.json")]
    started = time.monotonic()
    with (args.output / (name + ".stdout")).open("wb") as out, (args.output / (name + ".stderr")).open("wb") as err:
        child = subprocess.Popen(command, stdout=out, stderr=err)
        try:
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
        except BaseException:
            # Let the worker unwind its executor and join started Lean processes.
            child.send_signal(2)
            child.wait()
            raise
    receipt = {"command": command, "exitCode": child.returncode,
               "wallSecondsIncludingCollectionAndRehash": time.monotonic() - started,
               "cpuSecondsIncludingCollectionAndRehash": usage.ru_utime + usage.ru_stime,
               "osReportedMaxRssBytes": usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
               "stdoutSha256": digest(args.output / (name + ".stdout")),
               "stderrSha256": digest(args.output / (name + ".stderr"))}
    write_json(args.output / (name + ".receipt.json"), receipt)
    if child.returncode != 0:
        raise ValueError("benchmark sample failed: " + name)
    report = json.loads((output / "report.json").read_bytes())
    if report["status"] != "passed" or report["matrix"]["status"] != "passed":
        raise ValueError("benchmark sample incomplete: " + name)
    return report, receipt


def benchmark(args):
    if args.samples < 3:
        raise ValueError("request at least three interleaved pairs")
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    _, _, tools = gate.harness.lean_check.toolchain(args.lean_bin, 4)
    frozen = snapshot(tools)
    write_json(args.output / "inputs.json", frozen)
    report = {"schema": "oksolc.control-scheduling-benchmark.v1", "status": "failed",
              "freshKernelReplay": False, "host": platform.platform(),
              "cachePolicy": "existing library, frozen bytes, no cache clearing",
              "inputsSha256": digest(args.output / "inputs.json"),
              "memoryScope": "OS wait4 maxrss per worker; not aggregate concurrent RSS",
              "pairs": []}
    reference = None
    reference_plan = None
    try:
        for index in range(args.samples):
            pair = {"index": index, "order": [1, 4] if index % 2 == 0 else [4, 1], "runs": {}}
            report["pairs"].append(pair)
            for workers in pair["order"]:
                name = f"pair-{index}-jobs-{workers}"
                result, receipt = sample(args, name, workers)
                plan = (args.output / name / "control-plan.json").read_bytes()
                if reference is None:
                    reference, reference_plan = result["controls"], plan
                parity(reference, result["controls"])
                if plan != reference_plan:
                    raise ValueError("control source/validator plan changed: " + name)
                pair["runs"][str(workers)] = {"directory": name, "receipt": receipt,
                    "matrixSeconds": result["matrix"]["seconds"],
                    "childCpuSeconds": result["matrix"]["childUserSeconds"] + result["matrix"]["childSystemSeconds"],
                    "reportSha256": digest(args.output / name / "report.json"),
                    "planSha256": digest(args.output / name / "control-plan.json")}
                write_json(args.output / "report.json", report)
                print(json.dumps({"sample": name, "status": "passed", "parity": True,
                                  "seconds": result["matrix"]["seconds"]}), flush=True)
        if snapshot(tools) != frozen:
            raise ValueError("benchmark inputs changed after samples")
        report["controls"] = len(reference)
        report["positiveControls"] = sum(r["expectedAcceptance"] for r in reference)
        report["exactResultAndDiagnosticParity"] = True
        report["pairedSpeedup"] = interval([p["runs"]["1"]["matrixSeconds"] / p["runs"]["4"]["matrixSeconds"]
                                           for p in report["pairs"]])
        report["pairedSecondsSaved"] = interval([p["runs"]["1"]["matrixSeconds"] - p["runs"]["4"]["matrixSeconds"]
                                                for p in report["pairs"]])
        report["status"] = "passed"
    finally:
        write_json(args.output / "report.json", report)
    print(json.dumps({key: report[key] for key in ("status", "controls", "pairedSpeedup", "pairedSecondsSaved")}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--worker-jobs", type=int, choices=(1, 4), help=argparse.SUPPRESS)
    parser.add_argument("--frozen", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker_jobs:
        if args.frozen is None:
            parser.error("worker requires frozen inputs")
        worker(args)
    else:
        benchmark(args)
