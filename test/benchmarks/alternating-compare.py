#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2014-2026 The Solidity Authors.
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Benchmark two immutable solidity-zig executables in balanced alternating order."""

import argparse
import hashlib
import json
import os
import platform
import statistics
import sys
import tempfile
import time
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run_compiler(binary: Path, request: Path, jobs: int) -> dict[str, float | int]:
    arguments = [str(binary), "standard-json"]
    if jobs != 1:
        arguments.extend(("--parallel", "--jobs", str(jobs)))
    arguments.append("-")

    with request.open("rb") as standard_json, open(os.devnull, "wb") as discard, tempfile.TemporaryFile() as errors:
        started = time.perf_counter()
        pid = os.fork()
        if pid == 0:
            try:
                os.chdir(tempfile.gettempdir())
                os.dup2(standard_json.fileno(), 0)
                os.dup2(discard.fileno(), 1)
                os.dup2(errors.fileno(), 2)
                os.execv(binary, arguments)
            except BaseException:
                os._exit(127)

        _, status, usage = os.wait4(pid, 0)
        wall_seconds = time.perf_counter() - started
        if not os.WIFEXITED(status) or os.WEXITSTATUS(status) != 0:
            errors.seek(0)
            diagnostic = errors.read().decode("utf-8", errors="replace")
            raise RuntimeError(f"compiler failed ({status}): {diagnostic}")

    rss_scale = 1 if sys.platform == "darwin" else 1024
    return {
        "wall_seconds": wall_seconds,
        "max_rss_bytes": usage.ru_maxrss * rss_scale,
    }


def summary(samples: list[dict[str, float | int]]) -> dict[str, float | int]:
    walls = [float(sample["wall_seconds"]) for sample in samples]
    rss = [int(sample["max_rss_bytes"]) for sample in samples]
    return {
        "runs": len(samples),
        "wall_median_seconds": statistics.median(walls),
        "wall_mean_seconds": statistics.mean(walls),
        "wall_stdev_seconds": statistics.stdev(walls) if len(walls) > 1 else 0.0,
        "wall_min_seconds": min(walls),
        "wall_max_seconds": max(walls),
        "rss_median_bytes": int(statistics.median(rss)),
        "rss_max_bytes": max(rss),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--baseline-label", default="Baseline")
    parser.add_argument("--candidate-label", default="Candidate")
    parser.add_argument("--request", action="append", nargs=2, metavar=("NAME", "PATH"), required=True)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--start", choices=("baseline", "candidate"), default="baseline")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    if args.jobs < 1 or args.runs < 1 or args.warmups < 0:
        parser.error("jobs and runs must be positive; warmups must be nonnegative")

    binaries = {
        "baseline": args.baseline.resolve(),
        "candidate": args.candidate.resolve(),
    }
    initial_hashes = {name: sha256(path) for name, path in binaries.items()}
    if initial_hashes["baseline"] == initial_hashes["candidate"]:
        raise RuntimeError("Baseline and Candidate executables have identical SHA-256 hashes")

    report = {
        "schema": 1,
        "generated_unix_seconds": time.time(),
        "platform": platform.platform(),
        "jobs": args.jobs,
        "runs": args.runs,
        "warmups": args.warmups,
        "order_strategy": "alternating pair order: AB, BA",
        "variant_labels": {
            "baseline": args.baseline_label,
            "candidate": args.candidate_label,
        },
        "working_directory": tempfile.gettempdir(),
        "binaries": {
            name: {"path": str(path), "sha256_before": initial_hashes[name]}
            for name, path in binaries.items()
        },
        "workloads": {},
    }

    first = args.start
    second = "candidate" if first == "baseline" else "baseline"
    for workload_name, request_input in args.request:
        request = Path(request_input).resolve()
        workload = {
            "request_path": str(request),
            "request_sha256": sha256(request),
            "samples": {"baseline": [], "candidate": []},
            "invocation_order": [],
        }

        for warmup_index in range(args.warmups):
            warmup_order = (second, first) if warmup_index % 2 == 0 else (first, second)
            for variant in warmup_order:
                if sha256(binaries[variant]) != initial_hashes[variant]:
                    raise RuntimeError(f"{variant} executable changed before warmup")
                run_compiler(binaries[variant], request, args.jobs)

        for pair_index in range(args.runs):
            order = (first, second) if pair_index % 2 == 0 else (second, first)
            for variant in order:
                if sha256(binaries[variant]) != initial_hashes[variant]:
                    raise RuntimeError(f"{variant} executable changed before measurement")
                sample = run_compiler(binaries[variant], request, args.jobs)
                sample["pair"] = pair_index + 1
                sample["position"] = len(workload["invocation_order"]) + 1
                workload["samples"][variant].append(sample)
                workload["invocation_order"].append(variant)

        workload["summary"] = {
            variant: summary(workload["samples"][variant]) for variant in binaries
        }
        baseline_median = workload["summary"]["baseline"]["wall_median_seconds"]
        candidate_median = workload["summary"]["candidate"]["wall_median_seconds"]
        workload["candidate_over_baseline"] = candidate_median / baseline_median
        report["workloads"][workload_name] = workload

    for name, path in binaries.items():
        final_hash = sha256(path)
        report["binaries"][name]["sha256_after"] = final_hash
        if final_hash != initial_hashes[name]:
            raise RuntimeError(f"{name} executable changed during measurement")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    print(
        f"| Workload | Jobs | {args.baseline_label} median | "
        f"{args.candidate_label} median | {args.candidate_label}/{args.baseline_label} |"
    )
    print("|---|---:|---:|---:|---:|")
    for name, workload in report["workloads"].items():
        baseline = workload["summary"]["baseline"]["wall_median_seconds"]
        candidate = workload["summary"]["candidate"]["wall_median_seconds"]
        print(f"| `{name}` | {args.jobs} | {baseline:.4f} s | {candidate:.4f} s | {candidate / baseline:.4f}x |")
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
