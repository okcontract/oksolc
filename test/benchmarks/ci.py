#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Compile each CI benchmark once, measuring and validating the same invocation."""

import argparse
from dataclasses import asdict
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

import compare


BENCHMARK_DIR = Path(__file__).resolve().parent
MANIFEST = BENCHMARK_DIR / "ci-manifest.json"


def benchmark_request(command, request_path, expected_hash, work_dir):
    stdout_path = work_dir / "stdout.json"
    stderr_path = work_dir / "stderr.txt"
    sample = compare.measure_invocation(
        command, request_path, stdout_path=stdout_path, stderr_path=stderr_path
    )
    result = {
        "measurement": asdict(sample),
        "expected_contract_output_sha256": expected_hash,
        "status": "failed",
    }
    try:
        if sample.exit_code != 0:
            raise RuntimeError(
                f"oksolc exited with {sample.exit_code}: "
                + stderr_path.read_text(errors="replace").strip()
            )
        output = compare.parse_output("oksolc", stdout_path.read_bytes())
        errors = compare.compiler_errors(output)
        if errors:
            raise RuntimeError("compiler errors: " + "\n".join(errors))
        artifacts = compare.contract_output(output)
        if not artifacts or not any(artifacts.values()):
            raise RuntimeError("oksolc emitted no contract bytecode")
        actual_hash = compare.contract_output_sha256(artifacts)
        result["contract_output_sha256"] = actual_hash
        if actual_hash != expected_hash:
            raise RuntimeError(
                f"contract-output SHA256 changed: expected {expected_hash}, got {actual_hash}"
            )
        result["status"] = "passed"
    except (OSError, RuntimeError, ValueError) as error:
        result["error"] = str(error)
    return result


def markdown_report(report):
    lines = [
        "## External benchmarks",
        "",
        f"oksolc only; {report['protocol']['jobs']} compiler jobs; one compilation per "
        "project; no warmups; persistent compiler cache disabled.",
        "Time includes process startup and JSON output; validation runs afterward.",
        "Performance is informational; compilation and bytecode checks must pass.",
        "",
        "| Benchmark | Wall time | CPU time | Peak RAM | Validation |",
        "| --- | ---: | ---: | ---: | --- |",
    ]
    for name, result in report["benchmarks"].items():
        sample = result.get("measurement")
        if sample:
            cpu = sample["user_seconds"] + sample["system_seconds"]
            lines.append(
                f"| {name} | {sample['wall_seconds']:.2f} s | {cpu:.2f} s | "
                f"{sample['peak_rss_mib']:.0f} MiB | {result['status']} |"
            )
        else:
            lines.append(f"| {name} | — | — | — | {result['status']} |")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-solc", default="zig-out/bin/oksolc")
    parser.add_argument("--jobs", type=compare.positive_int, default=2)
    parser.add_argument(
        "--output-dir", type=Path,
        default=compare.REPO_ROOT / "build/benchmarks/ci",
    )
    options = parser.parse_args()
    try:
        manifest = json.loads(MANIFEST.read_text())
        if not manifest["requests"]:
            raise RuntimeError("CI benchmark manifest contains no requests")
        compiler = compare.resolve_executable(options.zig_solc)
        version = compare.compiler_version((str(compiler), "--version"))
        if compare.EXPECTED_ZIG_VERSION not in version:
            raise RuntimeError(f"unexpected compiler version: {version}")
        command = [str(compiler), "standard-json", "--no-cache"]
        if options.jobs > 1:
            command.extend(("--parallel", "--jobs", str(options.jobs)))
        command.append("-")
        report = {
            "schema_version": 1,
            "started_at": datetime.now(timezone.utc).isoformat(),
            "compiler_version": version,
            "reference_compiler": manifest["reference_compiler"],
            "command": command,
            "machine": {
                "platform": platform.platform(),
                "architecture": platform.machine(),
                "cpu_count": os.cpu_count(),
                "runner_image": os.environ.get("ImageOS"),
                "runner_image_version": os.environ.get("ImageVersion"),
            },
            "protocol": {
                "runs": 1, "warmups": 0, "jobs": options.jobs,
                "persistent_cache": False,
                "time": "whole compiler process, including JSON output to a file",
                "ram": "child process peak RSS from wait4, in MiB",
                "validation": "measured output checked after timing",
            },
            "benchmarks": {},
        }
        with tempfile.TemporaryDirectory(prefix="oksolc-ci-benchmarks-") as temp:
            work_dir = Path(temp)
            for name, expected in manifest["requests"].items():
                print(f"Benchmarking {name} ({options.jobs} jobs)...", flush=True)
                request_hash = None
                try:
                    request_path = work_dir / "request.json"
                    archive = BENCHMARK_DIR / "external-requests" / f"{name}.json.zst"
                    with request_path.open("wb") as request:
                        subprocess.run(
                            ["zstd", "-qdc", str(archive)], stdout=request, check=True
                        )
                    request_hash = compare.file_sha256(request_path)
                    if request_hash != expected["request_sha256"]:
                        raise RuntimeError("request SHA256 differs from the frozen baseline")
                    result = benchmark_request(
                        command, request_path, expected["contract_output_sha256"], work_dir
                    )
                except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
                    result = {"status": "failed", "error": str(error)}
                result["request_sha256"] = request_hash
                result["expected_request_sha256"] = expected["request_sha256"]
                report["benchmarks"][name] = result
                if "error" in result:
                    print(f"{name}: {result['error']}", file=sys.stderr, flush=True)
        report["provenance"] = {
            "source": compare.verified_source_provenance(compare.SOURCE_PROVENANCE_BEFORE),
            "executable": compare.executable_provenance(compiler),
        }
        report["completed_at"] = datetime.now(timezone.utc).isoformat()
        summary = markdown_report(report)
        compare.atomic_json_write(options.output_dir / "results.json", report)
        (options.output_dir / "summary.md").write_text(summary)
        print(summary, end="")
        return int(any(
            result["status"] != "passed" for result in report["benchmarks"].values()
        ))
    except (OSError, RuntimeError, ValueError) as error:
        print(f"benchmark error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
