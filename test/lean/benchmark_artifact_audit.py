#!/usr/bin/env python3
"""Compare source and compiled audits of one retained, accepted proof batch.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

This measures only auditing; it never issues or renews artifact acceptance.
Keep raw paired samples, input hashes and complete diagnostic streams.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import resource
import statistics
import sys

import compiler_artifacts as artifacts


def fingerprint(package):
    # Include the compiled dependencies actually imported, not just their sources.
    return {str(p.relative_to(package)): artifacts.gate.source.file_digest(p)
            for p in sorted(package.rglob("*")) if p.is_file()}


def benchmark(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    result = {"schema": "oksolc.artifact-audit-benchmark.v1", "status": "failed",
              "assurance": "diagnosticOnly", "artifactAcceptance": False,
              "scope": "oneRetainedProofBatchAudit", "jobs": args.jobs, "pairs": []}
    try:
        raw = args.report.read_bytes()
        prior = json.loads(raw)
        if prior.get("status") != "passed" or prior.get("accepted") is not True:
            raise ValueError("an accepted artifact report is required")
        batch = prior["proofBatches"][args.batch]
        parent = args.report.resolve().parent
        directory = (parent / batch["directory"]).resolve()
        if not directory.is_relative_to(parent):
            raise ValueError("proof batch escapes the report directory")
        package = directory / "package/lean"
        if artifacts.package_inputs(package) != batch["packageInputs"]:
            raise ValueError("retained package source identities changed")
        code = (directory / "Artifact.lean").read_bytes()
        if artifacts.gate.digest(code) != batch["proofSourceSha256"]:
            raise ValueError("retained artifact source changed")
        # Resolve the single generated module from its source identity, not a filename convention.
        modules = [p for p, digest in batch["packageInputs"].items()
                   if digest == batch["proofSourceSha256"] and p.endswith(".lean")]
        if len(modules) != 1:
            raise ValueError("ambiguous generated module")
        module = modules[0][:-5].replace("/", ".")
        obj = package / (".lake/build/lib/lean/" + modules[0][:-5] + ".olean")
        if artifacts.gate.source.file_digest(obj) != batch["proofObjectSha256"]:
            raise ValueError("retained compiled artifact changed")
        expected_raw = (directory / "audit.stdout").read_bytes()
        schema = json.loads(expected_raw)["schema"]
        expected = artifacts.audit(expected_raw, batch["claims"], schema)
        audit_code = artifacts.compiled_audit_source(module, batch["claims"], schema)
        (output / "Audit.lean").write_bytes(audit_code)
        env, _, tools = artifacts.gate.source.toolchain(args.lean_bin, args.jobs)
        if any(tools[key]["sha256"] != prior["tools"][key]["sha256"] for key in tools):
            raise ValueError("benchmark toolchain differs from accepted package")
        env["LEAN_PATH"] = str(package / ".lake/build/lib/lean")
        env["LEAN_SRC_PATH"] = str(package)
        before = fingerprint(package)
        drivers = artifacts.gate.snapshot()
        tools["python"] = {"path": str(Path(sys.executable).resolve()),
                           "sha256": artifacts.gate.source.file_digest(Path(sys.executable))}
        result.update(reportSha256=hashlib.sha256(raw).hexdigest(), batch=args.batch, module=module,
                      tools=tools, packageInputs=before, driverInputs=drivers,
                      auditSourceSha256=artifacts.gate.digest(audit_code))
        for pair in range(args.pairs):
            sample = {}
            for mode in (("source", "compiled") if pair % 2 == 0 else ("compiled", "source")):
                name = f"pair-{pair}-{mode}"
                command = [tools["lean"]["path"], "-M4096", "-DwarningAsError=true"]
                command += [str(package / modules[0])] if mode == "source" else ["--stdin"]
                cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
                actual = artifacts.gate.require_success(output, name, command, env, args.timeout,
                    data=b"" if mode == "source" else audit_code, cwd=package)
                cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
                if artifacts.gate.read(output, name + ".stderr").strip():
                    raise ValueError("unexpected audit stderr")
                if artifacts.audit(actual, batch["claims"], schema) != expected:
                    raise ValueError("audit statements, dependency closure or axioms changed")
                receipt = json.loads((output / (name + ".process.json")).read_bytes())
                sample[mode] = {"seconds": receipt["seconds"], "stdoutSha256": artifacts.gate.digest(actual),
                                "childUserSeconds": cpu_after.ru_utime - cpu_before.ru_utime,
                                "childSystemSeconds": cpu_after.ru_stime - cpu_before.ru_stime}
            result["pairs"].append(sample)
            if fingerprint(package) != before:
                raise ValueError("retained package changed during measurement")
            if artifacts.gate.snapshot() != drivers or args.report.read_bytes() != raw:
                raise ValueError("benchmark sources or report changed during measurement")
            if any(artifacts.gate.source.file_digest(Path(t["path"])) != t["sha256"] for t in tools.values()):
                raise ValueError("benchmark tool changed during measurement")
        savings = [p["source"]["seconds"] - p["compiled"]["seconds"] for p in result["pairs"]]
        rng = random.Random(0)
        means = sorted(statistics.mean(rng.choices(savings, k=len(savings))) for _ in range(10000))
        result.update(status="passed", meanSavedSeconds=statistics.mean(savings),
                      pairedBootstrap95Seconds=[means[249], means[9749]], samples=len(savings))
    except BaseException as error:
        result["failure"] = {"kind": type(error).__name__, "message": str(error)}
        raise
    finally:
        (output / "report.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--batch", type=int, default=0)
    parser.add_argument("--pairs", type=int, default=3)
    parser.add_argument("--jobs", type=int, choices=range(1, 5), default=4)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.batch < 0 or args.pairs < 3 or args.timeout <= 0:
        parser.error("nonnegative batch, at least three pairs and positive timeout required")
    benchmark(args)
