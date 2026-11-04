#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Native fresh-AIR capture checks; this gate does not verify the compiler.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean/zig_air"))
from build_toolchain import digest, run, write_json
from capture import capture, inspect_records, read_json


def rejects(output, label, command, diagnostic):
    # Even failed Zig compilations may create partial native output. Never let
    # a rejection control replace the accepted object retained as evidence.
    command = ["-femit-bin=" + str(output / (label + ".o")) if a.startswith("-femit-bin=") else a for a in command]
    try:
        run(output, label, command)
    except ValueError:
        receipt = read_json(output / (label + ".process.json"))
        if receipt.get("status") != "completed" or receipt.get("exitCode", 0) == 0:
            raise ValueError("negative control has no failing terminal process: " + label)
        if diagnostic not in (output / (label + ".stderr")).read_text():
            raise ValueError("wrong rejection diagnostic: " + label)
    else:
        raise ValueError("negative control unexpectedly compiled: " + label)


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.fresh-air-tests.v1", "status": "failed", "wholeCompilerVerified": False,
              "sourceSafetyVerified": False, "leanTranslationImplemented": False, "modes": {}}
    inputs = [*sorted((ROOT / "lean/zig_air").glob("*.*")), Path(__file__).resolve(),
              ROOT / "test/lean/zig_air_fixture.zig"]
    before = {str(path.relative_to(ROOT)): digest(path) for path in inputs if path.is_file()}
    report["inputs"] = before
    try:
        toolchain = read_json(args.toolchain)
        bootstrap = Path(toolchain["bootstrap"]["path"])
        if digest(bootstrap) != toolchain["bootstrap"]["sha256"]:
            raise ValueError("bootstrap binary hash mismatch")
        source = ROOT / "test/lean/zig_air_fixture.zig"
        roots = [source.stem + "." + name for name in
                 ("add_wrapping", "source_slice_bound", "source_parallel_lengths", "add_constant", "undefined_value")]
        for mode in ("ReleaseFast", "Debug"):
            directory = output / mode
            capture(argparse.Namespace(toolchain=args.toolchain, source=source, output=directory, root=roots, mode=mode))
            result = read_json(directory / "report.json")
            functions = result["functions"]
            if set(functions) != set(roots):
                raise ValueError("unexpected fixture function closure")
            records = {name: read_json(directory / "air" / functions[name]["file"]) for name in roots}
            if "add_wrap" not in [i["tag"] for i in records[roots[0]]["instructions"]]:
                raise ValueError("wrapping add missing from fresh AIR")
            if "addwrap" not in records[roots[0]]["sourceOperationTags"]:
                raise ValueError("source wrapping-add operation missing")
            if "slice_end" not in records[roots[1]]["sourceOperationTags"]:
                raise ValueError("source slice requirement silently disappeared")
            if "for_len" not in records[roots[2]]["sourceOperationTags"]:
                raise ValueError("source parallel-loop requirement silently disappeared")
            if any(i["tag"].startswith("legalize_") for r in records.values() for i in r["instructions"]):
                raise ValueError("AIR was captured after legalization")
            if not any(i.get("unsupportedPayload") for i in records[roots[2]]["instructions"]):
                raise ValueError("unmodeled loop payload lost its unsupported status")
            constants = [i["rhs"] for i in records[roots[3]]["instructions"] if i["tag"] == "add_wrap"]
            if constants != [{"kind": "constant", "type": {"kind": "int", "bits": 32, "signedness": "unsigned"}, "value": 7}]:
                raise ValueError("typed constant operand was not preserved")
            returned = [i["operand"] for i in records[roots[4]]["instructions"] if i["tag"] in ("ret", "ret_safe")]
            if returned != [{"kind": "undefined", "type": {"kind": "int", "bits": 32, "signedness": "unsigned"}}]:
                raise ValueError("undefined return lost its type or undefinedness")
            if result["objects"]["ordinary"] != result["objects"]["captured"] or not result["captureComplete"]:
                raise ValueError("native capture comparison incomplete")
            baseline = read_json(directory / "ordinary.process.json")["command"]
            baseline[0] = str(bootstrap)
            baseline[baseline.index("--cache-dir") + 1] = str(directory / "bootstrap-cache")
            baseline = ["-femit-bin=" + str(directory / "bootstrap.o") if a.startswith("-femit-bin=") else a for a in baseline]
            run(directory, "bootstrap", baseline)
            if digest(directory / "bootstrap.o") != result["objects"]["captured"]:
                raise ValueError("capture object differs from the installed pinned compiler")
            # Replay the structured, harness-owned invocation. This exercises
            # cache reuse and must fail on exclusive output creation, not reuse
            # the old AIR or skip semantic analysis.
            command = read_json(directory / "capture.process.json")["command"]
            rejects(directory, "stale-directory", command, "fresh AIR capture failed: PathAlreadyExists")
            after = inspect_records(directory / "air", roots, result["sourceSha256"], mode)
            if after != functions:
                raise ValueError("failed replay changed retained AIR records")
            missing = [a for a in command if not a.startswith("--semantic-export=")]
            missing.append("--semantic-export=" + str(directory / "missing-directory"))
            rejects(directory, "missing-directory", missing, "fresh AIR capture failed: FileNotFound")
            incremental = [a for a in command if a != "-fno-incremental"] + ["-fincremental"]
            rejects(directory, "incremental", incremental, "semantic export does not support incremental compilation")
            if any(digest(directory / (label + ".o")) != result["objects"]["captured"]
                   for label in ("ordinary", "captured", "bootstrap")):
                raise ValueError("negative controls changed accepted native objects")
            report["modes"][mode] = {"captureComplete": True, "objectSha256": result["objects"]["captured"],
                                     "functions": functions, "negativeCompilations": 3}
        after = {name: digest(ROOT / name) for name in before}
        if before != after or digest(bootstrap) != toolchain["bootstrap"]["sha256"]:
            raise ValueError("harness inputs changed during the run")
        report["status"] = "passed"
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
