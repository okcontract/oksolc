#!/usr/bin/env python3
"""Run or package commit-bound preview release evidence, never publish a release.
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Receipts summarize existing gates; they are not new semantic certificates.
Bundles retain the proof sources, packages, audits and replay diagnostics.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile

import bounded_run

ROOT = Path(__file__).resolve().parents[2]
PROFILES = ("words", "graphs", "graph_failures", "functions", "contracts", "storage", "preview")
REQUIRED = {"models", *PROFILES}
SCHEMA = "oksolc.verification-release-receipt.v1"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_bytes())


def write(path, value):
    Path(path).write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def identity():
    require(not git("status", "--porcelain", "--untracked-files=normal"),
            "release evidence requires a clean checkout; commit preparation changes first")
    return {"commit": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}")}


def accepted(report, profile=None):
    if profile:
        module = importlib.import_module("check_compiler_functions" if profile == "preview" else "check_compiler_" + profile)
        require(report.get("schema") == module.REPORT_SCHEMA, "wrong artifact profile")
        require((report.get("example") == "publicPreviewIdentity") == (profile == "preview"),
                "preview and full corpus receipts are distinct")
    for field in ("accepted", "corpusComplete", "freshPackage", "freshKernelReplay"):
        require(report.get(field) is True, "incomplete artifact gate: " + field)
    require(report.get("status") == "passed" and report.get("wholeCompilerVerified") is False,
            "invalid artifact assurance")
    cases, controls, batches = (report.get(key, []) for key in ("cases", "negativeControls", "proofBatches"))
    require(cases and len(cases) == report.get("requestedCases") and
            report.get("unvalidatedCases") == [] and
            all(c.get("accepted") is True for c in cases), "incomplete case coverage")
    require([c.get("case") for c in cases] == list(range(len(cases))), "duplicate or missing cases")
    require(controls and all(c.get("rejected") is True for c in controls), "missing rejected controls")
    require(batches and all(b.get("freshPackage") is True and b.get("freshKernelReplay") is True
                           for b in batches), "incomplete batch replay")
    require([i for b in batches for i in b.get("cases", [])] == list(range(len(cases))),
            "duplicate or missing batch coverage")
    return {"cases": len(cases), "negativeControls": len(controls), "proofBatches": len(batches),
            "proofScope": report.get("proofScope"), "axioms": report.get("axioms")}


def contained(root, name):
    path = root / name
    require(not Path(name).is_absolute() and ".." not in Path(name).parts and
            path.resolve().is_relative_to(root.resolve()), "evidence path escapes its root")
    require(path.is_file() and not path.is_symlink(), "evidence must be a regular file: " + str(path))
    return path


def receipt(profile, output):
    source = identity()
    process = read(output / (profile + "-process/receipt.json"))
    require(process.get("status") == "passed" and process.get("exitCode") == 0 and
            not process.get("resourceLimit") and not process.get("cleanupError"), "process gate failed")
    if profile == "models":
        summary = {"proofScope": "libraryBuildOnly", "freshKernelReplay": False}
        roots = [output / "models-process", output / "inventory.json"]
    else:
        report = read(output / profile / "report.json")
        summary = accepted(report, profile)
        require(report.get("sourceSha256"), "missing proof input identities")
        for name, expected in report["sourceSha256"].items():
            require(digest(contained(ROOT, name)) == expected, "proof input differs from release commit: " + name)
        roots = [output / profile, output / (profile + "-process")]
    files = {}
    for root in roots:
        for path in sorted(root.rglob("*")) if root.is_dir() else [root]:
            require(not path.is_symlink(), "symlinks are not allowed in release evidence")
            if path.is_file():
                files[path.relative_to(output).as_posix()] = digest(path)
    require(source == identity(), "source changed while preparing receipt")
    directory = output / "release-receipts"
    directory.mkdir(exist_ok=True)
    target = directory / (profile + ".json")
    require(not target.exists(), "release receipt already exists")
    value = {"schema": SCHEMA, "source": source, "profile": profile, "summary": summary,
             "createdAt": datetime.now(timezone.utc).isoformat(), "files": files,
             "wholeCompilerVerified": False, "assurance": "existingGateReceipt"}
    write(target, value)
    return value


def collect(directory, source):
    profiles, files = {}, {}
    for path in sorted(directory.rglob("release-receipts/*.json")):
        record = read(path)
        profile = record.get("profile")
        require(record.get("schema") == SCHEMA and record.get("source") == source,
                "receipt is not bound to this release commit")
        require(profile in REQUIRED and profile not in profiles, "unexpected or duplicate profile")
        require(record.get("wholeCompilerVerified") is False and record.get("files"), "invalid receipt")
        root = path.parent.parent
        for name, expected in record["files"].items():
            artifact = contained(root, name)
            require(digest(artifact) == expected, "evidence changed after receipt: " + name)
            files[artifact.relative_to(directory).as_posix()] = artifact
        # Recheck current reports as well as their receipt hashes.
        process = read(root / (profile + "-process/receipt.json"))
        require(process.get("status") == "passed" and process.get("exitCode") == 0 and
                not process.get("resourceLimit") and not process.get("cleanupError"), "failed process receipt")
        if profile != "models":
            accepted(read(root / profile / "report.json"), profile)
        profiles[profile] = record["summary"]
        files[path.relative_to(directory).as_posix()] = path
    require(set(profiles) == REQUIRED, "missing release profiles: " + ", ".join(sorted(REQUIRED - set(profiles))))
    return profiles, files


def bundle(directory, target):
    source = identity()
    require(not target.resolve().is_relative_to(directory.resolve()), "bundle must be outside evidence directory")
    require(not target.exists() and not Path(str(target) + ".sha256").exists(), "bundle already exists")
    profiles, files = collect(directory, source)
    # Archive only manifest-bound files, not stray files in a download directory.
    with tarfile.open(target, "x:gz") as archive:
        for name, path in sorted(files.items()):
            archive.add(path, arcname=name, recursive=False)
    collect(directory, source)
    require(source == identity(), "source changed while packaging evidence")
    Path(str(target) + ".sha256").write_text(digest(target) + "  " + target.name + "\n")
    return {"source": source, "profiles": profiles, "bundle": str(target), "wholeCompilerVerified": False}


def run(output, lean_bin):
    source = identity()
    require(not output.resolve().is_relative_to(ROOT), "keep release evidence outside the checkout")
    output.mkdir(parents=True, exist_ok=False)
    if lean_bin:
        os.environ["PATH"] = str(lean_bin.resolve()) + os.pathsep + os.environ["PATH"]
    os.environ["LEAN_NUM_THREADS"] = "2"
    os.chdir(ROOT)
    report = {"source": source, "status": "failed", "profiles": {}, "wholeCompilerVerified": False}

    def phase(name, command, timeout=3600):
        result = bounded_run.run(command, output / (name + "-process"), rss_mib=8192, timeout=timeout)
        require(result["status"] == "passed", name + " failed; inspect its process receipt")

    try:
        phase("build", ["zig", "build", "build-cli", "build-compiler-word-export", "build-compiler-graph-export",
                        "-Doptimize=ReleaseFast", "-j2"])
        phase("regressions", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_*.py"])
        phase("native", ["zig", "build", "fmt-check", "test-compiler-rewrites", "test-compiler-dispatch-trace",
                         "test-compiler-graph-export", "test-compiler-word-export", "-Doptimize=Debug", "-j2"])
        subprocess.run([sys.executable, "test/lean/check_verification_map.py", "--output", str(output / "inventory.json")],
                       check=True, timeout=120)
        # Use the selected real Lake binary from within the pinned Lean project.
        phase("models", [sys.executable, "-c", "import os; os.chdir('lean'); os.execvp('lake', ['lake', '--quiet', '--rehash', 'build', 'Compiler'])"])
        receipt("models", output)
        for profile in PROFILES:
            try:
                checker = "check_preview.py" if profile == "preview" else "check_compiler_" + profile + ".py"
                phase(profile, [sys.executable, "test/lean/" + checker, "--corpus", "--jobs", "2",
                                "--output", str(output / profile)])
                report["profiles"][profile] = receipt(profile, output)["summary"]
            except Exception as error:
                report["profiles"][profile] = {"failure": str(error)}
        require(source == identity(), "source revision changed during release checks")
        collect(output, source)
        report["status"] = "passed"
    except Exception as error:
        report["failure"] = str(error)
    finally:
        write(output / "release-run.json", report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    check = commands.add_parser("run", help="run all release gates sequentially from a clean checkout")
    check.add_argument("--output", type=Path, required=True)
    check.add_argument("--lean-bin", type=Path)
    record = commands.add_parser("receipt", help="bind one successful existing gate to the clean commit")
    record.add_argument("--profile", choices=sorted(REQUIRED), required=True)
    record.add_argument("--output", type=Path, required=True)
    pack = commands.add_parser("bundle", help="require all profiles and archive their checked evidence")
    pack.add_argument("--input", type=Path, required=True)
    pack.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == "run":
            result = run(args.output.resolve(), args.lean_bin)
            print(json.dumps(result, sort_keys=True))
            return 0 if result["status"] == "passed" else 1
        if args.command == "receipt":
            result = receipt(args.profile, args.output.resolve())
            print(json.dumps({key: result[key] for key in ("source", "profile", "summary")}))
        else:
            print(json.dumps(bundle(args.input.resolve(), args.output.resolve()), sort_keys=True))
        return 0
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
