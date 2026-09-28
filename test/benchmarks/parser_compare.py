#!/usr/bin/env python3
"""Compare ReleaseFast frontend snapshots without modifying the Git index.

Example: python3 test/benchmarks/parser_compare.py --output /tmp/frontend-bench
Use --variant name=git:REV or name=src:/absolute/path/to/src to select snapshots.
All builds finish before timing; measured variants rotate order between rounds.
"""

import argparse
import hashlib
import io
import json
from pathlib import Path
import platform
import shutil
import statistics
import subprocess
import tarfile


WORKLOADS = (
    "tokens-keywords", "tokens-identifiers", "tokens-sized", "tokens-corpus",
    "parse-chains", "parse-verifier", "parse-club", "dialect-init",
    "reserved-lookup", "parse-yul",
)
PROJECT_WORKLOADS = ("parse-project", "parse-project-cold")
ROOT = Path(__file__).resolve().parents[2]


def command(args, **kwargs):
    return subprocess.run(args, cwd=ROOT, check=True, text=True, capture_output=True, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--variant", action="append")
    parser.add_argument("--rounds", type=int, default=9)
    parser.add_argument("--workload", action="append", choices=WORKLOADS + PROJECT_WORKLOADS)
    parser.add_argument("--request", type=Path, help="Standard JSON source corpus (.json or .json.zst)")
    parser.add_argument("--iterations", type=int, default=10, help="complete corpus passes per warm sample")
    args = parser.parse_args()
    if args.rounds < 3:
        parser.error("at least three measured rounds are required")
    if args.iterations < 1:
        parser.error("iterations must be positive")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    variants = args.variant or ["parent=git:HEAD^", "head=git:HEAD", f"working=src:{ROOT / 'src'}"]
    workloads = args.workload or (PROJECT_WORKLOADS if args.request else WORKLOADS)
    if any((workload in PROJECT_WORKLOADS) != bool(args.request) for workload in workloads):
        parser.error("project workloads require --request and cannot mix with microbenchmarks")
    metadata = {"zig": command(["zig", "version"]).stdout.strip(), "machine": platform.platform(),
                "rounds": args.rounds, "optimize": "ReleaseFast", "allocator": "c_allocator", "variants": {}}
    inputs = output / "benchmark"
    inputs.mkdir()
    root_name = "parser_project.zig" if args.request else "parser.zig"
    input_names = (root_name,) if args.request else (root_name, "chains.sol", "verifier.sol", "OptimizorClub.sol")
    for name in input_names:
        shutil.copy2(ROOT / "test/benchmarks" / name, inputs / name)
    if args.request:
        request = args.request.resolve()
        raw = subprocess.check_output(["zstd", "-q", "-d", "-c", str(request)]) if request.suffix == ".zst" else request.read_bytes()
        document = json.loads(raw)
        sources = document["sources"]
        if not sources or any(not isinstance(source.get("content"), str) for source in sources.values()):
            parser.error("request must contain nonempty inline source contents")
        (inputs / "request.json").write_bytes(raw)
        metadata["corpus"] = {"request": str(request), "request_sha256": hashlib.sha256(raw).hexdigest(),
                             "sources": len(sources), "source_bytes": sum(len(s["content"].encode()) for s in sources.values()),
                             "source_lines": sum(len(s["content"].splitlines()) for s in sources.values()),
                             "evm_version": document["settings"]["evmVersion"], "warm_iterations": args.iterations}
    metadata["benchmark_sha256"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(inputs.iterdir())}
    binaries = {}
    for spec in variants:
        if "=" not in spec:
            parser.error("variants must have the form name=git:REV or name=src:PATH")
        name, source = spec.split("=", 1)
        if not name.replace("-", "").replace("_", "").isalnum() or name in binaries:
            parser.error(f"invalid or duplicate variant name: {name}")
        snapshot = output / name
        if snapshot.exists():
            parser.error(f"snapshot already exists: {snapshot}; choose a fresh output directory")
        snapshot.mkdir()
        if source.startswith("git:"):
            revision = source[4:]
            archive = subprocess.run(["git", "archive", revision, "src"], cwd=ROOT, check=True, capture_output=True).stdout
            with tarfile.open(fileobj=io.BytesIO(archive)) as files:
                for member in files.getmembers():
                    if member.isfile():
                        destination = snapshot / member.name
                        if not destination.resolve().is_relative_to(snapshot):
                            raise ValueError(f"invalid archive path: {member.name}")
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        destination.write_bytes(files.extractfile(member).read())
            metadata["variants"][name] = {"revision": command(["git", "rev-parse", revision]).stdout.strip()}
        elif source.startswith("src:"):
            shutil.copytree(Path(source[4:]).resolve(), snapshot / "src")
            metadata["variants"][name] = {"source": source[4:]}
        else:
            parser.error(f"unknown source: {source}")
        hashes = {}
        for path in sorted((snapshot / "src").rglob("*.zig")):
            hashes[str(path.relative_to(snapshot))] = hashlib.sha256(path.read_bytes()).hexdigest()
        metadata["variants"][name]["source_hashes"] = hashes
        binary = snapshot / "probe"
        src = snapshot / "src"
        print(f"Building {name}", flush=True)
        build = ["zig", "build-exe", "-O", "ReleaseFast", "-lc", "--dep", "frontend",
                 f"-Mroot={inputs / root_name}", "--dep", "big_int", "--dep", "cxx_compat",
                 f"-Mfrontend={src / 'modules.zig'}", f"-Mbig_int={src / 'libsolutil/big_int.zig'}",
                 "--dep", "big_int", f"-Mcxx_compat={src / 'cxx_compat/root.zig'}",
                 "--global-cache-dir", str(output / "global-cache"), "--cache-dir", str(output / "cache"),
                 f"-femit-bin={binary}"]
        result = subprocess.run(build, cwd=ROOT, text=True, capture_output=True)
        (snapshot / "build.log").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f"build failed for {name}:\n{result.stderr}")
        binaries[name] = binary
        metadata["variants"][name]["binary_sha256"] = hashlib.sha256(binary.read_bytes()).hexdigest()
    (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    results = {workload: {name: [] for name in binaries} for workload in workloads}
    checksums = {}
    counters = {}
    validation = {}

    def invoke(name, workload):
        return command([str(binaries[name]), workload] + ([str(args.iterations)] if args.request else []))

    if args.request:
        print("Validating complete AST output before timing", flush=True)
        for name in binaries:
            result = invoke(name, "validate-project")
            (output / name / "validation.json").write_text(result.stderr)
            validation[name] = json.loads(result.stderr)
        if any(value != next(iter(validation.values())) for value in validation.values()):
            raise RuntimeError("project AST or diagnostic mismatch")

    def measure(name, workload):
        result = invoke(name, workload)
        rows = [json.loads(line) for line in result.stderr.splitlines() if line.startswith("{")]
        timing = rows[-1]
        expected = checksums.setdefault(workload, timing["checksum"])
        if timing["checksum"] != expected:
            raise RuntimeError(f"checksum mismatch in {name}/{workload}")
        if len(rows) > 1:
            counters[name] = rows[0]
        return timing["ns_per_op"]

    print("Warming every variant and workload", flush=True)
    for name in binaries:
        for workload in workloads:
            measure(name, workload)
    names = list(binaries)
    for round_index in range(args.rounds):
        order = names[round_index % len(names):] + names[:round_index % len(names)]
        for workload in workloads:
            for name in order:
                results[workload][name].append(measure(name, workload))
        print(f"Round {round_index + 1}/{args.rounds}", flush=True)
    summary = {workload: {name: {"median_ns": statistics.median(values), "min_ns": min(values),
                                "max_ns": max(values), "samples_ns": values}
                          for name, values in variants.items()} for workload, variants in results.items()}
    (output / "results.json").write_text(json.dumps({"timings": summary, "allocation_counters": counters,
                                                    "checksums": checksums, "validation": validation}, indent=2) + "\n")
    for workload, values in summary.items():
        print(workload + ": " + ", ".join(f"{name}={result['median_ns']:.2f} ns" for name, result in values.items()))
    print("Allocation counters: " + json.dumps(counters))
    print(f"Results: {output / 'results.json'}")


if __name__ == "__main__":
    main()
