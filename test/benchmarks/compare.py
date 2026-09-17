#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2014-2026 The Solidity Authors.
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Benchmark solidity-zig, optionally against a system-installed Solidity compiler."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_FIXTURES = (
    REPO_ROOT / "test/benchmarks/verifier.sol",
    REPO_ROOT / "test/benchmarks/OptimizorClub.sol",
    REPO_ROOT / "test/benchmarks/chains.sol",
)
EXPECTED_REFERENCE_VERSION = "0.8.36"
EXPECTED_ZIG_VERSION = "0.8.36+zig"


@dataclass(frozen=True)
class Sample:
    wall_seconds: float
    user_seconds: float
    system_seconds: float
    peak_rss_mib: float
    exit_code: int


@dataclass(frozen=True)
class Request:
    name: str
    path: Path
    content: bytes


@dataclass(frozen=True)
class Case:
    name: str
    requests: tuple[Request, ...]


@dataclass(frozen=True)
class Preflight:
    exact_output_match: bool | None
    semantic_output_match: bool | None
    bytecode_match: bool | None
    bytecode_size: int
    deployed_bytecode_size: int
    contract_output_size: int
    bytecode_differences: tuple[str, ...]
    reference_errors: tuple[str, ...]
    zig_errors: tuple[str, ...]
    zig_output_sha256: tuple[str, ...]
    zig_contract_output_sha256: tuple[str, ...]


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be greater than zero")
    return parsed


def nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("must not be negative")
    return parsed


def named_sha256(value: str) -> tuple[str, str]:
    name, separator, digest = value.partition("=")
    if not separator or not name or len(digest) != 64:
        raise argparse.ArgumentTypeError("expected NAME=SHA256")
    try:
        int(digest, 16)
    except ValueError as error:
        raise argparse.ArgumentTypeError(
            "SHA256 must contain 64 hexadecimal digits"
        ) from error
    return name, digest.lower()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Benchmark solidity-zig with via-IR Standard JSON requests, with an "
            "optional exact comparison against system solc 0.8.36."
        )
    )
    parser.add_argument("--reference-solc", default="solc")
    parser.add_argument("--zig-solc", default="zig-out/bin/oksolc")
    parser.add_argument(
        "--zig-parallel",
        action="store_true",
        help="Run solidity-zig with its bounded parallel contract backend.",
    )
    parser.add_argument(
        "--zig-jobs",
        type=positive_int,
        help="Total solidity-zig compiler jobs; requires --zig-parallel.",
    )
    parser.add_argument(
        "--expect-zig-output-sha256",
        action="append",
        type=named_sha256,
        default=[],
        metavar="NAME=SHA256",
        help="Require a frozen complete-output hash for a named request; repeatable.",
    )
    parser.add_argument(
        "--expect-zig-contract-output-sha256",
        action="append",
        type=named_sha256,
        default=[],
        metavar="NAME=SHA256",
        help=(
            "Require a frozen creation-plus-runtime bytecode hash for a named "
            "request; repeatable."
        ),
    )
    parser.add_argument(
        "--zig-contract-output-hashes",
        type=Path,
        help="Load frozen per-request contract-output hashes from a JSON manifest.",
    )
    parser.add_argument("--runs", type=positive_int, default=3)
    parser.add_argument("--warmups", type=nonnegative_int, default=1)
    parser.add_argument(
        "--zig-only",
        action="store_true",
        help="Validate and measure only solidity-zig; do not invoke reference solc.",
    )
    parser.add_argument(
        "--fixture",
        action="append",
        type=Path,
        default=[],
        help="Solidity source fixture; may be supplied more than once.",
    )
    parser.add_argument(
        "--standard-json",
        action="append",
        type=Path,
        default=[],
        help="Prepared Standard JSON request; may be supplied more than once.",
    )
    parser.add_argument(
        "--aggregate",
        metavar="NAME",
        help="Measure all prepared inputs as one sequential project workload.",
    )
    parser.add_argument("--output", type=Path, help="Write the full report as JSON.")
    parser.add_argument(
        "--summary-output",
        type=Path,
        help="Write a nested numeric summary grouped by workload and compiler.",
    )
    parser.add_argument(
        "--allow-compiler-errors",
        action="store_true",
        help="Measure requests that return Standard JSON error diagnostics.",
    )
    parser.add_argument(
        "--allow-bytecode-mismatch",
        action="store_true",
        help="Measure even when creation or deployed bytecode differs.",
    )
    parser.add_argument(
        "--require-exact-output",
        action="store_true",
        help="Fail unless complete Standard JSON output bytes match exactly.",
    )
    parser.add_argument("--skip-version-check", action="store_true")
    return parser.parse_args()


def resolve_executable(value: str) -> Path:
    if os.sep in value or (os.altsep is not None and os.altsep in value):
        result = Path(value).expanduser().resolve()
        if not result.is_file():
            raise RuntimeError(f"executable does not exist: {result}")
        return result
    found = shutil.which(value)
    if found is None:
        raise RuntimeError(f"executable not found on PATH: {value}")
    return Path(found).resolve()


def compiler_version(command: Sequence[str]) -> str:
    verify_executable(command[0])
    completed = subprocess.run(
        command,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    verify_executable(command[0])
    if completed.returncode != 0:
        raise RuntimeError(
            f"version command failed with {completed.returncode}: {' '.join(command)}"
        )
    return completed.stdout.strip()


def local_request(path: Path) -> bytes:
    relative = path.resolve().relative_to(REPO_ROOT).as_posix()
    request = {
        "language": "Solidity",
        "sources": {relative: {"content": path.read_text(encoding="utf-8")}},
        "settings": {
            "optimizer": {"enabled": True, "runs": 200},
            "viaIR": True,
            "outputSelection": {
                "*": {
                    "*": [
                        "evm.bytecode.object",
                        "evm.deployedBytecode.object",
                    ]
                }
            },
        },
    }
    return (json.dumps(request, separators=(",", ":")) + "\n").encode()


def make_cases(options: argparse.Namespace) -> list[Case]:
    if options.fixture and options.standard_json:
        raise RuntimeError("--fixture and --standard-json cannot be combined")
    if options.aggregate and not options.standard_json:
        raise RuntimeError("--aggregate requires at least one --standard-json input")

    if options.standard_json:
        requests = tuple(
            Request(path.stem, path.resolve(), path.read_bytes())
            for path in options.standard_json
        )
        if options.aggregate:
            return [Case(options.aggregate, requests)]
        return [Case(request.name, (request,)) for request in requests]

    fixtures = options.fixture or list(DEFAULT_FIXTURES)
    return [
        Case(
            path.name,
            (Request(path.name, path.resolve(), local_request(path.resolve())),),
        )
        for path in fixtures
    ]


def run_capture(command: Sequence[str], request: bytes) -> tuple[int, bytes, bytes]:
    verify_executable(command[0])
    completed = subprocess.run(
        command,
        input=request,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    verify_executable(command[0])
    return completed.returncode, completed.stdout, completed.stderr


def parse_output(label: str, raw: bytes) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"{label} emitted invalid JSON: {error}") from error
    if not isinstance(value, dict):
        raise RuntimeError(f"{label} emitted a non-object Standard JSON result")
    return value


def compiler_errors(output: dict[str, Any]) -> tuple[str, ...]:
    return tuple(
        str(entry.get("message", ""))
        for entry in output.get("errors", [])
        if isinstance(entry, dict) and entry.get("severity") == "error"
    )


ContractOutputKey = tuple[str, str, str]


def contract_output(output: dict[str, Any]) -> dict[ContractOutputKey, str]:
    result: dict[ContractOutputKey, str] = {}
    contracts = output.get("contracts", {})
    if not isinstance(contracts, dict):
        return result
    for source_name, source_contracts in contracts.items():
        if not isinstance(source_contracts, dict):
            continue
        for contract_name, artifact in source_contracts.items():
            if not isinstance(artifact, dict):
                continue
            evm = artifact.get("evm", {})
            if not isinstance(evm, dict):
                continue
            for kind, member in (
                ("creation", "bytecode"),
                ("deployed", "deployedBytecode"),
            ):
                bytecode = evm.get(member, {})
                object_hex = (
                    bytecode.get("object") if isinstance(bytecode, dict) else None
                )
                if isinstance(object_hex, str):
                    result[(source_name, contract_name, kind)] = object_hex
    return result


def contract_output_sha256(artifacts: dict[ContractOutputKey, str]) -> str:
    canonical = [
        [source_name, contract_name, kind, object_hex]
        for (source_name, contract_name, kind), object_hex in sorted(artifacts.items())
    ]
    encoded = json.dumps(
        canonical,
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def contract_output_size(
    artifacts: dict[ContractOutputKey, str], kind: str | None = None
) -> int:
    return sum(
        len(object_hex) // 2
        for key, object_hex in artifacts.items()
        if kind is None or key[2] == kind
    )


def contract_output_label(key: ContractOutputKey) -> str:
    source_name, contract_name, kind = key
    return f"{source_name}:{contract_name}:{kind}"


def load_contract_output_hashes(path: Path | None) -> dict[str, str]:
    if path is None:
        return {}
    value = json.loads(path.read_text(encoding="utf-8"))
    requests = value.get("requests") if isinstance(value, dict) else None
    if not isinstance(requests, dict):
        raise RuntimeError(f"contract-output hash manifest has no request map: {path}")
    result: dict[str, str] = {}
    for name, digest in requests.items():
        if not isinstance(name, str) or not isinstance(digest, str):
            raise RuntimeError(f"invalid contract-output hash entry in {path}")
        try:
            parsed_name, parsed_digest = named_sha256(f"{name}={digest}")
        except argparse.ArgumentTypeError as error:
            raise RuntimeError(
                f"invalid contract-output hash entry in {path}: {name}"
            ) from error
        result[parsed_name] = parsed_digest
    return result


def preflight_case(
    case: Case,
    reference_command: Sequence[str],
    zig_command: Sequence[str],
    expected_zig_hashes: dict[str, str],
    expected_contract_hashes: dict[str, str],
) -> Preflight:
    exact = True
    semantic = True
    bytecode_equal = True
    bytecode_size = 0
    bytecode_differences: list[str] = []
    reference_diagnostics: list[str] = []
    zig_diagnostics: list[str] = []
    zig_hashes: list[str] = []
    zig_contract_hashes: list[str] = []
    deployed_bytecode_size = 0
    total_contract_output_size = 0

    for request in case.requests:
        reference_code, reference_raw, reference_stderr = run_capture(
            reference_command, request.content
        )
        zig_code, zig_raw, zig_stderr = run_capture(zig_command, request.content)
        if reference_code != 0:
            raise RuntimeError(
                f"reference solc failed for {request.name} with {reference_code}: "
                f"{reference_stderr.decode(errors='replace').strip()}"
            )
        if zig_code != 0:
            raise RuntimeError(
                f"solidity-zig failed for {request.name} with {zig_code}: "
                f"{zig_stderr.decode(errors='replace').strip()}"
            )

        reference_output = parse_output("reference solc", reference_raw)
        zig_output = parse_output("solidity-zig", zig_raw)
        zig_hash = hashlib.sha256(zig_raw).hexdigest()
        zig_hashes.append(f"{request.name}={zig_hash}")
        if (
            request.name in expected_zig_hashes
            and zig_hash != expected_zig_hashes[request.name]
        ):
            raise RuntimeError(
                f"{request.name} solidity-zig output SHA256 changed: "
                f"expected {expected_zig_hashes[request.name]}, got {zig_hash}"
            )
        reference_bytecode = contract_output(reference_output)
        zig_bytecode = contract_output(zig_output)
        zig_contract_hash = contract_output_sha256(zig_bytecode)
        zig_contract_hashes.append(f"{request.name}={zig_contract_hash}")
        expected_contract_hash = expected_contract_hashes.get(request.name)
        if (
            expected_contract_hash is not None
            and zig_contract_hash != expected_contract_hash
        ):
            raise RuntimeError(
                f"{request.name} solidity-zig contract-output SHA256 changed: "
                f"expected {expected_contract_hash}, got {zig_contract_hash}"
            )
        exact = exact and reference_raw == zig_raw
        semantic = semantic and reference_output == zig_output
        bytecode_equal = bytecode_equal and reference_bytecode == zig_bytecode
        for artifact_key in sorted(reference_bytecode.keys() | zig_bytecode.keys()):
            reference_object = reference_bytecode.get(artifact_key)
            zig_object = zig_bytecode.get(artifact_key)
            if reference_object == zig_object:
                continue
            if reference_object is None:
                detail = f"missing from reference; Zig has {len(zig_object or '') // 2} B"
            elif zig_object is None:
                detail = f"reference has {len(reference_object) // 2} B; missing from Zig"
            else:
                common_nibbles = min(len(reference_object), len(zig_object))
                first_nibble = next(
                    (
                        index
                        for index in range(common_nibbles)
                        if reference_object[index] != zig_object[index]
                    ),
                    common_nibbles,
                )
                detail = (
                    f"reference {len(reference_object) // 2} B, "
                    f"Zig {len(zig_object) // 2} B, "
                    f"first difference at byte {first_nibble // 2}"
                )
            bytecode_differences.append(
                f"{request.name}: {contract_output_label(artifact_key)}: {detail}"
            )
        bytecode_size += contract_output_size(reference_bytecode, "creation")
        deployed_bytecode_size += contract_output_size(reference_bytecode, "deployed")
        total_contract_output_size += contract_output_size(reference_bytecode)
        reference_diagnostics.extend(compiler_errors(reference_output))
        zig_diagnostics.extend(compiler_errors(zig_output))

    return Preflight(
        exact_output_match=exact,
        semantic_output_match=semantic,
        bytecode_match=bytecode_equal,
        bytecode_size=bytecode_size,
        deployed_bytecode_size=deployed_bytecode_size,
        contract_output_size=total_contract_output_size,
        bytecode_differences=tuple(bytecode_differences),
        reference_errors=tuple(reference_diagnostics),
        zig_errors=tuple(zig_diagnostics),
        zig_output_sha256=tuple(zig_hashes),
        zig_contract_output_sha256=tuple(zig_contract_hashes),
    )


def preflight_zig_case(
    case: Case,
    zig_command: Sequence[str],
    expected_zig_hashes: dict[str, str],
    expected_contract_hashes: dict[str, str],
) -> Preflight:
    bytecode_size = 0
    deployed_bytecode_size = 0
    total_contract_output_size = 0
    zig_diagnostics: list[str] = []
    zig_hashes: list[str] = []
    zig_contract_hashes: list[str] = []
    for request in case.requests:
        zig_code, zig_raw, zig_stderr = run_capture(zig_command, request.content)
        if zig_code != 0:
            raise RuntimeError(
                f"solidity-zig failed for {request.name} with {zig_code}: "
                f"{zig_stderr.decode(errors='replace').strip()}"
            )
        zig_output = parse_output("solidity-zig", zig_raw)
        zig_hash = hashlib.sha256(zig_raw).hexdigest()
        zig_hashes.append(f"{request.name}={zig_hash}")
        if (
            request.name in expected_zig_hashes
            and zig_hash != expected_zig_hashes[request.name]
        ):
            raise RuntimeError(
                f"{request.name} solidity-zig output SHA256 changed: "
                f"expected {expected_zig_hashes[request.name]}, got {zig_hash}"
            )
        artifacts = contract_output(zig_output)
        zig_contract_hash = contract_output_sha256(artifacts)
        zig_contract_hashes.append(f"{request.name}={zig_contract_hash}")
        expected_contract_hash = expected_contract_hashes[request.name]
        if zig_contract_hash != expected_contract_hash:
            raise RuntimeError(
                f"{request.name} solidity-zig contract-output SHA256 changed: "
                f"expected {expected_contract_hash}, got {zig_contract_hash}"
            )
        bytecode_size += contract_output_size(artifacts, "creation")
        deployed_bytecode_size += contract_output_size(artifacts, "deployed")
        total_contract_output_size += contract_output_size(artifacts)
        zig_diagnostics.extend(compiler_errors(zig_output))

    return Preflight(
        exact_output_match=None,
        semantic_output_match=None,
        bytecode_match=None,
        bytecode_size=bytecode_size,
        deployed_bytecode_size=deployed_bytecode_size,
        contract_output_size=total_contract_output_size,
        bytecode_differences=(),
        reference_errors=(),
        zig_errors=tuple(zig_diagnostics),
        zig_output_sha256=tuple(zig_hashes),
        zig_contract_output_sha256=tuple(zig_contract_hashes),
    )


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


EXECUTABLE_SHA256_BEFORE: dict[str, str] = {}


def verify_executable(executable: str | Path) -> str:
    path = Path(executable).resolve()
    path_key = str(path)
    current = file_sha256(path)
    before = EXECUTABLE_SHA256_BEFORE.setdefault(path_key, current)
    if current != before:
        raise RuntimeError(f"benchmark executable changed during measurement: {path}")
    return before


def executable_provenance(executable: str | Path) -> dict[str, str]:
    path = Path(executable).resolve()
    before = verify_executable(path)
    after = file_sha256(path)
    if after != before:
        raise RuntimeError(f"benchmark executable changed during measurement: {path}")
    return {
        "path": str(path),
        "sha256": before,
        "sha256_before": before,
        "sha256_after": after,
    }


def git_provenance() -> dict[str, Any]:
    def run(*arguments: str) -> str | None:
        completed = subprocess.run(
            ("git", *arguments),
            cwd=REPO_ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
        )
        return completed.stdout.strip() if completed.returncode == 0 else None

    revision = run("rev-parse", "HEAD")
    status = run("status", "--porcelain=v1", "--untracked-files=all")
    return {
        "revision": revision,
        "dirty": None if status is None else bool(status),
        "status_sha256": (
            None if status is None else hashlib.sha256(status.encode()).hexdigest()
        ),
    }


def peak_rss_mib(raw_value: int) -> float:
    if platform.system() == "Darwin":
        return raw_value / (1024.0 * 1024.0)
    return raw_value / 1024.0


def measure_invocation(command: Sequence[str], request_path: Path) -> Sample:
    if not hasattr(os, "wait4") or not hasattr(os, "posix_spawn"):
        raise RuntimeError("benchmark measurement requires POSIX posix_spawn() and wait4()")
    file_actions = (
        (os.POSIX_SPAWN_OPEN, 0, str(request_path), os.O_RDONLY, 0o444),
        (os.POSIX_SPAWN_OPEN, 1, os.devnull, os.O_WRONLY, 0o666),
        (os.POSIX_SPAWN_OPEN, 2, os.devnull, os.O_WRONLY, 0o666),
    )
    verify_executable(command[0])
    start = time.perf_counter_ns()
    pid = os.posix_spawn(command[0], command, os.environ, file_actions=file_actions)
    _, status, usage = os.wait4(pid, 0)
    elapsed = (time.perf_counter_ns() - start) / 1_000_000_000.0
    verify_executable(command[0])
    return Sample(
        wall_seconds=elapsed,
        user_seconds=usage.ru_utime,
        system_seconds=usage.ru_stime,
        peak_rss_mib=peak_rss_mib(usage.ru_maxrss),
        exit_code=os.waitstatus_to_exitcode(status),
    )


def measure_case(command: Sequence[str], paths: Sequence[Path]) -> Sample:
    samples = [measure_invocation(command, path) for path in paths]
    nonzero = next((sample.exit_code for sample in samples if sample.exit_code != 0), 0)
    return Sample(
        wall_seconds=sum(sample.wall_seconds for sample in samples),
        user_seconds=sum(sample.user_seconds for sample in samples),
        system_seconds=sum(sample.system_seconds for sample in samples),
        peak_rss_mib=max((sample.peak_rss_mib for sample in samples), default=0.0),
        exit_code=nonzero,
    )


def summarize(samples: Sequence[Sample]) -> dict[str, float | int]:
    return {
        "wall_seconds": statistics.median(sample.wall_seconds for sample in samples),
        "wall_mean_seconds": statistics.mean(sample.wall_seconds for sample in samples),
        "wall_stddev_seconds": statistics.pstdev(sample.wall_seconds for sample in samples),
        "user_seconds": statistics.median(sample.user_seconds for sample in samples),
        "system_seconds": statistics.median(sample.system_seconds for sample in samples),
        "peak_rss_mib": statistics.median(sample.peak_rss_mib for sample in samples),
        "exit_code": next((sample.exit_code for sample in samples if sample.exit_code != 0), 0),
    }


def ratio(numerator: float, denominator: float) -> float | None:
    return numerator / denominator if denominator != 0 else None


def atomic_json_write(path: Path, value: Any) -> None:
    path = path.resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=path.parent,
        prefix=f".{path.name}.",
        delete=False,
    ) as temporary:
        json.dump(value, temporary, indent=2, sort_keys=True)
        temporary.write("\n")
        temporary_path = Path(temporary.name)
    temporary_path.replace(path)


def markdown_report(results: dict[str, Any], zig_only: bool, zig_jobs: int) -> str:
    if zig_only:
        lines = [
            "| Workload | Creation bytecode | Runtime bytecode | Zig jobs | Zig wall | Zig RSS |",
            "|---|---:|---:|---:|---:|---:|",
        ]
        for name, result in results.items():
            zig = result["compilers"]["zig-via-ir"]["summary"]
            lines.append(
                f"| `{name}` | {result['preflight']['bytecode_size']} B | "
                f"{result['preflight']['deployed_bytecode_size']} B | "
                f"{zig_jobs} | {zig['wall_seconds']:.4f} s | "
                f"{zig['peak_rss_mib']:.1f} MiB |"
            )
        return "\n".join(lines)

    lines = [
        "| Workload | Creation bytecode | Runtime bytecode | solc wall | Zig jobs | Zig wall | Zig/solc | solc RSS | Zig RSS | Exact output |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|:---:|",
    ]
    for name, result in results.items():
        reference = result["compilers"]["system-solc-via-ir"]["summary"]
        zig = result["compilers"]["zig-via-ir"]["summary"]
        multiple = ratio(zig["wall_seconds"], reference["wall_seconds"])
        multiple_text = "n/a" if multiple is None else f"{multiple:.2f}x"
        lines.append(
            f"| `{name}` | {result['preflight']['bytecode_size']} B | "
            f"{result['preflight']['deployed_bytecode_size']} B | "
            f"{reference['wall_seconds']:.4f} s | {zig_jobs} | "
            f"{zig['wall_seconds']:.4f} s | "
            f"{multiple_text} | {reference['peak_rss_mib']:.1f} MiB | "
            f"{zig['peak_rss_mib']:.1f} MiB | "
            f"{'yes' if result['preflight']['exact_output_match'] else 'no'} |"
        )
    return "\n".join(lines)


def source_provenance() -> dict[str, object]:
    try:
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
        ).strip()
        status = subprocess.check_output(
            ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
            cwd=REPO_ROOT,
        )
        tracked_diff = subprocess.check_output(
            ["git", "diff", "--binary", "HEAD", "--"],
            cwd=REPO_ROOT,
        )
        untracked_output = subprocess.check_output(
            ["git", "ls-files", "--others", "--exclude-standard", "-z"],
            cwd=REPO_ROOT,
        )
    except (OSError, subprocess.CalledProcessError):
        return {
            "revision": None,
            "dirty": None,
            "status_sha256": None,
            "tracked_diff_sha256": None,
            "untracked_files_sha256": None,
            "source_state_sha256": None,
        }

    untracked_hasher = hashlib.sha256()
    source_hasher = hashlib.sha256()
    source_hasher.update(b"solidity-zig-source-state-v1\0")
    source_hasher.update(revision)
    source_hasher.update(b"\0")
    source_hasher.update(tracked_diff)
    source_hasher.update(b"\0")
    for encoded_path in sorted(filter(None, untracked_output.split(b"\0"))):
        path = os.fsdecode(encoded_path)
        full_path = REPO_ROOT / path
        if full_path.is_symlink():
            content_hash = hashlib.sha256(
                b"symlink\0" + os.fsencode(os.readlink(full_path))
            ).digest()
        elif full_path.is_file():
            content_hasher = hashlib.sha256()
            with full_path.open("rb") as source_file:
                for chunk in iter(lambda: source_file.read(1024 * 1024), b""):
                    content_hasher.update(chunk)
            content_hash = content_hasher.digest()
        else:
            content_hash = hashlib.sha256(b"non-file").digest()
        record = (
            len(encoded_path).to_bytes(8, "big")
            + encoded_path
            + full_path.lstat().st_mode.to_bytes(4, "big")
            + content_hash
        )
        untracked_hasher.update(record)
        source_hasher.update(record)

    return {
        "revision": os.fsdecode(revision),
        "dirty": bool(status),
        "status_sha256": hashlib.sha256(status).hexdigest(),
        "tracked_diff_sha256": hashlib.sha256(tracked_diff).hexdigest(),
        "untracked_files_sha256": untracked_hasher.hexdigest(),
        "source_state_sha256": source_hasher.hexdigest(),
    }


def verified_source_provenance(
    before: dict[str, object],
) -> dict[str, object]:
    after = source_provenance()
    before_hash = before.get("source_state_sha256")
    after_hash = after.get("source_state_sha256")
    if before_hash is None or after_hash is None:
        raise RuntimeError("could not capture Git source provenance")
    if before_hash != after_hash:
        raise RuntimeError("source state changed during benchmark measurements")
    return {**before, "after": after}


SOURCE_PROVENANCE_BEFORE = source_provenance()


def main() -> int:
    options = parse_args()
    try:
        zig = resolve_executable(options.zig_solc)
        cases = make_cases(options)
        if options.zig_jobs is not None and not options.zig_parallel:
            raise RuntimeError("--zig-jobs requires --zig-parallel")
        expected_zig_hashes = dict(options.expect_zig_output_sha256)
        if len(expected_zig_hashes) != len(options.expect_zig_output_sha256):
            raise RuntimeError("duplicate --expect-zig-output-sha256 request name")
        request_names = {request.name for case in cases for request in case.requests}
        unknown_hashes = sorted(expected_zig_hashes.keys() - request_names)
        if unknown_hashes:
            raise RuntimeError(
                "frozen output hashes name unknown requests: "
                + ", ".join(unknown_hashes)
            )
        expected_contract_hashes = load_contract_output_hashes(
            options.zig_contract_output_hashes
        )
        for name, digest in options.expect_zig_contract_output_sha256:
            if name in expected_contract_hashes:
                raise RuntimeError(f"duplicate frozen contract-output hash for {name}")
            expected_contract_hashes[name] = digest
        if options.zig_only:
            missing_contract_hashes = sorted(request_names - expected_contract_hashes.keys())
            if missing_contract_hashes:
                raise RuntimeError(
                    "Zig-only benchmarks require frozen contract-output hashes for: "
                    + ", ".join(missing_contract_hashes)
                )
        zig_jobs = (
            options.zig_jobs
            if options.zig_parallel and options.zig_jobs is not None
            else min(os.cpu_count() or 1, 2)
            if options.zig_parallel
            else 1
        )
        zig_version = compiler_version((str(zig), "version"))
        reference = (
            None if options.zig_only else resolve_executable(options.reference_solc)
        )
        reference_version = (
            None
            if reference is None
            else compiler_version((str(reference), "--version"))
        )
        if not options.skip_version_check:
            if (
                reference_version is not None
                and EXPECTED_REFERENCE_VERSION not in reference_version
            ):
                raise RuntimeError(
                    f"system solc is not version {EXPECTED_REFERENCE_VERSION}"
                )
            if EXPECTED_ZIG_VERSION not in zig_version:
                raise RuntimeError(
                    f"oksolc does not report version {EXPECTED_ZIG_VERSION}"
                )

        reference_command = (
            None if reference is None else (str(reference), "--standard-json")
        )
        zig_command_parts = [str(zig), "standard-json"]
        if options.zig_parallel:
            zig_command_parts.extend(("--parallel", "--jobs", str(zig_jobs)))
        zig_command_parts.append("-")
        zig_command = tuple(zig_command_parts)
        results: dict[str, Any] = {}
        summary_report: dict[str, Any] = {}

        with tempfile.TemporaryDirectory(prefix="solidity-zig-benchmark-") as temp_name:
            temp_dir = Path(temp_name)
            for case_index, case in enumerate(cases):
                preflight = (
                    preflight_zig_case(
                        case,
                        zig_command,
                        expected_zig_hashes,
                        expected_contract_hashes,
                    )
                    if reference_command is None
                    else preflight_case(
                        case,
                        reference_command,
                        zig_command,
                        expected_zig_hashes,
                        expected_contract_hashes,
                    )
                )
                if (
                    (preflight.reference_errors or preflight.zig_errors)
                    and not options.allow_compiler_errors
                ):
                    raise RuntimeError(
                        f"{case.name} produced compiler errors; pass "
                        "--allow-compiler-errors to measure the failure path"
                    )
                if (
                    preflight.bytecode_match is False
                    and not options.allow_bytecode_mismatch
                ):
                    raise RuntimeError(
                        f"{case.name} produced different contract bytecode; refusing "
                        "to compare unequal workloads:\n  "
                        + "\n  ".join(preflight.bytecode_differences)
                    )
                if (
                    options.require_exact_output
                    and preflight.exact_output_match is False
                ):
                    raise RuntimeError(
                        f"{case.name} Standard JSON bytes differ; refusing a strict comparison"
                    )

                request_paths: list[Path] = []
                for request_index, request in enumerate(case.requests):
                    request_path = temp_dir / f"{case_index}-{request_index}.json"
                    request_path.write_bytes(request.content)
                    request_paths.append(request_path)

                for warmup in range(options.warmups):
                    if reference_command is None:
                        commands = (zig_command,)
                    elif warmup % 2 == 0:
                        commands = (reference_command, zig_command)
                    else:
                        commands = (zig_command, reference_command)
                    for command in commands:
                        sample = measure_case(command, request_paths)
                        if sample.exit_code != 0:
                            raise RuntimeError(
                                f"warmup failed for {case.name} with exit {sample.exit_code}"
                            )

                measured: dict[str, list[Sample]] = {"zig-via-ir": []}
                if reference_command is not None:
                    measured["system-solc-via-ir"] = []
                for run in range(options.runs):
                    if reference_command is None:
                        order = (("zig-via-ir", zig_command),)
                    else:
                        order = (
                            ("system-solc-via-ir", reference_command),
                            ("zig-via-ir", zig_command),
                        )
                        if run % 2 != 0:
                            order = tuple(reversed(order))
                    for compiler_name, command in order:
                        sample = measure_case(command, request_paths)
                        measured[compiler_name].append(sample)
                        if sample.exit_code != 0:
                            raise RuntimeError(
                                f"measured run failed for {case.name}/{compiler_name} "
                                f"with exit {sample.exit_code}"
                            )

                compiler_results = {
                    name: {
                        "summary": summarize(samples),
                        "samples": [asdict(sample) for sample in samples],
                    }
                    for name, samples in measured.items()
                }
                zig_summary = compiler_results["zig-via-ir"]["summary"]
                result: dict[str, Any] = {
                    "preflight": asdict(preflight),
                    "compilers": compiler_results,
                }
                if reference_command is not None:
                    reference_summary = compiler_results["system-solc-via-ir"][
                        "summary"
                    ]
                    result["comparison"] = {
                        "wall_ratio_zig_over_system_solc": ratio(
                            float(zig_summary["wall_seconds"]),
                            float(reference_summary["wall_seconds"]),
                        ),
                        "peak_rss_ratio_zig_over_system_solc": ratio(
                            float(zig_summary["peak_rss_mib"]),
                            float(reference_summary["peak_rss_mib"]),
                        ),
                    }
                results[case.name] = result
                summary_report[case.name] = {
                    name: {
                        "bytecode_size": preflight.bytecode_size,
                        "deployed_bytecode_size": preflight.deployed_bytecode_size,
                        "contract_output_size": preflight.contract_output_size,
                        "compilation_time": data["summary"]["wall_seconds"],
                        "user_time": data["summary"]["user_seconds"],
                        "system_time": data["summary"]["system_seconds"],
                        "peak_memory_mib": data["summary"]["peak_rss_mib"],
                        "exit_code": data["summary"]["exit_code"],
                    }
                    for name, data in compiler_results.items()
                }

        report = {
            "schema_version": 3,
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "configuration": {
                "runs": options.runs,
                "warmups": options.warmups,
                "zig_only": options.zig_only,
                "zig_parallel": options.zig_parallel,
                "zig_jobs": zig_jobs,
                "zig_async_workers": max(zig_jobs - 1, 0),
                "reference_command": (
                    None if reference_command is None else list(reference_command)
                ),
                "zig_command": list(zig_command),
                "reference_version": reference_version,
                "zig_version": zig_version,
                "platform": platform.platform(),
            },
            "provenance": {
                "git": verified_source_provenance(SOURCE_PROVENANCE_BEFORE),
                "zig_executable": executable_provenance(zig),
                "reference_executable": (
                    None
                    if reference_command is None
                    else executable_provenance(reference_command[0])
                ),
                "requests": [
                    {
                        "name": request.name,
                        "path": str(request.path),
                        "sha256": hashlib.sha256(request.content).hexdigest(),
                    }
                    for case in cases
                    for request in case.requests
                ],
            },
            "benchmarks": results,
        }
        print(markdown_report(results, options.zig_only, zig_jobs))
        if options.output:
            atomic_json_write(options.output, report)
            print(f"wrote {options.output}")
        if options.summary_output:
            atomic_json_write(options.summary_output, summary_report)
            print(f"wrote {options.summary_output}")
        return 0
    except (OSError, RuntimeError, ValueError) as error:
        print(f"benchmark error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
