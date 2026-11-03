#!/usr/bin/env python3
"""Capture Wyhash's unchanged public bodies and expose AIR admission blockers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Exit zero means the capture/inspection gate completed, never hash verification.
Raw AIR and native objects stay in the new output directory. No rejected body
is translated by deleting instructions or replacing it with the scoped model.
"""
import argparse
from collections import Counter
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean/zig_air"))
from build_toolchain import digest, write_json
from capture import capture, read_json
from generate import captured_path
from generate_byte_memory import ByteLoopDecoder

ENTRIES = {"initialize": "init", "update": "update", "finish": "final"}
MODES = ("Debug", "ReleaseSafe", "ReleaseFast")


def inspect_body(record):
    """Report the real decoder result plus bounded, located exporter omissions.

    Exporter omissions are an inventory, not an exhaustive list of semantic
    obligations: even a decoded body still needs its preservation proof.
    """
    instructions = record["instructions"]
    active = [inst for inst in instructions if inst.get("payloadVisited") is True]
    omissions = {}

    def visit(value, location):
        if isinstance(value, dict):
            if value.get("kind") == "unsupported":
                reason = value.get("reason", value.get("zigTypeTag", "unspecified"))
                if not isinstance(reason, str):
                    raise ValueError("malformed unsupported marker")
                item = omissions.setdefault(reason, {"count": 0, "locations": []})
                item["count"] += 1
                if len(item["locations"]) < 2:
                    item["locations"].append(location)
            for key, child in value.items():
                visit(child, location + "/" + key)
        elif isinstance(value, list):
            for index, child in enumerate(value):
                visit(child, location + "/" + str(index))

    visit(record["signature"], "/signature")
    visit(record["sourceValidity"], "/sourceValidity")
    for inst in active:
        visit(inst, "/instructions/" + str(inst["index"]))
    try:
        ByteLoopDecoder(record).program(record)
        decoder = {"status": "decoded", "preservationVerified": False}
    except ValueError as error:
        decoder = {"status": "rejected", "reason": str(error)}
    return {
        "instructionCount": len(instructions), "visitedInstructionCount": len(active),
        "unvisitedInstructionCount": len(instructions) - len(active),
        "unsupportedPayloads": dict(sorted(Counter(inst["tag"] for inst in active
            if inst.get("unsupportedPayload") is True).items())),
        "unsupportedValues": {reason: {**item, "omittedLocations": item["count"] - len(item["locations"])}
                              for reason, item in sorted(omissions.items())},
        "sourceSliceCount": len(record["sourceValidity"]["slices"]),
        "lengthBasedSliceObserved": "slice_length" in record["sourceOperationTags"],
        "decoderProfile": "resumable-initialized-u32-byte-views",
        "decoder": decoder,
    }


def inspect_capture(report_path, std_sha):
    report = read_json(report_path)
    if (report.get("schema") != "oksolc.fresh-air-capture.v1" or
            report.get("status") != "captured" or report.get("captureComplete") is not True or
            report["objects"]["ordinary"] != report["objects"]["captured"]):
        raise ValueError("capture did not complete with identical native objects")
    records = {}
    for name, entry in report["functions"].items():
        path = captured_path(report_path, entry)
        if digest(path) != entry["sha256"]:
            raise ValueError("captured AIR hash mismatch")
        record = read_json(path)
        if record["name"] != name:
            raise ValueError("captured AIR name mismatch")
        records[name] = record
    result = {}
    for wrapper, method in ENTRIES.items():
        root = "wyhash_air." + wrapper
        if root not in records or report["functions"][root]["requested"] is not True:
            raise ValueError("missing requested Wyhash wrapper: " + root)
        body = records[root]
        if body["sourceSha256"] != report["sourceSha256"] or body["sourceFile"] != "wyhash_air.zig":
            raise ValueError("wrapper source identity mismatch")
        calls = [inst for inst in body["instructions"] if inst.get("payloadVisited") is True and
                 inst["tag"] in {"call", "call_always_tail", "call_never_tail", "call_never_inline"}]
        if len(calls) != 1 or calls[0].get("callee", {}).get("kind") != "function":
            raise ValueError("wrapper must retain exactly one direct stdlib call: " + root)
        target = calls[0]["callee"]["identity"]
        name = target["name"]
        if (not name.endswith(".Wyhash." + method) or target["sourceFile"] != "hash/wyhash.zig" or
                target["sourceSha256"] != std_sha or name not in records):
            raise ValueError("Wyhash call lost the pinned standard-library body")
        native = records[name]
        if target != {key: native[key] for key in ("name", "sourceFile", "sourceSha256")}:
            raise ValueError("call and captured body identities disagree")
        if native["configuration"] != body["configuration"]:
            raise ValueError("call and captured body configurations disagree")
        result[method] = {"name": name, "airSha256": report["functions"][name]["sha256"],
                          "wrapperAirSha256": report["functions"][root]["sha256"],
                          "wrapper": inspect_body(body), "body": inspect_body(native)}
    return {"captureReportSha256": digest(report_path), "objects": report["objects"], "entries": result}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.wyhash-air-inspection.v1", "status": "failed",
              "nativeHashProducerVerified": False, "sourceAdapterFormallyVerified": False,
              "callClosureVerified": False, "modes": {}}
    try:
        toolchain = read_json(args.toolchain)
        captured_std = Path(toolchain["compiler"]["zigLibDir"]) / "std/hash/wyhash.zig"
        native_std = args.zig_lib_dir / "std/hash/wyhash.zig"
        std_sha = digest(native_std)
        if digest(captured_std) != std_sha:
            raise ValueError("capture and native compiler Wyhash sources differ")
        fixture = ROOT / "test/lean/wyhash_air.zig"
        fixture_sha = digest(fixture)
        report.update(stdlibSourceSha256=std_sha, fixtureSha256=fixture_sha,
                      toolchainReportSha256=digest(args.toolchain))
        for mode in MODES:
            directory = output / mode
            capture(argparse.Namespace(source=fixture, source_file=[], toolchain=args.toolchain,
                output=directory, mode=mode, root=["wyhash_air." + name for name in ENTRIES]))
            report["modes"][mode] = inspect_capture(directory / "report.json", std_sha)
        if (digest(native_std) != std_sha or digest(captured_std) != std_sha or digest(fixture) != fixture_sha or
                digest(args.toolchain) != report["toolchainReportSha256"]):
            raise ValueError("Wyhash inspection inputs changed")
        report["status"] = "inspected"
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--zig-lib-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
