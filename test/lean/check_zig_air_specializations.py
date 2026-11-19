#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture generic call provenance without admitting unproved contracts.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import check_byte_invocation
from build_toolchain import digest, run, source_identity, write_json
from capture import capture, read_json
from generate import captured_path
from generate_byte_memory import ByteLoopDecoder
from link_specializations import link

SOURCE = ROOT / "test/lean/zig_air_specialization.zig"
ROOTS = ["zig_air_specialization." + n for n in ("swap_words", "swap_halves", "biased_word")]
REJECTED_ROOT = "zig_air_specialization.widened_result"


def inputs():
    result = check_byte_invocation.inputs()
    result[str(SOURCE.relative_to(ROOT))] = digest(SOURCE)
    return result


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.specialization-capture-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "exportedCallProvenanceOnly", "specializationSemanticsVerified": False,
              "noaliasVerified": False, "capturedSwapLoopVerified": False, "sourceSafetyVerified": False,
              "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["inputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["toolchainReportSha256"] = digest(args.toolchain)
        toolchain = read_json(args.toolchain)
        report["toolchainBuildStatus"] = toolchain["status"]
        exporter = [p for p in toolchain["freshAirCapturePatch"] if p["file"] == "src/SemanticExport.zig"]
        if len(exporter) != 1 or exporter[0]["afterSha256"] != digest(ROOT / "lean/zig_air/SemanticExport.zig"):
            raise ValueError("capturing toolchain has different exporter bytes")
        env, _, _ = lean_check.toolchain(args.lean_bin, 4)
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_zig_air_*.py"], cwd=ROOT, env=env)
        run(output, "format", [compiler, "fmt", "--check", SOURCE, ROOT / "lean/zig_air/SemanticExport.zig"], env=env)
        capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, output=output / "capture", root=ROOTS + [REJECTED_ROOT], mode="ReleaseFast"))
        path = output / "capture/report.json"
        captured = read_json(path)
        records = {}
        for name, entry in captured["functions"].items():
            source = captured_path(path, entry)
            if digest(source) != entry["sha256"]:
                raise ValueError("captured specialization record hash mismatch")
            records[name] = read_json(source)
        sources = {SOURCE.name: digest(SOURCE), "mem.zig": digest(lib / "std/mem.zig")}
        links = link(records, ROOTS, sources)
        write_json(output / "links.json", links)
        report["linksSha256"] = digest(output / "links.json")
        report["captureReportSha256"] = digest(path)
        if (len(links["edges"]) != 3 or len(links["functions"]) != 6 or
                {edge["caller"] for edge in links["edges"]} != set(ROOTS)):
            raise ValueError("unexpected specialization fixture call inventory")
        coerced = [i for i in records[REJECTED_ROOT]["instructions"] if i.get("payloadVisited") is True and i["tag"] == "call"]
        if len(coerced) != 1 or coerced[0].get("callee") != {
                "kind": "function", "identity": {"kind": "unsupported", "reason": "coerced-function"}}:
            raise ValueError("coerced function reference lost its explicit rejection")
        try:
            link(records, [REJECTED_ROOT], sources)
        except ValueError as error:
            report["expectedRejectedRoots"] = [{"root": REJECTED_ROOT, "reason": str(error)}]
        else:
            raise ValueError("coerced function root was linked to an uncoerced body")
        expected = {ROOTS[0]: ("mem.swap", 32, [1, 2], 3), ROOTS[1]: ("mem.swap", 16, [1, 2], 3),
                    ROOTS[2]: ("zig_air_specialization.biased", 32, [1], 0)}
        contracts = []
        for edge in links["edges"]:
            owner, bits, mapping, noalias = expected[edge["caller"]]
            record = records[edge["callee"]]
            spec, function = record["specialization"], links["functions"][edge["callee"]]
            if (spec["owner"]["name"] != owner or function["runtimeParameterIndices"] != mapping or
                    function["noaliasBits"] != noalias or spec["arguments"][0] !=
                    {"kind": "type", "value": {"kind": "int", "bits": bits, "signedness": "unsigned"}}):
                raise ValueError("specialization identity, type or runtime/noalias mapping changed")
            if owner.endswith(".biased") and spec["arguments"][2] != {
                    "kind": "value", "value": {"kind": "constant", "type": {"kind": "int", "bits": 32, "signedness": "unsigned"}, "value": 7}}:
                raise ValueError("interleaved compile-time argument changed")
            try:
                ByteLoopDecoder(record)
            except ValueError as error:
                contracts.append({"callee": edge["callee"], "noaliasBits": noalias, "semanticAdmission": False, "reason": str(error)})
            else:
                raise ValueError("metadata-only specialization was admitted without semantic proof")
        report["unresolvedContracts"] = contracts
        # Regression binds the new exporter to existing complete byte-access
        # proofs, fresh capture equality, native observations and kernel replay.
        check_byte_invocation.check(argparse.Namespace(toolchain=args.toolchain, lean_bin=args.lean_bin,
                                                       output=output / "byte-invocation-regression"))
        regression = output / "byte-invocation-regression/report.json"
        if read_json(regression)["status"] != "passed":
            raise ValueError("existing byte invocation regression failed")
        report["byteInvocationRegressionSha256"] = digest(regression)
        if (inputs() != report["inputs"] or lean_check.source_inputs() != report["leanInputs"] or
                digest(args.toolchain) != report["toolchainReportSha256"] or digest(compiler) != toolchain["compiler"]["sha256"] or
                source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("specialization capture inputs changed")
        report.update(status="passed", exportedCallLinksChecked=True, specializationMetadataChecked=True)
    finally:
        write_json(output / "report.json", report)
    print("Specialization call provenance passed; semantic admission and noalias remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
