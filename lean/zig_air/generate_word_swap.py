#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Decode the source-bound u32 std.mem.swap instance behind a word-pair contract.
// Copyright (C) 2026 OKcontract Pte. Ltd.

No generic flags or argument indices are erased. The normal body decoder
checks every instruction, SSA dominance and control ownership. This profile
does not prove specialization correctness or the body's noalias footprint.
"""
import argparse
from pathlib import Path

from build_toolchain import digest, write_json
from capture import read_json
from generate import captured_path
from generate_byte_memory import ByteLoopDecoder, WORD
from link_specializations import identity, link, signature, specialization


class WordSwapDecoder(ByteLoopDecoder):
    record_fields = ByteLoopDecoder.record_fields + " specialization"

    def __init__(self, record, sources):
        self.sources = sources
        identity({key: record[key] for key in ("name", "sourceFile", "sourceSha256")}, sources)
        super().__init__(record)

    def parameter_mapping(self, record):
        parameters, result = signature(record)
        mapping, self.specialization_key = specialization(record, self.sources)
        spec = record["specialization"]
        if (record["signature"]["genericInstance"] is not True or
                record["signature"]["callingConvention"] != {"auto": {}} or record["signature"]["noaliasBits"] != 3 or
                parameters != [("ptr", True, False, WORD)] * 2 or result != ("void",) or mapping != [1, 2] or
                spec["owner"]["name"] != "mem.swap" or spec["owner"]["sourceFile"] != "mem.zig" or
                spec["sourceParameterCount"] != 3 or spec["sourceComptimeBits"] != 1 or spec["sourceNoaliasBits"] != 6 or
                spec["arguments"][0] != {"kind": "type", "value": {"kind": "int", "bits": 32, "signedness": "unsigned"}}):
            raise ValueError("unsupported u32 word-swap specialization contract")
        return mapping

    def program(self, record):
        # Returning a wrapper here prevents callers of this specialized decoder
        # from accidentally publishing the ordinary, unrestricted Program text.
        return "{ program :=\n  " + super().program(record) + " }"


def generate(report_path, root, std_mem, output, manifest_path):
    report = read_json(report_path)
    if (report.get("schema") != "oksolc.fresh-air-capture.v1" or report.get("status") != "captured" or
            report.get("captureComplete") is not True):
        raise ValueError("word-swap capture was not completed")
    if root not in report["functions"] or report["functions"][root]["requested"] is not True:
        raise ValueError("word-swap selection requires a requested capture root")
    records = {}
    for name, entry in report["functions"].items():
        path = captured_path(report_path, entry)
        if digest(path) != entry["sha256"]:
            raise ValueError("word-swap captured AIR hash mismatch")
        records[name] = read_json(path)
    caller = records[root]
    if caller["sourceSha256"] != report["sourceSha256"] or caller["sourceFile"] == "mem.zig":
        raise ValueError("word-swap caller source identity mismatch")
    sources = {caller["sourceFile"]: report["sourceSha256"], "mem.zig": digest(std_mem)}
    links = link(records, [root], sources)
    if len(links["edges"]) != 1 or links["edges"][0]["caller"] != root:
        raise ValueError("word-swap selection requires one direct captured callee")
    edge = links["edges"][0]
    record = records[edge["callee"]]
    decoder = WordSwapDecoder(record, sources)
    definition = decoder.program(record)
    lines = ["/-", "// Copyright (C) 2026 OKcontract Pte. Ltd.", "// SPDX-License-Identifier: GPL-3.0",
             "Generated from captured AIR; do not edit. Source/backend preservation remains open.", "-/",
             "import Compiler.ZigAir.MemoryWordPair", "", "namespace Compiler.ZigAir.GeneratedMemory",
             "open MemoryAir", "", "def fn_swap_u32 : WordPairProgram :=", definition, "",
             "end Compiler.ZigAir.GeneratedMemory", ""]
    with output.open("x") as stream:
        stream.write("\n".join(lines))
    manifest = {"schema": "oksolc.word-swap-generation.v1", "proofScope": "zigFreshAirUnderWordPairContract",
                "captureReportSha256": digest(report_path), "leanSha256": digest(output), "selectedCall": edge,
                "links": links, "airSha256": report["functions"][edge["callee"]]["sha256"],
                "specialization": record["specialization"], "specializationSha256": decoder.specialization_key,
                "signature": record["signature"], "runtimeParameterIndices": decoder.source_parameters,
                "entryContract": "initialized-writable-disjoint-u32-pair-v1",
                "bodyInstructions": len(decoder.visited), "sourceGuards": len(decoder.guards_seen),
                "wordByteViews": decoder.byte_inventory(), "loops": sorted(decoder.loop_ids),
                "repeatTargets": sorted(decoder.repeat_targets), "executionModel": "resumableMemoryAir",
                "bodyDecoded": True, "specializationSemanticsVerified": False, "bodyFootprintVerified": False,
                "capturedSwapLoopVerified": False, "nativeNoaliasVerified": False, "sourceSafetyVerified": False,
                "nativeBackendVerified": False, "wholeCompilerVerified": False}
    write_json(manifest_path, manifest)
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", type=Path, required=True)
    parser.add_argument("--root", required=True)
    parser.add_argument("--std-mem", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    generate(args.capture, args.root, args.std_mem, args.output, args.manifest)
