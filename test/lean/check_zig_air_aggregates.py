#!/usr/bin/env python3
"""Check aggregate capture against a native fixture; no preservation claim.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean/zig_air"))
from build_toolchain import digest, run, write_json
from capture import capture, read_json, inspect_records
from generate import captured_path
from generate_memory import LoopDecoder

NAMES = ("initialize", "touch", "packed_read", "tagged_read", "ordinal_bytes", "open_bytes", "enum_byte")
HELPERS = ("initial", "signed_view")
MODES = ("Debug", "ReleaseSafe", "ReleaseFast")
PREFIX = "zig_air_aggregates."
FIXTURE = ROOT / "test/lean/zig_air_aggregates.zig"


def expect(actual, expected, message):
    # JSON identity also distinguishes booleans from integer indices/offsets.
    if json.dumps(actual, sort_keys=True) != json.dumps(expected, sort_keys=True):
        raise ValueError(message)


def types(source_sha):
    scalar = lambda bits: {"kind": "int", "bits": bits, "signedness": "unsigned"}
    def record(name, size, fields):
        return {"kind": "struct", "identity": {"name": PREFIX + name,
            "sourceFile": FIXTURE.name, "sourceSha256": source_sha}, "containerLayout": "extern",
            "layout": {"kind": "abi", "bytes": size, "alignment": 8},
            "fields": [{"index": i, "name": name, "offset": offset, "explicitAlignment": None, "type": ty}
                       for i, (name, offset, ty) in enumerate(fields)]}
    byte, word = scalar(8), scalar(64)
    inner = record("Inner", 16, [("byte", 0, byte), ("word", 8, word)])
    tail = {"kind": "array", "length": 3, "child": byte,
            "layout": {"kind": "abi", "bytes": 3, "alignment": 1}, "sentinel": None}
    outer = record("Record", 48, [("tiny", 0, byte), ("big", 8, word), ("child", 16, inner),
                                   ("tail", 32, tail), ("count", 40, word)])
    return outer, inner, byte, word, tail


def initializer(source_sha):
    outer, inner, byte, word, tail = types(source_sha)
    undef = lambda ty: {"kind": "undefined", "type": ty}
    number = lambda value: {"kind": "constant", "type": word, "value": value}
    return {"kind": "aggregate", "type": outer, "fields": [undef(byte), number(0),
        {"kind": "aggregate", "type": inner, "fields": [undef(byte), number(9)]}, undef(tail), number(0)]}


def enum_types(source_sha):
    def enum(name, bits, signedness, nonexhaustive, values):
        return {"kind": "enum", "identity": {"name": PREFIX + name, "sourceFile": FIXTURE.name,
            "sourceSha256": source_sha}, "backingType": {"kind": "int", "bits": bits, "signedness": signedness},
            "layout": {"kind": "abi", "bytes": bits // 8, "alignment": bits // 8},
            "nonexhaustive": nonexhaustive,
            "fields": [{"index": i, "name": field, "value": value} for i, (field, value) in enumerate(values)]}
    ordinal = enum("Ordinal", 32, "unsigned", False, [("zero", 0), ("one", 1)])
    signed = enum("Signed", 32, "signed", False, [("negative", -7), ("positive", 11)])
    opened = enum("Open", 16, "unsigned", True, [("one", 1), ("maximum", 65535)])
    owner = {"kind": "struct", "identity": {"name": PREFIX + "EnumRecord", "sourceFile": FIXTURE.name,
        "sourceSha256": source_sha}, "containerLayout": "extern", "layout": {"kind": "abi", "bytes": 8, "alignment": 4},
        "fields": [{"index": i, "name": name, "offset": offset, "explicitAlignment": None, "type": ty}
            for i, (name, offset, ty) in enumerate((("marker", 0, {"kind": "int", "bits": 8, "signedness": "unsigned"}),
                                                  ("tag", 4, signed)))]}
    return ordinal, signed, opened, owner


def inspect_enums(records, source_sha):
    ordinal, signed, opened, owner = enum_types(source_sha)
    for name, ty in (("ordinal_bytes", ordinal), ("open_bytes", opened), ("signed_view", signed), ("enum_byte", owner)):
        expect(records[PREFIX + name]["signature"]["parameters"][0]["child"], ty, "enum identity/backing/layout changed")
    instructions = records[PREFIX + "signed_view"]["instructions"]
    converted = [i for i in instructions if i.get("payloadVisited") is True and i["tag"] == "array_to_slice"]
    expect(len(converted), 1, "enum byte view lost array-to-slice conversion")
    ref = converted[0].get("operand", {})
    if (converted[0].get("unsupportedPayload", False) or ref.get("kind") != "instruction" or
            type(ref.get("index")) is not int or not 0 <= ref["index"] < converted[0]["index"]):
        raise ValueError("array-to-slice operand missing or invalid")
    producer = instructions[ref["index"]]
    if producer["tag"] != "call" or not producer["callee"]["identity"]["name"].startswith("mem.asBytes__func_"):
        raise ValueError("enum byte conversion lost its actual producer")
    return {"enumTypes": 3, "enumContainingRecord": True, "arrayConversionOperand": ref["index"]}


def inspect(records, source_sha):
    outer = types(source_sha)[0]
    active = lambda name: [x for x in records[PREFIX + name]["instructions"] if x.get("payloadVisited") is True]
    stored = [x["rhs"] for x in active("initial") if x["tag"] in ("store", "store_safe") and x["rhs"].get("kind") == "aggregate"]
    expect(stored, [initializer(source_sha)], "partial aggregate initializer changed")
    expect(records[PREFIX + "initialize"]["signature"]["parameters"][0]["child"], outer, "record layout changed")
    pointers = [x for x in active("touch") if x["tag"].startswith("struct_field_ptr")]
    for inst in pointers:
        index = inst.get("fieldIndex")
        tag = inst["tag"]
        if type(index) is not int or (tag != "struct_field_ptr" and tag != "struct_field_ptr_index_" + str(index)):
            raise ValueError("field index disagrees with AIR encoding")
        operand = inst.get("operand")
        if (not isinstance(operand, dict) or set(operand) != {"kind", "index"} or
                operand["kind"] != "instruction" or type(operand["index"]) is not int or
                not 0 <= operand["index"] < inst["index"]):
            raise ValueError("field pointer lost its actual source operand")
    expect(sorted(set(x["fieldIndex"] for x in pointers)), list(range(5)), "field-pointer coverage changed")
    expect(records[PREFIX + "initial"]["signature"]["returnType"], outer, "returned aggregate type changed")
    for name, reason in (("packed_read", "unresolved-or-packed-struct"), ("tagged_read", "comptime-struct-field")):
        expect(records[PREFIX + name]["signature"]["parameters"][0]["child"],
               {"kind": "unsupported", "reason": reason}, "unsupported struct was silently admitted")
    rejections = {}
    enums = inspect_enums(records, source_sha)
    for name in (*NAMES, *HELPERS):
        try:
            record = records[PREFIX + name]
            LoopDecoder(record).program(record)
        except ValueError as error:
            rejections[name] = str(error)
        else:
            raise ValueError("aggregate semantic admission requires a separate reviewed proof")
    return {"fieldPointers": len(pointers), "typedUndefinedFields": 3, "decoderRejections": rejections, "enumByteViews": enums}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.aggregate-air-inspection.v1", "status": "failed", "modes": {},
              "aggregateSemanticsVerified": False, "sourceAdapterFormallyVerified": False}
    inputs = [Path(__file__), FIXTURE, ROOT / "lean/zig_air/SemanticExport.zig",
              *[ROOT / "lean/zig_air" / name for name in ("build_toolchain.py", "capture.py", "generate.py", "generate_memory.py")],
              ROOT / "lean/extract_storage.py", ROOT / "lean/extract_compiler.py"]
    try:
        report["inputs"] = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
        toolchain = read_json(args.toolchain)
        report["toolchainReportSha256"] = digest(args.toolchain)
        export = [p for p in toolchain["freshAirCapturePatch"] if p["file"] == "src/SemanticExport.zig"]
        expect(len(export), 1, "missing exporter build binding")
        expect(export[0]["afterSha256"], report["inputs"]["lean/zig_air/SemanticExport.zig"], "built exporter differs from source")
        native = Path(toolchain["bootstrap"]["path"])
        expect(digest(native), toolchain["bootstrap"]["sha256"], "native compiler changed")
        roots = [PREFIX + name for name in NAMES]
        for mode in MODES:
            run(output, "native-" + mode, [native, "test", FIXTURE, "-fllvm", "-O" + mode,
                "--zig-lib-dir", toolchain["compiler"]["zigLibDir"], "--cache-dir", output / "native-cache",
                "--global-cache-dir", output / "global-cache"])
            directory = output / mode
            capture(argparse.Namespace(source=FIXTURE, source_file=[], toolchain=args.toolchain,
                                      output=directory, mode=mode, root=roots))
            captured = read_json(directory / "report.json")
            entries = inspect_records(directory / "air", roots, digest(FIXTURE), mode)
            expect(entries, captured["functions"], "captured record identity changed")
            records = {name: read_json(captured_path(directory / "report.json", entry)) for name, entry in entries.items()}
            for name in (*NAMES, *HELPERS):
                record = records[PREFIX + name]
                expect([record["name"], record["sourceFile"], record["sourceSha256"]],
                       [PREFIX + name, FIXTURE.name, digest(FIXTURE)], "fixture body identity changed")
            report["modes"][mode] = {**inspect(records, digest(FIXTURE)), "objects": captured["objects"],
                "captureReportSha256": digest(directory / "report.json")}
        expect({str(p.relative_to(ROOT)): digest(p) for p in inputs}, report["inputs"], "inspection inputs changed")
        expect(digest(args.toolchain), report["toolchainReportSha256"], "toolchain report changed")
        expect(digest(native), toolchain["bootstrap"]["sha256"], "native compiler changed")
        report["status"] = "inspected"
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
