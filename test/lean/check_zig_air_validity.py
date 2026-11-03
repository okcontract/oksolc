#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check preserved slice requirements, positions and unchanged native artifacts.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This audits selected capture metadata, not source safety or memory preservation.
"""

import argparse
import copy
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean/zig_air"))
from build_toolchain import digest, run, write_json
from capture import capture, read_json
from generate import Decoder, constant, fields, natural
from generate_memory import Decoder as MemoryDecoder


def positions(record):
    """Independent diagnostic traversal; it does not interpret AIR operations."""
    result = {}
    instructions = record["instructions"]

    def walk(body, visible, path):
        visible = set(visible)
        for index in body:
            natural(index, len(instructions) - 1)
            if index in result:
                raise ValueError("duplicate body ownership")
            result[index] = (set(visible), path)
            inst = instructions[index]
            if inst["tag"] in ("block", "loop"):
                walk(inst["body"], visible, (*path, (index, "body")))
            elif inst["tag"] == "cond_br":
                walk(inst["thenBody"], visible, (*path, (index, "then")))
                walk(inst["elseBody"], visible, (*path, (index, "else")))
            visible.add(index)

    walk(record["body"], set(), ())
    return result


def inspect_slices(record, source):
    located = positions(record)
    result = []
    for item in record["sourceValidity"]["slices"]:
        fields(item, "source anchor start end upperBound unsupportedReason")
        fields(item["source"], "file sha256 span")
        if item["source"]["sha256"] != digest(source) or item["source"]["file"] != source.name:
            raise ValueError("validity source hash mismatch")
        span = item["source"]["span"]
        fields(span, "start end main")
        data = source.read_bytes()
        for value in span.values():
            natural(value, len(data))
        if not span["start"] <= span["main"] < span["end"]:
            raise ValueError("invalid validity source span")
        anchor = item["anchor"]
        if anchor.get("kind") != "beforeInstruction":
            raise ValueError("fixture requires an exact validity position")
        fields(anchor, "kind index inSupportedBody")
        natural(anchor["index"], len(record["instructions"]) - 1)
        if anchor["inSupportedBody"] is not True or anchor["index"] not in located:
            raise ValueError("validity anchor outside supported body")
        if record["instructions"][anchor["index"]]["tag"] not in ("slice", "ptr_cast"):
            raise ValueError("validity anchor is not a slice result")
        visible, path = located[anchor["index"]]

        def reference(ref, integer=False):
            if ref.get("kind") == "instruction":
                fields(ref, "kind index")
                if type(ref["index"]) is not int or ref["index"] not in visible:
                    raise ValueError("validity operand does not dominate its position")
                ty = record["instructions"][ref["index"]]["type"]
                if integer and (ty.get("kind") != "int" or ty.get("signedness") != "unsigned"):
                    raise ValueError("validity bound is not an unsigned integer")
            elif integer:
                ty, _ = constant(ref)
                if ty[0] != "int" or ty[1]:
                    raise ValueError("validity constant is not an unsigned integer")
            else:
                raise ValueError("fixture original slice must be an AIR value")

        reference(item["start"], True)
        reference(item["end"], True)
        bound = item["upperBound"]
        if bound.get("kind") == "sliceLength":
            fields(bound, "kind original")
            reference(bound["original"])
        elif bound.get("kind") == "arrayLength":
            fields(bound, "kind value")
            natural(bound["value"], 2 ** 64 - 1)
        elif bound.get("kind") == "unboundedPointer":
            fields(bound, "kind requiresMemoryValidity")
            if bound["requiresMemoryValidity"] is not True:
                raise ValueError("unbounded pointer lost its memory obligation")
        elif bound == {"kind": "unsupported"}:
            if item["unsupportedReason"] not in ("sentinel", "c_pointer"):
                raise ValueError("missing unsupported validity reason")
        else:
            raise ValueError("unknown validity bound")
        if bound["kind"] != "unsupported" and item["unsupportedReason"] is not None:
            raise ValueError("inconsistent unsupported validity marker")
        result.append({"anchor": anchor["index"], "path": path, "bound": bound["kind"],
                       "source": data[span["start"]:span["end"]].decode(), "unsupported": item["unsupportedReason"]})
    return result


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = ROOT / "test/lean/zig_air_validity.zig"
    names = ("bounded_slice", "conditional_slice", "array_slice", "constant_length", "unused_slice", "sentinel_slice", "c_pointer_slice",
             "unbounded_constant_length", "length_form")
    roots = [source.stem + "." + name for name in names]
    report = {"schema": "oksolc.source-validity-tests.v1", "status": "failed", "sourceSafetyVerified": False,
              "wholeCompilerVerified": False, "modes": {}}
    tracked = [source, Path(__file__), *sorted((ROOT / "lean/zig_air").glob("*.*"))]
    report["inputs"] = {str(p.relative_to(ROOT)): digest(p) for p in tracked if p.is_file()}
    try:
        toolchain = read_json(args.toolchain)
        bootstrap = Path(toolchain["bootstrap"]["path"])
        if digest(bootstrap) != toolchain["bootstrap"]["sha256"]:
            raise ValueError("bootstrap identity mismatch")
        for mode in ("ReleaseFast", "Debug"):
            directory = output / mode
            capture(argparse.Namespace(toolchain=args.toolchain, source=source, output=directory, root=roots, mode=mode))
            captured = read_json(directory / "report.json")
            records = {name: read_json(directory / "air" / captured["functions"][root]["file"])
                       for name, root in zip(names, roots)}
            observations = {name: inspect_slices(record, source) for name, record in records.items()}
            # Persist exact observations before asserting fixture expectations.
            write_json(directory / "observations.json", observations)
            for name, expression in (("bounded_slice", "original[start..end]"),
                                     ("conditional_slice", "original[0..end]"),
                                     ("constant_length", "original[0..4]"), ("unused_slice", "original[0..end]"),
                                     ("array_slice", "p[start..end]"), ("sentinel_slice", "p[0..end]"),
                                     ("c_pointer_slice", "p[0..end]"), ("unbounded_constant_length", "p[0..4]"),
                                     ("length_form", "p[start..][0..length]")):
                if not observations[name] or observations[name][-1]["source"] != expression:
                    raise ValueError("validity source span does not identify its slice: " + name)
            for name in ("bounded_slice", "conditional_slice", "constant_length", "unused_slice"):
                if [r["bound"] for r in observations[name]] != ["unboundedPointer", "sliceLength"]:
                    raise ValueError("original slice length was not retained: " + name)
            if [r["bound"] for r in observations["unbounded_constant_length"]] != ["unboundedPointer"]:
                raise ValueError("constant-length pointer slice lost its memory obligation")
            if "slice_length" not in records["length_form"]["sourceOperationTags"]:
                raise ValueError("length-based slicing lost its Zig 0.17 source operation")
            if mode == "ReleaseFast":
                try:
                    MemoryDecoder(records["length_form"])
                except ValueError as error:
                    if "length-based slice" not in str(error):
                        raise
                else:
                    raise ValueError("unadmitted length-based slice was accepted")
            for item in observations["conditional_slice"]:
                if not any(branch == "then" for _, branch in item["path"]):
                    raise ValueError("conditional validity check lost its branch position")
            array = records["array_slice"]["sourceValidity"]["slices"]
            if len(array) != 1 or array[0]["upperBound"] != {"kind": "arrayLength", "value": 16}:
                raise ValueError("static array bound was not retained")
            for name, reason in (("sentinel_slice", "sentinel"), ("c_pointer_slice", "c_pointer")):
                if len(observations[name]) != 1 or observations[name][0]["unsupported"] != reason:
                    raise ValueError("unmodeled source requirement was not explicit")
            # The existing scalar interpreter must reject all sidecar-bearing roots.
            for record in records.values():
                if mode != "ReleaseFast":
                    continue
                try:
                    Decoder(record)
                except ValueError as error:
                    if "source-validity obligations" not in str(error):
                        raise
                else:
                    raise ValueError("scalar decoder silently erased source validity")
            invalid = copy.deepcopy(records["bounded_slice"])
            invalid["sourceValidity"]["slices"][-1]["end"] = {"kind": "instruction", "index": len(invalid["instructions"]) - 1}
            try:
                inspect_slices(invalid, source)
            except ValueError as error:
                if "dominate" not in str(error):
                    raise
            else:
                raise ValueError("invalid source operand was accepted")
            baseline = read_json(directory / "ordinary.process.json")["command"]
            baseline[0] = str(bootstrap)
            baseline[baseline.index("--cache-dir") + 1] = str(directory / "bootstrap-cache")
            baseline = ["-femit-bin=" + str(directory / "bootstrap.o") if a.startswith("-femit-bin=") else a for a in baseline]
            run(directory, "bootstrap", baseline)
            if any(digest(directory / (label + ".o")) != captured["objects"]["captured"]
                   for label in ("ordinary", "captured", "bootstrap")):
                raise ValueError("validity capture changed native code")
            report["modes"][mode] = {"status": "passed", "objectSha256": captured["objects"]["captured"],
                                     "observations": observations, "captureReportSha256": digest(directory / "report.json")}
        for name, sha in report["inputs"].items():
            if digest(ROOT / name) != sha:
                raise ValueError("validity gate input changed")
        if digest(bootstrap) != toolchain["bootstrap"]["sha256"]:
            raise ValueError("bootstrap changed during validity gate")
        report["status"] = "passed"
    except BaseException as error:
        report["error"] = str(error) or type(error).__name__
        raise
    finally:
        write_json(output / "report.json", report)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
