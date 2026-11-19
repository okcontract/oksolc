#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture production exponentiation; preserve its shifts and wide stack layout.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This is source-bound capture and native regression evidence, not preservation.
"""

import argparse
import copy
from collections import Counter
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean/zig_air"))
from build_toolchain import digest, run, source_identity, write_json
from capture import inspect_records, read_json
from generate import fields
from check_zig_air_loops import inspect_loops
from check_zig_air_memory import inspect_memory, layout, pointer, uint
from check_zig_air_validity import positions
from zig_air_exp_native import CASES

ROOTS = ["numeric.exp256"]


def inspect_shift(inst, instructions, visible):
    fields(inst, "index tag payloadVisited type lhs rhs")
    if inst["tag"] != "shr" or inst["payloadVisited"] is not True:
        raise ValueError("missing exponent right-shift payload")
    fields(inst["lhs"], "kind index")
    left = inst["lhs"]["index"]
    if (inst["lhs"]["kind"] != "instruction" or type(left) is not int or left not in visible or
            not 0 <= left < len(instructions) or inst["type"] != uint(256) or instructions[left]["type"] != uint(256)):
        raise ValueError("shift left operand lost type or dominance")
    if (not isinstance(inst["rhs"], dict) or type(inst["rhs"].get("value")) is not int or
            inst["rhs"] != {"kind": "constant", "type": uint(8), "value": 1}):
        raise ValueError("exponent halving lost its typed shift count")
    return {"instruction": inst["index"], "lhs": left, "count": 1, "countBits": 8}


def inspect_exp(record):
    config, signature = record["configuration"], record["signature"]
    if (config["arch"] != "aarch64" or config["os"] != "macos" or
            config["pointerBits"] != 64 or config["endianness"] != "little"):
        raise ValueError("exponentiation capture oracle requires aarch64-macos")
    if (signature["parameters"] != [uint(256), uint(256)] or signature["returnType"] != uint(256) or
            signature["genericInstance"] is not False or signature["varArgs"] is not False or signature["noaliasBits"] != 0):
        raise ValueError("production exponentiation signature changed")
    located, instructions = positions(record), record["instructions"]
    control, memory = inspect_loops(record), inspect_memory(record)
    tags = Counter(instructions[i]["tag"] for i in located)
    if len(control["loops"]) != 1 or any(tags[tag] != count for tag, count in
            (("alloc", 3), ("bit_and", 1), ("mul_wrap", 2), ("shr", 1))):
        raise ValueError("exponentiation capture lost required operations")
    shifts = []
    for index, (visible, _) in located.items():
        inst = instructions[index]
        if inst["tag"] == "alloc" and inst["type"] != pointer(uint(256), layout(32, 16)):
            raise ValueError("wide stack layout or attributes changed")
        if inst["tag"] != "shr":
            continue
        shifts.append(inspect_shift(inst, instructions, visible))
    for index, inst in enumerate(instructions):
        if index not in located and (inst.get("payloadVisited") is not False or
                inst.get("unsupportedPayload") is not True or
                set(inst) != {"index", "tag", "payloadVisited", "unsupportedPayload", "reason"}):
            raise ValueError("unused AIR placeholder was decoded")
    return {"control": control, "memory": memory, "tags": dict(tags), "shifts": shifts,
            "stackLayout": layout(32, 16), "unusedEntries": len(instructions) - len(located)}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.exp-air-capture-tests.v1", "status": "failed", "modes": {}, "captureExecution": "sequential",
              "productionRoot": ROOTS[0], "sourceSafetyVerified": False, "expPreservationVerified": False,
              "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        toolchain = read_json(args.toolchain)
        if toolchain.get("status") not in ("built", "built-with-diagnostics") or toolchain.get("freshAirCaptureImplemented") is not True:
            raise ValueError("incomplete capture toolchain")
        compiler, bootstrap = (Path(toolchain[name]["path"]) for name in ("compiler", "bootstrap"))
        lib = Path(toolchain["compiler"]["zigLibDir"])
        for name, binary in (("compiler", compiler), ("bootstrap", bootstrap)):
            if digest(binary) != toolchain[name]["sha256"]:
                raise ValueError("toolchain binary changed: " + name)
        if source_identity(lib.parent) != toolchain["sourceTree"]:
            raise ValueError("toolchain source changed")
        report["toolchainReportSha256"] = digest(args.toolchain)
        report["sourceTree"] = source_identity(ROOT / "src")
        source = ROOT / "src/libsolutil/numeric.zig"
        wrapper = ROOT / "test/lean/zig_air_exp.zig"
        report["numericSourceSha256"] = digest(source)
        tracked = [wrapper, *sorted((ROOT / "test/lean").glob("*zig_air*.py")),
                   *sorted((ROOT / "lean/zig_air").glob("*.*"))]
        report["inputs"] = {str(p.relative_to(ROOT)): digest(p) for p in tracked if p.is_file()}
        for mode in ("ReleaseFast", "ReleaseSafe", "Debug"):
            directory = output / mode
            directory.mkdir()
            fixture, air = directory / wrapper.name, directory / "air"
            fixture.write_bytes(wrapper.read_bytes())
            air.mkdir()
            common = ["--zig-lib-dir", lib, "-fllvm", "-fno-incremental", "-fstrip", "-O" + mode,
                      "--dep", "numeric", "-Mroot=" + str(fixture), "-Mnumeric=" + str(source),
                      "--global-cache-dir", directory / "global-cache"]
            for name, binary in (("captured", compiler), ("ordinary", compiler), ("bootstrap", bootstrap)):
                extra = ["--semantic-export=" + str(air)] if name == "captured" else []
                run(directory, name, [binary, "build-obj", *common, "--cache-dir", directory / (name + "-cache"),
                                      "-femit-bin=" + str(directory / (name + ".o")), *extra])
            functions = inspect_records(air, ROOTS, report["numericSourceSha256"], mode)
            record = read_json(air / functions[ROOTS[0]]["file"])
            observed = inspect_exp(record)
            negatives = []
            for name, change in (
                ("missing-rhs", lambda inst: inst.pop("rhs")),
                ("wrong-count", lambda inst: inst["rhs"].update(value=2)),
                ("wrong-count-width", lambda inst: inst["rhs"].update(type=uint(256))),
                ("non-dominating-lhs", lambda inst: inst.update(lhs={"kind": "instruction", "index": inst["index"]})),
                ("missing-shift", lambda inst: inst.update(tag="shr_exact"))):
                changed = copy.deepcopy(record)
                change(changed["instructions"][observed["shifts"][0]["instruction"]])
                try:
                    inspect_exp(changed)
                except ValueError as error:
                    negatives.append({"name": name, "rejected": True, "reason": str(error)})
                else:
                    raise ValueError("corrupt shift capture accepted: " + name)
            objects = {name: digest(directory / (name + ".o")) for name in ("captured", "ordinary", "bootstrap")}
            if len(set(objects.values())) != 1:
                raise ValueError("exponentiation native object differs across compiler or capture settings")
            library = directory / "native.dylib"
            run(directory, "native-build", [compiler, "build-lib", "-dynamic", *common,
                "--cache-dir", directory / "native-cache", "-femit-bin=" + str(library)])
            run(directory, "native-cases", [sys.executable, ROOT / "test/lean/zig_air_exp_native.py",
                "--library", library, "--output", directory / "native-observations.json"])
            native = read_json(directory / "native-observations.json")
            if (native.get("schema") != "oksolc.native-exp-cases.v1" or len(native["cases"]) != 14 or
                    [(case["base"], case["exponent"]) for case in native["cases"]] !=
                    [(str(base), str(exponent)) for base, exponent in CASES] or
                    any(case["expected"] != case["actual"] for case in native["cases"])):
                raise ValueError("incomplete or mismatching native exponentiation observations")
            report["modes"][mode] = {"functions": functions, "inspection": observed, "negativeControls": negatives,
                "objects": objects, "nativeCases": len(native["cases"]), "nativeLibrarySha256": digest(library),
                "nativeObservationsSha256": digest(directory / "native-observations.json")}
            write_json(directory / "report.json", {
                "schema": "oksolc.fresh-air-capture.v1", "status": "captured", "captureComplete": True,
                "sourceSha256": report["numericSourceSha256"], "functions": functions, "objects": objects,
                "sourceSafetyVerified": False, "wholeCompilerVerified": False,
                "toolchainReportSha256": report["toolchainReportSha256"]})
            report["modes"][mode]["captureReportSha256"] = digest(directory / "report.json")
        for path, expected in report["inputs"].items():
            if digest(ROOT / path) != expected:
                raise ValueError("capture harness input changed: " + path)
        if source_identity(ROOT / "src") != report["sourceTree"] or source_identity(lib.parent) != toolchain["sourceTree"]:
            raise ValueError("source tree changed during capture")
        if digest(args.toolchain) != report["toolchainReportSha256"]:
            raise ValueError("toolchain report changed")
        for name, binary in (("compiler", compiler), ("bootstrap", bootstrap)):
            if digest(binary) != toolchain[name]["sha256"]:
                raise ValueError("toolchain binary changed: " + name)
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
