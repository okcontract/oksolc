#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture actual production signed-word conversions for subsequent Lean proofs.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean/zig_air"))
from build_toolchain import digest, run, source_identity, write_json
from capture import inspect_records, read_json


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.fresh-air-numeric.v1", "status": "failed", "wholeCompilerVerified": False,
              "sourceSafetyVerified": False, "leanTranslationImplemented": False, "mode": "ReleaseFast"}
    try:
        toolchain = read_json(args.toolchain)
        if toolchain.get("status") not in ("built", "built-with-diagnostics") or not toolchain.get("freshAirCaptureImplemented"):
            raise ValueError("incomplete capture toolchain")
        compiler, bootstrap = (Path(toolchain[name]["path"]) for name in ("compiler", "bootstrap"))
        lib = Path(toolchain["compiler"]["zigLibDir"])
        for name, executable in (("compiler", compiler), ("bootstrap", bootstrap)):
            if digest(executable) != toolchain[name]["sha256"]:
                raise ValueError(name + " binary hash mismatch")
        if source_identity(lib.parent) != toolchain["sourceTree"]:
            raise ValueError("toolchain source tree changed")
        report["toolchainReportSha256"] = digest(args.toolchain)
        report["sourceTree"] = source_identity(ROOT / "src")
        wrapper = ROOT / "test/lean/zig_air_numeric.zig"
        inputs = [*sorted((ROOT / "lean/zig_air").glob("*.*")), Path(__file__).resolve(), wrapper]
        report["inputs"] = {str(path.relative_to(ROOT)): digest(path) for path in inputs if path.is_file()}
        numeric = ROOT / "src/libsolutil/numeric.zig"
        report["numericSourceSha256"] = digest(numeric)
        fixture = output / wrapper.name
        fixture.write_bytes(wrapper.read_bytes())
        air = output / "air"
        air.mkdir()
        common = ["build-obj", "--zig-lib-dir", lib, "-fllvm", "-fno-incremental", "-fstrip", "-OReleaseFast",
                  "--dep", "numeric", "-Mroot=" + str(fixture), "-Mnumeric=" + str(numeric),
                  "--global-cache-dir", output / "global-cache"]
        for name, executable in (("capture", compiler), ("ordinary", compiler), ("bootstrap", bootstrap)):
            extra = ["--semantic-export=" + str(air)] if name == "capture" else []
            run(output, name, [executable, *common, "--cache-dir", output / (name + "-cache"),
                              "-femit-bin=" + str(output / (name + ".o")), *extra])
        roots = ["numeric.u2s", "numeric.s2u"]
        report["functions"] = inspect_records(air, roots, report["numericSourceSha256"], "ReleaseFast")
        for name in roots:
            record = read_json(air / report["functions"][name]["file"])
            if record["signature"]["genericInstance"] or record["signature"]["varArgs"]:
                raise ValueError("unexpected numeric specialization")
            signed = {"kind": "int", "bits": 256, "signedness": "signed"}
            unsigned = {"kind": "int", "bits": 256, "signedness": "unsigned"}
            input_type, output_type = (unsigned, signed) if name == "numeric.u2s" else (signed, unsigned)
            if record["signature"]["parameters"] != [input_type] or record["signature"]["returnType"] != output_type:
                raise ValueError("production 256-bit signature changed")
            instructions = record["instructions"]
            reachable = set()
            pending = list(record["body"])
            while pending:
                index = pending.pop()
                if type(index) is not int or not 0 <= index < len(instructions):
                    raise ValueError("invalid numeric body reference")
                if index in reachable:
                    continue
                reachable.add(index)
                inst = instructions[index]
                if not inst.get("payloadVisited") or inst.get("unsupportedPayload"):
                    raise ValueError("numeric body payload is incomplete")
                for key in ("body", "thenBody", "elseBody"):
                    pending.extend(inst.get(key, []))
            for index, inst in enumerate(instructions):
                if index not in reachable and (inst.get("payloadVisited") is not False or not inst.get("unsupportedPayload")):
                    raise ValueError("unused numeric payload was decoded")
                if index not in reachable and set(inst) != {"index", "tag", "payloadVisited", "unsupportedPayload", "reason"}:
                    raise ValueError("unused entry leaked payload or type data")
            if name == "numeric.s2u" and len(reachable) == len(instructions):
                raise ValueError("unused-placeholder regression no longer exercised")
            if not {"block", "br", "cond_br", "int_cast"}.issubset(i["tag"] for i in instructions):
                raise ValueError("numeric control or cast instruction missing")
            constants = set()
            for inst in instructions:
                for key in ("lhs", "rhs", "operand", "condition"):
                    ref = inst.get(key)
                    if ref and ref["kind"] == "constant":
                        constants.add(ref["value"])
                    if ref and ref["kind"] == "unsupported":
                        raise ValueError("numeric operand was not represented")
                for key in ("body", "thenBody", "elseBody"):
                    if key in inst and any(type(i) is not int or not 0 <= i < len(instructions) for i in inst[key]):
                        raise ValueError("invalid nested AIR body")
                if inst["tag"] == "br" and instructions[inst["target"]]["tag"] != "block":
                    raise ValueError("invalid numeric branch destination")
            if not {2 ** 255, -(2 ** 255)}.issubset(constants):
                raise ValueError("signed 256-bit boundary constants changed")
        boundary = read_json(air / report["functions"][wrapper.stem + ".at_constant_limit"]["file"])
        constants = [i["rhs"] for i in boundary["instructions"] if i["tag"] == "add_wrap"]
        if constants != [{"kind": "constant", "type": {"kind": "int", "bits": 512, "signedness": "unsigned"}, "value": 2 ** 511}]:
            raise ValueError("512-bit constant was not exported exactly")
        beyond = read_json(air / report["functions"][wrapper.stem + ".above_constant_limit"]["file"])
        constants = [i["rhs"] for i in beyond["instructions"] if i["tag"] == "add_wrap"]
        if constants != [{"kind": "unsupported", "reason": "constant-width-above-512"}]:
            raise ValueError("constant beyond the export bound did not reject explicitly")
        report["objects"] = {name: digest(output / (name + ".o")) for name in ("capture", "ordinary", "bootstrap")}
        if len(set(report["objects"].values())) != 1:
            raise ValueError("numeric native object differs across capture settings or compiler")
        if source_identity(ROOT / "src") != report["sourceTree"] or source_identity(lib.parent) != toolchain["sourceTree"]:
            raise ValueError("source inputs changed during capture")
        for name, expected in report["inputs"].items():
            if digest(ROOT / name) != expected:
                raise ValueError("harness input changed during capture: " + name)
        for name, executable in (("compiler", compiler), ("bootstrap", bootstrap)):
            if digest(executable) != toolchain[name]["sha256"]:
                raise ValueError(name + " binary changed during capture")
        report["status"] = "captured"
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
