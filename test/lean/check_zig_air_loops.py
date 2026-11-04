#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check captured loop payloads and native transparency, not loop preservation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import argparse
import copy
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean/zig_air"))
from build_toolchain import digest, run, write_json
from capture import capture, read_json
from generate import fields, natural
from check_zig_air_validity import positions
from check_zig_air_memory import inspect_memory, layout, pointer, uint

ROOTS = ["zig_air_loops." + name for name in ("fill", "copy_forward", "nested_continue")]


def inspect_signature(record):
    word = pointer(uint(32), layout(4, 4), size="many")
    expected = {
        ROOTS[0]: [word, uint(64), uint(32)],
        ROOTS[1]: [word, pointer(uint(32), layout(4, 4), size="many", const=True), uint(64)],
        ROOTS[2]: [word, uint(64), uint(64), uint(64), uint(32)],
    }
    config, signature = record["configuration"], record["signature"]
    if (config["arch"] != "aarch64" or config["os"] != "macos" or
            config["pointerBits"] != 64 or config["endianness"] != "little"):
        raise ValueError("loop fixture oracle is scoped to aarch64-macos")
    if (signature["parameters"] != expected[record["name"]] or signature["returnType"] != {"kind": "void"} or
            signature["noaliasBits"] != 0 or signature["genericInstance"] is not False or signature["varArgs"] is not False):
        raise ValueError("loop fixture signature changed")


def inspect_loops(record):
    """Independent lexical-control inspection; does not interpret primitives."""
    instructions = record["instructions"]
    located = positions(record)
    loops, repeats = {}, []
    for index, (_, path) in located.items():
        inst = instructions[index]
        if inst.get("payloadVisited") is not True or inst.get("unsupportedPayload"):
            raise ValueError("loop fixture has unsupported or unvisited payload")
        if inst["tag"] == "loop":
            fields(inst, "index tag payloadVisited type body")
            if inst["type"] != {"kind": "noreturn"} or not inst["body"]:
                raise ValueError("loop lost non-returning body")
            loops[index] = {"bodyInstructions": len(inst["body"]), "backedges": 0}
        elif inst["tag"] == "repeat":
            fields(inst, "index tag payloadVisited type target")
            target = natural(inst["target"], len(instructions) - 1)
            ancestors = [owner for owner, _ in path if instructions[owner]["tag"] == "loop"]
            if inst["type"] != {"kind": "noreturn"} or target not in ancestors:
                raise ValueError("repeat target is not an enclosing loop")
            repeats.append((index, target))
        bodies = ([record["body"]] if index == record["body"][0] else [])
        if inst["tag"] in ("block", "loop"):
            bodies.append(inst["body"])
        elif inst["tag"] == "cond_br":
            bodies.extend((inst["thenBody"], inst["elseBody"]))
        for body in bodies:
            if not body or any(instructions[i]["tag"] in ("loop", "repeat", "br", "cond_br", "ret", "ret_safe", "ret_load")
                               for i in body[:-1]):
                raise ValueError("loop fixture body has code after a terminator")
            if instructions[body[-1]]["tag"] not in ("loop", "repeat", "br", "cond_br", "ret", "ret_safe", "ret_load"):
                raise ValueError("loop fixture body has no terminator")
    for _, target in repeats:
        loops[target]["backedges"] += 1
    if not loops or any(loop["backedges"] == 0 for loop in loops.values()):
        raise ValueError("loop fixture lost its back edges")
    return {"loops": loops, "repeats": [{"instruction": i, "target": t} for i, t in repeats],
            "bodyInstructions": len(located)}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = ROOT / "test/lean/zig_air_loops.zig"
    report = {"schema": "oksolc.loop-air-capture-tests.v1", "status": "failed", "modes": {},
              "sourceSafetyVerified": False, "loopPreservationVerified": False,
              "nativeBackendVerified": False, "wholeCompilerVerified": False}
    tracked = [source, Path(__file__), ROOT / "test/lean/zig_air_loops_native.py",
               ROOT / "test/lean/check_zig_air_validity.py", ROOT / "test/lean/check_zig_air_memory.py",
               *sorted((ROOT / "lean/zig_air").glob("*.*"))]
    report["inputs"] = {str(p.relative_to(ROOT)): digest(p) for p in tracked if p.is_file()}
    try:
        toolchain = read_json(args.toolchain)
        report["toolchainReportSha256"] = digest(args.toolchain)
        bootstrap = Path(toolchain["bootstrap"]["path"])
        if digest(bootstrap) != toolchain["bootstrap"]["sha256"]:
            raise ValueError("bootstrap identity mismatch")
        for mode in ("ReleaseFast", "ReleaseSafe", "Debug"):
            directory = output / mode
            capture(argparse.Namespace(toolchain=args.toolchain, source=source, output=directory, root=ROOTS, mode=mode))
            captured = read_json(directory / "report.json")
            observations = {}
            for root in ROOTS:
                entry = captured["functions"][root]
                path = directory / "air" / entry["file"]
                if entry["requested"] is not True or digest(path) != entry["sha256"]:
                    raise ValueError("loop AIR identity mismatch")
                record = read_json(path)
                inspect_signature(record)
                control = inspect_loops(record)
                if len(control["loops"]) != (2 if root.endswith("nested_continue") else 1):
                    raise ValueError("loop fixture lost expected nesting")
                observations[root] = {"control": control, "memory": inspect_memory(record)}
                # Target corruption must be rejected by this independent traversal.
                changed = copy.deepcopy(record)
                index = control["repeats"][0]["instruction"]
                changed["instructions"][index]["target"] = index
                try:
                    inspect_loops(changed)
                except ValueError:
                    pass
                else:
                    raise ValueError("self-targeting repeat was accepted")
                write_json(directory / (root.rsplit(".", 1)[-1] + ".invalid-repeat.json"), changed)
            write_json(directory / "observations.json", observations)
            baseline = read_json(directory / "ordinary.process.json")["command"]
            baseline[0] = str(bootstrap)
            baseline[baseline.index("--cache-dir") + 1] = str(directory / "bootstrap-cache")
            baseline = ["-femit-bin=" + str(directory / "bootstrap.o") if a.startswith("-femit-bin=") else a for a in baseline]
            run(directory, "bootstrap", baseline)
            if any(digest(directory / (label + ".o")) != captured["objects"]["captured"]
                   for label in ("ordinary", "captured", "bootstrap")):
                raise ValueError("loop capture changed native object bytes")
            library = directory / "loops.dylib"
            command = read_json(directory / "ordinary.process.json")["command"]
            command[command.index("build-obj")] = "build-lib"
            command.append("-dynamic")
            command[command.index("--cache-dir") + 1] = str(directory / "native-cache")
            command = ["-femit-bin=" + str(library) if a.startswith("-femit-bin=") else a for a in command]
            run(directory, "native-build", command)
            run(directory, "native-cases", [sys.executable, ROOT / "test/lean/zig_air_loops_native.py",
                                            "--library", library, "--output", directory / "native-observations.json"])
            report["modes"][mode] = {"status": "passed", "captureReportSha256": digest(directory / "report.json"),
                "observations": observations, "objectSha256": captured["objects"]["captured"],
                "nativeLibrarySha256": digest(library), "nativeObservationsSha256": digest(directory / "native-observations.json")}
        if any(digest(ROOT / path) != expected for path, expected in report["inputs"].items()):
            raise ValueError("loop capture inputs changed")
        if digest(args.toolchain) != report["toolchainReportSha256"]:
            raise ValueError("loop toolchain report changed")
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
