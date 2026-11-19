#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Audit memory AIR capture fields and unchanged native fixture objects.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This is an exporter regression gate, not a memory-safety or preservation proof.
"""

import argparse
import copy
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean/zig_air"))
from build_toolchain import digest, run, write_json
from capture import capture, read_json
from generate import fields
from check_zig_air_validity import check as check_validity, positions


def uint(bits):
    return {"kind": "int", "bits": bits, "signedness": "unsigned"}


def layout(size, alignment):
    return {"kind": "abi", "bytes": size, "alignment": alignment}


def pointer(child, pointee_layout, *, size="one", alignment=None, const=False,
            volatile=False, allow_zero=False, host_size=0, bit_offset=0):
    return {"kind": "pointer", "child": child, "sentinel": None,
            "layout": layout(16 if size == "slice" else 8, 8), "pointeeLayout": pointee_layout,
            "flags": {"size": size, "alignment": alignment, "isConst": const, "isVolatile": volatile,
                      "allowZero": allow_zero, "addressSpace": "generic", "vectorIndex": None,
                      "hostSizeBytes": host_size, "bitOffset": bit_offset}}


def inspect_memory(record):
    """Check operand retention against typed SSA, including local field aliases."""
    instructions = record["instructions"]
    located = positions(record)
    observed = {}
    for index, (visible, _) in located.items():
        inst = instructions[index]
        tag = inst["tag"]
        base = "index tag payloadVisited type "

        def operand(name):
            ref = inst[name]
            if ref.get("kind") == "instruction":
                fields(ref, "kind index")
                if type(ref["index"]) is not int or ref["index"] not in visible:
                    raise ValueError("memory operand does not dominate instruction")
                return instructions[ref["index"]]["type"]
            if ref.get("kind") == "constant":
                fields(ref, "kind type value")
                return ref["type"]
            if ref.get("kind") == "undefined":
                fields(ref, "kind type")
                return ref["type"]
            raise ValueError("unexpected memory operand")

        def require_pointer(ty):
            if not isinstance(ty, dict) or ty.get("kind") != "pointer":
                raise ValueError("memory operand lost pointer type")
            fields(ty, "kind flags child layout pointeeLayout sentinel")
            return ty["child"]

        if tag == "alloc":
            fields(inst, base + "allocationKind")
            require_pointer(inst["type"])
            if inst["allocationKind"] != "stack":
                raise ValueError("local allocation lost stack ownership")
        elif tag in ("store", "store_safe"):
            fields(inst, base + "lhs rhs")
            child, rhs = require_pointer(operand("lhs")), operand("rhs")
            if child != rhs:
                raise ValueError("store operand type mismatch")
        elif tag in ("ptr_add", "ptr_sub", "ptr_elem_ptr", "slice_elem_ptr", "slice"):
            fields(inst, base + "lhs rhs")
            left, right = operand("lhs"), operand("rhs")
            child = require_pointer(left)
            if right != uint(record["configuration"]["pointerBits"]):
                raise ValueError("pointer offset or slice length lost usize type")
            if tag == "slice":
                if require_pointer(inst["type"]) != child or inst["type"]["flags"]["size"] != "slice":
                    raise ValueError("slice constructor lost element type")
            elif tag in ("ptr_elem_ptr", "slice_elem_ptr"):
                expected = copy.deepcopy(left)
                expected["flags"]["size"] = "one"
                expected["layout"] = layout(8, 8)
                input_size = "slice" if tag == "slice_elem_ptr" else "many"
                if left["flags"]["size"] != input_size or inst["type"] != expected:
                    raise ValueError("fixture element pointer changed pointee or attributes")
            elif inst["type"] != left:
                raise ValueError("pointer arithmetic changed type")
        elif tag in ("load", "ret_load", "slice_len", "slice_ptr", "ptr_slice_len_ptr", "ptr_slice_ptr_ptr"):
            fields(inst, base + "operand")
            ty = operand("operand")
            child = require_pointer(ty)
            if tag in ("load", "ret_load"):
                result = record["signature"]["returnType"] if tag == "ret_load" else inst["type"]
                if child != result:
                    raise ValueError("loaded value lost pointee type")
            elif tag in ("ptr_slice_len_ptr", "ptr_slice_ptr_ptr"):
                require_pointer(child)
                if child["flags"]["size"] != "slice":
                    raise ValueError("field projection lost original slice pointer")
                projected = require_pointer(inst["type"])
                if tag == "ptr_slice_len_ptr" and projected != uint(record["configuration"]["pointerBits"]):
                    raise ValueError("slice length field has wrong type")
                if tag == "ptr_slice_ptr_ptr" and require_pointer(projected) != child["child"]:
                    raise ValueError("slice pointer field has wrong element type")
            elif ty["flags"]["size"] != "slice":
                raise ValueError("slice projection lost original slice")
        else:
            continue
        if inst["payloadVisited"] is not True:
            raise ValueError("memory instruction payload was not visited")
        observed[tag] = observed.get(tag, 0) + 1
    return observed


def inspect_signatures(records):
    u8, u32 = uint(8), uint(32)
    slice_ty = pointer(u8, layout(1, 1), size="slice")
    expected = {
        "move_back": [pointer(u32, layout(4, 4), size="many"), uint(64)],
        "load_store": [pointer(u32, layout(4, 4)), u32],
        "slice_fields": [pointer(slice_ty, layout(16, 8)), uint(64)],
        "buffer_alias": [pointer(u32, layout(4, 4), size="many"), uint(64), u32, u32],
        "initialize_slice": [pointer(slice_ty, layout(16, 8)), pointer(u8, layout(1, 1), size="many"), uint(64)],
        "initialize_length": [pointer(slice_ty, layout(16, 8)), uint(64)],
        "unaligned_volatile": [pointer(u32, layout(4, 4), alignment=1, volatile=True)],
        "allow_zero": [pointer(u8, layout(1, 1), allow_zero=True)],
        "packed_pointer": [pointer(uint(3), layout(1, 1), alignment=1, host_size=1, bit_offset=3)],
        "opaque_pointer": [pointer({"kind": "unsupported", "zigTypeTag": "opaque"},
                                   {"kind": "unsupported", "reason": "non-scalar-layout"})],
        "undefined_store": [pointer(u32, layout(4, 4))],
    }
    for name, parameters in expected.items():
        if records[name]["signature"]["parameters"] != parameters:
            raise ValueError("memory signature attributes changed: " + name)


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = ROOT / "test/lean/zig_air_memory.zig"
    names = ("move_back", "load_store", "slice_fields", "buffer_alias", "initialize_slice", "initialize_length", "unaligned_volatile", "allow_zero",
             "packed_pointer", "opaque_pointer", "undefined_store")
    roots = [source.stem + "." + name for name in names]
    report = {"schema": "oksolc.memory-air-tests.v1", "status": "failed", "memorySafetyVerified": False,
              "wholeCompilerVerified": False, "modes": {}}
    tracked = [source, Path(__file__), ROOT / "test/lean/check_zig_air_validity.py", ROOT / "test/lean/zig_air_validity.zig",
               *sorted((ROOT / "lean/zig_air").glob("*.*"))]
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
            for record in records.values():
                config = record["configuration"]
                if (config["arch"] != "aarch64" or config["os"] != "macos" or
                        config["pointerBits"] != 64 or config["endianness"] != "little"):
                    raise ValueError("fixture layout oracle is scoped to aarch64-macos")
            observations = {name: inspect_memory(record) for name, record in records.items()}
            write_json(directory / "observations.json", observations)
            inspect_signatures(records)
            required = {"alloc", "load", "ptr_sub", "ptr_slice_len_ptr", "ptr_slice_ptr_ptr"}
            if not required <= set().union(*(set(tags) for tags in observations.values())):
                raise ValueError("missing memory operation coverage")
            undefined = [i for i in records["undefined_store"]["instructions"] if i["tag"] in ("store", "store_safe")]
            undefined_word = {"kind": "undefined", "type": uint(32)}
            if not any(i["rhs"] == undefined_word for i in undefined):
                raise ValueError("undefined memory write disappeared")
            if not any(i["tag"] == ("store_safe" if mode == "Debug" else "store") and
                       i["rhs"] == undefined_word for i in undefined):
                raise ValueError("undefined write lost its safety mode")
            # Attribute erasure must invalidate the independent source oracle.
            mutant = copy.deepcopy(records)
            mutant["packed_pointer"]["signature"]["parameters"][0]["flags"]["bitOffset"] = 0
            try:
                inspect_signatures(mutant)
            except ValueError:
                pass
            else:
                raise ValueError("packed-pointer mutation was accepted")
            baseline = read_json(directory / "ordinary.process.json")["command"]
            baseline[0] = str(bootstrap)
            baseline[baseline.index("--cache-dir") + 1] = str(directory / "bootstrap-cache")
            baseline = ["-femit-bin=" + str(directory / "bootstrap.o") if a.startswith("-femit-bin=") else a for a in baseline]
            run(directory, "bootstrap", baseline)
            if any(digest(directory / (label + ".o")) != captured["objects"]["captured"]
                   for label in ("ordinary", "captured", "bootstrap")):
                raise ValueError("memory capture changed native code")
            report["modes"][mode] = {"status": "passed", "observations": observations,
                                     "captureReportSha256": digest(directory / "report.json"),
                                     "objectSha256": captured["objects"]["captured"]}
        # The slice gate also covers dead and constant-result memory work. Run
        # its source-position/native checks, then inspect the retained payloads.
        check_validity(argparse.Namespace(toolchain=args.toolchain, output=output / "slices"))
        slice_observations = {}
        for mode in ("ReleaseFast", "Debug"):
            directory = output / "slices" / mode
            captured = read_json(directory / "report.json")
            records = {name.rsplit(".", 1)[-1]: read_json(directory / "air" / entry["file"])
                       for name, entry in captured["functions"].items() if entry["requested"]}
            observations = {name: inspect_memory(record) for name, record in records.items()}
            write_json(directory / "memory-observations.json", observations)
            if not {"ptr_add", "slice", "slice_ptr", "ptr_slice_len_ptr"} <= set().union(
                    *(set(tags) for tags in observations.values())):
                raise ValueError("slice fixture lost memory coverage")
            for name, sentinel in (("array_slice", None), ("sentinel_slice", {"kind": "constant", "type": uint(8), "value": 0})):
                extent = 16 + (sentinel is not None)
                array = {"kind": "array", "length": 16, "child": uint(8), "layout": layout(extent, 1), "sentinel": sentinel}
                expected = pointer(array, layout(extent, 1), const=True)
                if records[name]["signature"]["parameters"][0] != expected:
                    raise ValueError("array bound or sentinel layout changed: " + name)
            slice_observations[mode] = observations
        report["slices"] = {"reportSha256": digest(output / "slices/report.json"), "observations": slice_observations}
        for name, sha in report["inputs"].items():
            if digest(ROOT / name) != sha:
                raise ValueError("memory gate input changed")
        if digest(bootstrap) != toolchain["bootstrap"]["sha256"]:
            raise ValueError("bootstrap changed during memory gate")
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
