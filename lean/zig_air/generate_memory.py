#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Decode admitted typed memory AIR and retained slice checks into Lean.
// Copyright (C) 2026 OKcontract Pte. Ltd.

Reuses the scalar decoder's SSA/control validation. Translation and native
refinement remain trusted boundaries; source-validity coverage is incomplete.
"""

import argparse
from pathlib import Path
import re

from build_toolchain import digest, write_json
from capture import read_json
import generate as scalar
from generate import fields, natural


def layout(ty):
    if ty[0] == "struct":
        return ty[2]
    if ty[0] == "aligned":
        return layout(ty[2])
    if ty == ("void",):
        return (0, 1)
    if ty == ("bool",):
        return (1, 1)
    if ty[0] == "int" and ty[2] in (8, 16, 32, 64):
        return (ty[2] // 8, ty[2] // 8)
    if ty == ("int", False, 256):
        return (32, 16)
    if ty[0] == "ptr":
        return (8, 8)
    if ty[0] == "slice":
        return (16, 8)
    if ty[0] == "array":
        size, alignment = layout(ty[2])
        return (natural(size * ty[1], 2**64 - 1), alignment)
    raise ValueError("unsupported memory layout")


def check_layout(record, expected):
    fields(record, "kind bytes alignment")
    if (record["kind"] != "abi" or type(record["bytes"]) is not int or
            type(record["alignment"]) is not int or (record["bytes"], record["alignment"]) != expected):
        raise ValueError("captured ABI layout disagrees with memory model")


def type_of(record, depth=0, *, byte_alignment=False, decode_child=None):
    if depth > 16 or not isinstance(record, dict):
        raise ValueError("memory type depth or shape")
    child_type = decode_child or (lambda value, level: type_of(value, level, byte_alignment=byte_alignment))
    if record.get("kind") == "pointer":
        fields(record, "kind flags child layout pointeeLayout sentinel")
        flags = record["flags"]
        fields(flags, "size alignment isConst isVolatile allowZero addressSpace vectorIndex hostSizeBytes bitOffset")
        if (flags["size"] not in ("one", "many", "slice") or (flags["alignment"] is not None and not byte_alignment) or
                any(type(flags[key]) is not bool for key in ("isConst", "isVolatile", "allowZero")) or
                flags["isVolatile"] or flags["allowZero"] or flags["addressSpace"] != "generic" or
                flags["vectorIndex"] is not None or type(flags["hostSizeBytes"]) is not int or
                type(flags["bitOffset"]) is not int or flags["hostSizeBytes"] != 0 or flags["bitOffset"] != 0 or
                record["sentinel"] is not None):
            raise ValueError("unsupported memory pointer attributes")
        child = child_type(record["child"], depth + 1)
        ty = (("slice", not flags["isConst"], child) if flags["size"] == "slice" else
              ("ptr", not flags["isConst"], flags["size"] == "many", child))
        check_layout(record["layout"], layout(ty))
        check_layout(record["pointeeLayout"], layout(child))
        if flags["alignment"] is not None:
            alignment = flags["alignment"]
            if type(alignment) is not int or alignment not in (1, 2, 4) or child != ("int", False, 8):
                raise ValueError("unsupported explicit byte alignment")
            return ("aligned", alignment, ty)
        return ty
    if record.get("kind") == "array":
        fields(record, "kind length child layout sentinel")
        if record["sentinel"] is not None:
            raise ValueError("unsupported memory array sentinel")
        ty = ("array", natural(record["length"], 2**64 - 1), child_type(record["child"], depth + 1))
        check_layout(record["layout"], layout(ty))
        return ty
    return scalar.type_of(record)


def lean_type(ty):
    if ty[0] == "struct":
        import json
        def field_type(child):
            return (f"(.scalar {scalar.lean_type(child)})" if child[0] in ("int", "bool", "void")
                    else f"(.object {lean_type(child)})")
        native = ", ".join(f"({offset}, {field_type(child)})"
                           for _, _, offset, child in sorted(ty[3], key=lambda field: field[2]))
        return f"(.aggregate {json.dumps(ty[1][0])} ⟨{ty[2][0]}, {ty[2][1]}⟩ [{native}])"
    if ty[0] == "ptr":
        return f"(.pointer {str(ty[1]).lower()} {str(ty[2]).lower()} {lean_type(ty[3])})"
    if ty[0] == "slice":
        return f"(.slice {str(ty[1]).lower()} {lean_type(ty[2])})"
    if ty[0] == "array":
        return f"(.array {ty[1]} {lean_type(ty[2])})"
    return f"(.scalar {scalar.lean_type(ty)})"


def constant(value):
    ty, text = scalar.constant(value)
    return ty, text.replace("(.constant ", "(.constant (.scalar ", 1) + ")"


class Decoder(scalar.Decoder):
    allow_length_slices = False
    type_of = staticmethod(type_of)
    lean_type = staticmethod(lean_type)
    constant = staticmethod(constant)
    scalar_type = staticmethod(scalar.lean_type)

    def __init__(self, record):
        super().__init__(record)
        config = record["configuration"]
        if (config.get("arch") != "aarch64" or config.get("os") != "macos" or
                type(config.get("pointerBits")) is not int or config["pointerBits"] != 64 or config.get("endianness") != "little"):
            raise ValueError("unsupported memory target configuration")
        if any(ty[0] == "array" for ty in [*self.parameters, self.result]):
            raise ValueError("array values are not implemented in memory AIR")

    def read_validity(self, record):
        # Zig 0.17 length-based slicing adds start + length evaluation.
        # Its overflow/source-validity correspondence has not been admitted.
        if "slice_length" in record["sourceOperationTags"] and not self.allow_length_slices:
            raise ValueError("length-based slice source validity is not admitted")
        validity = record["sourceValidity"]
        fields(validity, "schema coverage complete slices")
        if (validity["schema"] != "oksolc.source-validity.v1" or validity["coverage"] != "runtime-slice-results" or
                validity["complete"] is not False or not isinstance(validity["slices"], list) or len(validity["slices"]) > 512):
            raise ValueError("unsupported memory source-validity inventory")
        self.guards, self.guards_seen = {}, set()
        for position, item in enumerate(validity["slices"]):
            fields(item, "source anchor start end upperBound unsupportedReason")
            fields(item["source"], "file sha256 span")
            if item["source"]["sha256"] != record["sourceSha256"] or item["source"]["file"] != record["sourceFile"]:
                raise ValueError("source guard identity mismatch")
            span = item["source"]["span"]
            fields(span, "start end main")
            for value in span.values():
                natural(value, 2**32 - 1)
            if not span["start"] <= span["main"] < span["end"]:
                raise ValueError("invalid source guard span")
            anchor = item["anchor"]
            fields(anchor, "kind index inSupportedBody")
            index = natural(anchor["index"], self.instruction_limit - 1)
            if anchor["kind"] != "beforeInstruction" or anchor["inSupportedBody"] is not True or index in self.guards:
                raise ValueError("source guard lost its unique body position")
            if item["unsupportedReason"] is not None:
                raise ValueError("unsupported source guard semantics")
            self.guards[index] = (position, item)

    def before(self, index, env):
        if index not in self.guards:
            return []
        position, item = self.guards[index]
        if self.instructions[index]["tag"] not in ("slice", "ptr_cast"):
            raise ValueError("source guard does not precede a slice result")
        st, start = self.memory_ref(item["start"], env)
        et, end = self.memory_ref(item["end"], env)
        if st != ("int", False, 64) or et != st:
            raise ValueError("source guard does not use usize bounds")
        bound = item["upperBound"]
        if not isinstance(bound, dict):
            raise ValueError("malformed source guard bound")
        if bound.get("kind") == "sliceLength":
            fields(bound, "kind original")
            ty, original = self.memory_ref(bound["original"], env)
            if ty[0] != "slice":
                raise ValueError("source guard lost the original slice value")
            upper = f"(.slice {original})"
        elif bound.get("kind") == "arrayLength":
            fields(bound, "kind value")
            upper = f"(.array {natural(bound['value'], 2**64 - 1)})"
        elif bound.get("kind") == "unboundedPointer":
            fields(bound, "kind requiresMemoryValidity")
            if bound["requiresMemoryValidity"] is not True:
                raise ValueError("unbounded slice lost its memory obligation")
            upper = ".unbounded"
        else:
            raise ValueError("unsupported source guard bound")
        self.guards_seen.add(index)
        return [("bind", len(self.instructions) + position, "(.scalar .unit)", f"(.checkBounds {start} {end} {upper})")]

    def finish(self):
        if self.guards_seen != set(self.guards):
            raise ValueError("source guard was not executed by the decoded body")

    def scalar_ref(self, value, env):
        if isinstance(value, dict) and value.get("kind") == "instruction":
            return self.ref(value, env)
        return scalar.constant(value)

    def scalar_primitive(self, text):
        return f"(.scalar {text})"

    def memory_ref(self, value, env):
        return self.ref(value, env)

    def extra_primitive(self, inst, ty, env):
        tag, base = inst["tag"], "index tag payloadVisited type "
        if tag == "alloc":
            fields(inst, base + "allocationKind")
            if ty[0] != "ptr" or ty[1:3] != (True, False) or inst["allocationKind"] != "stack":
                raise ValueError("unsupported AIR allocation")
            return f"(.alloc {lean_type(ty[3])})"
        if tag in ("store", "store_safe", "ptr_add", "ptr_sub", "ptr_elem_ptr", "slice_elem_ptr", "slice"):
            fields(inst, base + "lhs rhs")
            lt, left = self.memory_ref(inst["lhs"], env)
            rt, right = self.memory_ref(inst["rhs"], env)
            if tag == "slice_elem_ptr":
                if (lt[0] != "slice" or rt != ("int", False, 64) or layout(lt[2])[0] == 0 or
                        ty != ("ptr", lt[1], False, lt[2])):
                    raise ValueError("indexed slice pointer changed type, extent or permissions")
                return f"(.sliceElementPointer {left} {right})"
            if lt[0] != "ptr":
                raise ValueError("memory operation requires a pointer")
            if tag in ("store", "store_safe"):
                if ty != ("void",) or not lt[1] or lt[3] != rt:
                    raise ValueError("ill-typed AIR store")
                return f"(.store {left} {right})"
            if rt != ("int", False, 64) or not lt[2] or layout(lt[3])[0] == 0:
                raise ValueError("unsupported memory element/offset type")
            if tag == "slice":
                if ty != ("slice", lt[1], lt[3]):
                    raise ValueError("ill-typed slice construction")
                return f"(.slice {lean_type(ty)} {left} {right})"
            if tag == "ptr_elem_ptr":
                if ty != ("ptr", lt[1], False, lt[3]):
                    raise ValueError("indexed pointer changed element type or permissions")
                return f"(.elementPointer {left} {right})"
            if ty != lt:
                raise ValueError("pointer arithmetic changed type")
            return f"(.offsetPointer {str(tag == 'ptr_sub').lower()} {left} {right})"
        if tag not in ("load", "ptr_cast", "slice_len", "slice_ptr", "ptr_slice_len_ptr", "ptr_slice_ptr_ptr"):
            return None
        fields(inst, base + "operand")
        source, operand = self.memory_ref(inst["operand"], env)
        if tag == "ptr_cast":
            if source[0] != "ptr" or ty[0] != "ptr" or (ty[1] and not source[1]):
                raise ValueError("unsupported pointer cast")
            child, dest = source[3], ty[3]
            if not (child == dest or (child[0] == "array" and child[2] == dest) or (dest[0] == "array" and dest[2] == child)):
                raise ValueError("unsupported pointer reinterpretation")
            return f"(.pointerCast {lean_type(ty)} {operand})"
        if tag == "load":
            if source[0] != "ptr" or source[3] != ty or ty[0] == "array":
                raise ValueError("unsupported or ill-typed AIR load")
            return f"(.load {operand})"
        if tag in ("slice_len", "slice_ptr"):
            if source[0] != "slice":
                raise ValueError("slice projection lost its slice")
            expected = ("int", False, 64) if tag == "slice_len" else ("ptr", source[1], True, source[2])
            if ty != expected:
                raise ValueError("ill-typed slice projection")
            return f"(.{'sliceLen' if tag == 'slice_len' else 'slicePtr'} {operand})"
        if source[0] != "ptr" or source[3][0] != "slice":
            raise ValueError("slice field projection lost its owner")
        child = source[3]
        field = ("int", False, 64) if tag == "ptr_slice_len_ptr" else ("ptr", child[1], True, child[2])
        if ty != ("ptr", source[1], False, field):
            raise ValueError("ill-typed slice field projection")
        return f"(.pointerField {str(tag == 'ptr_slice_len_ptr').lower()} {operand})"


class LoopDecoder(Decoder):
    allow_loops = True


def generate(report_path, roots, output, manifest_path, *, loops=False, word_bytes=False):
    report = read_json(report_path)
    if report.get("schema") != "oksolc.fresh-air-capture.v1" or report.get("status") != "captured" or report.get("captureComplete") is not True:
        raise ValueError("memory capture was not completed")
    if not roots or len(set(roots)) != len(roots):
        raise ValueError("memory roots must be nonempty and unique")
    lines = ["/-", "// Copyright (C) 2026 OKcontract Pte. Ltd.", "// SPDX-License-Identifier: GPL-3.0",
             "Generated from captured AIR; do not edit. Source/backend preservation remains open.", "-/",
             "import Compiler.ZigAir." + ("MemoryExecution" if loops else "MemoryAir"), "",
             "namespace Compiler.ZigAir.GeneratedMemory", "open MemoryAir", ""]
    manifest = {"schema": "oksolc.memory-air-generation.v1", "proofScope": "zigFreshAir", "sourceSafetyVerified": False,
                "wholeCompilerVerified": False, "captureReportSha256": digest(report_path), "functions": {}}
    names = set()
    for root in roots:
        name = "fn_" + root.rsplit(".", 1)[-1]
        if not re.fullmatch("fn_[A-Za-z][A-Za-z0-9_]*", name) or name in names:
            raise ValueError("invalid or duplicate generated memory name")
        names.add(name)
        entry = report["functions"][root]
        path = scalar.captured_path(report_path, entry)
        if entry["requested"] is not True or digest(path) != entry["sha256"]:
            raise ValueError("memory AIR identity mismatch")
        record = read_json(path)
        if record["name"] != root or record["sourceSha256"] != report["sourceSha256"]:
            raise ValueError("memory AIR source identity mismatch")
        if word_bytes:
            from generate_byte_memory import ByteDecoder, ByteLoopDecoder
            decoder = (ByteLoopDecoder if loops else ByteDecoder)(record)
        else:
            decoder = (LoopDecoder if loops else Decoder)(record)
        lines += [f"def {name} : Program{' true' if loops else ''} :=", decoder.program(record), ""]
        manifest["functions"][root] = {"airSha256": entry["sha256"], "sourceSha256": record["sourceSha256"],
            "bodyInstructions": len(decoder.visited), "sourceGuards": len(decoder.guards_seen), "configuration": record["configuration"]}
        if word_bytes:
            manifest["functions"][root]["wordByteViews"] = decoder.byte_inventory()
        if loops:
            manifest["functions"][root]["loops"] = sorted(decoder.loop_ids)
            manifest["functions"][root]["repeatTargets"] = sorted(decoder.repeat_targets)
    if word_bytes:
        manifest["memoryProfile"] = "initialized-u32-byte-views"
    if loops:
        manifest["executionModel"] = "resumableMemoryAir"
    lines += ["end Compiler.ZigAir.GeneratedMemory", ""]
    with output.open("x") as stream:
        stream.write("\n".join(lines))
    manifest["leanSha256"] = digest(output)
    write_json(manifest_path, manifest)
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", type=Path, required=True)
    parser.add_argument("--root", action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--loops", action="store_true", help="emit loop-enabled programs for resumable execution")
    parser.add_argument("--word-bytes", action="store_true", help="admit checked initialized-u32 byte views")
    args = parser.parse_args()
    generate(args.capture, args.root, args.output, args.manifest, loops=args.loops, word_bytes=args.word_bytes)
