#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Decode the supported scalar/control AIR fragment into total Lean programs.
// Copyright (C) 2026 OKcontract Pte. Ltd.

The decoder is a trusted translation boundary, not a source-validity proof.
It checks typed SSA dominance, block ownership, control targets and completion.
Every operation in the admitted body is retained, including dead-result work.
"""

import argparse
from pathlib import Path

from build_toolchain import digest, write_json
from capture import read_json


def fields(value, expected):
    if not isinstance(value, dict) or set(value) != set(expected.split()):
        raise ValueError("unexpected scalar AIR fields: " + str(expected))


def natural(value, limit):
    if type(value) is not int or not 0 <= value <= limit:
        raise ValueError("invalid or unsupported scalar AIR integer")
    return value


def type_of(value):
    if not isinstance(value, dict):
        raise ValueError("malformed AIR type")
    if value.get("kind") == "int":
        fields(value, "kind bits signedness")
        if value["signedness"] not in ("signed", "unsigned"):
            raise ValueError("unknown integer signedness")
        return ("int", value["signedness"] == "signed", natural(value["bits"], 512))
    fields(value, "kind")
    if value["kind"] not in ("bool", "void", "noreturn"):
        raise ValueError("unsupported AIR type")
    return (value["kind"],)


def lean_type(ty):
    if ty[0] == "int":
        return f"(.int {str(ty[1]).lower()} {ty[2]})"
    if ty[0] == "bool":
        return ".bool"
    if ty[0] == "void":
        return ".unit"
    raise ValueError("noreturn cannot be a runtime value type")


def constant(value):
    if not isinstance(value, dict):
        raise ValueError("malformed AIR constant")
    if value.get("kind") == "unit":
        fields(value, "kind")
        return ("void",), "(.constant .unit)"
    fields(value, "kind type value")
    if value["kind"] != "constant" or type(value["value"]) is not int:
        raise ValueError("unsupported or malformed AIR constant")
    ty, number = type_of(value["type"]), value["value"]
    if ty == ("bool",):
        if number not in (0, 1):
            raise ValueError("invalid boolean constant")
        return ty, "(.constant (.bool " + str(bool(number)).lower() + "))"
    if ty[0] != "int":
        raise ValueError("unsupported constant type")
    signed, width = ty[1:]
    lower, upper = (-(2 ** (width - 1)), 2 ** (width - 1)) if signed and width else (0, 2 ** width)
    if not lower <= number < upper:
        raise ValueError("AIR constant outside declared type")
    return ty, f"(.constant (.int {str(signed).lower()} {width} ({number})))"


class Decoder:
    allow_loops = False
    instruction_limit = 512
    record_fields = "schema capturePoint name sourceFile sourceSha256 configuration signature sourceOperationTags sourceValidityConditionsPreserved sourceValidity body bodyTraversal instructions"
    type_of = staticmethod(type_of)
    lean_type = staticmethod(lean_type)
    constant = staticmethod(constant)

    def read_validity(self, record):
        # This scalar interpreter has no source-slice or memory semantics. A
        # sidecar obligation must never disappear just because its result is dead.
        validity = record["sourceValidity"]
        fields(validity, "schema coverage complete slices")
        if (validity["schema"] != "oksolc.source-validity.v1" or validity["coverage"] != "runtime-slice-results" or
                validity["complete"] is not False or validity["slices"] != []):
            raise ValueError("unsupported source-validity obligations in scalar AIR")

    def before(self, index, env):
        return []

    def extra_primitive(self, inst, ty, env):
        return None

    def extra_terminator(self, inst, ty, env):
        return None

    def scalar_ref(self, value, env):
        return self.ref(value, env)

    def scalar_primitive(self, text):
        return text

    def argument_primitive(self, index):
        return f"(.argument {index})"

    def scalar_type(self, ty):
        return self.lean_type(ty)

    def finish(self):
        pass

    def parameter_mapping(self, record):
        signature = record["signature"]
        fields(signature, "callingConvention genericInstance varArgs noaliasBits parameters returnType")
        if (signature["genericInstance"] is not False or signature["varArgs"] is not False or
                type(signature["noaliasBits"]) is not int or signature["noaliasBits"] != 0):
            raise ValueError("unsupported function specialization or parameter contract")
        if not isinstance(signature["parameters"], list) or len(signature["parameters"]) > 512:
            raise ValueError("malformed or oversized parameter list")
        return list(range(len(signature["parameters"])))

    def __init__(self, record):
        fields(record, self.record_fields)
        if (record["schema"] != "oksolc.fresh-air.v3" or record["capturePoint"] != "after-sema-before-legalize" or
            record["bodyTraversal"] != "supported-structured-containers-only" or record["sourceValidityConditionsPreserved"] is not False):
            raise ValueError("wrong AIR schema, phase or source-validity claim")
        self.read_validity(record)
        config = record["configuration"]
        if not isinstance(config, dict):
            raise ValueError("malformed AIR configuration")
        if config.get("optimize") != "ReleaseFast" or config.get("useLlvm") is not True or config.get("isTest") is not False:
            raise ValueError("unsupported AIR build configuration")
        signature = record["signature"]
        self.source_parameters = self.parameter_mapping(record)
        self.parameters = [self.type_of(t) for t in signature["parameters"]]
        self.result = self.type_of(signature["returnType"])
        for ty in [*self.parameters, self.result]:
            self.lean_type(ty)
        self.instructions = record["instructions"]
        if not isinstance(self.instructions, list) or not 0 < len(self.instructions) <= self.instruction_limit:
            raise ValueError("scalar AIR instruction resource limit")
        for index, inst in enumerate(self.instructions):
            if (not isinstance(inst, dict) or type(inst.get("index")) is not int or
                    inst["index"] != index or not isinstance(inst.get("tag"), str)):
                raise ValueError("invalid AIR instruction table")
        self.visited = set()
        self.arguments = 0
        self.loop_ids, self.repeat_targets = set(), set()

    def ref(self, value, env):
        if not isinstance(value, dict):
            raise ValueError("malformed AIR reference")
        if value.get("kind") == "instruction":
            fields(value, "kind index")
            index = natural(value["index"], len(self.instructions) - 1)
            if index not in env:
                raise ValueError("AIR reference is not dominated by its definition")
            return env[index], f"(.local {index})"
        return self.constant(value)

    def body(self, indices, env, labels, depth=0):
        if not isinstance(indices, list) or not indices or depth > 64:
            raise ValueError("empty, malformed or too deeply nested AIR body")
        env = dict(env)
        prefixes = []
        terminal = None
        for position, index in enumerate(indices):
            natural(index, len(self.instructions) - 1)
            if index in self.visited or terminal is not None:
                raise ValueError("duplicate AIR body ownership or code after terminator")
            self.visited.add(index)
            inst = self.instructions[index]
            if inst.get("payloadVisited") is not True or inst.get("unsupportedPayload"):
                raise ValueError("unsupported or unvisited AIR body instruction")
            tag, ty = inst["tag"], self.type_of(inst["type"])
            base = "index tag payloadVisited type "
            prefixes.extend(self.before(index, env))
            terminal = self.extra_terminator(inst, ty, env)
            if terminal is not None:
                continue
            prim = self.extra_primitive(inst, ty, env)
            if prim is not None:
                pass
            elif tag == "arg":
                fields(inst, base + "zirParameterIndex")
                if depth != 0 or position != self.arguments or self.arguments >= len(self.parameters):
                    raise ValueError("invalid AIR argument prefix")
                if natural(inst["zirParameterIndex"], 511) != self.source_parameters[self.arguments] or ty != self.parameters[self.arguments]:
                    raise ValueError("AIR argument disagrees with signature")
                prim = self.argument_primitive(self.arguments)
                self.arguments += 1
            elif tag in {"add", "sub", "mul", "add_safe", "sub_safe", "mul_safe", "add_wrap", "sub_wrap", "mul_wrap"}:
                fields(inst, base + "lhs rhs")
                lt, left = self.scalar_ref(inst["lhs"], env)
                rt, right = self.scalar_ref(inst["rhs"], env)
                if lt != rt or lt != ty or ty[0] != "int":
                    raise ValueError("ill-typed AIR arithmetic")
                op = tag.split("_")[0]
                mode = "checked" if tag.endswith("_safe") else "wrapping" if tag.endswith("_wrap") else "unchecked"
                prim = self.scalar_primitive(f"(.arithmetic .{op} .{mode} {left} {right})")
            elif tag in {"bit_and", "xor", "shr"}:
                fields(inst, base + "lhs rhs")
                lt, left = self.scalar_ref(inst["lhs"], env)
                rt, right = self.scalar_ref(inst["rhs"], env)
                if lt != ty or lt[0] != "int" or lt[1] or rt[0] != "int" or rt[1]:
                    raise ValueError("unsupported or ill-typed unsigned AIR bit operation")
                if tag in {"bit_and", "xor"}:
                    if lt != rt:
                        raise ValueError("bitwise operation changes operand width")
                    op = "bitAnd" if tag == "bit_and" else "bitXor"
                else:
                    if lt[2] == 0 or rt[2] != (lt[2] - 1).bit_length():
                        raise ValueError("right shift has an invalid count type")
                    op = "shiftRight"
                prim = self.scalar_primitive(f"(.{op} {left} {right})")
            elif tag in {"cmp_eq", "cmp_neq", "cmp_lt", "cmp_lte", "cmp_gt", "cmp_gte"}:
                fields(inst, base + "lhs rhs")
                lt, left = self.scalar_ref(inst["lhs"], env)
                rt, right = self.scalar_ref(inst["rhs"], env)
                if lt != rt or lt[0] != "int" or ty != ("bool",):
                    raise ValueError("ill-typed AIR comparison")
                op = {"eq": "eq", "neq": "ne", "lt": "lt", "lte": "le", "gt": "gt", "gte": "ge"}[tag[4:]]
                prim = self.scalar_primitive(f"(.comparison .{op} {left} {right})")
            elif tag in {"int_cast", "int_cast_safe", "bit_cast", "trunc"}:
                fields(inst, base + "operand")
                source, operand = self.scalar_ref(inst["operand"], env)
                if source[0] != "int" or ty[0] != "int":
                    raise ValueError("unsupported AIR cast types")
                if tag == "bit_cast" and source[2] != ty[2]:
                    raise ValueError("bitcast changes width")
                if tag == "trunc" and (source[1] != ty[1] or source[2] < ty[2]):
                    raise ValueError("invalid truncation")
                op = {"int_cast": "unchecked", "int_cast_safe": "checked", "bit_cast": "bitcast", "trunc": "trunc"}[tag]
                prim = self.scalar_primitive(f"(.cast .{op} {self.scalar_type(ty)} {operand})")
            elif tag == "block":
                fields(inst, base + "body")
                body = self.body(inst["body"], env, {**labels, index: ty}, depth + 1)
                prefixes.append(("block", index, self.lean_type(ty), body))
                env[index] = ty
            elif tag == "loop" and self.allow_loops:
                fields(inst, base + "body")
                if ty != ("noreturn",):
                    raise ValueError("AIR loop must be non-returning")
                self.loop_ids.add(index)
                # None is a loop label; every value-producing block has a type.
                # A loop contributes no SSA value to its enclosing environment.
                body = self.body(inst["body"], env, {**labels, index: None}, depth + 1)
                terminal = f"(.loop rfl {index}\n  {body})"
            elif tag == "repeat" and self.allow_loops:
                fields(inst, base + "target")
                target = natural(inst["target"], len(self.instructions) - 1)
                if ty != ("noreturn",) or target not in labels or labels[target] is not None:
                    raise ValueError("AIR repeat must target an enclosing loop")
                self.repeat_targets.add(target)
                terminal = f"(.repeat rfl {target})"
            elif tag == "cond_br":
                fields(inst, base + "condition thenBody elseBody")
                condition_ty, condition = self.ref(inst["condition"], env)
                if condition_ty != ("bool",) or ty != ("noreturn",):
                    raise ValueError("ill-typed AIR conditional branch")
                yes = self.body(inst["thenBody"], env, labels, depth + 1)
                no = self.body(inst["elseBody"], env, labels, depth + 1)
                terminal = f"(.branch {condition}\n  {yes}\n  {no})"
            elif tag == "br":
                fields(inst, base + "target operand")
                target = natural(inst["target"], len(self.instructions) - 1)
                operand_ty, operand = self.ref(inst["operand"], env)
                if labels.get(target) != operand_ty or ty != ("noreturn",):
                    raise ValueError("invalid AIR block destination or result")
                terminal = f"(.jump {target} {operand})"
            elif tag in ("ret", "ret_safe"):
                fields(inst, base + "operand")
                operand_ty, operand = self.ref(inst["operand"], env)
                if operand_ty != self.result or ty != ("noreturn",):
                    raise ValueError("AIR return disagrees with signature")
                terminal = f"(.ret {operand})"
            elif tag in ("dbg_stmt", "dbg_var_val", "dbg_var_ptr", "dbg_arg_inline"):
                fields(inst, base + "debugOnly")
                if ty != ("void",) or inst["debugOnly"] is not True:
                    raise ValueError("invalid debug-only instruction")
            else:
                raise ValueError("unsupported AIR operation: " + str(tag))
            if prim is not None:
                prefixes.append(("bind", index, self.lean_type(ty), prim))
                env[index] = ty
        if terminal is None:
            raise ValueError("AIR body has no terminator")
        for kind, index, ty, child in reversed(prefixes):
            terminal = f"(.{kind} {index} {ty}\n  {child}\n  {terminal})"
        return terminal

    def program(self, record):
        body = self.body(record["body"], {}, {})
        if self.loop_ids != self.repeat_targets:
            raise ValueError("AIR loop has no repeat instruction")
        if self.arguments != len(self.parameters):
            raise ValueError("AIR argument prefix is incomplete")
        for index, inst in enumerate(self.instructions):
            if index not in self.visited:
                fields(inst, "index tag payloadVisited unsupportedPayload reason")
                if inst["payloadVisited"] is not False or inst["unsupportedPayload"] is not True or inst["reason"] != "outside-decoded-body-closure":
                    raise ValueError("unaccounted AIR body entry")
        self.finish()
        params = ", ".join(self.lean_type(ty) for ty in self.parameters)
        return f"{{ parameters := [{params}], returnType := {self.lean_type(self.result)}, body :=\n  {body} }}"


def captured_path(report_path, entry):
    name = entry["file"]
    if not isinstance(name, str) or not name or Path(name).name != name or Path(name).suffix != ".json":
        raise ValueError("invalid captured AIR filename")
    directory = report_path.parent / "air"
    path = directory / name
    if directory.is_symlink() or path.is_symlink() or not path.is_file():
        raise ValueError("captured AIR must be a regular file")
    return path


def generate(report_path, output, manifest_path):
    report = read_json(report_path)
    if report.get("schema") != "oksolc.fresh-air-numeric.v1" or report.get("status") != "captured":
        raise ValueError("numeric capture was not completed")
    lines = ["/-", "// Copyright (C) 2026 OKcontract Pte. Ltd.", "// SPDX-License-Identifier: GPL-3.0",
             "Generated from captured production AIR; do not edit.", "Source validity and backend preservation are not asserted here.",
             "-/", "import Compiler.ZigAir.Scalar", "", "namespace Compiler.ZigAir.Generated", "open Scalar", ""]
    manifest = {"schema": "oksolc.scalar-air-generation.v1", "proofScope": "zigFreshAir", "sourceSafetyVerified": False,
                "wholeCompilerVerified": False, "captureReportSha256": digest(report_path), "functions": {}}
    for root, name in (("numeric.u2s", "u2s"), ("numeric.s2u", "s2u")):
        entry = report["functions"][root]
        path = captured_path(report_path, entry)
        if entry["requested"] is not True or digest(path) != entry["sha256"]:
            raise ValueError("captured numeric AIR identity mismatch")
        record = read_json(path)
        if record["name"] != root or record["sourceSha256"] != report["numericSourceSha256"]:
            raise ValueError("captured numeric source identity mismatch")
        decoder = Decoder(record)
        program = decoder.program(record)
        lines += [f"def {name} : Program :=", program, ""]
        manifest["functions"][root] = {"airSha256": entry["sha256"], "sourceSha256": record["sourceSha256"],
            "bodyInstructions": len(decoder.visited), "unvisitedEntries": len(decoder.instructions) - len(decoder.visited),
            "configuration": record["configuration"], "sourceOperationTags": record["sourceOperationTags"]}
    lines += ["end Compiler.ZigAir.Generated", ""]
    with output.open("x") as stream:
        stream.write("\n".join(lines))
    manifest["leanSha256"] = digest(output)
    write_json(manifest_path, manifest)
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    generate(args.capture, args.output, args.manifest)
