#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Admit whole-root partial aggregates for finite captured AIR.
// Copyright (C) 2026 OKcontract Pte. Ltd.

Reuses typed SSA/control, primitive memory and scalar decoding. Field indices
refer to source declaration order; the heap type is ordered by byte offset.
Undefined leaves are omitted only inside aggregate transfers, never evaluated
as scalar constants. Source/AIR and native-backend preservation remain open.
"""

import re

import generate as scalar
import generate_memory as memory
from generate import fields, natural


def type_of(record, depth=0):
    if depth > 16 or not isinstance(record, dict):
        raise ValueError("aggregate type depth or shape")
    if record.get("kind") != "struct":
        return memory.type_of(record, depth, decode_child=type_of)
    fields(record, "kind identity containerLayout layout fields")
    identity = record["identity"]
    fields(identity, "name sourceFile sourceSha256")
    if (any(not isinstance(identity[key], str) or not identity[key] for key in identity) or
            not re.fullmatch(r"[0-9a-f]{64}", identity["sourceSha256"]) or
            record["containerLayout"] not in ("auto", "extern")):
        raise ValueError("unsupported aggregate identity or layout")
    fields(record["layout"], "kind bytes alignment")
    size = natural(record["layout"]["bytes"], 2**64 - 1)
    alignment = natural(record["layout"]["alignment"], 2**64 - 1)
    if record["layout"]["kind"] != "abi" or size == 0 or alignment == 0 or alignment & (alignment - 1) or size % alignment:
        raise ValueError("unsupported aggregate geometry")
    if not isinstance(record["fields"], list) or not 0 < len(record["fields"]) <= 64:
        raise ValueError("aggregate field count")
    result = []
    for index, field in enumerate(record["fields"]):
        fields(field, "index name offset explicitAlignment type")
        if (natural(field["index"], 63) != index or field["explicitAlignment"] is not None or
                not isinstance(field["name"], str) or not field["name"]):
            raise ValueError("unsupported aggregate field declaration")
        offset = natural(field["offset"], 2**64 - 1)
        child = type_of(field["type"], depth + 1)
        child_size, child_alignment = memory.layout(child)
        if (child_size == 0 or offset + child_size > size or offset % child_alignment or
                alignment % child_alignment):
            raise ValueError("invalid aggregate field geometry")
        result.append((index, field["name"], offset, child))
    ordered = sorted(result, key=lambda field: field[2])
    if (len({field[1] for field in result}) != len(result) or
            any(a[2] + memory.layout(a[3])[0] > b[2] for a, b in zip(ordered, ordered[1:]))):
        raise ValueError("overlapping or duplicate aggregate fields")
    return ("struct", tuple(identity[key] for key in ("name", "sourceFile", "sourceSha256")),
            (size, alignment), tuple(result))


def leaves(value, expected, offset=0):
    if not isinstance(value, dict):
        raise ValueError("malformed aggregate field value")
    if value.get("kind") == "undefined":
        fields(value, "kind type")
        if type_of(value["type"]) != expected:
            raise ValueError("undefined field changes type")
        return []
    if value.get("kind") == "aggregate":
        fields(value, "kind type fields")
        if expected[0] != "struct" or type_of(value["type"]) != expected:
            raise ValueError("aggregate constant changes type")
        if not isinstance(value["fields"], list) or len(value["fields"]) != len(expected[3]):
            raise ValueError("incomplete aggregate constant")
        return [leaf for field, item in zip(expected[3], value["fields"])
                for leaf in leaves(item, field[3], offset + field[2])]
    ty, text = memory.constant(value)
    if ty != expected:
        raise ValueError("aggregate leaf changes type")
    # The existing constant decoder emits exactly (.constant VALUE).
    return [(offset, text[len("(.constant "):-1])]


def constant(value):
    if isinstance(value, dict) and value.get("kind") in ("aggregate", "undefined"):
        ty = type_of(value.get("type"))
        if ty[0] != "struct":
            raise ValueError("undefined scalar/array cannot be an evaluated register")
        cells = leaves(value, ty)
        text = ", ".join(f"({offset}, {leaf})" for offset, leaf in reversed(cells))
        return ty, f"(.constant (.aggregate {memory.lean_type(ty)} [{text}]))"
    ty, text = memory.constant(value)
    return ty, text.replace("(.constant ", "(.constant (.value ", 1) + ")"


class Decoder(memory.Decoder):
    type_of = staticmethod(type_of)
    constant = staticmethod(constant)

    def read_validity(self, record):
        # This finite entry has no slice operations. Do not introduce source
        # guards using a different primitive/reference vocabulary.
        if "slice_length" in record["sourceOperationTags"]:
            raise ValueError("length-based slice source validity is not admitted")
        scalar.Decoder.read_validity(self, record)

    def before(self, index, env):
        return []

    def finish(self):
        pass

    def memory_ref(self, value, env):
        if isinstance(value, dict) and value.get("kind") == "instruction":
            return scalar.Decoder.ref(self, value, env)
        return memory.constant(value)

    def scalar_primitive(self, text):
        return f"(.memory (.scalar {text}))"

    def extra_primitive(self, inst, ty, env):
        tag, base = inst["tag"], "index tag payloadVisited type "
        if tag == "load":
            fields(inst, base + "operand")
            source, operand = self.ref(inst["operand"], env)
            if source[0] != "ptr" or source[3] != ty or ty[0] == "array":
                raise ValueError("unsupported aggregate AIR load")
            return f"(.load {operand})"
        if tag in ("store", "store_safe"):
            fields(inst, base + "lhs rhs")
            target, pointer = self.ref(inst["lhs"], env)
            value, operand = self.ref(inst["rhs"], env)
            if target[0] != "ptr" or not target[1] or target[3] != value or ty != ("void",):
                raise ValueError("ill-typed aggregate AIR store")
            return f"(.store {pointer} {operand})"
        if tag in {"struct_field_ptr", *(f"struct_field_ptr_index_{i}" for i in range(4))}:
            fields(inst, base + "operand fieldIndex")
            source, operand = self.ref(inst["operand"], env)
            if source[0] != "ptr" or source[3][0] != "struct":
                raise ValueError("field pointer lacks complete declaration")
            index = natural(inst["fieldIndex"], len(source[3][3]) - 1)
            if tag != "struct_field_ptr" and index != int(tag[-1]):
                raise ValueError("fixed field pointer changes index")
            _, _, offset, child = source[3][3][index]
            if ty != ("ptr", source[1], False, child):
                raise ValueError("field pointer changes type or permissions")
            return f"(.fieldPointer {operand} {offset})"
        if tag == "ptr_elem_ptr":
            fields(inst, base + "lhs rhs")
            source, pointer = self.ref(inst["lhs"], env)
            index, operand = self.ref(inst["rhs"], env)
            if source[0] == "ptr" and not source[2] and source[3][0] == "array":
                if index != ("int", False, 64) or ty != ("ptr", source[1], False, source[3][2]):
                    raise ValueError("array element pointer changes type")
                return f"(.arrayElementPointer {pointer} {operand})"
        # Primitive references use the original memory vocabulary. Aggregate
        # constants/values never enter this route; scalar references above use
        # the scalar decoder's constants directly.
        prim = super().extra_primitive(inst, ty, env)
        return None if prim is None else f"(.memory {prim})"


def render(record, namespace="GeneratedWyhashInit", name="fn_init"):
    if any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", item) for item in (namespace, name)):
        raise ValueError("invalid generated declaration name")
    decoder = Decoder(record)
    program = decoder.program(record)
    declaration = []
    if decoder.result[0] == "struct":
        result_type = memory.lean_type(decoder.result)
        declaration = [f"def resultType : Memory.Ty := {result_type}", ""]
        program = program.replace(result_type, "resultType")
    text = "\n".join([
        "/-", "// Copyright (C) 2026 OKcontract Pte. Ltd.", "// SPDX-License-Identifier: GPL-3.0",
        "Generated from captured AIR; do not edit. Source/backend preservation remains open.", "-/",
        "import Compiler.ZigAir.AggregateAir", "", f"namespace Compiler.ZigAir.{namespace}",
        "open AggregateAir", "", *declaration, f"def {name} : Program :=", program, "",
        f"end Compiler.ZigAir.{namespace}", "",
    ])
    return text, len(decoder.visited)
