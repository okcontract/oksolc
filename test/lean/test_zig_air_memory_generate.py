#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Negative controls for typed memory and positioned source-guard decoding.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import copy
import unittest

from test_zig_air_generate import fixture, inst, ref, const, U8, VOID, NEVER
from check_zig_air_memory import pointer, layout
from generate_memory import Decoder, type_of

USIZE = {"kind": "int", "bits": 64, "signedness": "unsigned"}
MANY = pointer(U8, layout(1, 1), size="many", const=True)
SLICE = pointer(U8, layout(1, 1), size="slice", const=True)


def memory_fixture():
    result = fixture()
    result["configuration"].update(arch="aarch64", os="macos", pointerBits=64, endianness="little")
    result["signature"].update(parameters=[MANY, USIZE], returnType=USIZE)
    result["instructions"] = [inst(0, "arg", MANY, zirParameterIndex=0), inst(1, "arg", USIZE, zirParameterIndex=1),
                              inst(2, "slice", SLICE, lhs=ref(0), rhs=ref(1)), inst(3, "ret", NEVER, operand=const(1, USIZE))]
    result["body"] = [0, 1, 2, 3]
    result["sourceValidity"]["slices"] = [{
        "source": {"file": result["sourceFile"], "sha256": result["sourceSha256"], "span": {"start": 0, "main": 1, "end": 2}},
        "anchor": {"kind": "beforeInstruction", "index": 2, "inSupportedBody": True},
        "start": const(0, USIZE), "end": ref(1),
        "upperBound": {"kind": "unboundedPointer", "requiresMemoryValidity": True}, "unsupportedReason": None}]
    return copy.deepcopy(result)


def slice_element_fixture():
    result = memory_fixture()
    element = pointer(U8, layout(1, 1), const=True)
    result["signature"].update(parameters=[SLICE, USIZE], returnType=element)
    result["sourceValidity"]["slices"] = []
    result["instructions"] = [inst(0, "arg", SLICE, zirParameterIndex=0), inst(1, "arg", USIZE, zirParameterIndex=1),
        inst(2, "slice_elem_ptr", element, lhs=ref(0), rhs=ref(1)), inst(3, "ret", NEVER, operand=ref(2))]
    return result


def decode(record):
    return Decoder(record).program(record)


class MemoryGenerationTests(unittest.TestCase):
    def rejects(self, edit, message):
        record = memory_fixture()
        edit(record)
        with self.assertRaisesRegex(ValueError, message):
            decode(record)

    def test_length_based_slice_requires_separate_source_admission(self):
        self.rejects(lambda r: r["sourceOperationTags"].append("slice_length"), "length-based slice")

    def test_dead_slice_still_emits_guard_and_operation(self):
        text = decode(memory_fixture())
        self.assertIn("(.bind 4 (.scalar .unit)", text)
        self.assertLess(text.index("(.checkBounds"), text.index("(.slice (.slice"))
        self.assertIn("(.ret (.constant (.scalar (.int false 64 (1)))))", text)

    def test_guard_identity_position_and_dominance(self):
        def guard(record):
            return record["sourceValidity"]["slices"][0]
        self.rejects(lambda r: guard(r)["source"].update(sha256="b" * 64), "identity")
        self.rejects(lambda r: guard(r)["anchor"].update(index=3), "slice result")
        self.rejects(lambda r: guard(r)["anchor"].update(index=20), "not executed")
        self.rejects(lambda r: guard(r).update(end=ref(2)), "dominated")
        self.rejects(lambda r: guard(r)["anchor"].update(inSupportedBody=False), "position")
        self.rejects(lambda r: r["sourceValidity"]["slices"].append(copy.deepcopy(guard(r))), "unique")
        self.rejects(lambda r: guard(r).update(upperBound={"kind": "sliceLength", "original": ref(0)}), "original slice")
        self.rejects(lambda r: guard(r)["upperBound"].update(requiresMemoryValidity=1), "memory obligation")
        self.rejects(lambda r: guard(r).update(unsupportedReason="sentinel"), "guard semantics")
        self.rejects(lambda r: guard(r).update(upperBound=[]), "malformed")

    def test_pointer_attributes_and_layout_cannot_be_erased(self):
        for key, value in (("isVolatile", True), ("allowZero", True), ("alignment", 1), ("size", "c"),
                           ("bitOffset", 3), ("hostSizeBytes", 1), ("addressSpace", "global"),
                           ("vectorIndex", 0), ("isConst", 1), ("bitOffset", False)):
            ty = copy.deepcopy(MANY)
            ty["flags"][key] = value
            with self.assertRaisesRegex(ValueError, "attributes"):
                type_of(ty)
        for field, key, value in (("layout", "bytes", 4), ("pointeeLayout", "alignment", 8), ("pointeeLayout", "bytes", True)):
            ty = copy.deepcopy(MANY)
            ty[field][key] = value
            with self.assertRaisesRegex(ValueError, "layout"):
                type_of(ty)

    def test_target_and_resource_limits_are_explicit(self):
        for key, value in (("pointerBits", 32), ("endianness", "big"), ("arch", "x86_64"), ("os", "linux")):
            self.rejects(lambda r: r["configuration"].update({key: value}), "target")
        self.rejects(lambda r: r["sourceValidity"]["slices"].extend([{}] * 512), "inventory")
        self.rejects(lambda r: r["instructions"][2].update(rhs=ref(0)), "offset type")
        self.rejects(lambda r: r["instructions"][3].update(tag="ret_load"), "unsupported AIR operation")

    def test_slice_element_retains_slice_and_index(self):
        text = decode(slice_element_fixture())
        self.assertIn("(.sliceElementPointer (.local 0) (.local 1))", text)
        self.assertIn("(.pointer false false (.scalar (.int false 8)))", text)

    def test_slice_element_cannot_erase_type_permissions_or_operands(self):
        edits = [lambda r: r["instructions"][2].update(lhs=ref(1)),
                 lambda r: r["instructions"][2].update(rhs=ref(0)),
                 lambda r: r["instructions"][2].update(rhs=ref(2)),
                 lambda r: r["instructions"][2].pop("lhs"),
                 lambda r: r["instructions"][2].update(unexpected=True),
                 lambda r: r["instructions"][2].update(payloadVisited=False),
                 lambda r: r["instructions"][2]["type"]["flags"].update(isConst=False),
                 lambda r: r["instructions"][2]["type"]["flags"].update(size="many"),
                 lambda r: r["instructions"][2].update(type=pointer(USIZE, layout(8, 8), const=True))]
        for edit in edits:
            record = slice_element_fixture()
            edit(record)
            with self.assertRaises(ValueError):
                decode(record)

    def test_scalar_client_still_uses_checked_control_decoder(self):
        record = fixture()
        record["configuration"].update(arch="aarch64", os="macos", pointerBits=64, endianness="little")
        text = decode(record)
        self.assertIn("(.scalar (.arithmetic", text)
        self.assertIn("(.scalar (.comparison", text)
        record["instructions"][4]["rhs"] = ref(4)
        with self.assertRaisesRegex(ValueError, "dominated"):
            decode(record)


if __name__ == "__main__":
    unittest.main()
