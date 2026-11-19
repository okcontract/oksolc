#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Reject byte-view provenance, alignment and storage-contract mutations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import copy
import unittest

from test_zig_air_generate import inst, ref, const, U8, VOID, NEVER
from test_zig_air_memory_generate import memory_fixture, USIZE
from check_zig_air_memory import pointer, layout
from generate_byte_memory import ByteDecoder
from generate_memory import Decoder

U32 = {"kind": "int", "bits": 32, "signedness": "unsigned"}
WORD_PTR = pointer(U32, layout(4, 4))


def byte_pointer(size, alignment=4, const=False):
    result = pointer(U8, layout(1, 1), size=size, const=const)
    result["flags"]["alignment"] = alignment
    return result


def fixture():
    result = memory_fixture()
    many, view, one = byte_pointer("many"), byte_pointer("slice"), byte_pointer("one", 1)
    slot = pointer(view, layout(16, 8))
    readonly = pointer(view, layout(16, 8), const=True)
    result["signature"].update(parameters=[WORD_PTR, USIZE, U8], returnType=VOID)
    result["sourceValidity"]["slices"] = []
    result["instructions"] = [inst(0, "arg", WORD_PTR, zirParameterIndex=0), inst(1, "arg", USIZE, zirParameterIndex=1),
        inst(2, "arg", U8, zirParameterIndex=2), inst(3, "ptr_cast", many, operand=ref(0)),
        inst(4, "slice", view, lhs=ref(3), rhs=const(4, USIZE)), inst(5, "alloc", slot, allocationKind="stack"),
        inst(6, "store", VOID, lhs=ref(5), rhs=ref(4)), inst(7, "ptr_cast", readonly, operand=ref(5)),
        inst(8, "load", view, operand=ref(7)), inst(9, "slice_elem_ptr", one, lhs=ref(8), rhs=ref(1)),
        inst(10, "store", VOID, lhs=ref(9), rhs=ref(2)), inst(11, "ret", NEVER, operand={"kind": "unit"})]
    result["body"] = list(range(12))
    return copy.deepcopy(result)


def decode(record):
    decoder = ByteDecoder(record)
    return decoder.program(record), decoder.byte_inventory()


class ByteGenerationTests(unittest.TestCase):
    def rejects(self, edit, message=None):
        record = fixture()
        edit(record)
        with self.assertRaisesRegex(ValueError, message or "."):
            decode(record)

    def test_fresh_slot_retains_origin_alignment_and_effects(self):
        text, inventory = decode(fixture())
        self.assertIn("(.wordByteCast true true 4 (.local 0))", text)
        self.assertIn("(.wordByteStore .little (.local 9) (.local 2))", text)
        self.assertIn("(.sliceElementPointer (.local 8) (.local 1))", text)
        self.assertEqual(inventory, {"values": [
            {"instruction": 3, "origin": 3, "alignment": 4}, {"instruction": 4, "origin": 3, "alignment": 4},
            {"instruction": 8, "origin": 5, "alignment": 4}, {"instruction": 9, "origin": 5, "alignment": 1}],
            "stackSlots": [{"instruction": 5, "allocation": 5}, {"instruction": 7, "allocation": 5}]})
        with self.assertRaisesRegex(ValueError, "attributes"):
            Decoder(fixture()).program(fixture())

    def test_alignment_metadata_is_checked(self):
        for alignment in (0, 3, 8, True, 4.0):
            self.rejects(lambda r: r["instructions"][3]["type"]["flags"].update(alignment=alignment), "alignment")
        self.rejects(lambda r: r["instructions"][4]["type"]["flags"].update(alignment=2), "extent and alignment")
        self.rejects(lambda r: r["instructions"][9]["type"]["flags"].update(alignment=4), "byte element")
        self.rejects(lambda r: r["instructions"][3]["type"]["pointeeLayout"].update(alignment=4), "layout")

    def test_source_extent_cannot_be_widened(self):
        for rhs in (const(3, USIZE), const(5, USIZE), ref(1)):
            self.rejects(lambda r: r["instructions"][4].update(rhs=rhs), "four-byte extent")
        self.rejects(lambda r: r["instructions"][4].update(type=VOID), "four-byte extent")
        # Equal alignment alone cannot justify changing the element type.
        self.rejects(lambda r: r["instructions"][4].update(type=pointer(U32, layout(4, 4), size="slice")), "four-byte extent")

    def test_constness_and_element_type_cannot_be_changed(self):
        self.rejects(lambda r: [x["flags"].update(isConst=True) for x in
                               (r["signature"]["parameters"][0], r["instructions"][0]["type"])], "cast contract")
        self.rejects(lambda r: r["instructions"][9]["type"]["flags"].update(isConst=True), "byte element")
        self.rejects(lambda r: r["instructions"][10].update(rhs=ref(1)), "byte view store")
        self.rejects(lambda r: r["instructions"][8].update(type=U8), "stored type")

    def test_arbitrary_aligned_inputs_and_generic_contracts_stay_closed(self):
        self.rejects(lambda r: r["signature"]["parameters"].__setitem__(0, byte_pointer("many")), "aligned signature")
        for child, shape in ((USIZE, layout(8, 8)), (WORD_PTR, layout(8, 8))):
            self.rejects(lambda r: r["signature"]["parameters"].__setitem__(0, pointer(child, shape)), "scalar or u32-pointer")
        self.rejects(lambda r: r["signature"].update(genericInstance=True), "specialization")
        self.rejects(lambda r: r["signature"].update(noaliasBits=1), "parameter contract")
        self.rejects(lambda r: r["configuration"].update(endianness="big"), "target")

    def test_storage_requires_provenance_and_exact_types(self):
        self.rejects(lambda r: r["instructions"][6].update(rhs=ref(0)), "checked origin")
        self.rejects(lambda r: r["instructions"][6].update(lhs=ref(0)), "escaped checked storage")
        self.rejects(lambda r: r["instructions"][5].update(allocationKind="heap"), "fresh stack")
        self.rejects(lambda r: r["instructions"][7]["type"]["flags"].update(isConst=False), "slot cast")
        self.rejects(lambda r: r["instructions"][9].update(lhs=ref(1)), "aligned result|byte view|slice pointer")
        self.rejects(lambda r: r["instructions"][9].update(rhs=ref(9)), "dominated")

    def test_byte_pointers_and_slots_cannot_escape(self):
        self.rejects(lambda r: r["instructions"][11].update(operand=ref(9)), "cannot escape")
        self.rejects(lambda r: r["instructions"][11].update(operand=ref(5)), "cannot escape")
        self.rejects(lambda r: r["instructions"][9].update(tag="ptr_add"), "cannot escape")
        self.rejects(lambda r: r["instructions"][6].update(rhs=ref(5)), "checked origin")

    def test_control_joins_and_unmodeled_pointer_attributes_reject(self):
        def join(record):
            element = byte_pointer("one", None)
            record["instructions"][9:] = [inst(9, "block", element, body=[10, 11]),
                inst(10, "slice_elem_ptr", element, lhs=ref(8), rhs=ref(1)),
                inst(11, "br", NEVER, target=9, operand=ref(10)),
                inst(12, "store", VOID, lhs=ref(9), rhs=ref(2)),
                inst(13, "ret", NEVER, operand={"kind": "unit"})]
            record["body"] = list(range(10)) + [12, 13]
        self.rejects(join, "cannot escape")
        self.rejects(lambda r: r["instructions"][3]["type"]["flags"].update(isVolatile=True), "attributes")
        self.rejects(lambda r: r["instructions"][3]["type"].update(child=USIZE), "layout|alignment")

    def test_uninitialized_slot_is_preserved_as_a_runtime_obligation(self):
        record = fixture()
        record["instructions"][6] = inst(6, "load", byte_pointer("slice"), operand=ref(5))
        text, _ = decode(record)
        self.assertIn("(.load (.local 5))", text)
        self.assertNotIn("(.store (.local 5)", text)

    def test_const_byte_load_and_slice_projections(self):
        record = fixture()
        record["instructions"][10] = inst(10, "load", U8, operand=ref(9))
        text, _ = decode(record)
        self.assertIn("(.wordByteLoad .little (.local 9))", text)
        for tag, ty in (("slice_len", USIZE), ("slice_ptr", byte_pointer("many"))):
            record = fixture()
            record["instructions"][10] = inst(10, tag, ty, operand=ref(8))
            text, _ = decode(record)
            self.assertIn("(." + ("sliceLen" if tag == "slice_len" else "slicePtr") + " (.local 8))", text)


if __name__ == "__main__":
    unittest.main()
