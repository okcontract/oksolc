#!/usr/bin/env python3
"""Admission controls for partial aggregates and declaration-order fields.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

from test_zig_air_generate import fixture, inst, ref, const, NEVER, VOID
from check_zig_air_memory import pointer, layout, uint
from generate_aggregate import Decoder, type_of, constant, render
from generate_memory import Decoder as MemoryDecoder


def aggregate_fixture():
    record = fixture()
    record["configuration"].update(arch="aarch64", os="macos", pointerBits=64, endianness="little")
    word = uint(64)
    owner = {"kind": "struct", "identity": {"name": "fixture.Pair", "sourceFile": "fixture.zig",
        "sourceSha256": "a" * 64}, "containerLayout": "auto", "layout": layout(16, 8),
        "fields": [{"index": i, "name": name, "offset": offset, "explicitAlignment": None, "type": word}
                   for i, (name, offset) in enumerate((("last", 8), ("first", 0)))]}
    initial = {"kind": "aggregate", "type": owner,
               "fields": [{"kind": "undefined", "type": word}, const(0, word)]}
    record["signature"].update(parameters=[word], returnType=owner)
    record["instructions"] = [
        inst(0, "arg", word, zirParameterIndex=0),
        inst(1, "alloc", pointer(owner, owner["layout"]), allocationKind="stack"),
        inst(2, "store", VOID, lhs=ref(1), rhs=initial),
        inst(3, "struct_field_ptr_index_1", pointer(word, layout(8, 8)), operand=ref(1), fieldIndex=1),
        inst(4, "store", VOID, lhs=ref(3), rhs=ref(0)),
        inst(5, "load", owner, operand=ref(1)), inst(6, "ret", NEVER, operand=ref(5))]
    record["body"] = list(range(7))
    return copy.deepcopy(record)


class AggregateGenerationTests(unittest.TestCase):
    def test_declaration_index_maps_to_offset_without_reordering_values(self):
        record = aggregate_fixture()
        original = copy.deepcopy(record)
        text, count = render(record)
        self.assertEqual(count, 7)
        self.assertIn("(.fieldPointer (.local 1) 0)", text)
        self.assertIn("[(0, (.scalar (.int false 64 (0))))]", text)
        self.assertEqual(record, original)
        with self.assertRaises(ValueError): MemoryDecoder(record).program(record)

    def test_fixed_index_dominance_and_permissions(self):
        for edit in (lambda i: i.update(fieldIndex=0), lambda i: i.update(operand=ref(3)),
                     lambda i: i["type"]["flags"].update(isConst=True),
                     lambda i: i.update(operand=ref(0))):
            record = aggregate_fixture()
            edit(record["instructions"][3])
            with self.subTest(edit=edit), self.assertRaises(ValueError): Decoder(record).program(record)

    def test_partial_values_preserve_field_count_and_type(self):
        for edit in (lambda v: v["fields"].pop(), lambda v: v["fields"][0].update(type=uint(32)),
                     lambda v: v["fields"][1].update(value=2**64),
                     lambda v: v["fields"][0].update(value=0)):
            record = aggregate_fixture()
            edit(record["instructions"][2]["rhs"])
            with self.subTest(edit=edit), self.assertRaises(ValueError): Decoder(record).program(record)
        with self.assertRaises(ValueError): constant({"kind": "undefined", "type": uint(64)})

    def test_complete_geometry_is_checked(self):
        for edit in (lambda t: t.update(containerLayout="packed"), lambda t: t["fields"][1].update(offset=8),
                     lambda t: t["fields"][1].update(offset=1), lambda t: t["fields"][1].update(index=False),
                     lambda t: t["fields"][1].update(name="last"), lambda t: t["layout"].update(bytes=8), lambda t: t["layout"].update(bytes=17),
                     lambda t: t["identity"].update(sourceSha256="bad"),
                     lambda t: t["fields"][1].update(explicitAlignment=4)):
            owner = aggregate_fixture()["signature"]["returnType"]
            edit(owner)
            with self.subTest(edit=edit), self.assertRaises(ValueError): type_of(owner)

    def test_no_source_obligation_or_operation_can_disappear(self):
        record = aggregate_fixture()
        record["instructions"][4]["tag"] = "memcpy"
        with self.assertRaises(ValueError): Decoder(record).program(record)
        record = aggregate_fixture()
        record["sourceValidity"]["slices"] = [{}]
        with self.assertRaises(ValueError): Decoder(record).program(record)
        record = aggregate_fixture()
        record["body"].remove(4)
        with self.assertRaises(ValueError): Decoder(record).program(record)
        record = aggregate_fixture()
        record["sourceOperationTags"].append("slice_length")
        with self.assertRaisesRegex(ValueError, "slice source validity"):
            Decoder(record).program(record)



if __name__ == "__main__":
    unittest.main()
