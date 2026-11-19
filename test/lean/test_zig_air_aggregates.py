#!/usr/bin/env python3
"""Negative controls for the aggregate capture inspection, not proof admission.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

import check_zig_air_aggregates as gate
from test_zig_air_memory_generate import memory_fixture


def fixture():
    records = {gate.PREFIX + name: memory_fixture() for name in (*gate.NAMES, *gate.HELPERS)}
    outer = gate.types("a" * 64)[0]
    for record in records.values():
        record["signature"]["parameters"][0]["child"] = copy.deepcopy(outer)
    records[gate.PREFIX + "initial"]["instructions"] = [
        {"index": 0, "tag": "store", "payloadVisited": True, "rhs": gate.initializer("a" * 64)}]
    records[gate.PREFIX + "touch"]["instructions"] = [
        {"index": i + 1, "tag": "struct_field_ptr_index_" + str(i) if i < 4 else "struct_field_ptr",
         "fieldIndex": i, "payloadVisited": True, "operand": {"kind": "instruction", "index": 0}}
        for i in range(5)]
    records[gate.PREFIX + "initial"]["signature"]["returnType"] = copy.deepcopy(outer)
    for name, reason in (("packed_read", "unresolved-or-packed-struct"), ("tagged_read", "comptime-struct-field")):
        records[gate.PREFIX + name]["signature"]["parameters"][0]["child"] = {"kind": "unsupported", "reason": reason}
    ordinal, signed, opened, owner = gate.enum_types("a" * 64)
    for name, ty in (("ordinal_bytes", ordinal), ("open_bytes", opened), ("signed_view", signed), ("enum_byte", owner)):
        records[gate.PREFIX + name]["signature"]["parameters"][0]["child"] = copy.deepcopy(ty)
    records[gate.PREFIX + "signed_view"]["instructions"] = [
        {"index": 0, "tag": "call", "payloadVisited": True,
         "callee": {"identity": {"name": "mem.asBytes__func_1"}}},
        {"index": 1, "tag": "array_to_slice", "payloadVisited": True, "operand": {"kind": "instruction", "index": 0}}]
    return records


class AggregateInspectionTests(unittest.TestCase):
    def test_explicit_partial_values_still_reject_semantic_admission(self):
        records = fixture()
        original = copy.deepcopy(records)
        result = gate.inspect(records, "a" * 64)
        self.assertEqual(result["typedUndefinedFields"], 3)
        self.assertEqual(set(result["decoderRejections"]), {*gate.NAMES, *gate.HELPERS})
        self.assertEqual(records, original)

    def test_initializer_layout_and_undefinedness_cannot_be_erased(self):
        mutations = [
            lambda x: x["fields"][0].update(kind="constant", value=0),
            lambda x: x["fields"][2]["fields"][0].update(kind="constant", value=0),
            lambda x: x["fields"].pop(),
            lambda x: x["type"]["identity"].update(sourceSha256="b" * 64),
            lambda x: x["type"]["fields"][2].update(offset=8),
            lambda x: x["type"]["fields"][0].update(index=False),
            lambda x: x["type"]["fields"][0].update(explicitAlignment=1),
        ]
        for mutate in mutations:
            records = fixture()
            mutate(records[gate.PREFIX + "initial"]["instructions"][0]["rhs"])
            with self.subTest(mutation=mutate), self.assertRaises(ValueError): gate.inspect(records, "a" * 64)

    def test_field_pointers_keep_operands_and_indices(self):
        for field, value in (("fieldIndex", 4), ("fieldIndex", None), ("operand", None),
                             ("operand", {"kind": "instruction", "index": 1})):
            records = fixture()
            records[gate.PREFIX + "touch"]["instructions"][0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError): gate.inspect(records, "a" * 64)

    def test_packed_or_comptime_fields_cannot_acquire_an_ordinary_layout(self):
        for name in ("packed_read", "tagged_read"):
            records = fixture()
            records[gate.PREFIX + name]["signature"]["parameters"][0]["child"] = gate.types("a" * 64)[0]
            with self.subTest(name=name), self.assertRaises(ValueError): gate.inspect(records, "a" * 64)

    def test_undefined_scalar_remains_uninterpreted(self):
        from generate import constant
        from generate_memory import constant as memory_constant
        undefined = {"kind": "undefined", "type": {"kind": "int", "bits": 32, "signedness": "unsigned"}}
        for decoder in (constant, memory_constant):
            with self.subTest(decoder=decoder), self.assertRaises(ValueError): decoder(undefined)

    def test_enum_identity_values_and_exhaustiveness_are_bound(self):
        for mutate in (lambda t: t['backingType'].update(signedness='unsigned'),
                       lambda t: t['fields'][0].update(value=7),
                       lambda t: t.update(nonexhaustive=True),
                       lambda t: t['layout'].update(bytes=8),
                       lambda t: t['identity'].update(sourceSha256='b' * 64),
                       lambda t: t['fields'].pop()):
            records = fixture()
            mutate(records[gate.PREFIX + 'signed_view']['signature']['parameters'][0]['child'])
            with self.assertRaises(ValueError): gate.inspect(records, 'a' * 64)

    def test_array_conversion_requires_actual_operand(self):
        for mutate in (lambda i: i.pop('operand'), lambda i: i.update(unsupportedPayload=True),
                       lambda i: i['operand'].update(index=1)):
            records = fixture()
            mutate(records[gate.PREFIX + 'signed_view']['instructions'][1])
            with self.assertRaises(ValueError): gate.inspect(records, 'a' * 64)


if __name__ == "__main__":
    unittest.main()
