#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Word-pair specialization admission; unchanged default decoders fail closed.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import copy
import unittest

from test_zig_air_specializations import records, CALLEE, SOURCES
from generate_byte_memory import ByteLoopDecoder
from generate_word_swap import WordSwapDecoder


def fixture():
    record = records()[CALLEE]
    record["signature"]["callingConvention"] = {"auto": {}}
    record["configuration"].update(arch="aarch64", os="macos", pointerBits=64, endianness="little")
    return record


class WordSwapTests(unittest.TestCase):
    def rejects(self, edit):
        record = fixture()
        edit(record)
        with self.assertRaises(ValueError):
            WordSwapDecoder(record, SOURCES).program(record)

    def test_explicit_contract_and_original_mapping_are_retained(self):
        record = fixture()
        original = copy.deepcopy(record)
        decoder = WordSwapDecoder(record, SOURCES)
        text = decoder.program(record)
        self.assertTrue(text.startswith("{ program :="))
        self.assertIn("(.argument 0)", text)
        self.assertIn("(.argument 1)", text)
        self.assertEqual(decoder.source_parameters, [1, 2])
        self.assertEqual(decoder.visited, {0, 1, 2})
        self.assertEqual(record, original)
        with self.assertRaises(ValueError):
            ByteLoopDecoder(record)

    def test_other_specializations_and_contract_erasure_reject(self):
        self.rejects(lambda r: r["signature"].update(genericInstance=False))
        self.rejects(lambda r: r["signature"].update(noaliasBits=0))
        self.rejects(lambda r: r["signature"].update(callingConvention={"c": {}}))
        self.rejects(lambda r: r["specialization"]["owner"].update(name="mem.other"))
        self.rejects(lambda r: r["specialization"]["arguments"][0]["value"].update(bits=16))
        self.rejects(lambda r: r["specialization"].update(sourceNoaliasBits=0))
        self.rejects(lambda r: r["specialization"]["arguments"][1].update(runtimeIndex=1))
        self.rejects(lambda r: r["instructions"][0].update(zirParameterIndex=0))
        self.rejects(lambda r: r["signature"]["parameters"][0]["flags"].update(isConst=True))

    def test_source_configuration_body_and_dominance_remain_checked(self):
        self.rejects(lambda r: r.update(sourceSha256="c" * 64))
        self.rejects(lambda r: r["configuration"].update(endianness="big"))
        self.rejects(lambda r: r["configuration"].update(pointerBits=32))
        self.rejects(lambda r: r["instructions"][2].update(tag="unrecognized"))
        self.rejects(lambda r: r["instructions"][2].update(operand={"kind": "instruction", "index": 3}))
        self.rejects(lambda r: r["instructions"][2].update(payloadVisited=False))
        self.rejects(lambda r: r.update(body=[0, 1, 2, 2]))
        self.rejects(lambda r: r.update(body=[0, 2]))


if __name__ == "__main__":
    unittest.main()
