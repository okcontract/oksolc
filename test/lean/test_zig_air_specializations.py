#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Direct-call provenance controls; metadata checks are not semantic admission.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import copy
import unittest

from test_zig_air_generate import fixture, inst, ref, const, U8, VOID, NEVER
from check_zig_air_memory import pointer, layout
from generate_memory import Decoder
from link_specializations import link, specialization

WORD = {"kind": "int", "bits": 32, "signedness": "unsigned"}
POINTER = pointer(WORD, layout(4, 4))
ROOT = "fixture.choose"
CALLEE = "mem.swap__anon_1"
SOURCES = {"fixture.zig": "a" * 64, "mem.zig": "b" * 64}


def records():
    root = fixture()
    root["signature"].update(parameters=[POINTER, POINTER], returnType=VOID)
    root["instructions"] = [inst(0, "arg", POINTER, zirParameterIndex=0), inst(1, "arg", POINTER, zirParameterIndex=1),
        inst(2, "call", VOID, callee={"kind": "function", "identity": {"name": CALLEE, "sourceFile": "mem.zig", "sourceSha256": "b" * 64}},
             arguments=[ref(0), ref(1)]), inst(3, "ret", NEVER, operand={"kind": "unit"})]
    root["body"] = [0, 1, 2, 3]
    callee = copy.deepcopy(root)
    callee.update(name=CALLEE, sourceFile="mem.zig", sourceSha256="b" * 64, body=[0, 1, 2])
    callee["signature"].update(genericInstance=True, noaliasBits=3)
    callee["instructions"] = [inst(0, "arg", POINTER, zirParameterIndex=1), inst(1, "arg", POINTER, zirParameterIndex=2),
                               inst(2, "ret", NEVER, operand={"kind": "unit"})]
    callee["specialization"] = {"schema": "oksolc.generic-instance.v1",
        "owner": {"name": "mem.swap", "sourceFile": "mem.zig", "sourceSha256": "b" * 64},
        "sourceNoaliasBits": 6, "sourceComptimeBits": 1, "sourceParameterCount": 3,
        "arguments": [{"kind": "type", "value": WORD}, {"kind": "runtime", "runtimeIndex": 0}, {"kind": "runtime", "runtimeIndex": 1}]}
    return copy.deepcopy({ROOT: root, CALLEE: callee})


class SpecializationTests(unittest.TestCase):
    def rejects(self, edit):
        data = records()
        edit(data)
        with self.assertRaises(ValueError):
            link(data, [ROOT], SOURCES)

    def test_links_preserve_mapping_noalias_and_unverified_obligations(self):
        data = records()
        result = link(data, [ROOT], SOURCES)
        self.assertEqual(result, link(dict(reversed(list(data.items()))), [ROOT], SOURCES))
        self.assertEqual(result["functions"][CALLEE]["runtimeParameterIndices"], [1, 2])
        self.assertEqual(result["functions"][CALLEE]["noaliasBits"], 3)
        self.assertEqual(result["edges"], [{"caller": ROOT, "callee": CALLEE, "instruction": 2, "tag": "call", "arguments": [ref(0), ref(1)]}])
        for key in ("bodyCoverageVerified", "argumentDominanceVerified", "specializationSemanticsVerified", "noaliasVerified", "wholeCompilerVerified"):
            self.assertFalse(result[key])

    def test_missing_or_changed_sources_and_targets_reject(self):
        self.rejects(lambda r: r.pop(CALLEE))
        self.rejects(lambda r: r[CALLEE].update(sourceSha256="c" * 64))
        self.rejects(lambda r: r[ROOT]["instructions"][2]["callee"]["identity"].update(sourceSha256="c" * 64))
        self.rejects(lambda r: r[CALLEE]["specialization"]["owner"].update(sourceFile="other.zig"))
        self.rejects(lambda r: r[CALLEE]["configuration"].update(optimize="Debug"))
        self.rejects(lambda r: r[CALLEE].update(capturePoint="after-legalize"))
        self.rejects(lambda r: r[ROOT]["instructions"][2].update(callee=ref(0)))
        self.rejects(lambda r: r[ROOT]["instructions"][2]["callee"].update(identity={"kind": "unsupported", "reason": "coerced-function"}))
        self.rejects(lambda r: r[ROOT]["instructions"][2].update(payloadVisited=1))

    def test_specialization_mapping_and_contracts_cannot_be_erased(self):
        self.rejects(lambda r: r[CALLEE].pop("specialization"))
        self.rejects(lambda r: r[CALLEE]["signature"].update(genericInstance=False))
        self.rejects(lambda r: r[CALLEE]["signature"].update(noaliasBits=0))
        self.rejects(lambda r: r[CALLEE]["specialization"].update(sourceNoaliasBits=0))
        self.rejects(lambda r: r[CALLEE]["specialization"].update(sourceComptimeBits=3))
        self.rejects(lambda r: r[CALLEE]["specialization"].update(sourceParameterCount=2))
        self.rejects(lambda r: r[CALLEE]["specialization"]["arguments"][2].update(runtimeIndex=0))
        self.rejects(lambda r: r[CALLEE]["specialization"]["arguments"][1].update(runtimeIndex=False))
        self.rejects(lambda r: r[CALLEE]["instructions"][0].update(zirParameterIndex=0))
        self.rejects(lambda r: r[CALLEE]["instructions"][0].update(zirParameterIndex=True))

    def test_known_values_and_runtime_types_bind_specialization_key(self):
        data = records()
        before = link(data, [ROOT], SOURCES)["functions"][CALLEE]["specializationSha256"]
        data[CALLEE]["specialization"]["arguments"][0]["value"] = U8
        after = link(data, [ROOT], SOURCES)["functions"][CALLEE]["specializationSha256"]
        self.assertNotEqual(before, after)
        # Metadata consistency is not the theorem that T=u8 produces *u32.
        self.assertFalse(link(data, [ROOT], SOURCES)["specializationSemanticsVerified"])
        record = data[CALLEE]
        record["specialization"]["sourceComptimeBits"] = 5
        record["specialization"]["sourceNoaliasBits"] = 2
        record["specialization"]["arguments"][2] = {"kind": "value", "value": const(7)}
        record["signature"].update(parameters=[POINTER], noaliasBits=1)
        self.assertEqual(specialization(record, SOURCES)[0], [1])

    def test_runtime_call_types_arity_and_references_reject(self):
        self.rejects(lambda r: r[ROOT]["instructions"][2].update(arguments=[ref(0)]))
        self.rejects(lambda r: r[ROOT]["instructions"][2].update(arguments=[const(0), ref(1)]))
        self.rejects(lambda r: r[ROOT]["instructions"][2].update(arguments=[ref(9), ref(1)]))
        self.rejects(lambda r: r[ROOT]["instructions"][1].update(payloadVisited=False))
        self.rejects(lambda r: r[ROOT]["instructions"][2].update(type=WORD))
        self.rejects(lambda r: r[ROOT]["instructions"][2].update(unsupportedPayload=True))

    def test_unknown_body_payloads_remain_visible_without_coverage_claim(self):
        data = records()
        data[CALLEE]["instructions"][2] = inst(2, "future_container", NEVER, unsupportedPayload=True)
        result = link(data, [ROOT], SOURCES)
        self.assertEqual(result["functions"][CALLEE]["unsupportedBodyInstructions"], [{"index": 2, "tag": "future_container"}])
        self.assertFalse(result["bodyCoverageVerified"])

    def test_strict_semantic_decoder_still_rejects_generic_and_noalias(self):
        record = records()[CALLEE]
        with self.assertRaises(ValueError):
            Decoder(record)
        del record["specialization"]
        with self.assertRaisesRegex(ValueError, "specialization or parameter contract"):
            Decoder(record)


if __name__ == "__main__":
    unittest.main()
