#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Closed Solidity admission, real source binding, and proof-encoder regressions.
"""
import copy
import json
import unittest
from types import SimpleNamespace

import check_compiler_functions as checker
from compiler_function_cases import cases, request
from solidity_function_source import parse
from common import BuildError


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def fake_response(req, code="00"):
    model = checker.model(req)
    return {"contracts": {"Function.sol": {model["contract"]: {"evm": {
        "bytecode": {"object": "608080604052346013576044908160188239f35b5f80fdfe" + code},
        "deployedBytecode": {"object": code}, "methodIdentifiers": {model["signature"]: "12345678"}}}}}}


class FunctionTests(unittest.TestCase):
    def test_batches_bind_every_case_once(self):
        pairs = [(req, fake_response(req)) for _, req in cases()]
        batches, claims = checker.artifacts.proof_batches(checker, pairs, 8)
        self.assertEqual([len(names) for _, names in batches], [16, 16, 16, 2])
        self.assertEqual(claims, [checker.MODULE + f".Case{i}.checked" for i in range(50)])
        for (_, names), first in zip(batches, (0, 16, 32, 48)):
            self.assertEqual(names[0], checker.MODULE + f".Case{first}.checked")
        for malformed in ([], [(b"proof", [])], [(b"", ["claim"])],
                          [(b"proof", ["same"]) for _ in pairs], [(b"proof", ["one"])],
                          [(b"proof", [None])]):
            with self.subTest(batches=len(malformed)), self.assertRaises(ValueError):
                checker.artifacts.proof_batches(SimpleNamespace(proof_batches=lambda *_: malformed), pairs, 8)
        legacy = SimpleNamespace(proof_source=lambda *_: (b"proof", ["one"]))
        self.assertEqual(checker.artifacts.proof_batches(legacy, pairs[:1], 8), ([(b"proof", ["one"])], ["one"]))
        for offset in (-1, True, 128):
            with self.assertRaises(ValueError):
                checker.proof_source(pairs[:1], 8, case_offset=offset)

    def test_arithmetic_mode_is_bound_to_source_and_claim(self):
        unchecked = checker.model(request("(x + y) - y"))
        checked_request = request("(x + y) - y", checked=True)
        checked = checker.model(checked_request)
        self.assertFalse(unchecked["checked"])
        self.assertTrue(checked["checked"])
        self.assertEqual({**unchecked, "checked": True}, checked)
        proof, _ = checker.proof_source([(checked_request, fake_response(checked_request))], 8)
        self.assertIn(b'checked := true', proof)
        self.assertIn(b'SolidityWord.Expr.evalChecked', proof)
        self.assertIn(b'SolidityDeployment.Preserves source creation code', proof)
        self.assertNotIn(b'theorem canonical :', proof)
        self.assertEqual(checker.case_metadata(checked_request, fake_response(checked_request))["arithmeticMode"], "checked")
        for body in ("unchecked { return x; } return x;", "{ return x; }", "unchecked { unchecked { return x; } }"):
            text = request("x", checked=True)["sources"]["Function.sol"]["content"].replace("return x;", body)
            with self.subTest(body=body), self.assertRaises(ValueError):
                parse(text)

    def test_precedence_and_associativity(self):
        model = checker.model(request("x - y - x << y + x & x ^ y | x"))
        expression = checker.words.source_expression(model["nodes"], model["root"])
        self.assertEqual(expression, '(.binary .bitor (.binary .bitxor (.binary .bitand (.binary .shl '
            '(.binary .sub (.binary .sub (.input "x") (.input "y")) (.input "x")) '
            '(.binary .add (.input "y") (.input "x"))) (.input "x")) (.input "y")) (.input "x"))')
        self.assertEqual(checker.model(request("uint256(0xff)", ()))['nodes'], [{"literal": "255"}])

    def test_public_word_maximum_and_wildcard_pragma(self):
        baseline = request("type(uint256).max + x", ("x",), checked=True)
        text = baseline["sources"]["Function.sol"]["content"]
        changed = text.replace("external", "public").replace("^0.8.0", "*")
        parsed = parse(changed)
        self.assertEqual(parsed, {**parse(text), "visibility": "public"})
        self.assertEqual(parsed["nodes"], [{"literal": str(2**256 - 1)}, {"input": "x"},
            {"binary": {"op": "add", "left": 0, "right": 1}}])
        explicit = parse(changed.replace("type(uint256).max", "uint256(" + str(2**256 - 1) + ")"))
        self.assertEqual(parsed, explicit)
        for replacement in ("type(uint8).max", "type(int256).max", "type(uint).max",
                "type(uint256).min", "type(uint256).max()", "type(C).runtimeCode", "type(x).max"):
            with self.subTest(expression=replacement), self.assertRaises(ValueError):
                parse(changed.replace("type(uint256).max", replacement))
        for visibility in ("private", "internal", "", "public external"):
            with self.subTest(visibility=visibility), self.assertRaises(ValueError):
                parse(changed.replace("public", visibility))
        for pragma in ("^0.7.0", "^0.9.0", "", "* || ^0.8.0", "*; pragma abicoder v1"):
            with self.subTest(pragma=pragma), self.assertRaises(ValueError):
                parse(changed.replace("solidity *", "solidity " + pragma))
        for body in ("f(x)", "this.f(x)"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                parse(changed.replace("type(uint256).max + x", body))

    def test_source_fail_closed(self):
        for expression in ("x + 1", "1 + 2", "uint256(1 + 2)", "uint256(-1)", "uint256(1.2)",
                           "uint256(" + str(2**256) + ")", "uint256(00)", "uint256(0x" + "1"*40 + ")",
                           "unknown", "x / y", "x % y", "x**y", "x==y",
                           "x ? y : x", "x++", "-x", "address(x)", "" , "(" * 34 + "x" + ")" * 34):
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                checker.model(request(expression))
        baseline = request("x")["sources"]["Function.sol"]["content"]
        self.assertEqual(parse(baseline.replace("return x;", "// comment\rreturn x;")), parse(baseline))
        for changed in (baseline.replace("unchecked", ""), baseline.replace("pure", "view"),
                        baseline.replace("uint256 x", "uint8 x"), baseline + "contract D {}",
                        baseline.replace("contract C {", "contract C { constructor() payable {}"),
                        baseline.replace("contract C {", "contract C { uint256 state = 1;"),
                        baseline.replace("contract C {", "contract C is Base {"),
                        baseline.replace("return x", "return\u00a0x"),
                        baseline + "/*unterminated", baseline.replace("return x;", "return x; return x;")):
            with self.subTest(source=changed), self.assertRaises(ValueError):
                parse(changed)
        for parameters in (("x", "x"), tuple("abcdefghi"), ("return",), ("assembly",), ("uint8",), ("bytes32",)):
            with self.assertRaises(ValueError):
                checker.model(request("x", parameters))

    def test_standard_json_binding(self):
        req = request("x")
        res = fake_response(req)
        self.assertEqual(checker.request(encoded(req)), req)
        self.assertEqual(checker.response(encoded(res), encoded(req)), res)
        changed = copy.deepcopy(req)
        changed["settings"]["optimizer"]["enabled"] = False
        with self.assertRaises(ValueError):
            checker.request(encoded(changed))
        for patch in ({"sources": {}}, {"language": "Yul"}, {"extra": 0}):
            with self.assertRaises(ValueError):
                checker.admit_request({**req, **patch})
        for patch in ({"contracts": {}}, {"errors": [{"severity": "error"}]}, {"errors": [42]}, {"extra": 1}):
            with self.assertRaises(ValueError):
                checker.response(encoded({**res, **patch}), encoded(req))
        with self.assertRaises(BuildError):
            checker.request(encoded(req).replace(b'"Solidity"', b'"Solidity","language":"Yul"'))
        with self.assertRaises(ValueError):
            checker.artifact(req, fake_response(req, "00" * 1025))
        for creation in ("", "0", "zz", "00" * 2049):
            changed = fake_response(req)
            changed['contracts']['Function.sol']['C']['evm']['bytecode']['object'] = creation
            with self.subTest(creation=creation[:12]), self.assertRaises(ValueError):
                checker.artifact(req, changed)
        changed = fake_response(req)
        del changed['contracts']['Function.sol']['C']['evm']['bytecode']
        with self.assertRaises(ValueError):
            checker.artifact(req, changed)

    def test_closed_proof_encoder(self):
        req = request("x << y")
        proof, claims = checker.proof_source([(req, fake_response(req))], 8)
        self.assertIn(b'(.binary .shl (.input "x") (.input "y"))', proof)
        self.assertIn(b'def code : List UInt8 := [0]', proof)
        self.assertIn(b'by decide +kernel', proof)
        self.assertIn(b'theorem calls : SolidityCall.Preserves source code 5', proof)
        self.assertIn(b'theorem checked : SolidityDeployment.Preserves source creation code 101 5', proof)
        self.assertIn(b'SolidityDeployment.certify', proof)
        self.assertIn(b'theorem runtime_image : padded creation 24 1 = code := by decide', proof)
        self.assertIn(b'theorem canonical : SolidityFunction.Preserves source code 5', proof)
        self.assertEqual(checker.REPORT_METADATA['callScope'], 'allValuesAndCalldataBelow2To64Bytes')
        self.assertFalse(checker.REPORT_METADATA['deploymentVerified'])
        self.assertEqual(claims, [checker.MODULE + ".Case0.checked"])
        for bad in ([], [(request('x"; axiom bad : False'), fake_response(req))]):
            with self.assertRaises(ValueError):
                checker.proof_source(bad, 8)
        with self.assertRaises(ValueError):
            checker.proof_source([(req, fake_response(req))], True)

    def test_corpus_and_corruption(self):
        records = cases()
        self.assertEqual(len(records), 50)
        self.assertEqual(len({n for n, _ in records}), len(records))
        code = "63123456783460403660031901126001600201f3fd"
        pairs = [(req, fake_response(req, code + ("601160045260245ffd" if checker.model(req)["checked"] else "")))
                 for _, req in records]
        for req, res in pairs:
            checker.artifact(req, res)
        negatives = checker.negative_pairs(pairs)
        self.assertEqual(len(negatives), 20)
        for _, negative in negatives:
            checker.artifact(*negative[0])
        self.assertTrue(all(checker.artifact(req, res)[1].hex() == code +
            ("601160045260245ffd" if checker.model(req)["checked"] else "") for req, res in pairs))

    def test_checked_corruption_keeps_native_pair_and_panic_shape(self):
        unchecked, checked = request("x + y"), request("x + y", checked=True)
        code = "601160045260245ffd"
        pairs = [(unchecked, fake_response(unchecked, "00")), (checked, fake_response(checked, code))]
        controls = dict(checker.checked_negative_pairs(pairs))
        erased_request, erased_response = controls["erase_overflow_checks_add"][0]
        self.assertTrue(checker.model(erased_request)["checked"])
        self.assertEqual(erased_response, pairs[0][1])
        for name, expected in (("wrong_panic_code", "601260045260245ffd"),
                               ("wrong_panic_length", "601160045260205ffd")):
            req, res = controls[name][0]
            parsed, runtime, _ = checker.artifact(req, res)
            self.assertEqual(runtime.hex(), expected)
            self.assertTrue(checker.creation_code(parsed, res).endswith(runtime))
        with self.assertRaisesRegex(ValueError, "missing matching unchecked"):
            checker.checked_negative_pairs(pairs[1:])
        with self.assertRaisesRegex(ValueError, "native arithmetic panic changed"):
            checker.checked_negative_pairs([pairs[0], (checked, fake_response(checked, code.replace("6011", "6012")))])

    def test_corruption_preserves_push_data_and_requires_guard(self):
        req = request("x + y")
        code = "63123456783460403660031901126001600201f3fd60fd"
        pairs = dict(checker.negative_pairs([(req, fake_response(req, code))]))
        changed = checker.artifact(*pairs['return_on_invalid_call'][0])[1]
        self.assertEqual(changed[-2:], b'\x60\xfd')
        self.assertEqual(changed[-3], 0xf3)
        with self.assertRaisesRegex(ValueError, 'native ABI length guard changed'):
            checker.negative_pairs([(req, fake_response(req, code.replace('604036', '604136')))])

    def test_creation_corruption_is_separate_from_runtime(self):
        req = request("x + y")
        res = fake_response(req, "63123456783460403660031901126001600201f3fd")
        model, runtime, _ = checker.artifact(req, res)
        creation = checker.creation_code(model, res)
        pairs = dict(checker.negative_pairs([(req, res)]))
        for name in ('creation_wrong_image', 'creation_accept_value', 'creation_reverts', 'creation_wrong_copy_offset'):
            _, changed = pairs[name][0]
            self.assertEqual(checker.artifact(req, changed)[1], runtime)
            self.assertNotEqual(checker.creation_code(model, changed), creation)
        for name in ('wrong_arithmetic', 'accept_nonzero_value', 'accept_truncated_arguments', 'return_on_invalid_call'):
            _, changed = pairs[name][0]
            self.assertTrue(checker.creation_code(model, changed).endswith(checker.artifact(req, changed)[1]))
        changed = copy.deepcopy(res)
        changed['contracts']['Function.sol']['C']['evm']['bytecode']['object'] = creation.hex().replace('60188239', '60198239')
        with self.assertRaisesRegex(ValueError, 'native creation copy changed'):
            checker.negative_pairs([(req, changed)])


if __name__ == "__main__":
    unittest.main()
