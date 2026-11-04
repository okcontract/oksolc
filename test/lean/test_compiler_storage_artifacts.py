#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Admission and binding tests for complete Solidity storage certificates.
Kernel rejection of semantic mutations belongs to the native acceptance gate.
"""
import copy
import hashlib
import json
import unittest

import check_compiler_storage as checker
from compiler_storage_cases import cases, function, request


def fake_response(req):
    parsed = checker.model(req)
    return {"contracts": {"Function.sol": {parsed["contract"]: {"evm": {
        "bytecode": {"object": "00"}, "deployedBytecode": {"object": "00"},
        "methodIdentifiers": {f["signature"]: f"{i:08x}"
            for i, f in enumerate(parsed["functions"])}}}}}}


class StorageArtifactTests(unittest.TestCase):
    def test_shared_public_entry_and_maximum_initializer(self):
        req = dict(cases())["public_maximum"]
        parsed = checker.model(req)
        self.assertEqual(parsed["initialization"]["nodes"], [{"literal": str(2**256 - 1)}])
        self.assertEqual(parsed["functions"][0]["visibility"], "public")
        self.assertEqual(checker.case_metadata(req, fake_response(req))["functions"][0]["visibility"], "public")
        changed = copy.deepcopy(req)
        changed["sources"]["Function.sol"]["content"] = changed["sources"]["Function.sol"]["content"].replace("^0.8.0", "*")
        self.assertEqual(checker.model(changed), parsed)
        for before, after in (("type(uint256).max", "type(uint8).max"),
                ("public view", "internal view"), ("private cell", "public cell"),
                ("return cell;", "return get();")):
            changed = copy.deepcopy(req)
            changed["sources"]["Function.sol"]["content"] = changed["sources"]["Function.sol"]["content"].replace(before, after)
            with self.subTest(after=after), self.assertRaises(ValueError):
                checker.model(changed)

    def test_complete_scope_and_sequential_assignments(self):
        for _, req in cases():
            self.assertEqual(checker.request(json.dumps(req).encode()), req)
        parsed = checker.model(dict(cases())["rollback"])
        self.assertEqual(parsed["storage"], ["first", "second"])
        setter, first, second = parsed["functions"]
        self.assertEqual([s["write"]["slot"] for s in setter["body"] if "write" in s], [0, 1])
        self.assertEqual(setter["nodes"][setter["body"][0]["write"]["root"]], {"input": "x"})
        self.assertEqual(first["nodes"], [{"input": "first"}])
        self.assertEqual(second["nodes"], [{"input": "second"}])
        self.assertTrue(setter["checked"])
        with self.assertRaises(ValueError):
            checker.functions.model(dict(cases())["cell"])

    def test_source_rejects_unmodeled_declarations_and_bodies(self):
        req = dict(cases())["cell"]
        content = req["sources"]["Function.sol"]["content"]
        mutations = [
            ("private cell;", "public cell;"), ("private cell;", "private cell = 1;"),
            ("uint256 private", "uint128 private"), ("uint256 private", "uint256 transient private"),
            ("contract C {", "contract C is Base {"), ("contract C {", "contract C layout at 42 {"),
            ("contract C {", "contract C { constructor() {}"),
            ("value; return cell;", "value; return cell; cell = value;"),
            ("cell = value;", "uint256 local = value; cell = local;"),
            ("cell = value;", "if (value) { cell = value; }"),
            ("cell = value;", "cell += value;"), ("cell = value;", "cell = get();"),
            ("cell = value;", "cell = 1;"), ("cell = value;", "cell = unknown;"),
            ("external  returns", "external view returns"),
            ("external view returns", "external pure returns"),
            ("uint256 value", "uint256 cell"), ("function set", "function cell"),
            ("private cell;", "private cell; uint256 private cell;"),
            ("private cell;", "private C;"),
        ]
        for before, after in mutations:
            self.assertIn(before, content)
            changed = copy.deepcopy(req)
            changed["sources"]["Function.sol"]["content"] = content.replace(before, after)
            with self.subTest(after=after), self.assertRaises(ValueError):
                checker.model(changed)
        for functions in ([], [function("f", "return cell;")] * 2,
                [function("f", "return cell;"), "uint256 private later;"],
                [function("f", "return cell;"), "fallback() external {}"]):
            with self.subTest(functions=functions), self.assertRaises(ValueError):
                checker.model(request(["cell"], functions))

    def test_boolean_storage_and_receive_admission(self):
        def parse(body):
            req = request([], [])
            req["sources"]["Function.sol"]["content"] = "pragma solidity *; contract C { " + body + " }"
            return checker.model(req)

        declarations = "bool private first; bool private second; uint256 private word; bool private last; "
        methods = "function set(bool value) public { second = value; } receive() external payable { if (!first) { revert(); } }"
        parsed = parse(declarations + methods)
        self.assertEqual(checker.layout_hints(parsed['fields']), [(0, 0), (0, 1), (1, 0), (2, 0)])
        self.assertEqual(parsed['functions'][0]['signature'], 'set(bool)')
        self.assertEqual(parsed['functions'][0]['returnType'], 'none')
        self.assertEqual(parsed['receive']['body'][0]['if']['yes'], [{'revert': True}])
        self.assertEqual(parse('bool private flag; receive() external payable {}')['functions'], [])
        for before, after in (
                ('second = value;', 'word = value;'), ('second = value;', 'second = word;'),
                ('second = value;', 'second = value + value;'),
                ('if (!first)', 'if (word)'), ('if (!first)', 'if (first == second)'),
                ('bool private first;', 'bool private first = true;'),
                ('receive() external payable', 'receive() external'),
                ('receive() external payable', 'receive(bool value) external payable'),
                ('receive() external payable', 'receive() public payable'),
                ('receive() external payable', 'fallback() external payable')):
            with self.subTest(after=after), self.assertRaises(ValueError):
                parse((declarations + methods).replace(before, after))
        with self.assertRaisesRegex(ValueError, 'duplicate receive'):
            parse(declarations + 'receive() external payable {} receive() external payable {}')
        with self.assertRaises(ValueError):
            parse('uint256 private x = uint256(1) garbage; function get() external view returns(uint256) { return x; }')

    def test_complete_receiver_corpus_identity(self):
        corpus = checker.corpus
        req = dict(cases())[corpus.RECEIVER_CASE]
        content = req['sources']['Function.sol']['content']
        self.assertEqual(hashlib.sha256(content.encode()).hexdigest(), corpus.RECEIVER_SHA256)
        parsed = checker.model(req)
        self.assertEqual(parsed['contract'], corpus.RECEIVER_TARGET)
        self.assertEqual([f['signature'] for f in parsed['functions']], ['setAcceptEther(bool)'])
        self.assertIsNotNone(parsed['receive'])
        metadata = checker.case_metadata(req, fake_response(req))
        self.assertEqual(metadata['corpusSource'], corpus.matching_origin(content, parsed['contract']))
        self.assertIsNone(corpus.matching_origin(content + '\n', parsed['contract']))
        proof, _ = checker.proof_source([(req, fake_response(req))], 8)
        self.assertIn(b'Stateful.step_jump', proof)
        self.assertIn(b'receive := some Receiver.receiver', proof)

    def test_native_rejection_is_separate_from_accepted_corpus(self):
        rejected = checker.rejection_cases()
        self.assertEqual([name for name, _ in rejected], ['static_store_before_revert'])
        self.assertNotIn(rejected[0][1], [req for _, req in cases()])
        parsed = checker.model(rejected[0][1])
        self.assertIn('writeBool', parsed['functions'][0]['body'][0])
        self.assertEqual(parsed['functions'][0]['body'][1], {'revert': True})

    def test_resource_boundaries(self):
        self.assertEqual(len(checker.model(dict(cases())["boundaries"])["storage"]), 8)
        good = function("f", "return cell;", tuple("p" + str(i) for i in range(8)))
        checker.model(request(["cell"], [good]))
        for storage, functions in (
                ([], [function("f", "return uint256(0);")]),
                ([f"slot{i}" for i in range(9)], [function("f", "return slot0;")]),
                (["cell"], [function("f", "cell = uint256(0); " * 9 + "return cell;")]),
                (["cell"], [function("f", "return cell;", tuple("p" + str(i) for i in range(9)))]),
                (["cell"], [function("f" + str(i), "return cell;") for i in range(9)]),
                (["cell"], [function("f", "return " + " + ".join(["cell"] * 65) + ";")])):
            with self.subTest(storage=storage), self.assertRaises(ValueError):
                checker.model(request(storage, functions))

    def test_initializers_bind_complete_names_order_and_checked_expressions(self):
        parsed = checker.model(dict(cases())["init_forward"])
        init = parsed["initialization"]
        self.assertEqual([i["slot"] for i in init["initializers"]], [0, 1])
        self.assertEqual(init["nodes"][0], {"input": "second"})
        self.assertEqual(parsed["functions"][0]["nodes"], [{"input": "first"}])
        proof, _ = checker.proof_source([(dict(cases())["init_forward"], fake_response(dict(cases())["init_forward"]))], 8)
        self.assertIn(b"Constructor.certify contractSource initializers constructor creation code", proof)
        self.assertIn(b'(.input "second")', proof)
        for declaration in ("cell = unknown", "cell = f()", "cell = msg.value", "cell = 7",
                "cell = unchecked { uint256(7) }", "cell = uint256(1) / uint256(0)",
                "cell = " + " + ".join(["uint256(1)"] * 65)):
            with self.subTest(declaration=declaration), self.assertRaises(ValueError):
                checker.model(request([declaration], [function("get", "return cell;", mutability="view")]))
        for name in ("init_self", "init_panic", "init_bound"):
            self.assertTrue(checker.model(dict(cases())[name])["initialization"]["initializers"])

    def test_constructor_binds_complete_body_order_and_modes(self):
        fixtures = dict(cases())
        parsed = checker.model(fixtures["constructor_dependency"])
        body = parsed["constructor"]
        self.assertEqual([s["write"]["slot"] for s in body["body"]], [1, 0])
        self.assertEqual(body["nodes"][0], {"input": "first"})
        self.assertEqual(parsed["initialization"]["nodes"], [{"literal": "7"}])
        self.assertEqual(parsed["functions"][0]["nodes"], [{"input": "second"}])
        self.assertTrue(checker.model(fixtures["constructor_payable"])["constructor"]["payable"])
        self.assertFalse(checker.model(fixtures["constructor_unchecked"])["constructor"]["checked"])
        self.assertFalse(checker.model(fixtures["cell"])["constructor"]["explicit"])
        early = checker.model(fixtures["constructor_return"])["constructor"]
        self.assertEqual(early["body"][0]["if"]["yes"], [{"stop": True}])
        req = fixtures["constructor_return"]
        proof, _ = checker.proof_source([(req, fake_response(req))], 8)
        self.assertIn(b"Constructor.certify contractSource initializers constructor creation code", proof)
        self.assertIn(b".stop", proof)
        self.assertIn(b"Constructor.result", proof)

    def test_constructor_rejects_unmodeled_or_ambiguous_semantics(self):
        get = function("get", "return cell;", mutability="view")
        for constructor in ("constructor(uint256 x) { cell = x; }", "constructor() external {}",
                "constructor() returns(uint256) { return uint256(7); }", "constructor() { return uint256(7); }",
                "constructor() { return; cell = uint256(7); }", "constructor() { cell = unknown; }",
                "constructor() { cell = msg.value; }", "constructor() { cell = get(); }",
                "constructor() { while (cell < uint256(7)) { cell = cell + uint256(1); } }",
                "constructor() { uint256 local = uint256(7); cell = local; }",
                "constructor() {} constructor() {}",
                "constructor() { " + "cell = uint256(7); " * 9 + "}",
                "constructor() { " + "if (cell == uint256(0)) { cell = uint256(1); } " * 5 + "}"):
            with self.subTest(constructor=constructor), self.assertRaises(ValueError):
                checker.model(request(["cell"], [get, constructor]))
        # The optional constructor is not a ninth external function.
        admitted = request(["cell"], [function("f" + str(i), "return cell;") for i in range(8)] +
            ["constructor() { cell = uint256(7); }"])
        self.assertEqual(len(checker.model(admitted)["functions"]), 8)
        self.assertTrue(checker.model(admitted)["constructor"]["explicit"])

    def test_exact_artifact_inventory(self):
        req = dict(cases())["cell"]
        res = fake_response(req)
        self.assertEqual(checker.response(json.dumps(res).encode(), json.dumps(req).encode()), res)
        methods = res["contracts"]["Function.sol"]["C"]["evm"]["methodIdentifiers"]
        for changed in ({}, {**methods, "unmodeled()": "12345678"},
                {name: "00000000" for name in methods}, {**methods, "get()": "not-a-selector"}):
            mutant = copy.deepcopy(res)
            mutant["contracts"]["Function.sol"]["C"]["evm"]["methodIdentifiers"] = changed
            with self.subTest(methods=changed), self.assertRaises(ValueError):
                checker.artifact(req, mutant)
        for path in ("bytecode", "deployedBytecode"):
            mutant = copy.deepcopy(res)
            mutant["contracts"]["Function.sol"]["C"]["evm"][path]["object"] = "00" * 2049
            with self.assertRaises(ValueError):
                checker.proof_source([(req, mutant)], 8)

    def test_symbolic_resource_rejection(self):
        def conditions(body, checked=True):
            req = request(["cell"], [function("f", body, ("x",), checked=checked)])
            parsed = checker.model(req)["functions"][0]
            return checker.source_conditions(parsed, [{"name": "cell", "type": "uint256"}])

        # Five independent arithmetic conditions plus static mode admit 64
        # partitions. A sixth is an explicit rejection, never a dropped path.
        guards, _ = conditions("cell = cell + x; " * 5 + "return cell;")
        self.assertEqual(len(guards), 5)
        with self.assertRaisesRegex(ValueError, "64 proof paths"):
            conditions("cell = cell + x; " * 6 + "return cell;")
        # Substituting sequential assignments can grow hints exponentially
        # even though the source itself stays inside all admission bounds.
        self.assertEqual(conditions("cell = cell + cell; " * 8 + "return cell;", False), ([], []))
        with self.assertRaisesRegex(ValueError, "8192 characters"):
            conditions("cell = cell + cell + cell; " * 8 + "return cell;", False)

    def test_complete_certificate_roots_and_source_storage(self):
        pairs = [(req, fake_response(req)) for _, req in cases()]
        batches, claims = checker.artifacts.proof_batches(checker, pairs, 8)
        self.assertEqual([len(roots) for _, roots in batches], [4] * 12 + [1])
        self.assertEqual(claims, [checker.MODULE + f".Case{i}.checked" for i in range(49)])
        boundary = pairs[8]
        proof, _ = checker.proof_source([boundary], 8)
        text = proof.decode()
        self.assertIn("SolidityStorage.Constructor.Preserves contractSource initializers constructor creation code", text)
        self.assertIn('def variables : SolidityStorage.Layout := [{ name := "slot0", type := .word }', text)
        for slot in range(8):
            self.assertIn("(.assign " + str(slot) + " ", text)
        for index in range(2):
            self.assertIn(f"Function{index}.trace input sized header chosen state env", text)
            self.assertIn(f"Function{index}.inhabited", text)
        self.assertEqual(text.count("theorem trace_short"), 1)
        self.assertEqual(text.count("theorem trace_unknown"), 1)
        self.assertTrue(checker.case_metadata(*boundary)["functions"][0]["writes"] == 8)
        for offset in (-1, True, 128):
            with self.assertRaises(ValueError):
                checker.proof_source(pairs[:1], 8, case_offset=offset)

    def test_branch_admission_and_path_bindings(self):
        for name in ('branch_join', 'early_return', 'nested_branch', 'condition_panic', 'sequential_branch', 'branch_bound'):
            req = dict(cases())[name]
            parsed = checker.model(req)['functions'][0]
            self.assertGreater(parsed['branches'], 0)
            code, _ = checker.proof_source([(req, fake_response(req))], 8)
            self.assertIn(b'(.branch (.compare .', code)
            self.assertIn(b'by_cases _branch_0', code)
        parsed = checker.model(dict(cases())['sequential_branch'])['functions'][0]
        _, conditions = checker.source_conditions(parsed, [{"name": "cell", "type": "uint256"}])
        self.assertEqual(len(conditions), 3)  # Joined slot contains x or y, never its old value.
        self.assertTrue(all('state.storage' not in c for c, _ in conditions))
        self.assertEqual(checker.model(dict(cases())['branch_bound'])['functions'][0]['branches'], 4)
        for body in (
                'if (x) { return x; } else { return y; }',
                'if (x < y) return x; else return y;',
                'if (x < y) { return x; }',
                'if (x < y) { return x; cell = y; } return y;',
                'if (x < y) { return x; } else { return y; } return x;',
                'if (x < y) { unchecked { cell = x; } } return y;',
                'while (x < y) { cell = x; } return y;',
                'if (x < y) { return uint256(0); } ' * 5 + 'return y;',
                'if (x < y) { ' + 'cell = x; ' * 5 + '} else { ' + 'cell = y; ' * 4 + '} return cell;'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                checker.model(request(['cell'], [function('f', body, ('x', 'y'))]))

    def test_boolean_types_precedence_and_bounds(self):
        def parsed(condition):
            return checker.model(request(['cell'], [function('f',
                'if (' + condition + ') { return x; } else { return y; }', ('x', 'y', 'z'))]))['functions'][0]

        tree = parsed('!(x < y) || y < z && x == uint256(0)')['body'][0]['if']['condition']
        self.assertIn('not', tree['or'][0])
        self.assertIn('and', tree['or'][1])
        grouped = parsed('(x < y || y < z) && x == uint256(0)')['body'][0]['if']['condition']
        self.assertIn('or', grouped['and'][0])
        word = parsed('(x + y) * z < ~x | y')['body'][0]['if']['condition']['compare']
        self.assertEqual(word['op'], '<')
        self.assertEqual(parsed('true || false && !false')['body'][0]['if']['condition'],
            {'or': [{'literal': True}, {'and': [{'literal': False}, {'not': {'literal': False}}]}]})
        self.assertEqual(len(checker.source_conditions(parsed('x < y || y < z && x != z'), [{"name": "cell", "type": "uint256"}])[1]), 3)
        for condition in ('x', '!x < y', 'x < y < z', 'true == false', 'x && y',
                '(x < y) | (y < z)', '(x < y) + z', 'x < true', 'true & false',
                '!' * 34 + 'true', ' || '.join(['true'] * 65)):
            with self.subTest(condition=condition), self.assertRaises(ValueError):
                parsed(condition)
        with self.assertRaisesRegex(ValueError, '64 proof paths'):
            checker.source_conditions(parsed(' || '.join('x == uint256(' + str(i) + ')' for i in range(6))), [{"name": "cell", "type": "uint256"}])


if __name__ == "__main__":
    unittest.main()
