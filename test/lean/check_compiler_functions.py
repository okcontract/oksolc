#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Certify ordinary Solidity Standard JSON creation/runtime pairs for a closed pure
uint256 fragment, by kernel-checked symbolic execution of the exact EVM bytes.
"""
import copy
import json
import re
import sys

import compiler_artifacts as artifacts
import check_compiler_graphs as graphs
import check_compiler_words as words
import solidity_function_source as source
from common import decode_json

MODULE = "Compiler.Validation.FunctionArtifact"
BINARY_NAME = "oksolc"
NATIVE_ARGS = ("--standard-json",)
NEGATIVE_DIAGNOSTICS = ("unsolved goals", "is false")
NEGATIVE_FORBIDDEN_DIAGNOSTICS = ("maximum", "deep recursion", "timed out", "timeout",
    "unknown identifier", "unknown constant", "unexpected token")
EXTRA_INPUTS = ("docs/compiler-verification-map.json", "docs/compiler-verification-boundary.md")
REPORT_SCHEMA = "oksolc.compiler-function-verification.v4"
AUDIT_SCHEMA = "oksolc.compiler-function-audit.v4"
PROOF_SCOPE = "emittedEvm"
EMITTED_EVM = True
DEPLOYMENT_PROOF = True
REPORT_METADATA = {"sourceScope": "singlePureUint256Function", "fork": "cancun",
    "functionVisibilities": ["external", "public"], "versionPragmas": ["^0.8.0", "*"],
    "typeConstants": ["type(uint256).max"],
    "arithmeticModes": ["checked", "unchecked"],
    "gasModel": "exactExecutionGasAllBudgets", "wholeEvmRefinement": False,
    "sourceParserVerified": False, "ordinarySolidityPipeline": True,
    "observation": "deploymentAndCallBytesAndPersistentWorldAllGasBudgets",
    "callScope": "allValuesAndCalldataBelow2To64Bytes",
    "deploymentVerified": False, "deploymentScope": "exactInitcodeFreshTargetFrameAllValuesAndGasBudgets",
    "creationGasModel": "executionAndCodeDepositAfterAdmissionCharges",
    "constructorScope": "implicitNonpayableWithoutEffects",
    "transactionAdmissionVerified": False}
SETTINGS = {"viaIR": True, "optimizer": {"enabled": True, "runs": 200}, "evmVersion": "cancun",
    "metadata": {"appendCBOR": False, "bytecodeHash": "none"},
    "outputSelection": {"*": {"*": ["evm.bytecode.object", "evm.deployedBytecode.object", "evm.methodIdentifiers"]}}}


def admitted_source(value, expected_settings=SETTINGS):
    graphs.fields(value, ("language", "sources", "settings"))
    if value["language"] != "Solidity" or value["settings"] != expected_settings:
        raise ValueError("unsupported language or compiler settings")
    graphs.fields(value["sources"], ("Function.sol",))
    graphs.fields(value["sources"]["Function.sol"], ("content",))
    return value["sources"]["Function.sol"]["content"]


def admit_request(value, *, parser=source.parse):
    parser(admitted_source(value))
    return value


def model(req):
    return source.parse(admitted_source(req))


def request(data):
    return admit_request(decode_json(data.decode("utf-8")))


def artifact(req, res):
    parsed = model(req)
    code, selectors = admit_response(res, parsed["contract"], [parsed["signature"]])
    return parsed, code, selectors[0]


def admit_response(res, contract_name, signatures):
    if not isinstance(res, dict) or set(res) - {"contracts", "sources", "errors"}:
        raise ValueError("unsupported Standard JSON response")
    errors = res.get("errors", [])
    if not isinstance(errors, list) or any(not isinstance(e, dict) or e.get("severity") != "warning" for e in errors):
        raise ValueError("compiler error or malformed diagnostics")
    contracts = res.get("contracts")
    graphs.fields(contracts, ("Function.sol",))
    graphs.fields(contracts["Function.sol"], (contract_name,))
    contract = contracts["Function.sol"][contract_name]
    graphs.fields(contract, ("evm",))
    evm = contract["evm"]
    graphs.fields(evm, ("bytecode", "deployedBytecode", "methodIdentifiers"))
    graphs.fields(evm["bytecode"], ("object",))
    graphs.fields(evm["deployedBytecode"], ("object",))
    methods = evm["methodIdentifiers"]
    graphs.fields(methods, signatures)
    selectors = [methods[signature] for signature in signatures]
    if any(not isinstance(selector, str) or not re.fullmatch(r"[0-9a-f]{8}", selector) for selector in selectors):
        raise ValueError("invalid method selector")
    if len(set(selectors)) != len(selectors):
        raise ValueError("duplicate method selector")
    code = words.bytecode(evm["deployedBytecode"]["object"])
    creation = words.bytecode(evm["bytecode"]["object"])
    if len(code) > 1024:
        raise ValueError("runtime exceeds symbolic proof limit")
    if len(creation) > 2048:
        raise ValueError("creation exceeds symbolic proof limit")
    return code, [int(selector, 16) for selector in selectors]


def creation_code(parsed, res):
    return words.bytecode(res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["bytecode"]["object"])


def replace_runtime(pair, contract_name, changed):
    """Keep a semantic corruption's installed image bound to its runtime."""
    req, res = copy.deepcopy(pair)
    evm = res["contracts"]["Function.sol"][contract_name]["evm"]
    code = words.bytecode(evm["deployedBytecode"]["object"])
    creation = words.bytecode(evm["bytecode"]["object"])
    if not code or len(changed) != len(code) or not creation.endswith(code):
        raise ValueError("corruption requires an equal-size runtime at the creation tail")
    evm["deployedBytecode"]["object"] = changed.hex()
    evm["bytecode"]["object"] = (creation[:-len(code)] + changed).hex()
    return req, res


def response(data, request_bytes):
    req = request(request_bytes)
    res = decode_json(data.decode("utf-8"))
    artifact(req, res)
    return res


def instructions(code):
    pc = 0
    while pc < len(code):
        op = code[pc]
        width = op - 0x5f if 0x60 <= op <= 0x7f else 0
        yield pc, op, width
        pc += 1 + width


def byte_facts(name, code):
    lines = [f"def {name} : List UInt8 := " + str(list(code)),
        f"@[simp] theorem {name}_length : {name}.length = {len(code)} := rfl"]
    jumps = []
    for pc, op, width in instructions(code):
        lines.append(f"@[simp] theorem {name}_byte_{pc} : {name}[{pc}]'(by decide) = ({op} : UInt8) := rfl")
        if width:
            immediate = int.from_bytes(code[pc+1:pc+1+width].ljust(width, b'\0'), 'big')
            lines.append(f"@[simp] theorem {name}_push_{pc} : bytesWord (padded {name} {pc+1} {width}) = {immediate}#256 := by decide")
        if op == 0x5b:
            jumps.append(pc)
    lines.append(f"@[simp] theorem {name}_jumps : jumpDestinations {name} = " + str(jumps) + " := by decide")
    return lines


def arithmetic_guard(operation, left, right):
    if operation == "sub":
        return f"{right} ≤ {left}", [f"Contract.WordProofs.subtraction_guard_exact {left} {right}"]
    op = "+" if operation == "add" else "*"
    guards = [f"SolidityWord.add_guard_le {left} {right}"] if op == "+" else [
        f"SolidityWord.mul_guard {left} {right}", f"SolidityWord.mul_guard {right} {left}",
        f"SolidityWord.mul_guard_reverse {left} {right}", f"SolidityWord.mul_guard_reverse {right} {left}"]
    return f"{left}.toNat {op} {right}.toNat < 2^256", guards


def arithmetic_conditions(parsed):
    conditions = []
    for node in parsed["nodes"]:
        binary = node.get("binary", {})
        if binary.get("op") not in ("add", "sub", "mul"):
            continue
        def value(index):
            expression = words.source_expression(parsed["nodes"], index)
            return f"(({expression} : SolidityWord.Expr).eval (source.locals input))"
        conditions.append(arithmetic_guard(binary["op"], value(binary["left"]), value(binary["right"])))
    return conditions


def proof_batches(pairs, fuel):
    return [proof_source(pairs[start:start + 16], fuel, case_offset=start)
            for start in range(0, len(pairs), 16)]


def proof_header(module, *, contract=False):
    lines = ["/-", "// SPDX-License-Identifier: GPL-3.0", "// Copyright (C) 2026 OKcontract Pte. Ltd.", "-/",
        "import Compiler.Validation.SolidityDeployment", "import Contract.Check.Declarations", "import Lean.Elab.Command",
        "open Contract.Evm Contract.Interaction Compiler.Validation",
        "open Compiler.Validation.SolidityFunction Compiler.Validation.SolidityCall", "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 2000000", "set_option linter.unusedSimpArgs false", "namespace " + module]
    if contract:
        lines[4] = "import Compiler.Validation.SolidityContract"
        lines.insert(5, "import Compiler.Validation.SolidityAddressLiteral")
        lines.insert(6, "import Compiler.Validation.SolidityBoolLiteral")
        lines.insert(7, "import Compiler.Validation.SolidityBytes32Literal")
    return lines


def typed_body(parsed):
    return parsed.get("returnType") == "none" or parsed.get("bodyScope") == "rawWordReturn"


def function_facts(parsed, selector, *, body=None):
    size = 4 + 32 * len(parsed["parameters"])
    typed = typed_body(parsed)
    raw = parsed.get("bodyScope") == "rawWordReturn"
    encoding = []
    if not raw and parsed.get("returnType") in ("address", "bool", "bytes32"):
        if body is not None or parsed["root"] != 0 or len(parsed["nodes"]) != 1 or set(parsed["nodes"][0]) != {"literal"}:
            raise ValueError("typed result must be one admitted literal")
        value = parsed["nodes"][0]["literal"]
        if parsed["returnType"] == "address":
            body = "SolidityAddressLiteral.literal " + value + " (by decide)"
        elif parsed["returnType"] == "bool":
            if value not in ("0", "1"):
                raise ValueError("boolean literal must be zero or one")
            body = "SolidityBoolLiteral.literal " + ("true" if value == "1" else "false")
        else:
            data = parsed["literalBytes"]
            if (not isinstance(data, list) or len(data) > 32 or
                    any(type(b) is not int or not 32 <= b <= 126 or b in (34, 92) for b in data) or
                    not value.isdecimal() or not 0 <= int(value) < 2**256):
                raise ValueError("invalid bytes32 literal descriptor")
            encoding = ["def literalBytes : List UInt8 := " + json.dumps(data),
                "def literalWord : BitVec 256 := " + value,
                "theorem literal_encoding : wordBytes literalWord = literalBytes ++",
                "    List.replicate (32 - literalBytes.length) 0 := by decide +kernel"]
            body = "SolidityBytes32Literal.literal literalBytes (by decide) literalWord literal_encoding"
    if typed:
        parameters = [".bytes4" if kind == "bytes4" else ".word" for kind in parsed["parameterTypes"]]
        lines = ["def source : SolidityNoReturn.Source := { name := " + json.dumps(parsed["name"]) +
            ", parameters := [" + ", ".join(parameters) + "]" +
            (", payable := true" if parsed.get("payable", False) else "") + " }"]
    else:
        lines = ["def source : Source := { name := " + json.dumps(parsed["name"]) +
            ", parameters := " + json.dumps(parsed["parameters"]) + ", body := " +
            (words.source_expression(parsed["nodes"], parsed["root"]) if body is None else body) +
            ", checked := " + str(parsed["checked"]).lower() +
            (", payable := true" if parsed.get("payable", False) else "") + " }"]
    if raw:
        lines += ["def returnedWord : BitVec 256 := " + parsed["rawReturnWord"]]
    local_facts = []
    for parameter, name in enumerate([] if typed else parsed["parameters"]):
        local_facts.append(f"local_{parameter}")
        lines += [f"@[simp] theorem local_{parameter} (input : Input) : source.locals input {json.dumps(name)} = loadWord input.calldata {4 + 32 * parameter} := rfl"]
    lines += call_facts(selector, size, valid_call="SolidityNoReturn.Source.ValidCall" if typed else "Source.ValidCall")
    return encoding + lines, local_facts


def call_facts(selector, size, *, source_name="source", valid_call="Source.ValidCall"):
    """Selector, canonical-call witness and ABI-length laws shared by bodies."""
    witness = list(selector.to_bytes(4, 'big')) + [0] * (size - 4)
    return [f"theorem selector : {source_name}.selector = {selector} := by decide +kernel",
        f"theorem inhabited : ∃ input, Sized input ∧ {source_name}.ValidCall input := by",
        "  refine ⟨⟨" + str(witness) + ", 0⟩, ?_⟩",
        "  unfold Sized " + valid_call,
        "  rw [selector]", "  decide",
        "theorem signed_length (input : Input) (sized : Sized input) (header : 4 ≤ input.calldata.length) :",
        f"    ((BitVec.ofNat 256 input.calldata.length).toInt + -4).bmod {2**256} = (input.calldata.length - 4 : Nat) := by",
        "  simpa only [BitVec.toInt_add, BitVec.reduceNot, BitVec.reduceToInt, Int.add_comm] using length_sub_four input.calldata.length sized header",
        "theorem length_test (input : Input) (header : 4 ≤ input.calldata.length) :",
        f"    (↑(input.calldata.length - 4) : Int) < {size-4} ↔ input.calldata.length < {size} := by omega"]


def function_proof(parsed, code, selector, *, other_selectors=(), common=True):
    steps = len(code) * 4 + 1
    size = 4 + 32 * len(parsed["parameters"])
    typed = typed_body(parsed)
    raw = parsed.get("bodyScope") == "rawWordReturn"
    lines, local_facts = function_facts(parsed, selector)
    simplify = ["  repeat", "    rw [Contract.Evm.run]",
        "    simp +decide +contextual -implicitDefEqProofs (maxSteps := 30000) [Contract.Evm.step, Contract.Evm.push,",
        "    Contract.Evm.binary, Contract.Evm.unary, pushWidth, expansionCost, expandedWords, memoryCost, charge_add, charge_finished,",
        "    Source.returnBytes, source, SolidityWord.Expr.eval, shl_word, shr_word, SolidityWord.Binary.eval,",
        "    Source.locals, List.idxOf?, List.findIdx?_cons, return_word,",
        "    SolidityWord.panic_overflow_memory, SolidityWord.shift_one, SolidityWord.division,",
        "    BitVec.le_def,",
        "    BitVec.shiftLeft_eq_zero, BitVec.ushiftRight_eq_zero,",
        "    BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm,"]
    conditions = {
        "short": ["(short : input.calldata.length < 4)"],
        "unknown": ["(header : 4 ≤ input.calldata.length)", f"(selected : loadWord input.calldata 0 >>> 224 ≠ {selector}#256)"],
        "paid": ["(header : 4 ≤ input.calldata.length)", f"(selected : loadWord input.calldata 0 >>> 224 = {selector}#256)", "(value : input.value ≠ 0#256)"],
        "truncated": ["(header : 4 ≤ input.calldata.length)", f"(selected : loadWord input.calldata 0 >>> 224 = {selector}#256)", "(value : input.value = 0#256)", f"(shortArguments : input.calldata.length < {size})"],
        "returned": [f"(selected : loadWord input.calldata 0 >>> 224 = {selector}#256)", "(value : input.value = 0#256)", f"(full : {size} ≤ input.calldata.length)"],
    }
    if typed:
        conditions["malformed"] = [*conditions["returned"], "(arguments : ¬source.Arguments input)"]
        conditions["returned"] += ["(arguments : source.Arguments input)"]
    if parsed.get("payable", False):
        del conditions["paid"]
        for branch in ("truncated", "returned", *(["malformed"] if typed else [])):
            conditions[branch] = [p for p in conditions[branch] if not p.startswith("(value :")]
    conditions["unknown"] += [f"(other_{i} : loadWord input.calldata 0 >>> 224 ≠ {other}#256)"
                              for i, other in enumerate(other_selectors)]
    for branch, premises in conditions.items():
        if not common and branch in ("short", "unknown"):
            continue
        result = (".returned (SolidityRawReturn.bytes returnedWord (fun _ => 0))" if raw else
                  ".returned []" if typed else "source.result input") if branch == "returned" else ".reverted []"
        impossible = typed and branch == "malformed" and "bytes4" not in parsed["parameterTypes"]
        unused = (branch == "truncated" and size == 4) or impossible
        sized_name = "_sized" if unused else "sized"
        if unused:
            premises = [p.replace("(selected :", "(_selected :").replace("(value :", "(_value :").replace("(full :", "(_full :") for p in premises]
        if typed and branch == "returned" and "bytes4" not in parsed["parameterTypes"]:
            premises = [p.replace("(arguments :", "(_arguments :") for p in premises]
        lines += [f"theorem trace_{branch} (input : Input) ({sized_name} : Sized input)",
            "    " + " ".join(premises) + " :",
            f"    ∃ cost, Contract.Evm.run code input {steps} {{}} = .finished cost ({result}) := by"]
        if impossible:
            lines += ["  simp [SolidityNoReturn.Source.Arguments, source, SolidityNoReturn.Parameter.Accepts, List.zipIdx] at arguments"]
            continue
        if branch == "truncated" and size == 4:
            lines += ["  omega"]
            continue
        if branch == "returned" and not typed:
            if parsed.get("returnType") == "address":
                literal = parsed["nodes"][0]["literal"]
                lines += [f"  rw [SolidityAddressLiteral.result source {literal} (by decide) rfl input]",
                    "  rw [BitVec.setWidth_ofNat_of_le_of_lt (by decide : 160 ≤ 256) (by decide)]"]
            elif parsed.get("returnType") == "bool":
                value = "true" if parsed["nodes"][0]["literal"] == "1" else "false"
                lines += [f"  rw [SolidityBoolLiteral.result source {value} rfl input]"]
            elif parsed.get("returnType") == "bytes32":
                lines += ["  rw [SolidityBytes32Literal.result source literalBytes (by decide) literalWord literal_encoding rfl input]",
                    "  rw [← literal_encoding]", "  unfold literalWord"]
            lines += ["  have header : 4 ≤ input.calldata.length := by omega",
                "  try simp -implicitDefEqProofs only [Source.result, source]",
                "  try simp -implicitDefEqProofs only [Source.returnBytes, source, SolidityWord.Expr.eval, shl_word, shr_word,",
                "    SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked, Bind.bind, Except.bind, Pure.pure, Except.pure]",
                "  try simp -implicitDefEqProofs only [Source.locals, List.idxOf?, List.findIdx?_cons]",
                "  try simp -implicitDefEqProofs only [Contract.CheckedOp.eval]"]
        if raw and branch == "returned":
            lines += ["  rw [SolidityRawReturn.bytes_eq]", "  unfold returnedWord"]
        if typed and branch in ("returned", "malformed"):
            lines += ["  have header : 4 ≤ input.calldata.length := by omega"]
            if "bytes4" in parsed["parameterTypes"]:
                lines += ["  simp [SolidityNoReturn.Source.Arguments, source, SolidityNoReturn.Parameter.Accepts, List.zipIdx] at arguments"]
        if branch != "short":
            lines += ["  have short : ¬input.calldata.length < 4 := by omega"]
        extras = ["length_word input.calldata.length sized", "short"]
        if branch == "unknown":
            extras += ["selected", "Ne.symm selected"]
            extras += [fact for i in range(len(other_selectors)) for fact in (f"other_{i}", f"Ne.symm other_{i}")]
        if branch in ("paid", "truncated", "returned", "malformed"):
            extras += ["selected"]
            if not parsed.get("payable", False):
                extras += ["value"]
        if branch in ("truncated", "returned", "malformed"):
            extras += ["signed_length input sized header", "length_test input header",
                       "shortArguments" if branch == "truncated" else "Nat.not_lt.mpr full"]
        if typed and branch in ("returned", "malformed"):
            for index, kind in enumerate(parsed["parameterTypes"]):
                if kind == "bytes4":
                    word = f"loadWord input.calldata {4 + 32 * index}"
                    lines += [f"  all_goals by_cases padding_{index} : {2**256 - 2**224}#256 &&& {word} = {word}",
                              "  all_goals try simp_all only [BitVec.and_comm, not_true_eq_false, not_false_eq_true, true_and, and_true, false_and, and_false, true_implies, false_implies, implies_true]"]
            lines += ["  all_goals try clear arguments", "  all_goals"] + ["  " + line for line in simplify] + [
                "      " + ", ".join(extras) + ", SolidityNoReturn.sub_mask_zero, SolidityNoReturn.zero_sub_mask, SolidityNoReturn.mask_sub_zero, SolidityNoReturn.zero_mask_sub, *]"]
        elif branch == "returned" and parsed["checked"]:
            for index in range(len(parsed["parameters"])):
                word = f"loadWord input.calldata {4 + 32 * index}"
                lines += [f"  have word_bound_{index} := ({word}).isLt",
                    f"  simp only [Nat.reducePow] at word_bound_{index}",
                    f"  have word_zero_{index} : ({word}).toNat = 0 ↔ {word} = 0#256 :=",
                    f"    BitVec.toNat_inj (x := {word}) (y := 0#256)"]
            expression_facts = ["SolidityWord.Expr.eval", "shl_word", "shr_word", *local_facts]
            facts = ["SolidityWord.Binary.eval", "BitVec.le_def", "BitVec.mul_comm", "Nat.mul_comm", "Nat.add_comm",
                     *(f"word_zero_{index}" for index in range(len(parsed["parameters"]))),
                     "-Nat.not_lt", "-Nat.not_le"]
            for index, (_, guards) in enumerate(arithmetic_conditions(parsed)):
                for number, guard in enumerate(guards):
                    lines += [f"  have guard_{index}_{number} := {guard}",
                        "  try simp -implicitDefEqProofs only [" + ", ".join(expression_facts) + f"] at guard_{index}_{number}",
                        "  try simp +decide +contextual -implicitDefEqProofs [" + ", ".join(facts) + f"] at guard_{index}_{number}"]
            for index, (condition, _) in enumerate(arithmetic_conditions(parsed)):
                lines += [f"  all_goals by_cases arithmetic_{index} : {condition}"]
                lines += [f"  all_goals try simp -implicitDefEqProofs only [" + ", ".join(expression_facts) + f"] at arithmetic_{index}",
                          "  all_goals try simp +decide +contextual -implicitDefEqProofs [" + ", ".join(facts) + f"] at arithmetic_{index}"]
            lines += ["  all_goals",
                "    try simp only [Source.locals, source, SolidityWord.Expr.eval, SolidityWord.Binary.eval,",
                "      List.idxOf?, List.findIdx?_cons] at *",
                "    try simp only [Except.bind, *]",
                "    try omega"]
            lines += ["  " + line for line in simplify] + ["      " + ", ".join(extras) + ", Nat.add_comm, Nat.mul_comm, *]"]
        else:
            lines += simplify + ["    " + ", ".join(extras) + "]"]
    return lines


def creation_image(creation, code):
    # The tail identity is checked by Lean; it is not trusted from layout or
    # from a substring match. A mismatched returned image rejects the pair.
    offset = max(0, len(creation) - len(code))
    return [f"theorem runtime_image : padded creation {offset} {len(code)} = code := by decide",
        f"theorem copy_return (memory : Memory) (dest : Nat) :",
        f"    (memory.write dest (padded creation {offset} {len(code)})).read dest {len(code)} = code := by",
        "  rw [runtime_image]",
        "  simpa only [code_length] using Memory.read_write memory dest code"]


def creation_proof(creation, code):
    creation_steps = len(creation) * 4 + 1
    lines = creation_image(creation, code) + ["theorem creation_trace (input : Input) :",
        f"    ∃ cost, Contract.Evm.run creation input {creation_steps} {{}} =",
        "      .finished cost (SolidityDeployment.outcome code input) := by",
        "  by_cases value : input.value = 0#256 <;>",
        "    simp only [SolidityDeployment.outcome, value, if_true, if_false]",
        "  all_goals",
        "    repeat",
        "      rw [Contract.Evm.run]",
        "      simp +decide -implicitDefEqProofs (maxSteps := 30000) [Contract.Evm.step, Contract.Evm.push,",
        "        Contract.Evm.binary, Contract.Evm.unary, pushWidth, expansionCost, expandedWords, memoryCost,",
        "        charge_add, charge_finished, copy_return, value]"]
    return lines


def proof_source(pairs, fuel, *, case_offset=0):
    if not 1 <= len(pairs) <= 128 or type(fuel) is not int or not 0 <= fuel <= 16:
        raise ValueError("unsupported proof batch or normalization fuel")
    if type(case_offset) is not int or not 0 <= case_offset <= 128 - len(pairs):
        raise ValueError("unsupported artifact case offset")
    lines = proof_header(MODULE)
    claims = []
    for i, (req, res) in enumerate(pairs, case_offset):
        parsed, code, selector = artifact(req, res)
        creation = creation_code(parsed, res)
        creation_steps, steps = len(creation) * 4 + 1, len(code) * 4 + 1
        size = 4 + 32 * len(parsed["parameters"])
        lines += [f"namespace Case{i}"] + byte_facts("code", code) + byte_facts("creation", creation)
        lines += function_proof(parsed, code, selector)
        lines += ["theorem trace (input : Input) (sized : Sized input) :",
            f"    ∃ cost, Contract.Evm.run code input {steps} {{}} = .finished cost (outcome source input) := by",
            f"  apply dispatch source code {steps} trace_short ?_ ?_ ?_ ?_ input sized",
            "  · intro input sized header selected; rw [selector] at selected; exact trace_unknown input sized header selected",
            "  · intro input sized header selected value; rw [selector] at selected; exact trace_paid input sized header selected value",
            "  · intro input sized header selected value shortArguments; rw [selector] at selected",
            f"    change input.calldata.length < {size} at shortArguments",
            "    exact trace_truncated input sized header selected value shortArguments",
            "  · intro input sized accepted; rcases accepted with ⟨value, full, selected⟩; rw [selector] at selected",
            f"    change {size} ≤ input.calldata.length at full",
            "    exact trace_returned input sized selected value full",
            f"theorem calls : SolidityCall.Preserves source code {steps} := SolidityCall.certify source code {steps} inhabited trace"]
        if not parsed["checked"]:
            lines += [f"theorem canonical : SolidityFunction.Preserves source code {steps} := SolidityCall.canonical source code {steps} (by decide) (by decide) calls"]
        lines += creation_proof(creation, code)
        lines += [f"theorem checked : SolidityDeployment.Preserves source creation code {creation_steps} {steps} :=",
            f"  SolidityDeployment.certify source creation code {creation_steps} {steps} calls",
            "    (by decide) (by decide) (by decide) creation_trace",
            f"end Case{i}"]
        claims.append(MODULE + f".Case{i}.checked")
    lines += artifacts.audit_source(MODULE, claims, AUDIT_SCHEMA)
    return "\n".join(lines).encode(), claims


def case_metadata(req, res):
    parsed, code, selector = artifact(req, res)
    creation = creation_code(parsed, res)
    return {"sourceNodes": len(parsed["nodes"]), "parameters": parsed["parameters"],
        "visibility": parsed["visibility"],
        "arithmeticMode": "checked" if parsed["checked"] else "unchecked",
        "signature": parsed["signature"], "selector": f"{selector:08x}", "bytecodeBytes": len(code),
        "bytecodeSha256": artifacts.gate.digest(code), "provedStepBound": len(code) * 4 + 1,
        "creationBytecodeBytes": len(creation), "creationBytecodeSha256": artifacts.gate.digest(creation),
        "creationProvedStepBound": len(creation) * 4 + 1}


def write_cases(output):
    from compiler_function_cases import write_cases as write
    return write(output)


def negative_pairs(pairs):
    pair = next(p for p in pairs if not model(p[0])["checked"] and
                "return x + y;" in p[0]["sources"]["Function.sol"]["content"])
    parsed, code, _ = artifact(*pair)
    decoded = list(instructions(code))
    arithmetic = max(pc for pc, op, _ in decoded if op == 0x01)
    returned = next(pc for pc, op, _ in decoded if op == 0xf3)
    selector = next(pc for pc, op, _ in decoded if op == 0x63)
    value_check = next(pc for pc, op, _ in decoded if op == 0x34)
    guard_index = next(i for i, (_, op, _) in enumerate(decoded) if op == 0x12)
    guard_start, guard_push, guard_width = decoded[guard_index - 5]
    guard_end = decoded[guard_index][0] + 1
    if ([op for _, op, _ in decoded[guard_index - 5:guard_index + 1]] != [0x60, 0x36, 0x60, 0x19, 0x01, 0x12]
            or guard_push != 0x60 or guard_width != 1 or code[guard_start+1] != 64 or guard_end - guard_start != 8):
        raise ValueError("native ABI length guard changed; review corruption controls")
    reverts = {pc for pc, op, _ in decoded if op == 0xfd}
    result = []
    for name, changed in (("wrong_arithmetic", code[:arithmetic] + b'\x03' + code[arithmetic+1:]),
                          ("revert_instead_of_return", code[:returned] + b'\xfd' + code[returned+1:]),
                          ("truncated_runtime", code[:returned]),
                          ("unsupported_opcode", b'\x55' + code[1:]),
                          ("wrong_dispatch_selector", code[:selector+1] + bytes([code[selector+1] ^ 1]) + code[selector+2:]),
                          ("accept_nonzero_value", code[:value_check] + b'\x5f' + code[value_check+1:]),
                          ("accept_truncated_arguments", code[:guard_start+1] + b'\x00' + code[guard_start+2:]),
                          ("reject_trailing_calldata", code[:guard_start] + bytes([0x60, 68, 0x36, 0x14, 0x15, 0x5b, 0x5b, 0x5b]) + code[guard_end:]),
                          ("return_on_invalid_call", bytes(0xf3 if pc in reverts else byte for pc, byte in enumerate(code)))):
        req, res = copy.deepcopy(pair)
        res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["deployedBytecode"]["object"] = changed.hex()
        # Keep the installed image paired for equal-size runtime mutations, so
        # these controls still exercise runtime semantics rather than only the
        # creation/runtime identity check.
        if len(changed) == len(code):
            creation = creation_code(parsed, res)
            res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["bytecode"]["object"] = (
                creation[:-len(code)] + changed).hex()
        result.append((name, [(req, res)]))
    req, res = copy.deepcopy(pair)
    req["sources"]["Function.sol"]["content"] = req["sources"]["Function.sol"]["content"].replace("return x + y;", "return x - y;")
    result.append(("wrong_source_expression", [(req, res)]))
    creation = creation_code(parsed, pair[1])
    header = list(instructions(creation[:len(creation) - len(code)]))
    value_check = next(pc for pc, op, _ in header if op == 0x34)
    returned = next(pc for pc, op, _ in header if op == 0xf3)
    copy_index = next(i for i, (_, op, _) in enumerate(header) if op == 0x39)
    copy_offset, _, _ = header[copy_index - 2]
    if ([op for _, op, _ in header[copy_index - 2:copy_index + 1]] != [0x60, 0x82, 0x39]
            or creation[copy_offset + 1] != len(creation) - len(code)):
        raise ValueError("native creation copy changed; review corruption controls")
    for name, changed in (
            ("creation_wrong_image", creation[:-1] + bytes([creation[-1] ^ 1])),
            ("creation_accept_value", creation[:value_check] + b'\x5f' + creation[value_check+1:]),
            ("creation_reverts", creation[:returned] + b'\xfd' + creation[returned+1:]),
            ("creation_wrong_copy_offset", creation[:copy_offset+1] +
                bytes([creation[copy_offset+1] ^ 1]) + creation[copy_offset+2:])):
        req, res = copy.deepcopy(pair)
        res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["bytecode"]["object"] = changed.hex()
        result.append((name, [(req, res)]))
    return result + checked_negative_pairs(pairs)


def checked_negative_pairs(pairs):
    """Wrong arithmetic mode and panic payloads must fail semantic checking.

    Reuse complete native unchecked pairs so creation/runtime identity remains
    valid; a rejected layout cannot mask erased overflow checks.
    """
    result = []
    for name, expression in (("add", "x + y"), ("sub", "x - y"), ("mul", "x * y"),
                             ("nested", "(x + y) - y")):
        candidates = [pair for pair in pairs if "return " + expression + ";" in
                      pair[0]["sources"]["Function.sol"]["content"]]
        checked = next((p for p in candidates if model(p[0])["checked"]), None)
        if checked is None:
            continue
        unchecked = next((p for p in candidates if not model(p[0])["checked"]), None)
        if unchecked is None or {**model(checked[0]), "checked": False} != model(unchecked[0]):
            raise ValueError("missing matching unchecked artifact for corruption control")
        result.append(("erase_overflow_checks_" + name, [(copy.deepcopy(checked[0]), copy.deepcopy(unchecked[1]))]))
        if name != "add":
            continue
        parsed, code, _ = artifact(*checked)
        decoded = list(instructions(code))
        panic = bytes.fromhex("601160045260245ffd")
        offsets = [pc for pc, _, _ in decoded if code[pc:pc + len(panic)] == panic]
        creation = creation_code(parsed, checked[1])
        if len(offsets) != 1 or not creation.endswith(code):
            raise ValueError("native arithmetic panic changed; review corruption controls")
        for label, offset, value in (("wrong_panic_code", 1, 0x12), ("wrong_panic_length", 6, 0x20)):
            position = offsets[0] + offset
            changed = code[:position] + bytes([value]) + code[position+1:]
            req, res = copy.deepcopy(checked)
            evm = res["contracts"]["Function.sol"][parsed["contract"]]["evm"]
            evm["deployedBytecode"]["object"] = changed.hex()
            evm["bytecode"]["object"] = (creation[:-len(code)] + changed).hex()
            result.append((label, [(req, res)]))
    return result


if __name__ == "__main__":
    sys.exit(artifacts.main(sys.modules[__name__]))
