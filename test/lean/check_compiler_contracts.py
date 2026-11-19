#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Certify selected expression contracts with per-function payability against ordinary artifacts.
The independent source parser is trusted; selectors, dispatch, all function
bodies and deployment are checked by Lean against the exact emitted bytes.
"""
import copy
import sys

import check_compiler_functions as functions
import compiler_contract_corpus as corpus
import compiler_contract_address_controls as address_controls
import compiler_contract_literal_controls as literal_controls
import compiler_contract_payable_controls as payable_controls
import compiler_contract_empty_controls as empty_controls
import compiler_contract_no_return_controls as no_return_controls
import compiler_contract_raw_return_controls as raw_return_controls
import compiler_contract_bytes32_controls as bytes32_controls
import compiler_contract_integer_controls as integer_controls
import solidity_contract_source as source
from check_compiler_functions import (artifacts, decode_json, BINARY_NAME,
    NATIVE_ARGS, NEGATIVE_DIAGNOSTICS, NEGATIVE_FORBIDDEN_DIAGNOSTICS, EXTRA_INPUTS,
    PROOF_SCOPE, EMITTED_EVM, DEPLOYMENT_PROOF, SETTINGS)

MODULE = "Compiler.Validation.ContractArtifact"
REPORT_SCHEMA = "oksolc.compiler-contract-verification.v1"
AUDIT_SCHEMA = "oksolc.compiler-contract-audit.v1"
REPORT_METADATA = {**functions.REPORT_METADATA, "sourceScope": "expressionEmptyAndRawWordReturnContract",
    "functionLimit": 8, "emptyContractScope": "noHandlersOrStateAllInputsRevert", "sourceUnitContractLimit": 8, "selectorUniquenessChecked": True,
    "explicitTargetSelection": True, "addressReturnScope": "boundedLiteralConversionOr40NumericHexDigits",
    "booleanReturnScope": "trueFalseLiteralsOnly",
    "bytes32ReturnScope": "explicitConversionOfPrintableAsciiLiteralWithoutEscapesAtMost32BytesKernelCheckedRightPadding",
    "noReturnScope": "emptyPureViewPayableBodiesWithUnusedUint256OrBytes4Parameters",
    "rawReturnScope": "literalMstoreZeroThenReturnZero32WithUnusedUint256OrBytes4Parameters",
    "valueScope": "perFunctionPayabilityWithSuccessTransferAndFailureRollback",
    "metadataScope": "noneOrLiteralContentIpfsCbor"}
EXTRA_INPUTS = (*EXTRA_INPUTS, corpus.ARCHIVE, corpus.PROVENANCE, corpus.CLASHING_ARCHIVE, corpus.PAYABLE_ARCHIVE, corpus.NO_RETURN_ARCHIVE, corpus.BYTES32_ARCHIVE, corpus.INTEGER_ARCHIVE)
IPFS_METADATA = {"useLiteralContent": True, "bytecodeHash": "ipfs", "appendCBOR": True}


def request(data):
    req = decode_json(data.decode("utf-8"))
    model(req)
    return req


def model(req):
    functions.graphs.fields(req, ("language", "sources", "settings"))
    settings = req["settings"]
    if not isinstance(settings, dict):
        raise ValueError("unsupported compiler settings")
    selection = settings.get("outputSelection")
    target, expected = None, SETTINGS
    metadata = settings.get("metadata")
    if (metadata == IPFS_METADATA and type(metadata.get("useLiteralContent")) is bool and
            type(metadata.get("appendCBOR")) is bool):
        expected = {**SETTINGS, "metadata": IPFS_METADATA}
    if selection != SETTINGS["outputSelection"]:
        functions.graphs.fields(selection, ("Function.sol",))
        contracts = selection["Function.sol"]
        if not isinstance(contracts, dict) or len(contracts) != 1:
            raise ValueError("select exactly one contract")
        target = next(iter(contracts))
        expected = {**expected, "outputSelection": {
            "Function.sol": {target: SETTINGS["outputSelection"]["*"]["*"]}}}
    return source.parse(functions.admitted_source(req, expected), target)


def artifact(req, res):
    parsed = model(req)
    code, selectors = functions.admit_response(res, parsed["contract"],
        [function["signature"] for function in parsed["functions"]])
    return parsed, code, selectors


def response(data, request_bytes):
    res = decode_json(data.decode("utf-8"))
    artifact(request(request_bytes), res)
    return res


def proof_batches(pairs, fuel):
    return [proof_source(pairs[start:start + 4], fuel, case_offset=start)
            for start in range(0, len(pairs), 4)]


def proof_source(pairs, fuel, *, case_offset=0):
    if not 1 <= len(pairs) <= 128 or type(fuel) is not int or not 0 <= fuel <= 16:
        raise ValueError("unsupported proof batch or normalization fuel")
    if type(case_offset) is not int or not 0 <= case_offset <= 128 - len(pairs):
        raise ValueError("unsupported artifact case offset")
    lines, claims = functions.proof_header(MODULE, contract=True), []
    lines.insert(4, "import Compiler.Validation.SolidityEmptyContract")
    if any(functions.typed_body(f) for req, _ in pairs for f in model(req)["functions"]):
        lines.insert(4, "import Compiler.Validation.SolidityMethodContract")
    for i, (req, res) in enumerate(pairs, case_offset):
        parsed, code, selectors = artifact(req, res)
        creation = functions.creation_code(parsed, res)
        steps, creation_steps = len(code) * 4 + 1, len(creation) * 4 + 1
        lines += [f"namespace Case{i}"] + functions.byte_facts("code", code) + functions.byte_facts("creation", creation)
        for j, (function, selector) in enumerate(zip(parsed["functions"], selectors)):
            size = 4 + 32 * len(function["parameters"])
            lines += [f"namespace Function{j}"]
            lines += functions.function_proof(function, code, selector, common=j == 0,
                other_selectors=selectors[1:] if j == 0 else ())
            lines += selected_trace(function, steps, size) + [f"end Function{j}"]
        names = [f"Function{j}" for j in range(len(selectors))]
        mixed = any(functions.typed_body(f) for f in parsed["functions"])
        certificate = "SolidityMethodContract" if mixed else "SolidityContract" if names else "SolidityEmptyContract"
        dispatch = ("SolidityDispatch.dispatch SolidityMethodContract.Method.selector SolidityMethodContract.Method.outcome"
                    if mixed else "SolidityContract.dispatch")
        outcome = ("SolidityDispatch.outcome SolidityMethodContract.Method.selector SolidityMethodContract.Method.outcome"
                   if mixed else "SolidityContract.outcome")
        entries = []
        for n, f in zip(names, parsed["functions"]):
            if not mixed:
                entries.append(n + ".source")
            else:
                kind = "rawWord" if f.get("bodyScope") == "rawWordReturn" else "empty" if f["returnType"] == "none" else "expression"
                value = " " + n + ".returnedWord" if kind == "rawWord" else ""
                entries.append("(SolidityMethodContract.Method." + kind + " " + n + ".source" + value + ")")
        if names:
            lines += ["def sources : List " + ("SolidityMethodContract.Method" if mixed else "Source") + " := [" + ", ".join(entries) + "]",
                "theorem trace (input : Input) (sized : Sized input) :",
                f"    ∃ cost, Contract.Evm.run code input {steps} {{}} = .finished cost ({outcome} sources input) := by",
                f"  apply {dispatch} sources code {steps} Function0.trace_short ?_ ?_ input sized",
                "  · intro input sized header unknown",
                "    apply Function0.trace_unknown input sized header"]
            for n, entry in zip(names, entries):
                reduction = "SolidityMethodContract.Method.selector, " if mixed else ""
                lines += [f"    · simpa only [{reduction}{n}.selector] using unknown {entry} (by simp [sources])"]
            lines += ["  · intro source member input sized header chosen",
                "    simp only [sources, List.mem_cons, List.not_mem_nil, or_false] at member",
                "    rcases member with " + " | ".join("rfl" for _ in names)]
            lines += [f"    · exact {n}.trace input sized header chosen" for n in names]
            lines += [f"theorem calls : {certificate}.CallsPreserves sources code {steps} := by",
                f"  apply {certificate}.certifyCalls sources code {steps} (by simp [sources]) ?_ ?_ trace",
                "  · simp only [sources, List.map_cons, List.map_nil, " + ("SolidityMethodContract.Method.selector, " if mixed else "") + ", ".join(n + ".selector" for n in names) + "]",
                "    decide",
                "  · intro source member",
                "    simp only [sources, List.mem_cons, List.not_mem_nil, or_false] at member",
                "    rcases member with " + " | ".join("rfl" for _ in names)]
            lines += [f"    · exact {n}.inhabited" for n in names]
        else:
            lines += empty_calls_proof(code)
        lines += functions.creation_proof(creation, code)
        inventory = "sources " if names else ""
        lines += [f"theorem checked : {certificate}.Preserves {inventory}creation code {creation_steps} {steps} :=",
            f"  {certificate}.certify {inventory}creation code {creation_steps} {steps} calls",
            "    (by decide) (by decide) (by decide) creation_trace", f"end Case{i}"]
        claims.append(MODULE + f".Case{i}.checked")
    lines += artifacts.audit_source(MODULE, claims, AUDIT_SCHEMA)
    return "\n".join(lines).encode(), claims


def selected_trace(function, steps, size):
    """Compose the same dispatch branches; typed terminal bodies add padding rejection."""
    typed, payable = functions.typed_body(function), function["payable"]
    raw = function.get("bodyScope") == "rawWordReturn"
    scope = "SolidityNoReturn" if typed else "SolidityContract"
    outcome = "SolidityNoReturn.outcome" if typed else "outcome"
    accepts_value = "SolidityNoReturn.Source.AcceptsValue" if typed else "AcceptsValue"
    selected = f"{scope}.selected source"
    result = f"{outcome} source input"
    if raw:
        selected = "SolidityNoReturn.selected_returning source (SolidityRawReturn.bytes returnedWord (fun _ => 0))"
        result = "SolidityRawReturn.outcome source returnedWord input"
    value = "" if payable else "value "
    lines = ["theorem trace (input : Input) (sized : Sized input) (header : 4 ≤ input.calldata.length)",
        "    (chosen : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector) :",
        f"    ∃ cost, Contract.Evm.run code input {steps} {{}} = .finished cost ({result}) := by",
        f"  apply {selected} code {steps} ?_ ?_ ?_" + (" ?_" if typed else "") + " input sized header chosen",
        (f"  · intro input sized header selected value; simp [{accepts_value}, source] at value" if payable else
         "  · intro input sized header selected value; rw [selector] at selected; exact trace_paid input sized header selected value"),
        "  · intro input sized header selected value shortArguments; rw [selector] at selected",
        f"    change input.calldata.length < {size} at shortArguments",
        "    exact trace_truncated input sized header selected " + value + "shortArguments"]
    if typed:
        lines += ["  · intro input sized value full selected arguments; rw [selector] at selected",
            f"    change {size} ≤ input.calldata.length at full",
            "    exact trace_malformed input sized selected " + value + "full arguments"]
    lines += ["  · intro input sized accepted; rcases accepted with ⟨value, full, selected" +
              (", arguments" if typed else "") + "⟩; rw [selector] at selected",
        f"    change {size} ≤ input.calldata.length at full",
        "    exact trace_returned input sized selected " + value + "full" + (" arguments" if typed else "")]
    return lines


def empty_calls_proof(code):
    """A universal runtime obligation; no selector/member premise can make it vacuous."""
    steps = len(code) * 4 + 1
    return ["theorem trace (input : Input) :",
        f"    ∃ cost, Contract.Evm.run code input {steps} {{}} = .finished cost (.reverted []) := by",
        "  repeat",
        "    rw [Contract.Evm.run]",
        "    simp +decide -implicitDefEqProofs (maxSteps := 30000) [Contract.Evm.step, Contract.Evm.push,",
        "      Contract.Evm.binary, Contract.Evm.unary, pushWidth, expansionCost, expandedWords, memoryCost,",
        "      charge_add, charge_finished]",
        f"theorem calls : SolidityEmptyContract.CallsPreserves code {steps} :=",
        f"  SolidityEmptyContract.certifyCalls code {steps} trace"]


def case_metadata(req, res):
    parsed, code, selectors = artifact(req, res)
    creation = functions.creation_code(parsed, res)
    record = {"contract": parsed["contract"],
        "certificateKind": ("mixedMethodContract" if any(functions.typed_body(f) for f in parsed["functions"])
                            else "expressionContract" if parsed["functions"] else "emptyContract"),
        "callInputScope": "calldataBelow2To64Bytes" if parsed["functions"] else "allFiniteCalldata", "sourceUnitContracts": parsed["sourceUnitContracts"],
        "uncertifiedSiblingContracts": [name for name in parsed["sourceUnitContracts"] if name != parsed["contract"]],
        "functions": [{"signature": f["signature"], "selector": f"{s:08x}",
            "visibility": f["visibility"], "returnType": f["returnType"], "payable": f["payable"],
            "parameters": f["parameters"], "sourceNodes": len(f["nodes"]),
            "arithmeticMode": "checked" if f["checked"] else "unchecked",
            **({"literalBytes": f["literalBytes"]} if f["returnType"] == "bytes32" else {}),
            **({"parameterTypes": f["parameterTypes"], "bodyScope": f.get("bodyScope", "empty"), "sourceMutability": f["mutability"],
                **({"rawReturnWord": f["rawReturnWord"]} if f.get("bodyScope") == "rawWordReturn" else {})}
               if functions.typed_body(f) else {})}
            for f, s in zip(parsed["functions"], selectors)],
        "bytecodeBytes": len(code), "bytecodeSha256": artifacts.gate.digest(code),
        "provedStepBound": len(code) * 4 + 1, "creationBytecodeBytes": len(creation),
        "creationBytecodeSha256": artifacts.gate.digest(creation),
        "creationProvedStepBound": len(creation) * 4 + 1,
        "metadataSettings": copy.deepcopy(req["settings"]["metadata"])}
    origin = corpus.matching_origin(req["sources"]["Function.sol"]["content"], parsed["contract"])
    if origin is not None:
        record["corpusSource"] = origin
    return record


def write_cases(output):
    from compiler_contract_cases import write_cases as write
    return write(output)


def negative_pairs(pairs):
    # Source mutations preserve complete native creation/runtime images. They
    # test the second function and arithmetic mode without an image mismatch
    # hiding a bad dispatch or result. Byte mutations are installed together.
    pair = next(pair for pair in pairs if len(model(pair[0])["functions"]) == 2 and
        "return x + y;" in pair[0]["sources"]["Function.sol"]["content"])
    parsed, code, selectors = artifact(*pair)
    creation = functions.creation_code(parsed, pair[1])
    result = []
    for label, before, after in (
            ("second_body", "return x + y;", "return x - y;"),
            ("second_arity", "uint256 x,uint256 y", "uint256 x,uint256 y,uint256 z"),
            ("erase_overflow_check", "unchecked { return x + y; }", "return x + y;")):
        req, res = copy.deepcopy(pair)
        content = req["sources"]["Function.sol"]["content"]
        if before not in content:
            raise ValueError("missing native source corruption anchor")
        req["sources"]["Function.sol"]["content"] = content.replace(before, after)
        if label == "second_arity":
            # Keep the old selector as untrusted output: the kernel must reject
            # its disagreement with the newly admitted source signature.
            methods = res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["methodIdentifiers"]
            signature = parsed["functions"][1]["signature"]
            methods[model(req)["functions"][1]["signature"]] = methods.pop(signature)
        result.append((label, [(req, res)]))
    positions = []
    for selector in selectors:
        positions.append(next(pc for pc, op, width in functions.instructions(code)
            if op == 0x63 and code[pc + 1:pc + 1 + width] == selector.to_bytes(4, "big")))
    swapped = bytearray(code)
    for pc, selector in zip(positions, reversed(selectors)):
        swapped[pc + 1:pc + 5] = selector.to_bytes(4, "big")
    reverts = {pc for pc, op, _ in functions.instructions(code) if op == 0xfd}
    value = next(pc for pc, op, _ in functions.instructions(code) if op == 0x34)
    argument_guards = [pc for pc, op, _ in functions.instructions(code)
        if op == 0x60 and code[pc:pc + 8] == bytes.fromhex("6040366003190112")]
    if len(argument_guards) != 1 or not creation.endswith(code):
        raise ValueError("native second-function ABI guard or creation image changed; review corruption controls")
    guard = argument_guards[0]
    for label, changed in (
            ("swapped_dispatch", bytes(swapped)),
            ("missing_second_selector", code[:positions[1]+1] + bytes([code[positions[1]+1] ^ 1]) + code[positions[1]+2:]),
            ("accept_value", code[:value] + b'\x5f' + code[value+1:]),
            ("second_short_arguments", code[:guard+1] + b'\x00' + code[guard+2:]),
            ("return_on_rejection", bytes(0xf3 if pc in reverts else byte for pc, byte in enumerate(code)))):
        result.append((label, [functions.replace_runtime(pair, parsed["contract"], changed)]))
    req, res = copy.deepcopy(pair)
    res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["bytecode"]["object"] = (
        creation[:-1] + bytes([creation[-1] ^ 1])).hex()
    result.append(("creation_image", [(req, res)]))
    corpus_pair = next(pair for pair in pairs if
        corpus.sha(pair[0]["sources"]["Function.sol"]["content"].encode()) == corpus.SOURCE_SHA256)
    req, res = copy.deepcopy(corpus_pair)
    content = req["sources"]["Function.sol"]["content"]
    anchor = "return type(uint256).max;"
    if content.count(anchor) != 1:
        raise ValueError("retained maximum source control changed")
    req["sources"]["Function.sol"]["content"] = content.replace(anchor,
        "return uint256(" + str(2**256 - 2) + ");")
    result.append(("corpus_wrong_maximum", [(req, res)]))
    parsed, code, selectors = artifact(*corpus_pair)
    creation = functions.creation_code(parsed, corpus_pair[1])
    instructions = list(functions.instructions(code))
    maximum = [pc for index, (pc, op, _) in enumerate(instructions)
        if op == 0x19 and index > 0 and instructions[index - 1][1] == 0x5f]
    if len(maximum) != 1 or not creation.endswith(code):
        raise ValueError("native corpus maximum or creation image changed; review corruption controls")
    # NOT(0) -> ISZERO(0) changes the returned word while keeping a valid,
    # equally sized instruction and a matching installed runtime image.
    changed = code[:maximum[0]] + b'\x15' + code[maximum[0] + 1:]
    result.append(("corpus_wrong_runtime_word", [functions.replace_runtime(corpus_pair, parsed["contract"], changed)]))
    dispatch = [pc for pc, op, width in instructions if op == 0x63 and
        code[pc + 1:pc + 1 + width] == selectors[0].to_bytes(4, "big")]
    if len(selectors) != 1 or len(dispatch) != 1:
        raise ValueError("native corpus selector changed; review corruption controls")
    pc = dispatch[0]
    changed = code[:pc + 1] + bytes([code[pc + 1] ^ 1]) + code[pc + 2:]
    result.append(("corpus_wrong_public_selector", [functions.replace_runtime(corpus_pair, parsed["contract"], changed)]))
    req, res = copy.deepcopy(corpus_pair)
    res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["bytecode"]["object"] = (
        creation[:-1] + bytes([creation[-1] ^ 1])).hex()
    result.append(("corpus_wrong_creation_image", [(req, res)]))
    return (result + address_controls.negative_pairs(sys.modules[__name__], pairs) +
            literal_controls.negative_pairs(sys.modules[__name__], pairs) + metadata_controls(pairs) +
            payable_controls.negative_pairs(sys.modules[__name__], pairs) +
            empty_controls.negative_pairs(sys.modules[__name__], pairs) +
            no_return_controls.negative_pairs(sys.modules[__name__], pairs) +
            raw_return_controls.negative_pairs(sys.modules[__name__], pairs) +
            bytes32_controls.negative_pairs(sys.modules[__name__], pairs) +
            integer_controls.negative_pairs(sys.modules[__name__], pairs))


def metadata_controls(pairs):
    pair = next(pair for pair in pairs if pair[0]["settings"]["metadata"] == IPFS_METADATA and
        corpus.sha(pair[0]["sources"]["Function.sol"]["content"].encode()) == corpus.CLASHING_SHA256)
    req, res = copy.deepcopy(pair)
    parsed, code, _ = artifact(req, res)
    creation = functions.creation_code(parsed, res)
    if not creation.endswith(code) or len(code) < 2 or int.from_bytes(code[-2:], "big") + 2 >= len(code):
        raise ValueError("metadata-bearing runtime tail changed; review native artifact")
    result = []
    # These controls are not a CBOR parser or an IPFS-content authenticity claim.
    # They check that the complete advertised runtime is installed, including
    # data bytes which ordinary calls never execute.
    for name, suffix in (("metadata_runtime_truncated", code[:-1]),
                         ("metadata_runtime_changed", code[:-1] + bytes([code[-1] ^ 1]))):
        changed = copy.deepcopy(res)
        changed["contracts"]["Function.sol"][parsed["contract"]]["evm"]["deployedBytecode"]["object"] = suffix.hex()
        result.append((name, [(copy.deepcopy(req), changed)]))
    changed = copy.deepcopy(req)
    content = changed["sources"]["Function.sol"]["content"]
    if content.count("return true;") != 1:
        raise ValueError("metadata corpus literal anchor changed")
    changed["sources"]["Function.sol"]["content"] = content.replace("return true;", "return false;")
    result.append(("metadata_wrong_boolean_source", [(changed, copy.deepcopy(res))]))
    return result


if __name__ == "__main__":
    sys.exit(artifacts.main(sys.modules[__name__]))
