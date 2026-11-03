#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Exact-byte validation for closed Solidity word/Boolean-storage contracts.
"""
import copy
import json
import itertools
import sys

import check_compiler_functions as functions
import solidity_storage_source as source
import compiler_contract_corpus as corpus
from check_compiler_functions import (artifacts, decode_json, BINARY_NAME,
    NATIVE_ARGS, NEGATIVE_DIAGNOSTICS, NEGATIVE_FORBIDDEN_DIAGNOSTICS, EXTRA_INPUTS,
    PROOF_SCOPE, EMITTED_EVM, DEPLOYMENT_PROOF)

MODULE = "Compiler.Validation.StorageArtifact"
REPORT_SCHEMA = "oksolc.compiler-storage-verification.v5"
AUDIT_SCHEMA = "oksolc.compiler-storage-audit.v5"
REPORT_METADATA = {**functions.REPORT_METADATA, "sourceScope": "wordBooleanStorageContract",
    "functionLimit": 8, "storageFieldLimit": 8, "writesPerFunctionLimit": 8,
    "branchesPerFunctionLimit": 4, "statementsPerFunctionLimit": 32,
    "proofPathsPerFunctionLimit": 64, "symbolicExpressionCharactersLimit": 8192,
    "selectorUniquenessChecked": True, "storageLayout": "sourceDeclarationOrderPackedBooleansAndFullWords",
    "initialization": "checkedDeclarationOrderFromZeroStorage",
    "booleanDeclarationInitializersSupported": False,
    "constructor": "parameterlessSequentialBodyAfterInitializers",
    "constructorPayabilityVerified": True,
    "conditions": "shortCircuitTypedBooleanAndWordComparisons",
    "receive": "exactEmptyCalldataPayableCompleteBody",
    "arguments": "canonicalBooleanAndWordStaticABI",
    "returns": "wordOrEmptyBytes",
    "booleanReturnsSupported": False,
    "gasModel": "exactTargetGasSentryWarmthAndSignedRefundAllBudgets",
    "sourceGasObservation": "opaque", "staticCallsVerified": True,
    "observation": "deploymentAndCallBytesWholeStorageAndTransactionRollbackAllGasBudgets"}


def request(data):
    return functions.admit_request(decode_json(data.decode("utf-8")), parser=source.parse)


def response(data, request_bytes):
    res = decode_json(data.decode("utf-8"))
    artifact(request(request_bytes), res)
    return res


def proof_batches(pairs, fuel):
    return [proof_source(pairs[start:start + 4], fuel, case_offset=start)
            for start in range(0, len(pairs), 4)]


def model(req):
    functions.admit_request(req, parser=source.parse)
    return source.parse(req["sources"]["Function.sol"]["content"])


def artifact(req, res):
    parsed = model(req)
    code, selectors = functions.admit_response(res, parsed["contract"],
        [function["signature"] for function in parsed["functions"]])
    return parsed, code, selectors


def layout_hints(fields):
    """Only symbolic-execution hints. Lean independently derives every location
    from the complete typed declaration list in the certificate's source model.
    """
    slot, byte, result = 0, 0, []
    for field in fields:
        if field["type"] == "uint256":
            slot += bool(byte)
            byte = 0
            result.append((slot, byte))
            slot += 1
        elif field["type"] == "bool":
            result.append((slot, byte))
            byte += 1
            if byte == 32:
                slot, byte = slot + 1, 0
        else:
            raise ValueError("unsupported storage type")
    return result


def source_conditions(parsed, fields):
    """Proof hints follow each branch's sequential environment. The complete
    source AST and target execution, never these hints, determine acceptance.
    """
    variables = [field["name"] for field in fields]
    initial = {}
    for field, (slot, byte) in zip(fields, layout_hints(fields)):
        word = f"(state.storage {slot}#256)"
        if field["type"] == "bool":
            word = f"(if ({word} &&& {255 << (8 * byte)}#256) = 0#256 then 0#256 else 1#256)"
        initial[field["name"]] = word
    initial.update({name: f"(loadWord input.calldata {4 + 32 * index})"
                    for index, name in enumerate(parsed["parameters"])})
    arithmetic, branches = {}, {}

    def bounded(text):
        if len(text) > 8192:
            raise ValueError("symbolic expression exceeds 8192 characters")
        return text

    def partition_bound():
        if len(branches) + (len(arithmetic) if parsed['checked'] else 0) + 2 * parsed.get('parameterTypes', []).count('bool') > 5:
            raise ValueError("symbolic source partition exceeds 64 proof paths")

    def expression(index, values):
        node = parsed["nodes"][index]
        if "input" in node:
            return values[node["input"]]
        if "literal" in node:
            return f"({node['literal']}#256)"
        if "unary" in node:
            return bounded(f"(~~~{expression(node['unary']['arg'], values)})")
        binary = node["binary"]
        left, right = expression(binary["left"], values), expression(binary["right"], values)
        operation = binary["op"]
        if parsed['checked'] and operation in ("add", "sub", "mul"):
            condition, guards = functions.arithmetic_guard(operation, left, right)
            arithmetic[condition] = guards
            partition_bound()
        operator = {"add": "+", "sub": "-", "mul": "*", "and": "&&&", "or": "|||",
                    "xor": "^^^", "shl": "<<<", "shr": ">>>"}[operation]
        return bounded(f"({left} {operator} {right}{'.toNat' if operation in ('shl', 'shr') else ''})")

    def condition(node, values):
        if "literal" in node:
            return
        if "boolean" in node:
            value = expression(node["boolean"], values)
            branches[f"{value} ≠ 0#256"] = (value, "0#256")
            partition_bound()
        elif "not" in node:
            condition(node["not"], values)
        elif "compare" in node:
            comparison = node["compare"]
            left, right = expression(comparison["left"], values), expression(comparison["right"], values)
            operator = comparison["op"]
            if operator in ("==", "!="):
                guard = f"{left} {'=' if operator == '==' else '≠'} {right}"
            else:
                if operator in (">", ">="):
                    left, right = right, left
                guard = f"{left}.toNat {'≤' if '=' in operator else '<'} {right}.toNat"
            branches[guard] = (left, right) if operator in ("==", "!=") else None
            partition_bound()
        else:
            for child in node["and" if "and" in node else "or"]:
                condition(child, values)

    def boolean_term(node, values):
        if "literal" in node:
            return "True" if node["literal"] else "False"
        if "boolean" in node:
            return f"({expression(node['boolean'], values)} ≠ 0#256)"
        if "not" in node:
            return "¬(" + boolean_term(node["not"], values) + ")"
        if "compare" in node:
            c = node["compare"]
            left, right = expression(c["left"], values), expression(c["right"], values)
            op = {"==": "=", "!=": "≠", "<": "<", "<=": "≤", ">": ">", ">=": "≥"}[c["op"]]
            if c["op"] not in ("==", "!="):
                left, right = left + ".toNat", right + ".toNat"
            return f"({left} {op} {right})"
        op = "and" if "and" in node else "or"
        return "(" + (" ∧ " if op == "and" else " ∨ ").join(boolean_term(child, values) for child in node[op]) + ")"

    def walk(body, values):
        if not body:
            return
        stmt, rest = body[0], body[1:]
        if "stop" in stmt or "revert" in stmt:
            return
        if "return" in stmt:
            expression(stmt["return"], values)
        elif "writeBool" in stmt:
            write = stmt["writeBool"]
            condition(write["condition"], values)
            value = bounded("(if " + boolean_term(write["condition"], values) + " then 1#256 else 0#256)")
            values[variables[write["field"]]] = value
            walk(rest, values)
        elif "write" in stmt:
            write = stmt["write"]
            values[variables[write["slot"]]] = expression(write["root"], values)
            walk(rest, values)
        else:
            branch = stmt["if"]
            condition(branch["condition"], values)
            walk(branch["yes"] + rest, dict(values))
            walk(branch["no"] + rest, dict(values))

    walk(parsed["body"], initial)
    return list(arithmetic.items()), list(branches.items())


def condition_source(parsed, node):
    if "literal" in node:
        return "(.literal " + str(node["literal"]).lower() + ")"
    if "boolean" in node:
        return "(.boolean " + functions.words.source_expression(parsed["nodes"], node["boolean"]) + ")"
    if "not" in node:
        return "(.not " + condition_source(parsed, node["not"]) + ")"
    if "compare" in node:
        comparison = node["compare"]
        op = {"==": "eq", "!=": "ne", "<": "lt", "<=": "le", ">": "gt", ">=": "ge"}[comparison["op"]]
        expr = lambda root: functions.words.source_expression(parsed["nodes"], root)
        return f"(.compare .{op} {expr(comparison['left'])} {expr(comparison['right'])})"
    op = "and" if "and" in node else "or"
    return "(." + op + " " + " ".join(condition_source(parsed, child) for child in node[op]) + ")"


def statements(parsed, body):
    expr = lambda root: functions.words.source_expression(parsed["nodes"], root)
    result = []
    for stmt in body:
        if "stop" in stmt:
            result.append(".stop")
        elif "revert" in stmt:
            result.append(".revert")
        elif "writeBool" in stmt:
            write = stmt["writeBool"]
            result.append(f"(.assignBool {write['field']} {condition_source(parsed, write['condition'])})")
        elif "return" in stmt:
            result.append("(.ret " + expr(stmt["return"]) + ")")
        elif "write" in stmt:
            write = stmt["write"]
            result.append(f"(.assign {write['slot']} {expr(write['root'])})")
        else:
            branch = stmt["if"]
            result.append(f"(.branch {condition_source(parsed, branch['condition'])} " +
                          statements(parsed, branch["yes"]) + " " + statements(parsed, branch["no"]) + ")")
    return "[" + ", ".join(result) + "]"


def execution_proof(extras, *, separate_jumps=False):
    lines = ["  all_goals repeat", "    rw [Stateful.projected_succ]"]
    if separate_jumps:
        # Reduce the checked transition before the decoder under its execution
        # continuation. Combining these simp passes can exceed kernel stack
        # limits on subtraction-based selector dispatch.
        lines += ["    try simp +decide -implicitDefEqProofs [Stateful.step_jump, word_sub_eq_zero, " +
                  ", ".join(extras) + ", *]"]
    return lines + [
            "    simp +decide +contextual -implicitDefEqProofs (maxSteps := 30000) [Stateful.step, Stateful.coreStep,",
            "      Contract.Evm.step, Contract.Evm.push, Contract.Evm.binary, Contract.Evm.unary,",
            "      pushWidth, expansionCost, expandedWords, memoryCost, Stateful.Result.effects,",
            "      SolidityStorage.conforms_charge, SolidityStorage.conforms_finished_returned,",
            "      SolidityStorage.conforms_finished_reverted, SolidityStorage.conforms_fault,",
            "      return_word, SolidityWord.panic_overflow_memory, BitVec.add_comm, BitVec.mul_comm,",
            "      BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm, Nat.add_comm, Nat.mul_comm,",
            "      SolidityStorage.write_overwrite, Stateful.write, word_sub_eq_zero, SolidityABI.boolean_double_iszero, " + ", ".join(extras) + ", *]"]


STORAGE_LAYOUT_SIMPS = ", ".join("SolidityStorage." + name for name in (
    "Layout.read", "Layout.write", "Layout.names", "Layout.words", "Layout.locate", "Layout.locateFrom",
    "Location.allocate", "Variable.read", "PackedBool.read", "PackedBool.encode", "PackedBool.insert", "PackedBool.mask"))


def function_proof(parsed, fields, code, selector=None, *, receive=False):
    size, steps = 4 + 32 * len(parsed["parameters"]), len(code) * 4 + 1
    payable = parsed["mutability"] == "payable"
    variables = [field["name"] for field in fields]
    arithmetic, branches = source_conditions(parsed, fields)
    if receive:
        lines = ["def receiver : SolidityStorage.Receive := { body := " + statements(parsed, parsed["body"]) +
                 ", checked := " + str(parsed["checked"]).lower() + " }"]
        conditions = {"returned": ["(empty : input.calldata.length = 0)"]}
        source_result = "receiver.result variables input state.storage env.isStatic"
    else:
        lines = ["def source : Source := { name := " + json.dumps(parsed["name"]) +
            ", parameters := " + json.dumps(parsed["parameters"]) + ", body := .literal 0, checked := " +
            str(parsed["checked"]).lower() + ", payable := " + str(payable).lower() + " }",
            "def function : SolidityStorage.Function := { abi := source, body := " + statements(parsed, parsed["body"]) +
            ", parameterTypes := [" + ", ".join({"uint256": ".word", "bool": ".boolean"}[kind] for kind in parsed['parameterTypes']) +
            "], returnsWord := " + str(parsed['returnType'] == 'uint256').lower() + " }",
            "theorem abi_eq : function.abi = source := rfl",
            "def call : SolidityABI.Source := function.call",
            "theorem call_eq : function.call = call := rfl"]
        lines += functions.call_facts(selector, size, source_name="call", valid_call="SolidityABI.Source.ValidCall")
        conditions = {
            "paid": ["(header : 4 ≤ input.calldata.length)", f"(selected : loadWord input.calldata 0 >>> 224 = {selector}#256)", "(value : input.value ≠ 0#256)"],
            "truncated": ["(header : 4 ≤ input.calldata.length)", f"(selected : loadWord input.calldata 0 >>> 224 = {selector}#256)", "(value : input.value = 0#256)", f"(shortArguments : input.calldata.length < {size})"],
            "returned": [f"(selected : loadWord input.calldata 0 >>> 224 = {selector}#256)", "(value : input.value = 0#256)", f"(full : {size} ≤ input.calldata.length)"],
        }
        conditions['malformed'] = [*conditions['returned'], '(arguments : ¬call.Arguments input)']
        conditions['returned'] += ['(arguments : call.Arguments input)']
        if payable:
            del conditions['paid']
            for branch in ('truncated', 'returned', 'malformed'):
                conditions[branch] = [premise for premise in conditions[branch] if not premise.startswith('(value :')]
        conditions = {branch: [premise.replace('(value :', '(_value :') for premise in premises]
                      for branch, premises in conditions.items()}
        source_result = "function.result variables input state.storage env.isStatic"
    partitions = [("_static", "env.isStatic = true")]
    if parsed["checked"]:
        partitions += [(f"_arithmetic_{i}", condition) for i, (condition, _) in enumerate(arithmetic)]
    partitions += [(f"_branch_{i}", condition) for i, (condition, _) in enumerate(branches)]
    if 2 ** len(partitions) * 4 ** parsed['parameterTypes'].count('bool') > 64:
        raise ValueError("symbolic source partition exceeds 64 proof paths")
    paths = list(itertools.product((True, False), repeat=len(partitions)))
    traces = [(branch, premises, None) for branch, premises in conditions.items() if branch != "returned"]
    traces += [("returned", conditions["returned"], i) for i in range(len(paths))]
    for branch, premises, path in traces:
        result = source_result if branch == "returned" else ".reverted []"
        premises = [p.replace("(selected :", "(_selected :") for p in premises]
        unused = (branch == "truncated" and size == 4) or (branch == "malformed" and "bool" not in parsed["parameterTypes"])
        if unused:
            premises = [p.replace("(selected :", "(_selected :").replace("(value :", "(_value :").replace("(full :", "(_full :") for p in premises]
        if path is not None:
            premises = [p.replace("(selected :", "(_selected :").replace("(value :", "(_value :").replace("(full :", "(_full :").replace("(arguments :", "(_arguments :") for p in premises]
        sized_name = "_sized"
        lines += [f"theorem trace_{branch}{'' if path is None else '_' + str(path)} (input : Input) ({sized_name} : Sized input)",
            "    " + " ".join(premises),
            "    (state : Stateful.State) (env : Stateful.Environment)" +
                ("" if path is None else " " + " ".join(f"({name} : {condition if yes else '¬(' + condition + ')'})"
                    for (name, condition), yes in zip(partitions, paths[path]))) + " :",
            f"    SolidityStorage.Conforms ({result}) ((Stateful.run code input env {steps}",
            "      { state with machine := {} }).map Stateful.Result.effects) := by"]
        if branch == "truncated" and size == 4:
            lines += ["  omega"]
            continue
        if branch == "malformed" and "bool" not in parsed["parameterTypes"]:
            lines += ["  simp [SolidityABI.Source.Arguments, call, SolidityStorage.Function.call, function, SolidityABI.Parameter.Accepts, List.zipIdx] at arguments"]
            continue
        if not receive and branch in ("returned", "malformed"):
            lines += ["  have header : 4 ≤ input.calldata.length := by omega"]
        if branch == "returned":
            if parsed["checked"]:
                values = [f"loadWord input.calldata {4 + 32 * i}" for i in range(len(parsed["parameters"]))]
                values += [f"state.storage {slot}#256" for slot in dict.fromkeys(slot for slot, _ in layout_hints(fields))]
                for index, word in enumerate(values):
                    lines += [f"  all_goals have word_bound_{index} := ({word}).isLt",
                        f"  all_goals simp only [Nat.reducePow] at word_bound_{index}",
                        f"  all_goals have word_zero_{index} : ({word}).toNat = 0 ↔ {word} = 0#256 :=",
                        f"    BitVec.toNat_inj (x := {word}) (y := 0#256)"]
                facts = ["BitVec.le_def", "BitVec.mul_comm", "Nat.mul_comm", "Nat.add_comm",
                    *(f"word_zero_{i}" for i in range(len(values))), "-Nat.not_lt", "-Nat.not_le"]
                for index, (_, guards) in enumerate(arithmetic):
                    for number, guard in enumerate(guards):
                        lines += [f"  all_goals have guard_{index}_{number} := {guard}",
                            "  all_goals try simp +decide +contextual -implicitDefEqProofs [" + ", ".join(facts) + f"] at guard_{index}_{number}"]
                for index, (condition, _) in enumerate(arithmetic):
                    lines += ["  all_goals try simp +decide +contextual -implicitDefEqProofs [" + ", ".join(facts) + f"] at _arithmetic_{index}"]
            for index, (condition, symmetry) in enumerate(branches):
                lines += ["  all_goals try simp +decide +contextual -implicitDefEqProofs [",
                    "    BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm,",
                    f"    Nat.add_comm, Nat.mul_comm, -Nat.not_lt, -Nat.not_le, *] at _branch_{index}"]
        if not receive:
            lines += ["  all_goals have short : ¬input.calldata.length < 4 := by omega"]
        extras = [f"length_word input.calldata.length {sized_name}", "empty" if receive else "short"]
        if not receive and branch in ("paid", "truncated", "returned", "malformed"):
            extras += ["_selected"]
            if not payable:
                extras += ["_value"]
        if not receive and branch in ("truncated", "returned", "malformed"):
            extras += [f"signed_length input {sized_name} header", "length_test input header",
                "shortArguments" if branch == "truncated" else "Nat.not_lt.mpr " + ("full" if path is None else "_full")]
        if not receive and branch in ("returned", "malformed") and "bool" in parsed["parameterTypes"]:
            argument_name = "_arguments" if path is not None else "arguments"
            # Split the complete Boolean input domain: zero, one, and malformed.
            # The typed ABI hypothesis prunes only semantically impossible arms.
            for index, kind in enumerate(parsed["parameterTypes"]):
                if kind == "bool":
                    word = f"loadWord input.calldata {4 + 32 * index}"
                    lines += [f"  all_goals by_cases boolean_zero_{index} : {word} = 0#256",
                        f"  all_goals by_cases boolean_one_{index} : {word} = 1#256"]
            canonical = [f"(loadWord input.calldata {4 + 32 * i} = 0#256 ∨ loadWord input.calldata {4 + 32 * i} = 1#256)"
                for i, kind in enumerate(parsed["parameterTypes"]) if kind == "bool"]
            argument_type = " ∧ ".join(canonical) or "True"
            if branch == "malformed":
                argument_type = "¬(" + argument_type + ")"
            lines += ["  all_goals simp only [Nat.reduceAdd, Nat.reduceMul, SolidityABI.Source.Arguments, call, SolidityStorage.Function.call, function, SolidityABI.Parameter.Accepts, List.zipIdx, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, forall_const, true_and, and_true, false_implies, implies_true] at " + argument_name,
                "  all_goals change " + argument_type + " at " + argument_name,
                "  all_goals simp +decide -implicitDefEqProofs only [" + ", ".join(
                    fact for i, kind in enumerate(parsed["parameterTypes"]) if kind == "bool"
                    for fact in (f"boolean_zero_{i}", f"boolean_one_{i}")) + (", " if canonical else "") + "or_self, or_false, false_or, not_true_eq_false, not_false_eq_true, true_and, false_and, and_true, and_false] at " + argument_name]
            for index, kind in enumerate(parsed['parameterTypes']):
                if kind == 'bool':
                    lines += [f"  all_goals try simp +decide [boolean_zero_{index}] at boolean_one_{index}"]
            if branch == 'returned':
                boolean_facts = [fact for i, kind in enumerate(parsed['parameterTypes']) if kind == 'bool'
                    for fact in (f'boolean_zero_{i}', f'boolean_one_{i}')]
                for index in range(len(branches)):
                    lines += ["  all_goals try simp +decide [" + ', '.join(boolean_facts) + f"] at _branch_{index}"]
        if branch == "returned":
            # Simplify just the source outcome and prune Boolean branches as
            # they become known. Traversing unreduced dead arms duplicates the
            # recursive evaluator's work, especially around arithmetic binds.
            lines += ["  all_goals conv =>", "    arg 1",
                "    simp +decide -implicitDefEqProofs [SolidityStorage.Function.result, SolidityStorage.Receive.result, SolidityStorage.bodyResult, " + ("receiver," if receive else "function, source,"),
                "    SolidityStorage.statements, SolidityStorage.statement, SolidityStorage.Condition.eval, SolidityStorage.Comparison.test,",
                "    SolidityStorage.expression, variables, SolidityStorage.locals, " + STORAGE_LAYOUT_SIMPS + ", BitVec.lt_def, BitVec.le_def,",
                "    SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked, Contract.CheckedOp.eval,",
                "    SolidityWord.Expr.eval, SolidityWord.Binary.eval, Source.locals, List.idxOf?, List.findIdx?_cons,",
                "    Stateful.write, shl_word, shr_word, List.mem_cons, List.not_mem_nil, or_false,",
                "    Except.bind, Except.pure, Bind.bind, Pure.pure, Nat.add_comm, Nat.mul_comm, *]"]
            extras += ["_static"]
            for index, (condition, symmetry) in enumerate(branches):
                if symmetry:
                    left, right = symmetry
                    lines += [f"  all_goals have reverse_branch_{index} : ({right} = {left}) ↔ ({left} = {right}) := eq_comm"]
                    extras.append(f"reverse_branch_{index}")
        lines += execution_proof(extras)
    lines += ["theorem trace_returned (input : Input) (sized : Sized input)",
        "    " + " ".join(conditions["returned"]),
        "    (state : Stateful.State) (env : Stateful.Environment) :",
        f"    SolidityStorage.Conforms ({source_result})",
        f"      ((Stateful.run code input env {steps} {{ state with machine := {{}} }}).map Stateful.Result.effects) := by"]

    def compose(depth, offset, indent):
        if depth == len(partitions):
            arguments = " ".join(premise[1:premise.index(" :")] for premise in conditions["returned"])
            lines.append(indent + f"exact trace_returned_{offset} input sized {arguments} state env " +
                         " ".join(name for name, _ in partitions))
            return
        name, condition = partitions[depth]
        lines.append(indent + f"by_cases {name} : {condition}")
        for positive in (True, False):
            start = len(lines)
            compose(depth + 1, offset + (0 if positive else 2**(len(partitions) - depth - 1)), indent + "  ")
            lines[start] = indent + "· " + lines[start][len(indent) + 2:]
    compose(0, 0, "  ")
    return lines


def creation_proof(creation, code):
    steps = len(creation) * 4 + 1
    # A statically reverting constructor may omit the runtime image entirely.
    # The hint is optional, not a success/failure classification: the complete
    # trace still has to prove the source outcome and exact bytes on any return.
    image = creation.endswith(code)
    return (functions.creation_image(creation, code) if image else []) + [
        "theorem creation_trace : SolidityStorage.Constructor.TracePreserves variables initializers constructor",
        f"    creation code {steps} := by",
        "  intro input state original",
        "  by_cases value : input.value = 0#256",
        "  all_goals conv =>",
        "    arg 1",
        "    simp +decide -implicitDefEqProofs [SolidityStorage.Creation.expected,",
        "      SolidityStorage.Constructor.result, SolidityStorage.Initialization.evaluate, initializers, constructor,",
        "      SolidityStorage.statements, SolidityStorage.statement, SolidityStorage.expression,",
        "      SolidityStorage.Condition.eval, SolidityStorage.Comparison.test, SolidityWord.Expr.eval,",
        "      variables, SolidityStorage.locals, " + STORAGE_LAYOUT_SIMPS + ", Source.locals, SolidityWord.Expr.evalChecked,",
        "      SolidityWord.Binary.evalChecked, Contract.CheckedOp.eval, SolidityWord.Binary.eval,",
        "      Stateful.write, List.idxOf?, List.findIdx?_cons, Except.bind, Except.pure,",
        "      Bind.bind, Pure.pure, value]",
        "  all_goals repeat",
        "    rw [Stateful.projected_succ]",
        "    simp +decide -implicitDefEqProofs (maxSteps := 30000) [Stateful.step, Stateful.coreStep,",
        "      Contract.Evm.step, Contract.Evm.push, Contract.Evm.binary, Contract.Evm.unary,",
        "      pushWidth, expansionCost, expandedWords, memoryCost, Stateful.Result.effects,",
        "      SolidityStorage.conforms_charge, SolidityStorage.conforms_finished_returned,",
        "      SolidityStorage.conforms_finished_reverted, SolidityStorage.conforms_fault,",
        "      SolidityWord.panic_overflow_memory, SolidityStorage.write_overwrite, SolidityStorage.write_shadow,",
        "      Stateful.write, " + ("copy_return, " if image else "") + "value]"]


def dispatch_proofs(code, selectors, has_receive):
    steps = len(code) * 4 + 1
    conditions = {
        "short": ["(_nonempty : 0 < input.calldata.length)", "(_short : input.calldata.length < 4)"],
        "unknown": ["(header : 4 ≤ input.calldata.length)"] +
            [f"(_absent_{i} : loadWord input.calldata 0 >>> 224 ≠ {selector}#256)" for i, selector in enumerate(selectors)],
    }
    if not has_receive:
        conditions['empty'] = ["(_empty : input.calldata.length = 0)"]
    lines = []
    for name, premises in conditions.items():
        lines += [f"theorem trace_{name} (input : Input) (sized : Sized input)", "    " + " ".join(premises),
            "    (state : Stateful.State) (env : Stateful.Environment) :",
            "    SolidityStorage.Conforms (.reverted [])",
            f"      ((Stateful.run code input env {steps} {{ state with machine := {{}} }}).map Stateful.Result.effects) := by"]
        lines += ["  have length_zero : (BitVec.ofNat 256 input.calldata.length = 0#256) ↔ input.calldata.length = 0 := by",
            "    rw [← BitVec.toNat_inj]; simp only [length_word input.calldata.length sized]; rfl"]
        extras = ["length_word input.calldata.length sized", "length_zero"]
        if name == 'empty':
            extras += ["_empty"]
        elif name == 'short':
            extras += ["_short", "Nat.ne_of_gt _nonempty"]
        else:
            lines += ["  have short : ¬input.calldata.length < 4 := Nat.not_lt.mpr header",
                "  have nonempty : input.calldata.length ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 4) header)"]
            extras += ["short", "nonempty"] + [fact for i in range(len(selectors)) for fact in (f"_absent_{i}", f"Ne.symm _absent_{i}")]
        lines += execution_proof(extras, separate_jumps=name == 'unknown')
    return lines


def selected_trace(parsed, steps):
    size = 4 + 32 * len(parsed['parameters'])
    payable = parsed['mutability'] == 'payable'
    value = "" if payable else "value "
    lines = ["theorem trace (input : Input) (sized : Sized input) (header : 4 ≤ input.calldata.length)",
        "    (chosen : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 function.call.selector)",
        "    (state : Stateful.State) (env : Stateful.Environment) :",
        "    SolidityStorage.Conforms (function.outcome variables input state.storage env.isStatic)",
        f"      ((Stateful.run code input env {steps} {{ state with machine := {{}} }}).map Stateful.Result.effects) := by",
        f"  apply SolidityStorage.selected variables function code {steps} ?_ ?_ ?_ ?_ input sized header chosen state env"]
    if payable:
        lines += ["  · intro input sized header selected value; simp [SolidityABI.Source.AcceptsValue, SolidityStorage.Function.call, function, source] at value"]
    else:
        lines += ["  · intro input sized header selected value; rw [call_eq, selector] at selected",
            "    change input.value ≠ 0#256 at value", "    exact trace_paid input sized header selected value"]
    lines += ["  · intro input sized header selected value shortArguments; rw [call_eq, selector] at selected",
        f"    change input.calldata.length < {size} at shortArguments",
        *( [] if payable else ["    change input.value = 0#256 at value"]),
        "    exact trace_truncated input sized header selected " + value + "shortArguments",
        "  · intro input sized value full selected arguments; rw [call_eq, selector] at selected",
        f"    change {size} ≤ input.calldata.length at full",
        *( [] if payable else ["    change input.value = 0#256 at value"]),
        "    exact trace_malformed input sized selected " + value + "full arguments",
        "  · intro input sized accepted; rcases accepted with ⟨value, full, selected, arguments⟩; rw [call_eq, selector] at selected",
        f"    change {size} ≤ input.calldata.length at full",
        *( [] if payable else ["    change input.value = 0#256 at value"]),
        "    exact trace_returned input sized selected " + value + "full arguments"]
    return lines


def proof_source(pairs, fuel, *, case_offset=0):
    if not 1 <= len(pairs) <= 128 or type(fuel) is not int or not 0 <= fuel <= 16:
        raise ValueError("unsupported proof batch or normalization fuel")
    if type(case_offset) is not int or not 0 <= case_offset <= 128 - len(pairs):
        raise ValueError("unsupported artifact case offset")
    lines, claims = functions.proof_header(MODULE), []
    lines[4] = "import Compiler.Validation.SolidityStorageConstructor"
    for index, (req, res) in enumerate(pairs, case_offset):
        parsed, code, selectors = artifact(req, res)
        creation = functions.creation_code(parsed, res)
        steps, creation_steps = len(code) * 4 + 1, len(creation) * 4 + 1
        fields = ["{ name := " + json.dumps(field['name']) + ", type := ." +
                  {'uint256': 'word', 'bool': 'boolean'}[field['type']] + " }" for field in parsed['fields']]
        lines += [f"namespace Case{index}", "def variables : SolidityStorage.Layout := [" + ", ".join(fields) + "]"]
        initialization = parsed["initialization"]
        lines += ["def initializers : List SolidityStorage.Initialization.Initializer := [" + ", ".join(
            "(" + str(item['slot']) + ", " + functions.words.source_expression(initialization['nodes'], item['root']) + ")"
            for item in initialization['initializers']) + "]"]
        constructor = parsed["constructor"]
        lines += ["def constructor : SolidityStorage.Constructor.Body := { statements := " +
            statements(constructor, constructor["body"]) + ", checked := " + str(constructor["checked"]).lower() +
            ", payable := " + str(constructor["payable"]).lower() + " }"]
        lines += functions.byte_facts("code", code) + functions.byte_facts("creation", creation)
        lines += dispatch_proofs(code, selectors, parsed['receive'] is not None)
        if parsed['receive'] is not None:
            lines += ['namespace Receiver']
            lines += function_proof(parsed['receive'], parsed['fields'], code, receive=True)
            lines += ['end Receiver']
        for i, (function, selector) in enumerate(zip(parsed["functions"], selectors)):
            lines += [f"namespace Function{i}"]
            lines += function_proof(function, parsed["fields"], code, selector)
            lines += selected_trace(function, steps) + [f"end Function{i}"]
        names = [f"Function{i}" for i in range(len(selectors))]
        receiver = 'some Receiver.receiver' if parsed['receive'] is not None else 'none'
        lines += ["def contractSource : SolidityStorage.ContractSource := { variables := variables, functions := [" +
                  ", ".join(name + ".function" for name in names) + "], receive := " + receiver + " }",
            f"theorem trace : SolidityStorage.TracePreserves contractSource code {steps} := by",
            f"  apply SolidityStorage.dispatch contractSource code {steps} ?_ trace_short ?_ ?_",
            "  · intro input sized empty state env"]
        if parsed['receive'] is not None:
            lines += ['    exact Receiver.trace_returned input sized empty state env']
        else:
            lines += ['    exact trace_empty input sized empty state env']
        lines += ["  · intro input sized header unknown state env",
            "    apply trace_unknown input sized header " + "?_ " * len(names) + "state env"]
        for name in names:
            lines += [f"    · simpa only [{name}.call_eq, {name}.selector] using unknown {name}.function (by simp [contractSource])"]
        lines += ["  · intro function member input sized header chosen state env",
            "    simp only [contractSource, List.mem_cons, List.not_mem_nil, or_false] at member"]
        if names:
            lines += ["    rcases member with " + " | ".join("rfl" for _ in names)]
            lines += [f"    · exact {name}.trace input sized header chosen state env" for name in names]
        lines += [f"theorem calls : SolidityStorage.CallsPreserves contractSource code {steps} := by",
            f"  apply SolidityStorage.certifyCalls contractSource code {steps} (by simp [contractSource]) (by decide) (by decide) ?_ ?_ trace",
            "  · simp only [contractSource, List.map_cons, List.map_nil" +
                (", " + ", ".join(fact for name in names for fact in (name + ".call_eq", name + ".selector")) if names else "") + "]",
            "    decide",
            "  · intro function member",
            "    simp only [contractSource, List.mem_cons, List.not_mem_nil, or_false] at member"]
        if names:
            lines += ["    rcases member with " + " | ".join("rfl" for _ in names)]
            lines += [f"    · exact {name}.inhabited" for name in names]
        lines += creation_proof(creation, code)
        lines += [f"theorem checked : SolidityStorage.Constructor.Preserves contractSource initializers constructor creation code {creation_steps} {steps} :=",
            f"  SolidityStorage.Constructor.certify contractSource initializers constructor creation code {creation_steps} {steps} calls",
            "    (by decide) (by decide) (by decide) creation_trace", f"end Case{index}"]
        claims.append(MODULE + f".Case{index}.checked")
    lines += functions.artifacts.audit_source(MODULE, claims, AUDIT_SCHEMA)
    return "\n".join(lines).encode(), claims


def case_metadata(req, res):
    parsed, code, selectors = artifact(req, res)
    creation = functions.creation_code(parsed, res)
    record = {"storageVariables": parsed["storage"], "storageFields": parsed["fields"],
        "receive": None if parsed["receive"] is None else {key: parsed["receive"][key]
            for key in ("checked", "writes", "branches", "statements", "conditionNodes")},
        "initializers": len(parsed["initialization"]["initializers"]),
        "initializationNodes": len(parsed["initialization"]["nodes"]),
        "constructor": {key: parsed["constructor"][key] for key in ("explicit", "payable", "checked", "writes", "branches", "statements", "conditionNodes")},
        "functions": [{"signature": f["signature"], "selector": f"{s:08x}",
            "visibility": f["visibility"],
            "parameters": f["parameters"], "parameterTypes": f["parameterTypes"], "returnType": f["returnType"], "sourceNodes": len(f["nodes"]), "conditionNodes": f["conditionNodes"],
            "writes": f["writes"], "branches": f["branches"], "statements": f["statements"], "mutability": f["mutability"],
            "arithmeticMode": "checked" if f["checked"] else "unchecked"}
            for f, s in zip(parsed["functions"], selectors)],
        "bytecodeBytes": len(code), "bytecodeSha256": artifacts.gate.digest(code),
        "provedStepBound": len(code) * 4 + 1, "creationBytecodeBytes": len(creation),
        "creationBytecodeSha256": artifacts.gate.digest(creation),
        "creationProvedStepBound": len(creation) * 4 + 1}
    origin = corpus.matching_origin(req["sources"]["Function.sol"]["content"], parsed["contract"])
    if origin is not None:
        record["corpusSource"] = origin
    return record


def write_cases(output):
    from compiler_storage_cases import write_cases as write
    return write(output)


def rejection_cases():
    from compiler_storage_cases import rejection_cases as cases
    return cases()


def negative_pairs(pairs):
    # Bind fixture identity to the complete request, not a substring which could
    # accidentally select a different function/contract after corpus changes.
    from compiler_storage_cases import cases
    fixtures = dict(cases())

    def case(name):
        return next(pair for pair in pairs if pair[0] == fixtures[name])

    result = []
    for label, fixture, before, after in (
            ("wrong_receiver_guard", corpus.RECEIVER_CASE, "if (!_acceptEther)", "if (_acceptEther)"),
            ("lost_receiver_revert", corpus.RECEIVER_CASE, "revert();", "return;"),
            ("wrong_boolean_store", corpus.RECEIVER_CASE, "_acceptEther = acceptEther;", "_acceptEther = !acceptEther;"),
            ("added_boolean_payability", corpus.RECEIVER_CASE, "public {", "public payable {"),
            ("wrong_packed_field", "packed_flags", "right = value;", "left = value;"),
            ("wrong_mixed_layout", "mixed_storage", "bool private left; uint256 private word; bool private right;",
                "uint256 private word; bool private left; bool private right;"),
            ("lost_boolean_payability", "mixed_storage", "external payable", "external"),
            ("wrong_empty_return", "mixed_storage", "return;", "revert();"),
            ("lost_boolean_revert", "boolean_returns", "revert();", "return;"),
            ("lost_boolean_early_return", "boolean_returns", "if (value) { return; }", "if (value) { gate = false; }"),
            ("wrong_boolean_constructor", "receive_only", "gate = true;", "gate = false;"),
            ("lost_constructor_revert", "constructor_revert", "constructor() { gate = true; revert(); }",
                "constructor() { gate = true; return; }"),
            ("wrong_boolean_and", "boolean_and", "x == uint256(0) &&", "x == uint256(0) ||"),
            ("wrong_boolean_or", "boolean_or", "x == uint256(0) ||", "x == uint256(0) &&"),
            ("eager_boolean_operand", "boolean_and", "x == uint256(0) && y + z > y", "y + z > y && x == uint256(0)"),
            ("lost_boolean_negation", "boolean_precedence", "!(x < y)", "(x < y)"),
            ("wrong_boolean_grouping", "boolean_parentheses", "(x == uint256(0) || y == uint256(0)) && z != uint256(0)",
                "x == uint256(0) || y == uint256(0) && z != uint256(0)"),
            ("constructor_eager_boolean", "constructor_boolean_skip", "true || cell - uint256(1) == uint256(0)",
                "cell - uint256(1) == uint256(0) || true"),
            ("constructor_hidden_boolean_panic", "constructor_boolean_panic", "false ||", "true ||"),
            ("wrong_constructor_value", "constructor_literal", "cell = uint256(7);", "cell = uint256(8);"),
            ("wrong_constructor_initial_value", "constructor_dependency", "first = uint256(7);", "first = uint256(9);"),
            ("erased_constructor_return", "constructor_return", "return;", "cell = uint256(0);"),
            ("erased_constructor_panic", "constructor_panic", "second - uint256(1)", "second + uint256(1)"),
            ("wrong_constructor_arithmetic_mode", "constructor_unchecked", "unchecked { cell = cell - uint256(1); }", "cell = cell - uint256(1);"),
            ("lost_constructor_payability", "constructor_payable", "constructor() payable", "constructor()"),
            ("added_constructor_payability", "constructor_literal", "constructor()", "constructor() payable"),
            ("wrong_initializer", "init_literal", "cell = uint256(7);", "cell = uint256(8);"),
            ("missing_initializer", "init_literal", "cell = uint256(7);", "cell;"),
            ("wrong_initialization_dependency", "init_dependency", "first * uint256(3)", "first * uint256(4)"),
            ("eager_forward_initializer", "init_forward", "second + uint256(1)", "uint256(10)"),
            ("erase_initializer_panic", "init_panic", "second - uint256(1)", "second + uint256(1)"),
            ("wrong_store_value", "cell", "cell = value;", "cell = uint256(1);"),
            ("missing_store", "cell", "cell = value; return cell;", "return value;"),
            ("wrong_getter", "cell", "return cell;", "return ~cell;"),
            ("swapped_slots", "pair", "uint256 private first; uint256 private second;",
                "uint256 private second; uint256 private first;"),
            ("lost_second_slot", "pair", "second = y;", "first = y;"),
            ("wrong_last_write", "overwrite", "cell = y;", "cell = x;"),
            ("wrong_sequential_read", "rollback", "second = first + y;", "second = second + y;"),
            ("reversed_branch", "branch_return", "if (x < y)", "if (x > y)"),
            ("wrong_branch_write", "branch_join", "cell = y;", "cell = uint256(7);"),
            ("missing_early_return", "early_return", "if (x != uint256(0)) { return cell; }", "if (x != uint256(0)) { cell = y; }"),
            ("wrong_join_read", "sequential_branch", "if (cell == uint256(0))", "if (x == uint256(0))"),
            ("wrong_nested_return", "nested_branch", "return z;", "return y;")):
        req, res = copy.deepcopy(case(fixture))
        content = req["sources"]["Function.sol"]["content"]
        if before not in content:
            raise ValueError("missing storage source corruption anchor: " + label)
        req["sources"]["Function.sol"]["content"] = content.replace(before, after)
        model(req)
        result.append((label, [(req, res)]))
    req, res = copy.deepcopy(case("pair"))
    content = req["sources"]["Function.sol"]["content"]
    req["sources"]["Function.sol"]["content"] = content.replace("unchecked { ", "", 1).replace("; } }", "; }", 1)
    if not model(req)["functions"][0]["checked"]:
        raise ValueError("missing checked source for overflow-erasure control")
    result.append(("erase_overflow_check", [(req, res)]))
    req, res = copy.deepcopy(case("condition_panic"))
    content = req["sources"]["Function.sol"]["content"]
    content = content.replace("{ cell = x; if", "{ unchecked { cell = x; if", 1)
    content = content.replace("return z; } }", "return z; } } }", 1)
    req["sources"]["Function.sol"]["content"] = content
    if model(req)['functions'][0]['checked']:
        raise ValueError('missing unchecked condition corruption')
    result.append(('erase_condition_panic', [(req, res)]))

    def runtime(label, pair, changed):
        req, res = copy.deepcopy(pair)
        parsed, code, _ = artifact(req, res)
        creation = functions.creation_code(parsed, res)
        if len(changed) != len(code) or not creation.endswith(code):
            raise ValueError("storage mutation must preserve the paired creation image")
        evm = res["contracts"]["Function.sol"][parsed["contract"]]["evm"]
        evm["deployedBytecode"]["object"] = changed.hex()
        evm["bytecode"]["object"] = (creation[:-len(code)] + changed).hex()
        result.append((label, [(req, res)]))

    # Pin each opcode-level corruption to the complete selected native unit.
    # These preserve byte lengths and the embedded runtime image, so rejection
    # must come from the source/execution certificate rather than image binding.
    receiver = case(corpus.RECEIVER_CASE)
    _, code, _ = artifact(*receiver)
    for label, pattern, offset, replacement in (
            ("inverted_boolean_validation", bytes.fromhex("1515809103601c57"), 4, 0x14),
            ("uncleared_boolean_byte", bytes.fromhex("60ff80195f5416911617"), 1, 0x01),
            ("nonempty_receive", bytes.fromhex("5b3615601157"), 1, 0x5f)):
        positions = [pc for pc, _, _ in functions.instructions(code) if code[pc:pc+len(pattern)] == pattern]
        if len(positions) != 1:
            raise ValueError("native Boolean/receive corruption anchor changed: " + label)
        pc = positions[0] + offset
        runtime(label, receiver, code[:pc] + bytes([replacement]) + code[pc+1:])

    pair = case("cell")
    parsed, code, _ = artifact(*pair)
    decoded = list(functions.instructions(code))
    value = next(pc for pc, op, _ in decoded if op == 0x34)
    store = next(pc for pc, op, _ in decoded if op == 0x55)
    runtime("accept_value", pair, code[:value] + b'\x5f' + code[value+1:])
    runtime("replace_sstore", pair, code[:store] + b'\x50' + code[store+1:])
    creation = functions.creation_code(parsed, pair[1])
    req, res = copy.deepcopy(pair)
    res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["bytecode"]["object"] = (
        creation[:-1] + bytes([creation[-1] ^ 1])).hex()
    result.append(("creation_image", [(req, res)]))

    # Omitting a runtime image is admissible only when the exact execution
    # proves the source's failure. A successful source cannot borrow that route.
    req, res = copy.deepcopy(case("constructor_literal"))
    failing_req, failing_res = case("constructor_initializer_panic")
    failing = functions.creation_code(model(failing_req), failing_res)
    if failing.endswith(artifact(req, res)[1]):
        raise ValueError("constructor failure fixture no longer omits its runtime image")
    res["contracts"]["Function.sol"]["C"]["evm"]["bytecode"]["object"] = failing.hex()
    result.append(("missing_successful_creation_image", [(req, res)]))

    pair = case("checked_update")
    _, code, _ = artifact(*pair)
    panic = bytes.fromhex("601160045260245ffd")
    positions = [pc for pc, _, _ in functions.instructions(code) if code[pc:pc + len(panic)] == panic]
    if len(positions) != 1:
        raise ValueError("native storage panic changed; review corruption controls")
    pc = positions[0] + 1
    runtime("wrong_panic_code", pair, code[:pc] + b'\x12' + code[pc+1:])
    for label, fixture, opcode in (("replace_initial_sstore", "init_literal", 0x55),
                                   ("wrong_initializer_panic", "init_panic", None)):
        req, res = copy.deepcopy(case(fixture))
        parsed, code, _ = artifact(req, res)
        creation = functions.creation_code(parsed, res)
        if not creation.endswith(code):
            raise ValueError("initializer corruption must preserve the paired runtime image")
        prefix = creation[:-len(code)]
        if opcode is not None:
            pc = next(pc for pc, op, _ in functions.instructions(prefix) if op == opcode)
            changed = prefix[:pc] + b'\x50' + prefix[pc+1:]
        else:
            positions = [pc for pc, _, _ in functions.instructions(prefix) if prefix[pc:pc+len(panic)] == panic]
            if len(positions) != 1:
                raise ValueError("native initializer panic changed; review corruption controls")
            pc = positions[0] + 1
            changed = prefix[:pc] + b'\x12' + prefix[pc+1:]
        res["contracts"]["Function.sol"][parsed["contract"]]["evm"]["bytecode"]["object"] = (changed + code).hex()
        result.append((label, [(req, res)]))
    return result


if __name__ == "__main__":
    sys.exit(artifacts.main(sys.modules[__name__]))
