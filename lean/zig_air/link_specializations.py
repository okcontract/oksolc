#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check exported direct-call and explicit-comptime specialization provenance.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This is a metadata boundary, not a semantic decoder. Body coverage, dominance,
specialization correctness, noalias and source/backend preservation stay open.
"""
import hashlib
import json
import re

from generate import fields, natural
from generate_memory import type_of, constant


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()).hexdigest()


def identity(value, sources):
    fields(value, "name sourceFile sourceSha256")
    if (not isinstance(value["name"], str) or not value["name"] or len(value["name"]) > 1024 or
            not isinstance(value["sourceFile"], str) or value["sourceFile"] not in sources or
            not isinstance(value["sourceSha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", value["sourceSha256"]) or
            value["sourceSha256"] != sources[value["sourceFile"]]):
        raise ValueError("function source identity is not in the pinned source inventory")
    return value


def signature(record):
    result = record["signature"]
    fields(result, "callingConvention genericInstance varArgs noaliasBits parameters returnType")
    if type(result["genericInstance"]) is not bool or result["varArgs"] is not False:
        raise ValueError("unsupported specialization or variadic signature")
    parameters = result["parameters"]
    if not isinstance(parameters, list) or len(parameters) > 32:
        raise ValueError("unsupported signature parameter count")
    natural(result["noaliasBits"], (1 << len(parameters)) - 1)
    return [type_of(p, byte_alignment=True) for p in parameters], type_of(result["returnType"], byte_alignment=True)


def specialization(record, sources):
    parameters, _ = signature(record)
    if record["signature"]["genericInstance"] is False:
        if "specialization" in record:
            raise ValueError("nongeneric function has specialization metadata")
        return list(range(len(parameters))), None
    spec = record.get("specialization")
    fields(spec, "schema owner sourceNoaliasBits sourceComptimeBits sourceParameterCount arguments")
    if spec["schema"] != "oksolc.generic-instance.v1":
        raise ValueError("unsupported specialization schema")
    owner = identity(spec["owner"], sources)
    if (owner["sourceFile"], owner["sourceSha256"]) != (record["sourceFile"], record["sourceSha256"]):
        raise ValueError("generic owner and instance source disagree")
    count = natural(spec["sourceParameterCount"], 32)
    noalias = natural(spec["sourceNoaliasBits"], (1 << count) - 1)
    comptime = natural(spec["sourceComptimeBits"], (1 << count) - 1)
    args = spec["arguments"]
    if not isinstance(args, list) or len(args) != count:
        raise ValueError("specialization argument count disagrees with owner")
    mapping, remapped_noalias = [], 0
    for index, arg in enumerate(args):
        if not isinstance(arg, dict):
            raise ValueError("invalid specialization argument")
        if arg.get("kind") == "runtime":
            fields(arg, "kind runtimeIndex")
            if natural(arg["runtimeIndex"], 31) != len(mapping) or comptime & (1 << index):
                raise ValueError("runtime/source parameter mapping disagrees")
            if noalias & (1 << index):
                remapped_noalias |= 1 << len(mapping)
            mapping.append(index)
        else:
            fields(arg, "kind value")
            if not comptime & (1 << index) or noalias & (1 << index):
                raise ValueError("implicit comptime or comptime noalias is outside this metadata profile")
            if arg["kind"] == "type":
                type_of(arg["value"], byte_alignment=True)
            elif arg["kind"] == "value":
                constant(arg["value"])
            else:
                raise ValueError("unsupported compile-time argument")
    if len(mapping) != len(parameters) or remapped_noalias != record["signature"]["noaliasBits"]:
        raise ValueError("specialization lost runtime parameters or noalias bits")
    return mapping, fingerprint({"specialization": spec, "signature": record["signature"], "configuration": record["configuration"]})


def link(records, roots, sources):
    """Validate exported edges reachable from roots, retaining unresolved scope.

    The caller supplies hash-checked records and the authoritative source hashes.
    Unknown body payloads are retained, never converted into call-graph coverage.
    """
    if not roots or len(set(roots)) != len(roots) or any(root not in records for root in roots):
        raise ValueError("missing or duplicate requested link roots")
    configuration = records[roots[0]]["configuration"]
    if (configuration.get("optimize") != "ReleaseFast" or configuration.get("useLlvm") is not True or
            configuration.get("isTest") is not False):
        raise ValueError("unsupported link build configuration")
    pending, functions, edges = list(roots), {}, []
    while pending:
        name = pending.pop()
        if name in functions:
            continue
        record = records[name]
        if (record.get("name") != name or record.get("schema") != "oksolc.fresh-air.v3" or
                record.get("capturePoint") != "after-sema-before-legalize" or record["configuration"] != configuration):
            raise ValueError("linked function identity, phase or configuration mismatch")
        identity({key: record[key] for key in ("name", "sourceFile", "sourceSha256")}, sources)
        parameters, _ = signature(record)
        mapping, key = specialization(record, sources)
        instructions, body = record["instructions"], record["body"]
        if not isinstance(instructions, list) or not 0 < len(instructions) <= 512 or not isinstance(body, list):
            raise ValueError("invalid linked instruction inventory")
        for index, inst in enumerate(instructions):
            if (not isinstance(inst, dict) or type(inst.get("index")) is not int or inst["index"] != index or
                    type(inst.get("payloadVisited")) is not bool or not isinstance(inst.get("tag"), str)):
                raise ValueError("invalid linked instruction index")
        for runtime_index, source_index in enumerate(mapping):
            if runtime_index >= len(body):
                raise ValueError("missing linked argument prefix")
            inst = instructions[natural(body[runtime_index], len(instructions) - 1)]
            if (inst.get("tag") != "arg" or inst.get("payloadVisited") is not True or
                    type(inst.get("zirParameterIndex")) is not int or inst["zirParameterIndex"] != source_index or
                    type_of(inst["type"], byte_alignment=True) != parameters[runtime_index]):
                raise ValueError("linked AIR arguments disagree with runtime/source mapping")
        functions[name] = {"recordSha256": fingerprint(record), "specializationSha256": key,
                           "runtimeParameterIndices": mapping, "noaliasBits": record["signature"]["noaliasBits"],
                           "unsupportedBodyInstructions": [{"index": i["index"], "tag": i["tag"]} for i in instructions
                                                           if i.get("payloadVisited") is True and i.get("unsupportedPayload") is True],
                           "unvisitedInstructions": sum(i.get("payloadVisited") is not True for i in instructions)}
        for inst in instructions:
            if inst.get("payloadVisited") is not True or inst.get("tag") not in {"call", "call_always_tail", "call_never_tail", "call_never_inline"}:
                continue
            fields(inst, "index tag payloadVisited type callee arguments")
            callee = inst["callee"]
            fields(callee, "kind identity")
            if callee["kind"] != "function":
                raise ValueError("indirect or unsupported function reference")
            target = identity(callee["identity"], sources)
            if target["name"] not in records:
                raise ValueError("missing captured callee body")
            target_record = records[target["name"]]
            if target != {key: target_record[key] for key in ("name", "sourceFile", "sourceSha256")}:
                raise ValueError("call reference and captured callee identity disagree")
            expected, returns = signature(target_record)
            if not isinstance(inst["arguments"], list) or len(inst["arguments"]) != len(expected):
                raise ValueError("call runtime argument count disagrees with callee")
            for argument, wanted in zip(inst["arguments"], expected):
                if isinstance(argument, dict) and argument.get("kind") == "instruction":
                    fields(argument, "kind index")
                    source = instructions[natural(argument["index"], len(instructions) - 1)]
                    if source.get("payloadVisited") is not True:
                        raise ValueError("call uses an unvisited argument")
                    actual = type_of(source["type"], byte_alignment=True)
                else:
                    actual, _ = constant(argument)
                if actual != wanted:
                    raise ValueError("call runtime argument type disagrees with callee")
            if type_of(inst["type"], byte_alignment=True) != returns:
                raise ValueError("call return type disagrees with callee")
            edges.append({"caller": name, "instruction": inst["index"], "tag": inst["tag"], "callee": target["name"],
                          "arguments": inst["arguments"]})
            pending.append(target["name"])
    return {"schema": "oksolc.specialization-links.v1", "exportedCallLinksChecked": True,
            "bodyCoverageVerified": False, "argumentDominanceVerified": False, "specializationSemanticsVerified": False,
            "noaliasVerified": False, "sourceSafetyVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False,
            "roots": list(roots), "sources": sources, "configuration": configuration,
            "functions": dict(sorted(functions.items())), "edges": sorted(edges, key=lambda edge: (edge["caller"], edge["instruction"]))}
