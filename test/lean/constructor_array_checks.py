#!/usr/bin/env python3
"""Inventory captured Id literals without admitting AIR control semantics.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean/zig_air"))
from capture import read_json


def stack_arrays(instructions, extent, count):
    """The shared ABI boundary; initializer/store shape belongs to each caller."""
    arrays = [inst for inst in instructions if inst["tag"] == "alloc" and
              inst.get("type", {}).get("child", {}).get("kind") == "array" and
              inst["type"]["child"].get("length") == extent and
              inst["type"]["child"].get("child") == {"kind": "int", "bits": 32, "signedness": "unsigned"}]
    if len(arrays) != count:
        raise ValueError("native initializer array count changed")
    for array in arrays:
        if (array.get("allocationKind") != "stack" or
                array["type"]["child"]["layout"] != {"kind": "abi", "bytes": extent * 4, "alignment": 4} or
                "sentinel" not in array["type"]["child"] or array["type"]["child"]["sentinel"] is not None):
            raise ValueError("native initializer stack kind or array layout changed")
    return arrays


def array_inventory(path, extent, count):
    return initialized_arrays(read_json(path)["instructions"], extent, count)


def initialized_arrays(instructions, extent, count):
    inventory = []
    for array in stack_arrays(instructions, extent, count):
        elements = [inst for inst in instructions if inst["tag"] == "ptr_elem_ptr" and
                    inst.get("lhs") == {"kind": "instruction", "index": array["index"]}]
        stores = [inst for inst in instructions if inst["tag"] == "store" and
                  any(inst.get("lhs") == {"kind": "instruction", "index": element["index"]} for element in elements)]
        if (len(elements) != extent or len(stores) != extent or
                [element.get("rhs", {}).get("value") for element in elements] != list(range(extent)) or
                [store.get("lhs") for store in stores] !=
                [{"kind": "instruction", "index": element["index"]} for element in elements] or
                any(not array["index"] < element["index"] < store["index"] for element, store in zip(elements, stores)) or
                [store["index"] for store in stores] != sorted(store["index"] for store in stores)):
            raise ValueError("native initializer element or store inventory changed")
        inventory.append({"arrayInstruction": array["index"], "arrayBytes": extent * 4, "arrayAlignment": 4,
            "elementInstructions": [inst["index"] for inst in elements],
            "storeInstructions": [inst["index"] for inst in stores]})
    return {"arrays": inventory,
        "unsupportedPayloadCount": sum(inst.get("unsupportedPayload") is True for inst in instructions),
        "unsupportedPayloadTags": sorted({inst["tag"] for inst in instructions if inst.get("unsupportedPayload") is True}),
        "airControlSemanticsVerified": False}


def max_exponent_inventory(path, pair_count=30, unary_count=3):
    """Inventory the decoded EXP initializer operands, not opaque try/control.

    The exporter traverses block/loop/conditional bodies only. Switch descendants
    remain outside its decoded closure; these counts are not source coverage.
    """
    captured = read_json(path)
    if captured.get("bodyTraversal") != "supported-structured-containers-only":
        raise ValueError("max-base EXP capture traversal changed; review its scope")
    instructions = captured["instructions"]
    by_index = {inst["index"]: inst for inst in instructions}
    if len(by_index) != len(instructions):
        raise ValueError("max-base EXP capture contains duplicate instruction IDs")
    pairs = initialized_arrays(instructions, 2, pair_count)
    unary = initialized_arrays(instructions, 1, unary_count)
    reference = lambda index: {"kind": "instruction", "index": index}
    resolve = lambda ref: by_index.get(ref.get("index")) if ref.get("kind") == "instruction" else None
    calls = [inst for inst in instructions if inst["tag"] == "call" and inst.get("payloadVisited") is True]
    word = {"kind": "int", "bits": 32, "signedness": "unsigned"}

    def operation_after(array):
        stores = array["storeInstructions"]
        slices = [inst for inst in instructions if inst["tag"] == "array_to_slice" and
                  inst.get("payloadVisited") is True and stores[-1] < inst["index"]]
        if not slices:
            return None
        slice_inst = slices[0]
        matches = [call for call in calls if len(call.get("arguments", [])) == 4 and
                   call["arguments"][2] == reference(slice_inst["index"]) and
                   call.get("callee", {}).get("identity", {}).get("name", "").endswith(".Graph.makeOperation")]
        if len(matches) != 1 or not stores[-1] < slice_inst["index"] < matches[0]["index"]:
            return None
        return matches[0]

    def returned_between(call, bound):
        tries = [inst for inst in instructions if inst["tag"] == "try" and
                 inst.get("payloadVisited") is True and call["index"] < inst["index"] < bound]
        return tries[0] if len(tries) == 1 else None

    candidates = []
    for pair in pairs["arrays"]:
        first, second = [resolve(by_index[index]["rhs"]) for index in pair["storeInstructions"]]
        if not first or not second or first["tag"] != "load" or second["tag"] != "try":
            continue
        element = resolve(first.get("operand", {}))
        base = resolve(element.get("lhs", {})) if element else None
        if (first.get("type") != word or not element or element["tag"] != "slice_elem_ptr" or
                element.get("rhs", {}).get("value") != 1 or not base or base["tag"] != "load" or
                base.get("type", {}).get("kind") != "pointer" or base["type"].get("child") != word or
                base["type"].get("flags", {}).get("size") != "slice" or base["type"]["flags"].get("isConst") is not True):
            continue
        constants = [call for call in calls if len(call.get("arguments", [])) == 3 and
                     call.get("callee", {}).get("identity", {}).get("name", "").endswith(".Graph.makeConstant") and
                     call["arguments"][1].get("value") == 1 and
                     returned_between(call, first["index"]) == second]
        parity_call = operation_after(pair)
        if (len(constants) != 1 or not parity_call or not constants[0]["index"] < second["index"] <
                base["index"] < element["index"] < first["index"] < pair["arrayInstruction"]):
            continue
        for one in unary["arrays"]:
            odd = resolve(by_index[one["storeInstructions"][0]]["rhs"])
            even_call = operation_after(one)
            if not odd or not even_call or returned_between(parity_call, one["arrayInstruction"]) != odd:
                continue
            for final in pairs["arrays"]:
                even, final_odd = [resolve(by_index[index]["rhs"]) for index in final["storeInstructions"]]
                final_call = operation_after(final)
                if (not even or not final_call or final_odd != odd or
                        returned_between(even_call, final["arrayInstruction"]) != even):
                    continue
                candidates.append({"constantCallInstruction": constants[0]["index"],
                    "constantTryInstruction": second["index"], "exponentSliceLoadInstruction": base["index"],
                    "exponentElementInstruction": element["index"], "exponentLoadInstruction": first["index"],
                    "parityArray": pair, "parityCallInstruction": parity_call["index"],
                    "parityTryInstruction": odd["index"], "evenArray": one, "evenCallInstruction": even_call["index"],
                    "evenTryInstruction": even["index"], "finalArray": final, "finalCallInstruction": final_call["index"]})
    if len(candidates) != 1:
        raise ValueError("max-base EXP decoded initializer inventory is absent or ambiguous")
    return {**pairs, "constructorChain": candidates[0], "bodyTraversal": captured["bodyTraversal"],
        "unvisitedInstructionCount": sum(inst.get("payloadVisited") is not True for inst in instructions),
        "sourceCallSiteCoverageVerified": False, "tryAndSliceProvenanceVerified": False}


def local_inventory(path):
    """Retain the named local's aggregate store and later dynamic overwrite.

    This inventories a captured helper. Source admission binds operands and
    control; unsupported aggregate/call payloads do not acquire AIR semantics.
    """
    instructions = read_json(path)["instructions"]
    array, = stack_arrays(instructions, 2, 1)
    if array["type"].get("kind") != "pointer" or array["type"].get("flags", {}).get("isConst") is not False:
        raise ValueError("native named local is not a mutable array pointer")
    reference = lambda inst: {"kind": "instruction", "index": inst["index"]}
    initializers = [inst for inst in instructions if inst["tag"] == "store" and inst.get("lhs") == reference(array)]
    if len(initializers) != 1:
        raise ValueError("native local aggregate store count changed")
    initializer, = initializers
    aggregates = [inst for inst in instructions if inst["tag"] == "aggregate_init" and reference(inst) == initializer.get("rhs")]
    if len(aggregates) != 1 or aggregates[0].get("type") != array["type"]["child"]:
        raise ValueError("native local aggregate initialization changed")
    aggregate, = aggregates
    elements = [inst for inst in instructions if inst["tag"] == "slice_elem_ptr" and
                array["index"] < inst["index"] < aggregate["index"]]
    if len(elements) != 2 or [inst.get("rhs", {}).get("value") for inst in elements] != [0, 1]:
        raise ValueError("native local initializer read order changed")
    reads = []
    sources = []
    for element in elements:
        bases = [inst for inst in instructions if inst["tag"] == "load" and reference(inst) == element.get("lhs")]
        if (len(bases) != 1 or bases[0].get("type", {}).get("flags", {}).get("size") != "slice" or
                bases[0]["type"]["flags"].get("isConst") is not True or
                bases[0]["type"].get("child") != array["type"]["child"]["child"]):
            raise ValueError("native local initializer does not read a readonly Id slice")
        sources.append(bases[0].get("operand"))
        loaded = [inst for inst in instructions if inst["tag"] == "load" and inst.get("operand") == reference(element)]
        if len(loaded) != 1 or not element["index"] < loaded[0]["index"] < aggregate["index"]:
            raise ValueError("native local initializer source load changed")
        reads.append(loaded[0])
    if sources[0] is None or sources[0] != sources[1] or not reads[0]["index"] < elements[1]["index"]:
        raise ValueError("native local initializer source or read sequencing changed")
    updates = [inst for inst in instructions if inst["tag"] == "ptr_elem_ptr" and inst.get("lhs") == reference(array)]
    if len(updates) != 1 or updates[0].get("rhs", {}).get("kind") != "instruction":
        raise ValueError("native local selected overwrite pointer changed")
    update, = updates
    stores = [inst for inst in instructions if inst["tag"] in ("store", "store_safe") and inst.get("lhs") == reference(update)]
    if len(stores) != 1 or not aggregate["index"] < initializer["index"] < update["index"] < stores[0]["index"]:
        raise ValueError("native local overwrite store changed")
    slices = [inst for inst in instructions if inst["tag"] == "array_to_slice"]
    if len(slices) != 1 or not stores[0]["index"] < slices[0]["index"]:
        raise ValueError("native local array-to-slice boundary changed")
    return {"arrayInstruction": array["index"], "arrayBytes": 8, "arrayAlignment": 4,
        "initializerReadInstructions": [inst["index"] for inst in reads],
        "aggregateInstruction": aggregate["index"], "aggregateStoreInstruction": initializer["index"],
        "overwritePointerInstruction": update["index"], "overwriteStoreInstruction": stores[0]["index"],
        "sliceInstruction": slices[0]["index"],
        "unsupportedPayloadCount": sum(inst.get("unsupportedPayload") is True for inst in instructions),
        "unsupportedPayloadTags": sorted({inst["tag"] for inst in instructions if inst.get("unsupportedPayload") is True}),
        "airControlSemanticsVerified": False}
