#!/usr/bin/env python3
"""Admit the complete representative header and its enclosing owner layout.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import extract_graph_init as graph
from generate_item_layout import checked_layout, checked_fields, require

ROOT = graph.ROOT
OUTPUT = ROOT / "lean/Compiler/Extraction/RepresentativeArrayLayout.lean"
OWNER_OUTPUT = ROOT / "lean/Compiler/Extraction/RepresentativeOwnerLayout.lean"
CACHE_OUTPUT = ROOT / "lean/Compiler/Extraction/ExpressionMapLayout.lean"
NATIVE = "array_list.Aligned(libevmasm.expression_classes.Expression,null)"
ELEMENT = "libevmasm.expression_classes.Expression"
IDENTITY = "src/libevmasm/expression_classes.zig::Expression"
OWNER = "libevmasm.expression_classes.ExpressionClasses"
MAP = "hash_map.Custom(libevmasm.expression_classes.ExpressionKey,u32,libevmasm.expression_classes.ExpressionKeyContext,80)"
CAPTURED = {"Debug": (72, 24), "ReleaseSafe": (72, 24), "ReleaseFast": (56, 16)}


def exact_record(actual, expected, message):
    require(isinstance(actual, dict) and actual.keys() == expected.keys() and
            all(type(actual[key]) is type(value) and actual[key] == value for key, value in expected.items()), message)


def programs(record, lib, source=None):
    source = graph.storage.SOURCE.read_bytes() if source is None else source
    require(graph.storage.extract(source) == graph.storage.OUTPUT.read_bytes(), "representative body/source admission changed")
    require(graph.extract(source) == graph.OUTPUT.read_bytes(), "representative owner/source admission changed")
    graph.check_std(lib)
    require(isinstance(record, dict) and set(record) == {"schema", "target", "fields", "element", "owner", "cache"} and
            record["schema"] == "oksolc.representative-array-layout.v5", "unsupported representative array profile")
    size, alignment = checked_layout(record["target"], "oksolc.representative-header-layout.v1", NATIVE)
    safety = record["target"]["mode"] != "ReleaseFast"
    header_lock = {"name": "pointer_stability", "type": "debug.SafetyLock", "offset": 24,
                   "bytes": 8 if safety else 0, "alignment": 8 if safety else 1}
    require(isinstance(record["fields"], list) and len(record["fields"]) == 3,
            "incomplete representative header inventory")
    require(sum(field == header_lock and all(type(field[key]) is type(value) for key, value in header_lock.items())
                for field in record["fields"] if isinstance(field, dict)) == 1,
            "native representative safety lock changed")
    element = record["element"]
    require(isinstance(element, dict) and set(element) == {"name", "bytes", "alignment"} and
            element["name"] == ELEMENT and type(element["bytes"]) is int and element["bytes"] == 32 and
            type(element["alignment"]) is int and element["alignment"] == 8, "representative element layout changed")
    fields = checked_fields([field for field in record["fields"] if field != header_lock], size, alignment, {
        "items": ("[]" + ELEMENT, 16, 8, '.recordSlice true "' + IDENTITY + '" ⟨32, 8⟩'),
        "capacity": ("usize", 8, 8, ".scalar (.int false 64)"),
    })
    owner = record["owner"]
    require(isinstance(owner, dict) and set(owner) == {"target", "fields"}, "incomplete representative owner profile")
    owner_size, owner_alignment = checked_layout(owner["target"], "oksolc.expression-owner-layout.v1", OWNER)
    require(all(owner["target"][key] == value for key, value in record["target"].items()
                if key not in {"schema", "name", "bytes", "alignment"}), "header and owner build contexts differ")
    require((size, alignment) == (32 if safety else 24, 8), "embedded representative header extent changed")
    require([(offset, name) for offset, _, name, _ in fields] == [(0, "items"), (16, "capacity")],
            "native representative data offsets changed")
    captured_owner, captured_cache = CAPTURED[record["target"]["mode"]]
    require((owner_size, owner_alignment) == (captured_owner, 8), "native owner build-mode extent changed")
    # The test limit has type void in these production executables. It has
    # no memory representation; still require it in the complete field table.
    require(isinstance(owner["fields"], list) and len(owner["fields"]) == 4,
            "incomplete representative owner inventory")
    limits = [field for field in owner["fields"] if isinstance(field, dict) and field.get("name") == "test_id_limit"]
    require(len(limits) == 1, "missing or duplicate test-only expression limit")
    limit = limits[0]
    require(set(limit) == {"name", "type", "offset", "bytes", "alignment"} and
            limit["type"] == "void" and type(limit["bytes"]) is int and limit["bytes"] == 0 and
            type(limit["alignment"]) is int and limit["alignment"] == 1 and
            type(limit["offset"]) is int and 0 <= limit["offset"] <= owner_size,
            "test-only expression limit has production storage")
    owner_fields = checked_fields([field for field in owner["fields"] if field is not limit], owner_size, owner_alignment, {
        "allocator": ("mem.Allocator", 16, 8, "⟨16, 8⟩"),
        "representatives": (NATIVE, size, alignment, "⟨" + str(size) + ", " + str(alignment) + "⟩"),
        "expressions": (MAP, captured_cache, 8, "⟨if runtimeSafety then 24 else 16, 8⟩"),
    })
    require([(offset, name) for offset, _, name, _ in owner_fields] ==
            [(0, "allocator"), (16, "representatives"), (48 if safety else 40, "expressions")],
            "native owner field offsets changed")
    cache = record["cache"]
    require(isinstance(cache, dict) and set(cache) == {"target", "fields", "metadata", "lock"}, "incomplete expression map profile")
    cache_size, cache_alignment = checked_layout(cache["target"], "oksolc.expression-map-layout.v1", MAP)
    require(all(cache["target"][key] == value for key, value in record["target"].items()
                if key not in {"schema", "name", "bytes", "alignment"}), "header and map build contexts differ")
    require((cache_size, cache_alignment) == (captured_cache, 8), "native map build-mode extent changed")
    # The ReleaseFast lock has no storage. Admit its complete native metadata
    # before omitting it from the positive-extent storage tree; never generalize
    # this exception to an arbitrary missing, overlapping or zero-sized field.
    cache_fields = cache["fields"]
    require(isinstance(cache_fields, list) and len(cache_fields) == 4, "incomplete native map inventory")
    lock = {"name": "pointer_stability", "type": "debug.SafetyLock", "offset": 8 if safety else 16,
            "bytes": 8 if safety else 0, "alignment": 8 if safety else 1}
    require(all(isinstance(field, dict) for field in cache_fields) and
            sum(field == lock and all(type(field[key]) is type(value) for key, value in lock.items())
                for field in cache_fields) == 1, "native map safety lock changed")
    storage_fields = [field for field in cache_fields if field != lock]
    metadata = "?[*]" + MAP + ".Metadata"
    pointer = cache["metadata"]
    require(isinstance(pointer, dict) and pointer.keys() == {"pointer", "child"}, "incomplete metadata pointer profile")
    exact_record(pointer["pointer"], {"name": "[*]" + MAP + ".Metadata", "bytes": 8, "alignment": 8,
        "is_const": False, "is_allowzero": False, "size": "many"}, "unsupported metadata pointer")
    exact_record(pointer["child"], {"name": MAP + ".Metadata", "bytes": 1, "alignment": 1}, "unsupported metadata pointee")
    state = cache["lock"]
    require(isinstance(state, dict) and state.keys() == {"fields", "state_bits", "exhaustive", "states", "initial"},
            "incomplete map lock profile")
    require(isinstance(state["fields"], list) and len(state["fields"]) == 1 and isinstance(state["fields"][0], dict),
            "incomplete map lock field")
    state_name = state["fields"][0].get("type")
    # Zig's anonymous enum suffix depends on declaration discovery order. Its
    # complete tag set, width, extent, default and owning source remain bound.
    require(isinstance(state_name, str) and len(state_name) < 128 and
            re.fullmatch(r"debug\.SafetyLock\.State__enum_[0-9]+", state_name), "unreviewed map lock state type")
    exact_record(state["fields"][0], {"name": "state", "type": state_name, "offset": 0,
        "bytes": 8 if safety else 0, "alignment": 8 if safety else 1}, "native lock state geometry changed")
    require(type(state["state_bits"]) is int and state["state_bits"] == (64 if safety else 0) and
            state["exhaustive"] is (not safety) and type(state["initial"]) is int and state["initial"] == 0,
            "native lock tag/default changed")
    expected_tags = [("unlocked", 0), ("exclusive", 2**64 - 1)] if safety else [("unknown", 0)]
    require(isinstance(state["states"], list) and len(state["states"]) == len(expected_tags), "incomplete lock tags")
    for actual, (name, value) in zip(state["states"], expected_tags):
        exact_record(actual, {"name": name, "value": value}, "native lock tag changed")
    admitted_cache = checked_fields(storage_fields, cache_size, cache_alignment, {
        "metadata": (metadata, 8, 8, '.object metadataType'),
        "size": ("u32", 4, 4, ".scalar (.int false 32)"),
        "available": ("u32", 4, 4, ".scalar (.int false 32)"),
    })
    require([(offset, name) for offset, _, name, _ in admitted_cache] ==
            [(0, "metadata"), (16 if safety else 8, "size"), (20 if safety else 12, "available")],
            "native map field offsets changed")
    cache_program = ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.ZigAir.MemoryTypes\n\nnamespace Compiler.Extraction.ExpressionMap\n\n"
        "-- Complete captured HashMapUnmanaged field inventory in all three admitted modes.\n"
        "-- Nullable metadata pointers are atomic values, not pointer/tag byte projections.\n"
        "-- ReleaseFast's captured zero-byte lock at offset 16 has no storage leaf.\n"
        "-- Source SHA-256: " + hashlib.sha256(source).hexdigest() + "\n"
        "-- std/hash_map.zig SHA-256: " + graph.STD["hash_map.zig"] + "\n"
        "-- std/debug.zig SHA-256: " + graph.STD["debug.zig"] + "\n"
        'def metadataPointerType : Compiler.ZigAir.Memory.Ty := .pointer true true (.record "' + MAP + '.Metadata" ⟨1, 1⟩)\n'
        "def metadataType : Compiler.ZigAir.Memory.Ty := .optionalObject metadataPointerType ⟨8, 8⟩\n"
        "def lockType : Compiler.ZigAir.Memory.Ty :=\n"
        '  .aggregate "debug.SafetyLock" ⟨8, 8⟩ [(0, .scalar (.int false 64))]\n'
        "def metadataOffset : Nat := 0\ndef sizeOffset (runtimeSafety : Bool) : Nat := if runtimeSafety then 16 else 8\n"
        "def availableOffset (runtimeSafety : Bool) : Nat := if runtimeSafety then 20 else 12\n"
        "def lockOffset (runtimeSafety : Bool) : Nat := if runtimeSafety then 8 else 16\n"
        "def countType : Compiler.ZigAir.Memory.Ty := .scalar (.int false 32)\n"
        "def allocationType (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Ty :=\n"
        '  .aggregate "' + MAP + '" ⟨if runtimeSafety then 24 else 16, 8⟩\n'
        "    ([(0, .object metadataType)] ++ (if runtimeSafety then [(8, .object lockType)] else []) ++\n"
        "      [(sizeOffset runtimeSafety, .scalar (.int false 32)), (availableOffset runtimeSafety, .scalar (.int false 32))])\n\n"
        "end Compiler.Extraction.ExpressionMap\n").encode()
    offsets = "\n".join("def " + name + "Offset : Nat := " + str(offset) for offset, _, name, _ in fields)
    terms = ",\n    ".join("(" + str(offset) + ", " + term + ")" for offset, _, _, term in fields)
    header_program = ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.ZigAir.MemoryTypes\n\nnamespace Compiler.Extraction.RepresentativeArray\n\n"
        "-- Captured items/capacity prefix of std.ArrayList(Expression).\n"
        "-- The native safety-lock suffix is represented separately in the complete owner view.\n"
        "-- Source SHA-256: " + hashlib.sha256(source).hexdigest() + "\n"
        "-- std/array_list.zig SHA-256: " + graph.STD["array_list.zig"] + "\n"
        'def elementType : Compiler.ZigAir.Memory.Ty := .record "' + IDENTITY + '" ⟨32, 8⟩\n'
        'def itemsType : Compiler.ZigAir.Memory.Ty := .slice true elementType\n'
        + offsets + "\n\n"
        "def allocationType : Compiler.ZigAir.Memory.Ty :=\n"
        '  .aggregate "std.ArrayList(' + IDENTITY + ')::DataFields" ⟨24, 8⟩\n'
        "    [" + terms + "]\n\nend Compiler.Extraction.RepresentativeArray\n").encode()
    owner_constants = """def allocatorOffset : Nat := 0
def allocatorLayout : Compiler.ZigAir.Memory.Layout := ⟨16, 8⟩
def representativesOffset : Nat := 16
def representativesLayout : Compiler.ZigAir.Memory.Layout := ⟨24, 8⟩
def representativesStorageLayout (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Layout := ⟨if runtimeSafety then 32 else 24, 8⟩
def representativesLockOffset : Nat := 40
def expressionsOffset (runtimeSafety : Bool) : Nat := if runtimeSafety then 48 else 40
def expressionsLayout (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Layout := ⟨if runtimeSafety then 24 else 16, 8⟩"""
    owner_regions = "(allocatorOffset, allocatorLayout), (representativesOffset, representativesStorageLayout runtimeSafety), (expressionsOffset runtimeSafety, expressionsLayout runtimeSafety)"
    owner_program = ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.Extraction.RepresentativeArrayLayout\n"
        "import Compiler.Extraction.ExpressionMapLayout\n\nnamespace Compiler.Extraction.RepresentativeArray.Owner\n\n"
        "-- Complete captured owner metadata; allocator/cache contents and native initialization remain open.\n"
        "-- Runtime safety selects the captured Debug/ReleaseSafe layout; false selects ReleaseFast.\n"
        "-- Each native mode must match its captured extent; this is not an ABI rule for other builds.\n"
        "-- Source SHA-256: " + hashlib.sha256(source).hexdigest() + "\n"
        + "\n".join("-- std/" + name + " SHA-256: " + value for name, value in sorted(graph.STD.items())) + "\n"
        "def layout (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Layout := ⟨if runtimeSafety then 72 else 56, 8⟩\n"
        'def allocationType (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Ty := .record "src/libevmasm/expression_classes.zig::ExpressionClasses" (layout runtimeSafety)\n'
        + owner_constants + "\n\n"
        "def regions (runtimeSafety : Bool) : List (Nat × Compiler.ZigAir.Memory.Layout) :=\n  [" + owner_regions + "]\n\n"
        "-- Decompose the native representative field into its data prefix and lock suffix.\n"
        "-- This groups the same captured leaves; it adds no storage or native allocation.\n"
        "def viewType (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Ty :=\n"
        '  .aggregate "src/libevmasm/expression_classes.zig::ExpressionClasses" (layout runtimeSafety)\n'
        '    ([(allocatorOffset, .object (.record "mem.Allocator" allocatorLayout)),\n'
        "      (representativesOffset, .object Compiler.Extraction.RepresentativeArray.allocationType)] ++\n"
        "      (if runtimeSafety then [(representativesLockOffset, .object Compiler.Extraction.ExpressionMap.lockType)] else []) ++\n"
        '      [(expressionsOffset runtimeSafety, .object (Compiler.Extraction.ExpressionMap.allocationType runtimeSafety))])\n\n'
        "end Compiler.Extraction.RepresentativeArray.Owner\n").encode()
    return {OUTPUT: header_program, OWNER_OUTPUT: owner_program, CACHE_OUTPUT: cache_program}


def generate(record, lib, source=None):
    return programs(record, lib, source)[OUTPUT]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", type=Path)
    parser.add_argument("--zig-lib-dir", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = args.profile.read_bytes()
    require(len(raw) <= 16384, "representative array profile exceeds admission bound")
    for path, generated in programs(json.loads(raw), args.zig_lib_dir).items():
        if args.check:
            require(generated == path.read_bytes(), "representative layout/source admission changed: " + path.name)
        else:
            path.write_bytes(generated)
