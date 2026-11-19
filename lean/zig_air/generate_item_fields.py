#!/usr/bin/env python3
"""Admit complete AssemblyItem field metadata for its existing allocation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from extract_assembly_item import member_body
from extract_storage import function, struct_member
from extract_cache import opcode_values, OPCODES
from generate_item_layout import checked_fields, checked_layout, generate as nominal, OUTPUT as NOMINAL, require

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "src/libevmasm/assembly_item.zig"
OUTPUT = ROOT / "lean/Compiler/Extraction/AssemblyItemFieldLayout.lean"
DEBUG_SOURCE = ROOT / "src/liblangutil/debug_data.zig"
LOCATION_SOURCE = ROOT / "src/liblangutil/source_location.zig"
ITEM = "libevmasm.assembly_item."
ITEM_TAGS = ("UndefinedItem", "Operation", "Push", "PushTag", "PushSub", "PushSubSize", "PushProgramSize", "Tag",
             "PushData", "PushLibraryAddress", "PushDeployTimeAddress", "PushImmutable", "AssignImmutable", "VerbatimBytecode")
JUMP_TAGS = ("Ordinary", "IntoFunction", "OutOfFunction")



FIELDS = {
    "item_type": (ITEM + "AssemblyItemType", 4, 4, ".scalar (.int true 32)"),
    "instruction_value": ("?libevmasm.instruction.Instruction", 2, 1, ".object (.optionalScalar (.int false 8))"),
    "data_value": ("u256", 32, 16, ".scalar (.int false 256)"),
    "verbatim": ("?" + ITEM + "VerbatimBytecode", 40, 8, ".object verbatimOptionalType"),
    "debug_data": ("liblangutil.debug_data.DebugData", 64, 8, ".object debugDataType"),
    "jump_type": (ITEM + "JumpType", 4, 4, ".scalar (.int true 32)"),
    "pushed_value": ("?u256", 48, 16, ".object (.optionalScalar (.int false 256))"),
    "immutable_occurrences": ("?usize", 16, 8, ".object (.optionalScalar (.int false 64))"),
    "modifier_depth": ("usize", 8, 8, ".scalar (.int false 64)"),
}


NESTED = {
    "source_location": ("liblangutil.source_location.SourceLocation", 24, 8, "sourceLocationType", {
        "start": ("i32", 4, 4, ".scalar (.int true 32)"),
        "end": ("i32", 4, 4, ".scalar (.int true 32)"),
        "source_name": ("?[]const u8", 16, 8, ".object sourceNameType"),
    }),
    "verbatim": (ITEM + "VerbatimBytecode", 32, 8, "verbatimType", {
        "arguments": ("usize", 8, 8, ".scalar (.int false 64)"),
        "return_variables": ("usize", 8, 8, ".scalar (.int false 64)"),
        "data": ("[]u8", 16, 8, ".slice true (.int false 8)"),
    }),
    "debug_data": ("liblangutil.debug_data.DebugData", 64, 8, "debugDataType", {
        "native_location": ("liblangutil.source_location.SourceLocation", 24, 8, ".object sourceLocationType"),
        "origin_location": ("liblangutil.source_location.SourceLocation", 24, 8, ".object sourceLocationType"),
        "ast_id": ("?i64", 16, 8, ".object (.optionalScalar (.int true 64))"),
    }),
}


def nested_declarations(records):
    require(type(records) is dict and records.keys() == NESTED.keys(), "incomplete nested item inventory")
    declarations = ["def sourceNameType : Compiler.ZigAir.Memory.Ty := .optionalObject (.slice false (.scalar (.int false 8))) ⟨16, 8⟩"]
    for name, (native, size, alignment, definition, fields) in NESTED.items():
        record = records[name]
        require(type(record) is dict and record.keys() == {"type", "bytes", "alignment", "fields"} and
                record["type"] == native and type(record["bytes"]) is int and record["bytes"] == size and
                type(record["alignment"]) is int and record["alignment"] == alignment, "unsupported nested item layout")
        admitted = checked_fields(record["fields"], size, alignment, fields)
        declarations += ["def " + name + "_" + field + "Offset : Nat := " + str(offset) for offset, _, field, _ in admitted]
        entries = ", ".join("(" + str(offset) + ", " + term + ")" for offset, _, _, term in admitted)
        declarations.append('def ' + definition + ' : Compiler.ZigAir.Memory.Ty :=\n  .aggregate "' + native + '" ⟨' +
                            str(size) + ', ' + str(alignment) + '⟩ [' + entries + ']')
    declarations.append("def verbatimOptionalType : Compiler.ZigAir.Memory.Ty := .optionalObject verbatimType ⟨40, 8⟩")
    return "\n".join(declarations)


def bind_nested_sources(source, debug, location):
    function(source, 'const DebugData =').expect('@import("../liblangutil/debug_data.zig").DebugData;')
    function(debug, 'const SourceLocation =').expect('@import("source_location.zig").SourceLocation;')
    # Only declarations/defaults are admitted here. No create/eql body claim is made.
    struct_member(debug, 'pub const DebugData =',
                  'native_location: SourceLocation = .{}, origin_location: SourceLocation = .{}, ast_id: ?i64 = null,',
                  'create', 'pub fn create(allocator: std.mem.Allocator, native_location: SourceLocation, origin_location: SourceLocation, ast_id: ?i64,) !*const DebugData')
    struct_member(location, 'pub const SourceLocation =',
                  'start: i32 = -1, end: i32 = -1, source_name: ?[]const u8 = null,',
                  'eql', 'pub fn eql(self: SourceLocation, other: SourceLocation) bool')


def checked_tags(record, names):
    require(isinstance(record, dict) and set(record) == {"type", "values"} and record["type"] == "c_int",
            "unsupported native enum tag")
    values = record["values"]
    require(isinstance(values, list) and len(values) == len(names), "incomplete native enum inventory")
    for index, (entry, name) in enumerate(zip(values, names)):
        require(isinstance(entry, dict) and set(entry) == {"name", "value"} and entry["name"] == name and
                type(entry["value"]) is int and entry["value"] == index, "native enum value changed")


def generate(record, source=None, instructions=None, debug=None, location=None):
    source = SOURCE.read_bytes() if source is None else source
    instructions = OPCODES.read_bytes() if instructions is None else instructions
    debug = DEBUG_SOURCE.read_bytes() if debug is None else debug
    location = LOCATION_SOURCE.read_bytes() if location is None else location
    bind_nested_sources(source, debug, location)
    opcode_values(instructions)  # Reuse the complete enum parser.
    enum = function(instructions, "pub const Instruction = enum(u8)").items
    end = enum.index("}")
    require(enum[end - 2:end] == ["_", ","] and enum[:end].count("_") == 1,
            "instruction optional requires the reviewed non-exhaustive byte enum")
    # Reuse the complete member/field scanner, including fields after methods.
    body = member_body(source, "initPush", "pub fn initPush(value: u256, debug_data: DebugData) AssemblyItem")
    body.expect("return initType(.Push, value, debug_data);")
    require(body.pos == len(body.items), "unreviewed initPush suffix")
    for name, tags in (("AssemblyItemType", ITEM_TAGS), ("JumpType", JUMP_TAGS)):
        function(source, "pub const " + name + " =").expect("enum(c_int) { " + ", ".join(tags) + ", };")
    require(isinstance(record, dict) and set(record) == {"schema", "target", "fields", "itemTag", "jumpTag", "instruction", "integerOptionals", "nested", "observations"} and
            record["schema"] == "oksolc.assembly-item-fields.v5", "unsupported item field profile")
    size, alignment = checked_layout(record["target"], "oksolc.assembly-item-layout.v1", ITEM + "AssemblyItem")
    require(nominal(record["target"]) == NOMINAL.read_bytes(), "item fields differ from admitted nominal extent")
    require(type(record["instruction"]) is dict and record["instruction"].keys() == {"type", "tagType", "exhaustive"} and
            record["instruction"]["type"] == "libevmasm.instruction.Instruction" and
            record["instruction"]["tagType"] == "u8" and record["instruction"]["exhaustive"] is False,
            "unsupported instruction optional child")
    children = record["integerOptionals"]
    require(type(children) is dict and children.keys() == {"pushed_value", "immutable_occurrences", "ast_id"},
            "incomplete optional integer inventory")
    for name, native, bits, signed in (("pushed_value", "u256", 256, False), ("immutable_occurrences", "usize", 64, False), ("ast_id", "i64", 64, True)):
        child = children[name]
        require(type(child) is dict and child.keys() == {"type", "bits", "signed"} and
                child["type"] == native and type(child["bits"]) is int and child["bits"] == bits and child["signed"] is signed,
                "unsupported optional integer child")
    nested = nested_declarations(record["nested"])
    checked_tags(record["itemTag"], ITEM_TAGS)
    checked_tags(record["jumpTag"], JUMP_TAGS)
    admitted = checked_fields(record["fields"], size, alignment, FIELDS)
    offsets = "\n".join("def " + name + "Offset : Nat := " + str(offset) for offset, _, name, _ in admitted)
    fields = ",\n    ".join("(" + str(offset) + ", " + term + ")" for offset, _, _, term in admitted)
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
            "import Compiler.Extraction.AssemblyItemLayout\n\nnamespace Compiler.Extraction.AssemblyItem\n\n"
            "-- Complete nested declarations; optional payloads are atomic typed values.\n"
            "-- This declares allocation geometry, not initialized native values.\n"
            "-- Source SHA-256: " + hashlib.sha256(source).hexdigest() + "\n"
            "-- Instruction source SHA-256: " + hashlib.sha256(instructions).hexdigest() + "\n"
            "-- Debug source SHA-256: " + hashlib.sha256(debug).hexdigest() + "\n"
            "-- Source-location SHA-256: " + hashlib.sha256(location).hexdigest() + "\n" + offsets + "\n\n" + nested + "\n\n"
            "def itemTagValues : List Int := [" + ", ".join(map(str, range(len(ITEM_TAGS)))) + "]\n"
            "def jumpTagValues : List Int := [" + ", ".join(map(str, range(len(JUMP_TAGS)))) + "]\n\n"
            "def viewType : Compiler.ZigAir.Memory.Ty :=\n"
            '  .aggregate "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨' + str(size) + ", " + str(alignment) + "⟩\n"
            "    [" + fields + "]\n\nend Compiler.Extraction.AssemblyItem\n").encode()


def check_observations(record):
    expected = {
        "operation": {"kind": 1, "opcode": 1, "data": 0, "jump": 0, "modifier": 0},
        "pushed": {"kind": 2, "opcodeAbsent": True, "data": 2**255 + 17, "jump": 2, "modifier": 19},
    }
    # Strict JSON types: bool must not impersonate the native integer one.
    actual = record.get("observations")
    require(isinstance(actual, dict) and actual.keys() == expected.keys() | {"optionalInstructions", "optionalIntegers", "verbatim", "debug", "initializers"}, "incomplete native item observations")
    for name, values in expected.items():
        row = actual[name]
        require(isinstance(row, dict) and row.keys() == values.keys() and
                all(type(row[k]) is type(v) and row[k] == v for k, v in values.items()), "native item observation changed")
    values = actual["optionalInstructions"]
    require(isinstance(values, list) and len(values) == 257 and values[0] is None and
            all(type(value) is int and value == index for index, value in enumerate(values[1:])),
            "native optional instruction observations changed")
    integers = actual["optionalIntegers"]
    require(type(integers) is list and len(integers) == 8, "incomplete optional integer observations")
    for row in integers:
        require(type(row) is dict and row.keys() == {"pushed_value", "immutable_occurrences"},
                "incomplete optional integer observation")
    for name, bits in (("pushed_value", 256), ("immutable_occurrences", 64)):
        expected_values = [None, 0, 1, 2**(bits - 1), 2**(bits - 1) + 17, 2**bits - 1, None, 0]
        require(all(type(row[name]) is type(value) and row[name] == value for row, value in zip(integers, expected_values)),
                "native optional integer observations changed")

    expected_verbatim = [None, {"arguments": 0, "returns": 0, "data": {"offset": 2, "length": 0}},
                        {"arguments": 3, "returns": 2, "data": {"offset": 1, "length": 3}},
                        {"arguments": 2**64 - 1, "returns": 2**64 - 1, "data": {"offset": 0, "length": 6}},
                        None, {"arguments": 1, "returns": 0, "data": {"offset": 5, "length": 0}}]
    expected_debug = [{"native": {"start": -1, "end": -1, "source": None},
                       "origin": {"start": -1, "end": -1, "source": None}, "ast_id": None}]
    for index, identity in enumerate([0, -1, -(2**63), 2**63 - 1, 17, None, 0], 1):
        expected_debug.append({"native": {"start": -1, "end": 17, "source": None if index == 6 else {"offset": 2, "length": 3}},
                               "origin": {"start": -(2**31), "end": 2**31 - 1, "source": {"offset": 7, "length": 0}},
                               "ast_id": identity})
    expected_initializers = [
        {"kind": kind, "instruction": instruction, "data": data, "verbatim": None,
         "debug": expected_debug[debug], "jump": 0, "pushed": None, "immutable": None, "modifier": 0}
        for kind, instruction, data, debug in ((2, None, 0, 0), (2, None, 2**256 - 1, 4),
                                              (2, None, 2**255 + 17, 2), (1, 0, 0, 0), (1, 1, 0, 1), (1, 255, 0, 3))]
    # Canonical JSON equality keeps integer, boolean, null and collection shapes distinct.
    for name, expected_rows in (("verbatim", expected_verbatim), ("debug", expected_debug), ("initializers", expected_initializers)):
        require(json.dumps(actual[name], sort_keys=True) == json.dumps(expected_rows, sort_keys=True),
                "native compound item observations changed: " + name)


def check_profile(record):
    require(generate(record) == OUTPUT.read_bytes(), "native item fields differ from admitted declaration")
    check_observations(record)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = args.profile.read_bytes()
    require(len(raw) <= 16384, "item field profile exceeds admission bound")
    record = json.loads(raw)
    if args.check:
        check_profile(record)
    else:
        check_observations(record)
        OUTPUT.write_bytes(generate(record))
