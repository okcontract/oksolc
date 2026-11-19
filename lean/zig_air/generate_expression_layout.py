#!/usr/bin/env python3
"""Admit every captured Expression field into the existing typed heap.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import extract_storage as storage
from generate_item_layout import checked_layout, checked_fields, require

ROOT = storage.SOURCE.parents[2]
OUTPUT = ROOT / "lean/Compiler/Extraction/ExpressionLayout.lean"
NATIVE = "libevmasm.expression_classes.Expression"
ITEM = "libevmasm.assembly_item.AssemblyItem"
FIELDS = {
    "id": ("u32", 4, 4, ".scalar (.int false 32)"),
    "item": ("*" + ITEM, 8, 8, None),
    "arguments": ("[]u32", 16, 8, ".slice true (.int false 32)"),
    "sequence_number": ("u32", 4, 4, ".scalar (.int false 32)"),
}


def generate(record, source=None):
    source = storage.SOURCE.read_bytes() if source is None else source
    storage.struct_member(source, "pub const Expression =",
        "id: Id, item: *AssemblyItem, arguments: []Id, sequence_number: u32 = 0,",
        "eql", "pub fn eql(self: *const Expression, other: *const Expression) bool")
    storage.extract(source)
    require(isinstance(record, dict) and set(record) == {"schema", "target", "fields", "item"} and
        record["schema"] == "oksolc.expression-field-layout.v1", "unsupported expression layout profile")
    size, alignment = checked_layout(record["target"], "oksolc.expression-layout.v1", NATIVE)
    item = record["item"]
    require(isinstance(item, dict) and set(item) == {"name", "bytes", "alignment"} and item["name"] == ITEM and
        type(item["bytes"]) is int and type(item["alignment"]) is int, "unsupported expression item target")
    # Reuse the independently captured item allocation type, rather than inventing
    # a second nominal pointer target for a descriptor's item field.
    from generate_item_layout import generate as item_layout, OUTPUT as item_output
    target = {**record["target"], "schema": "oksolc.assembly-item-layout.v1", **item}
    require(item_layout(target) == item_output.read_bytes(), "expression pointer target differs from admitted item layout")
    terms = {**FIELDS, "item": (*FIELDS["item"][:3],
        '.pointer true "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨' + str(item["bytes"]) + ', ' + str(item["alignment"]) + '⟩')}
    admitted = checked_fields(record["fields"], size, alignment, terms)
    definitions = "\n".join("def " + name + "Offset : Nat := " + str(offset) for offset, _, name, _ in admitted)
    typed = ",\n    ".join("(" + str(offset) + ", " + term + ")" for offset, _, _, term in admitted)
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.ZigAir.MemoryTypes\n\nnamespace Compiler.Extraction.Expression\n\n"
        "-- Complete captured Expression fields; item storage and graph/container correspondence remain open.\n"
        "-- Source SHA-256: " + hashlib.sha256(source).hexdigest() + "\n" + definitions + "\n\n"
        "def allocationType : Compiler.ZigAir.Memory.Ty :=\n"
        '  .aggregate "src/libevmasm/expression_classes.zig::Expression" ⟨' + str(size) + ", " + str(alignment) + "⟩\n"
        "    [" + typed + "]\n\nend Compiler.Extraction.Expression\n").encode()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = args.profile.read_bytes()
    require(len(raw) <= 16384, "expression layout profile exceeds admission bound")
    generated = generate(json.loads(raw))
    if args.check:
        require(generated == OUTPUT.read_bytes(), "expression layout/source admission changed")
    else:
        OUTPUT.write_bytes(generated)
