#!/usr/bin/env python3
"""Admit the actual private Header from pinned LLVM debug type metadata.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

DICompositeType.elements and DIDerivedType.baseType/bit offsets supply the
complete field inventory (https://llvm.org/docs/LangRef.html#diderivedtype).
This is reviewed ABI admission, not a proof of the compiler or debug emitter.
The native region capture independently binds component pointers and extents.
"""
import argparse
import json
from pathlib import Path
import re
import generate_map_bucket_layout as buckets

require = buckets.require
OUTPUT = buckets.ROOT / 'lean/Compiler/Extraction/ExpressionMapBucketStorageLayout.lean'
HEADER = buckets.MAP + '.Header'
METADATA = buckets.MAP + '.Metadata'
ATTRIBUTE = re.compile(r'(\w+): ("[^"\\]*"|![0-9]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+)(?:, |$)')

METADATA_SOURCE = """packed struct {
        const FingerPrint = u7;
        const free: FingerPrint = 0; const tombstone: FingerPrint = 1;
        fingerprint: FingerPrint = free, used: u1 = 0,
        const slot_free: u8 = @bitCast(Metadata{ .fingerprint = free });
        const slot_tombstone: u8 = @bitCast(Metadata{ .fingerprint = tombstone });
        pub fn isUsed(self: Metadata) bool { return self.used == 1; }
        pub fn isTombstone(self: Metadata) bool { return @as(u8, @bitCast(self)) == slot_tombstone; }
        pub fn isFree(self: Metadata) bool { return @as(u8, @bitCast(self)) == slot_free; }
    """


def metadata(raw):
    require(len(raw) <= 64 * 1024 * 1024, 'LLVM capture exceeds admission bound')
    text = raw.decode('utf-8')
    targets = re.findall(r'^target triple = "([^"]*)"$', text, re.M)
    require(len(targets) == 1 and re.fullmatch(r'aarch64-apple-macosx[0-9.]+-unknown', targets[0]), 'wrong LLVM target')
    require(re.findall(r'^target datalayout = "([^"]*)"$', text, re.M) ==
            ['e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32'],
            'unreviewed LLVM data layout')
    nodes = {}
    for match in re.finditer(r'^(![0-9]+) = (.*)$', text, re.M):
        key, body = match.groups()
        require(key not in nodes, 'duplicate LLVM metadata identity')
        nodes[key] = body
    return nodes


def attributes(nodes, key, kind):
    body = nodes.get(key, '')
    require(body.startswith('!' + kind + '(') and body.endswith(')'), 'wrong LLVM metadata kind: ' + key)
    body = body[len(kind) + 2:-1]
    fields, cursor = {}, 0
    for match in ATTRIBUTE.finditer(body):
        require(match.start() == cursor and match[1] not in fields, 'unsupported or duplicate LLVM attribute')
        fields[match[1]] = match[2]
        cursor = match.end()
    require(cursor == len(body), 'unparsed LLVM attributes')
    return fields


def named(nodes, name):
    marker = 'name: ' + json.dumps(name) + ','
    found = [key for key, body in nodes.items() if body.startswith('!DICompositeType(') and marker in body]
    require(len(found) == 1, 'missing or ambiguous native type: ' + name)
    return found[0], attributes(nodes, found[0], 'DICompositeType')


def scoped_record(nodes, name, lib, bits, alignment, declaration):
    identity, value = named(nodes, name)
    require(set(value) == {'tag', 'name', 'scope', 'file', 'line', 'size', 'align', 'elements'} and
            value['tag'] == 'DW_TAG_structure_type' and (value['size'], value['align']) == (str(bits), str(alignment)),
            'unreviewed private declaration: ' + name)
    parent, _ = named(nodes, buckets.MAP)
    require(value['scope'] == parent, 'private declaration belongs to another map')
    file = attributes(nodes, value['file'], 'DIFile')
    require(set(file) == {'filename', 'directory'} and
            (Path(json.loads(file['directory'])) / json.loads(file['filename'])).resolve() ==
            (Path(lib) / 'std/hash_map.zig').resolve(), 'private declaration belongs to another source')
    line = int(value['line']); lines = (Path(lib) / 'std/hash_map.zig').read_text().splitlines()
    require(0 < line <= len(lines) and lines[line - 1].strip() == declaration,
            'private declaration source location changed')
    return identity, value


def header(raw, lib):
    nodes = metadata(raw)
    identity, value = scoped_record(nodes, HEADER, lib, 192, 64, 'const Header = struct {')
    members = nodes.get(value['elements'], '')
    require(re.fullmatch(r'!\{![0-9]+, ![0-9]+, ![0-9]+\}', members), 'incomplete header member inventory')
    result = []
    for key, name, offset, size, alignment, native in zip(re.findall(r'![0-9]+', members),
            ('values', 'keys', 'capacity'), (0, 64, 128), (64, 64, 32), (64, 64, 32),
            ('[*]u32', '[*]' + buckets.KEY, 'u32')):
        field = attributes(nodes, key, 'DIDerivedType')
        required = {'tag', 'name', 'scope', 'baseType', 'size', 'align'}
        require(set(field) in (required, required | {'offset'}) and field['tag'] == 'DW_TAG_member' and
                json.loads(field['name']) == name and field['scope'] == identity and
                (int(field.get('offset', 0)), int(field['size']), int(field['align'])) == (offset, size, alignment),
                'native header field changed: ' + name)
        if name == 'capacity':
            target = attributes(nodes, field['baseType'], 'DIBasicType')
            require(target == {'name': '"u32"', 'size': '32', 'encoding': 'DW_ATE_unsigned'}, 'wrong capacity type')
        else:
            target = attributes(nodes, field['baseType'], 'DIDerivedType')
            require(set(target) == {'tag', 'name', 'scope', 'baseType', 'size', 'align'} and
                    target['tag'] == 'DW_TAG_pointer_type' and json.loads(target['name']) == native and
                    (target['size'], target['align']) == ('64', '64'), 'wrong native header pointer')
            if name == 'values':
                child = attributes(nodes, target['baseType'], 'DIBasicType')
                require(child == {'name': '"u32"', 'size': '32', 'encoding': 'DW_ATE_unsigned'}, 'wrong value child')
            else:
                child_id, child = named(nodes, buckets.KEY)
                require(target['baseType'] == child_id and child['tag'] == 'DW_TAG_structure_type' and
                        (child['size'], child['align']) == ('512', '128'), 'wrong key child')
        result.append({'name': name, 'offset': offset // 8, 'bytes': size // 8, 'alignment': alignment // 8, 'type': native})
    return {'name': HEADER, 'bytes': 24, 'alignment': 8, 'fields': result}


def packed_metadata(raw, lib):
    """Bind the complete packed backing, not an invented record/byte alias.

    Zig 0.17 gives packed structs their backing integer's ABI:
    https://ziglang.org/documentation/0.17.0/#packed-struct
    The pinned native source supplies the bit-field interpretation; this LLVM
    declaration independently supplies its actual one-byte backing leaf.
    """
    native = (Path(lib) / 'std/hash_map.zig').read_bytes()
    buckets.storage.function(native, 'const Metadata =').expect(METADATA_SOURCE)
    nodes = metadata(raw)
    identity, value = scoped_record(nodes, METADATA, lib, 8, 8, 'const Metadata = packed struct {')
    members = nodes.get(value['elements'], '')
    require(re.fullmatch(r'!\{![0-9]+\}', members), 'incomplete packed backing inventory')
    member = re.findall(r'![0-9]+', members)[0]
    field = attributes(nodes, member, 'DIDerivedType')
    require(set(field) == {'tag', 'name', 'scope', 'baseType', 'size', 'align'} and
            field['tag'] == 'DW_TAG_member' and field['name'] == '"bits"' and field['scope'] == identity and
            (field['size'], field['align']) == ('8', '8'), 'wrong packed backing leaf')
    backing = attributes(nodes, field['baseType'], 'DIBasicType')
    require(backing == {'name': '"u8"', 'size': '8', 'encoding': 'DW_ATE_unsigned'}, 'wrong packed backing integer')
    return {'name': METADATA, 'bytes': 1, 'alignment': 1, 'backing': 'u8',
            'fingerprintBits': 7, 'usedBit': 7, 'free': 0, 'tombstone': 1}


def generate(raw, lib):
    buckets.source_binding(lib)
    header(raw, lib)
    packed_metadata(raw, lib)
    return ('''/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapKeyLayout

namespace Compiler.Extraction.ExpressionMap.Buckets
open Compiler.ZigAir.Memory

-- Declared component regions use the captured key fields and packed-u8 backing.
def metadataType : Ty := .aggregate "''' + METADATA + '''" ⟨1, 1⟩ [(0, .scalar (.int false 8))]
def headerType : Ty := .aggregate "''' + HEADER + '''" ⟨24, 8⟩
  [(0, .object (.pointer true true (.scalar (.int false 32)))),
   (8, .object (.pointer true true keyType)), (16, .scalar (.int false 32))]
def storageFields (capacity : Nat) : List (Nat × Field) :=
  [(0, .object headerType), (24, .object (.array capacity metadataType)),
   (keysOffset capacity, .object (.array capacity keyType)),
   (valuesOffset capacity, .object (.array capacity (.scalar (.int false 32))))]
def storageType (capacity : Nat) : Ty :=
  .aggregate "std/hash_map.zig::aligned(ExpressionKey,u32)" ⟨bytes capacity, 16⟩ (storageFields capacity)

end Compiler.Extraction.ExpressionMap.Buckets
''').encode()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('llvm_ir', type=Path)
    parser.add_argument('--zig-lib-dir', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = generate(args.llvm_ir.read_bytes(), args.zig_lib_dir)
    if args.check: require(result == OUTPUT.read_bytes(), 'bucket storage admission changed')
    else: OUTPUT.write_bytes(result)
