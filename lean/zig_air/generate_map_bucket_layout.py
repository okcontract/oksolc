#!/usr/bin/env python3
"""Bind native hash-map region geometry to the existing typed allocator.
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
import extract_graph_init
from generate_item_layout import checked_layout, checked_fields, require

ROOT = storage.SOURCE.parents[2]
OUTPUT = ROOT / 'lean/Compiler/Extraction/ExpressionMapBucketLayout.lean'
KEY_OUTPUT = ROOT / 'lean/Compiler/Extraction/ExpressionMapKeyLayout.lean'
KEY = 'libevmasm.expression_classes.ExpressionKey'
MAP = 'hash_map.Custom(' + KEY + ',u32,libevmasm.expression_classes.ExpressionKeyContext,80)'
MEM_SHA256 = 'db78007af4878dd75a0fc1c24f1fdb90f44f2d15c4c6177c43e388262a17a44e'
FIELDS = {
    'item_type': ('libevmasm.assembly_item.AssemblyItemType', 4, 4, '.scalar (.int false 32)'),
    'instruction': ('u8', 1, 1, '.scalar (.int false 8)'),
    'data': ('u256', 32, 16, '.scalar (.int false 256)'),
    'arguments': ('[]const u32', 16, 8, '.slice false (.int false 32)'),
    'sequence_number': ('u32', 4, 4, '.scalar (.int false 32)'),
}
ALLOCATE = '''{
    const header_align = @alignOf(Header);
    const key_align = if (@sizeOf(K) == 0) 1 else @alignOf(K);
    const val_align = if (@sizeOf(V) == 0) 1 else @alignOf(V);
    const max_align: Alignment = comptime .fromByteUnits(@max(header_align, key_align, val_align));
    const new_cap: usize = new_capacity;
    const meta_size = @sizeOf(Header) + new_cap * @sizeOf(Metadata);
    comptime assert(@alignOf(Metadata) == 1);
    const keys_start = std.mem.alignForward(usize, meta_size, key_align);
    const keys_end = keys_start + new_cap * @sizeOf(K);
    const vals_start = std.mem.alignForward(usize, keys_end, val_align);
    const vals_end = vals_start + new_cap * @sizeOf(V);
    const total_size = max_align.forward(vals_end);
    const slice = try allocator.alignedAlloc(u8, max_align, total_size);
    const ptr: [*]u8 = @ptrCast(slice.ptr);
    const metadata = ptr + @sizeOf(Header);
    const hdr = @as(*Header, @ptrCast(@alignCast(ptr)));
    if (@sizeOf([*]V) != 0) { hdr.values = @ptrCast(@alignCast((ptr + vals_start))); }
    if (@sizeOf([*]K) != 0) { hdr.keys = @ptrCast(@alignCast((ptr + keys_start))); }
    hdr.capacity = new_capacity;
    self.metadata = @ptrCast(@alignCast(metadata));
}'''


def source_binding(lib, source=None, native=None):
    source = storage.SOURCE.read_bytes() if source is None else source
    native = (Path(lib) / 'std/hash_map.zig').read_bytes() if native is None else native
    storage.function(source, 'const ExpressionKey =').expect('''struct {
        item_type: AssemblyItemType, instruction: u8, data: u256,
        arguments: []const Id, sequence_number: u32,
    };''')
    storage.function(source, 'const ExpressionMap =').expect(
        'std.HashMapUnmanaged(ExpressionKey, Id, ExpressionKeyContext, 80);')
    storage.function(native, 'const Header =').expect('struct { values: [*]V, keys: [*]K, capacity: Size, };')
    storage.function(native, 'fn allocate(self: *Self, allocator: Allocator, new_capacity: Size) Allocator.Error!void').expect(ALLOCATE)
    require(hashlib.sha256(native).hexdigest() == extract_graph_init.STD['hash_map.zig'], 'unreviewed hash-map source')
    require(hashlib.sha256((Path(lib) / 'std/mem.zig').read_bytes()).hexdigest() == MEM_SHA256,
            'unreviewed native alignment implementation')
    extract_graph_init.check_std(lib)
    return {'sourceSha256': hashlib.sha256(source).hexdigest(), 'hashMapSha256': hashlib.sha256(native).hexdigest()}


def fields(value, expected, label):
    require(type(value) is dict and set(value) == set(expected), label + ': unexpected fields')


def natural(value):
    return type(value) is int and 0 <= value < 2**64


def align(value, alignment):
    return (value + alignment - 1) // alignment * alignment


def geometry(capacity):
    keys = align(24 + capacity, 16)
    values = align(keys + capacity * 64, 4)
    return keys, values, align(values + capacity * 4, 16)


def check_profile(record):
    fields(record, ('schema', 'target', 'fields', 'metadata', 'value', 'cases'), 'bucket profile')
    require(record['schema'] == 'oksolc.expression-map-buckets.v1', 'wrong bucket schema')
    size, alignment = checked_layout(record['target'], 'oksolc.expression-key-layout.v1', KEY)
    require((size, alignment) == (64, 16), 'unreviewed key geometry')
    checked_fields(record['fields'], size, alignment, FIELDS)
    for field, name, size, alignment in (('metadata', MAP + '.Metadata', 1, 1), ('value', 'u32', 4, 4)):
        entry = record[field]
        fields(entry, ('name', 'bytes', 'alignment') +
               (('bits', 'backing', 'fingerprint_offset', 'used_offset') if field == 'metadata' else ()), field)
        if field == 'metadata':
            require(all(type(entry[k]) is int for k in ('bits', 'fingerprint_offset', 'used_offset')) and
                    (entry['bits'], entry['backing'], entry['fingerprint_offset'], entry['used_offset']) == (8, 'u8', 0, 7),
                    'unreviewed packed metadata backing')
        require(entry['name'] == name and type(entry['bytes']) is int and type(entry['alignment']) is int and
                (entry['bytes'], entry['alignment']) == (size, alignment), 'unreviewed ' + field + ' geometry')
    cases = record['cases']
    require(type(cases) is list and len(cases) == 4, 'incomplete bucket cases')
    summaries = []
    for case, count, capacity in zip(cases, (1, 7, 25, 100), (8, 16, 32, 128)):
        fields(case, ('requested_count', 'oom_error', 'oom_request', 'oom_capacity', 'oom_metadata',
            'reserve_error', 'insert_error', 'allocation', 'capacity', 'metadata', 'metadata_cleared', 'available', 'empty_lookup', 'index', 'key_pointer',
            'value_pointer', 'value', 'attempts', 'allocations', 'frees', 'resizes', 'remaps', 'released'), 'bucket case')
        integers = ('requested_count', 'oom_capacity', 'oom_metadata', 'capacity', 'metadata', 'index',
                    'key_pointer', 'value_pointer', 'value', 'attempts', 'allocations', 'frees', 'resizes', 'remaps', 'available')
        require(all(natural(case[k]) for k in integers), 'bucket case: invalid integer or missing entry')
        require(case['requested_count'] == count and case['capacity'] == capacity and case['index'] < capacity,
                'wrong bucket capacity or occupied slot')
        for key in ('oom_request', 'allocation', 'released'):
            fields(case[key], ('base', 'bytes', 'alignment'), key)
            require(all(natural(v) for v in case[key].values()), 'invalid region observation')
        keys, values, total = geometry(capacity)
        require(case['oom_error'] == 'OutOfMemory' and case['oom_request'] == {'base': 0, 'bytes': total, 'alignment': 16} and
                (case['oom_capacity'], case['oom_metadata']) == (0, 0), 'OOM changed the map or requested a different region')
        allocation = case['allocation']
        require(allocation['base'] > 0 and allocation['base'] % 16 == 0 and allocation['base'] + total <= 2**64 and
                (allocation['bytes'], allocation['alignment']) == (total, 16), 'wrong native bucket request')
        require(case['reserve_error'] is None and case['insert_error'] is None and case['value'] == 37,
                'native bucket reservation/insertion failed')
        require(case['metadata_cleared'] is True, 'native grow left nonzero or used metadata')
        require(case['available'] == capacity * 80 // 100, 'native grow has the wrong available count')
        require(case['empty_lookup'] is True, 'allocated empty map lookup did not miss')
        base, index = allocation['base'], case['index']
        require(case['metadata'] == base + 24 and case['key_pointer'] == base + keys + index * 64 and
                case['value_pointer'] == base + values + index * 4, 'native bucket component offsets disagree')
        require((case['attempts'], case['allocations'], case['frees'], case['resizes'], case['remaps']) == (2, 1, 1, 0, 0) and
                case['released'] == allocation, 'unexpected allocator calls or incomplete bucket release')
        summaries.append({'capacity': capacity, 'keysOffset': keys, 'valuesOffset': values, 'bytes': total, 'alignment': 16})
    return summaries


def key_layout(record, lib):
    source_binding(lib)
    check_profile(record)
    return key_layout_fields(record['fields'])


def key_layout_fields(native_fields):
    """Share the complete key layout between native observations and AIR capture."""
    members = checked_fields(native_fields, 64, 16, FIELDS)
    fields = ', '.join('(' + str(offset) + ', ' + term + ')' for offset, _, _, term in members)
    offsets = {field['name']: field['offset'] for field in native_fields}
    selectors = '\n'.join('  | .' + slot + ' => ' + str(offsets[native]) for slot, native in
                         (('kind', 'item_type'), ('instruction', 'instruction'), ('data', 'data'),
                          ('arguments', 'arguments'), ('sequence', 'sequence_number')))
    return ('''/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketLayout
import Compiler.Extraction.CacheIR

namespace Compiler.Extraction.ExpressionMap.Buckets

-- Complete native key field inventory from the existing three-mode capture.
-- The argument slice retains its constness and allocation identity; padding
-- is not a field or a readable byte representation.
def keyType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "''' + KEY + '''" ⟨64, 16⟩ [''' + fields + ''']

-- Bind field identity as well as type: two u32 fields may exchange offsets.
def KeyFields.offset : Compiler.Extraction.Cache.Field → Nat
''' + selectors + '''

end Compiler.Extraction.ExpressionMap.Buckets
''').encode()


def generate(record, lib, source=None, native=None):
    binding = source_binding(lib, source, native)
    check_profile(record)
    return ('''/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

namespace Compiler.Extraction.ExpressionMap.Buckets

-- Source-bound extent of the one aligned byte allocation. Component pointers
-- are observed without reading padding or copying private stdlib declarations.
-- This opaque allocation type admits no bucket/header/key field operations.
-- Initialization, ownership by a map, probing and release remain obligations.
-- Source SHA-256: ''' + binding['sourceSha256'] + '''
-- std/hash_map.zig SHA-256: ''' + binding['hashMapSha256'] + '''
-- std/mem.zig SHA-256: ''' + MEM_SHA256 + '''
def alignForward (value alignment : Nat) : Nat := (value + alignment - 1) / alignment * alignment
def headerBytes : Nat := 24
def metadataBytes : Nat := 1
def keyBytes : Nat := 64
def keyAlignment : Nat := 16
def valueBytes : Nat := 4
def valueAlignment : Nat := 4
def allocationAlignment : Nat := 16

def keysOffset (capacity : Nat) : Nat := alignForward (headerBytes + capacity * metadataBytes) keyAlignment
def valuesOffset (capacity : Nat) : Nat := alignForward (keysOffset capacity + capacity * keyBytes) valueAlignment
def bytes (capacity : Nat) : Nat := alignForward (valuesOffset capacity + capacity * valueBytes) allocationAlignment

def allocationType (capacity : Nat) : Compiler.ZigAir.Memory.Ty :=
  .record "std/hash_map.zig::aligned(ExpressionKey,u32)" ⟨bytes capacity, allocationAlignment⟩

end Compiler.Extraction.ExpressionMap.Buckets
''').encode()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('profile', type=Path)
    parser.add_argument('--zig-lib-dir', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--key-fields', action='store_true', help='generate the complete captured key view')
    args = parser.parse_args()
    raw = args.profile.read_bytes()
    require(len(raw) <= 32768, 'bucket profile exceeds admission bound')
    generated = (key_layout if args.key_fields else generate)(json.loads(raw), args.zig_lib_dir)
    target = KEY_OUTPUT if args.key_fields else OUTPUT
    if args.check:
        require(generated == target.read_bytes(), 'bucket layout/source admission changed')
    else:
        target.write_bytes(generated)
