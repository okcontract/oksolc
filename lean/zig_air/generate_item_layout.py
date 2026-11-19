#!/usr/bin/env python3
"""Admit a captured AssemblyItem allocation layout, without field semantics.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / 'lean/Compiler/Extraction/AssemblyItemLayout.lean'
FIELDS = {'schema', 'zigVersion', 'arch', 'os', 'osVersionRange', 'abi', 'cpu', 'cpuFeatures',
          'endianness', 'mode', 'backend', 'pointerBits', 'name', 'bytes', 'alignment'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checked_layout(record, schema, name):
    require(isinstance(record, dict) and record.keys() == FIELDS, 'unexpected layout profile fields')
    expected = {'schema': schema, 'zigVersion': '0.17.0',
                'arch': 'aarch64', 'os': 'macos', 'abi': 'none', 'endianness': 'little',
                'backend': 'stage2_llvm', 'pointerBits': 64, 'name': name}
    require(all(type(record[k]) is type(v) and record[k] == v for k, v in expected.items()),
            'unsupported native type, target or compiler')
    require(record['mode'] in ('Debug', 'ReleaseSafe', 'ReleaseFast'), 'unsupported native build mode')
    require(isinstance(record['cpu'], str) and re.fullmatch(r'[A-Za-z0-9_]+', record['cpu']) and
            len(record['cpu']) <= 128, 'invalid CPU model')
    features = record['cpuFeatures']
    require(isinstance(features, list) and 0 < len(features) <= 16 and
            all(type(v) is int and 0 <= v < 2**64 for v in features), 'invalid CPU features')
    version = record['osVersionRange']
    require(isinstance(version, dict) and version.keys() == {'semver'} and
            isinstance(version['semver'], dict) and version['semver'].keys() == {'min', 'max'}, 'invalid OS version range')
    versions = []
    for bound in ('min', 'max'):
        v = version['semver'][bound]
        require(isinstance(v, dict) and v.keys() == {'major', 'minor', 'patch', 'pre', 'build'} and
                all(type(v[k]) is int and 0 <= v[k] < 2**32 for k in ('major', 'minor', 'patch')) and
                v['pre'] is None and v['build'] is None, 'invalid OS semantic version')
        versions.append(tuple(v[k] for k in ('major', 'minor', 'patch')))
    require(versions[0] <= versions[1], 'reversed OS version range')
    size, alignment = record['bytes'], record['alignment']
    require(type(size) is int and type(alignment) is int and 0 < alignment <= size < 2**64 and
            alignment & (alignment - 1) == 0 and size % alignment == 0, 'invalid nonempty object extent')
    return size, alignment


def checked_fields(fields, size, alignment, expected):
    """Admit a complete closed field table, in deterministic byte-offset order."""
    require(isinstance(fields, list) and len(fields) == len(expected), 'incomplete native field inventory')
    seen, admitted = set(), []
    for field in fields:
        require(isinstance(field, dict) and set(field) == {'name', 'type', 'offset', 'bytes', 'alignment'},
                'malformed native field')
        name = field['name']
        require(isinstance(name, str) and name in expected and name not in seen, 'unknown or duplicate native field')
        seen.add(name)
        native, extent, aligned, term = expected[name]
        require(field['type'] == native and type(field['bytes']) is int and field['bytes'] == extent and
                type(field['alignment']) is int and field['alignment'] == aligned and type(field['offset']) is int and
                0 <= field['offset'] < size and field['offset'] + extent <= size and
                field['offset'] % aligned == 0 and alignment % aligned == 0, 'native field type/extent/alignment changed')
        admitted.append((field['offset'], extent, name, term))
    admitted.sort()
    require(all(a[0] + a[1] <= b[0] for a, b in zip(admitted, admitted[1:])), 'overlapping native fields')
    return admitted


def generate(record):
    size, alignment = checked_layout(record, 'oksolc.assembly-item-layout.v1', 'libevmasm.assembly_item.AssemblyItem')
    # CPU/OS-version/mode observations remain bound in the native run report.
    # This nominal type gives no rule for computing layouts on other builds;
    # every accepted native build must agree with this exact generated extent.
    return ('/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n'
            'import Compiler.ZigAir.MemoryTypes\n\n'
            'namespace Compiler.Extraction.AssemblyItem\n\n'
            '-- Captured Zig 0.17.0, aarch64/macos/none, little-endian, LLVM.\n'
            '-- Allocation extent only: native field projection is not admitted.\n'
            'def allocationType : Compiler.ZigAir.Memory.Ty :=\n'
            '  .record "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨' + str(size) + ', ' + str(alignment) + '⟩\n\n'
            'end Compiler.Extraction.AssemblyItem\n').encode()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('profile', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    raw = args.profile.read_bytes()
    if len(raw) > 16384:
        parser.error('layout profile exceeds admission limit')
    generated = generate(json.loads(raw))
    if args.check:
        if generated != OUTPUT.read_bytes():
            parser.error('captured item layout differs from the admitted allocation type')
    else:
        OUTPUT.write_bytes(generated)
