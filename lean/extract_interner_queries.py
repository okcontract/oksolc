#!/usr/bin/env python3
"""Bind the complete read-only query dependencies of physical find/forceEqual.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Reuse the existing item/key, opcode and representative profiles. This admits
source control over their value projection, not native descriptor field loads.
"""
import argparse
import hashlib

import extract_cache as cache
import extract_interner as interner
import extract_storage as storage
from extract_assembly_item import member_body

OUTPUT = cache.ROOT / 'lean/Compiler/Extraction/InternerQueryProgram.lean'


def boolean(p):
    value = p.pop()
    if value not in ('true', 'false'):
        raise storage.Unsupported('expected literal query result')
    return value


def extract(data, semantics, items, opcodes):
    # These existing admissions bind u32 IDs, c_int item tags, the source entry
    # capacity check, representative bounds and both complete caller bodies.
    cache.extract(data, semantics, items, opcodes)
    interner.extract(data)
    storage.extract(data)
    p = member_body(items, 'hasInstruction', 'pub fn hasInstruction(self: *const AssemblyItem) bool')
    p.expect('const should_have_instruction = self.item_type')
    comparison = p.pop()
    if comparison not in ('==', '!='):
        raise storage.Unsupported('unmodeled instruction-kind predicate')
    p.expect('.Operation;')
    checked = p.take('std')
    if checked:
        p.expect('.debug.assert(should_have_instruction == (self.instruction_value != null));')
    p.expect('return should_have_instruction;')
    if p.pos != len(p.items):
        raise storage.Unsupported('extra hasInstruction behavior')
    p = storage.function(semantics,
        'pub fn isDeterministic(item: *const AssemblyItemModule.AssemblyItem) error{AssemblyException}!bool')
    p.expect('{ if (item.item_type')
    verbatim = p.pop()
    if verbatim not in ('==', '!='):
        raise storage.Unsupported('unmodeled verbatim predicate')
    p.expect('.VerbatimBytecode) return error.AssemblyException; if (!item.hasInstruction()) return')
    plain = boolean(p)
    p.expect('; return switch (item.instruction_value.?) {')
    names = []
    while p.take('.'):
        name = p.ident()
        if name in names:
            raise storage.Unsupported('duplicate determinism opcode')
        names.append(name)
        p.expect(',')
    if not names:
        raise storage.Unsupported('missing determinism switch cases')
    p.expect('=>')
    selected = boolean(p)
    p.expect(', else =>')
    fallback = boolean(p)
    p.expect(', }; }')
    bindings = cache.opcode_values(opcodes)
    if any(name not in bindings for name in names):
        raise storage.Unsupported('unbound determinism opcode')
    hashes = '\n'.join('-- ' + name + ' SHA-256: ' + hashlib.sha256(raw).hexdigest()
        for name, raw in [('ExpressionClasses', data), ('SemanticInformation', semantics),
                          ('AssemblyItem', items), ('Instruction', opcodes)])
    return ('/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n'
        'import Compiler.Extraction.InternerQueryIR\n\nnamespace Compiler.Extraction.Interner.Queries\n\n' +
        hashes + '\n'
        'def determinismCode : Determinism := {\n  verbatim := 13, rejectOnVerbatim := ' +
        ('true' if verbatim == '==' else 'false') + ',\n  instructionTest := .' +
        ('operation' if comparison == '==' else 'notOperation') + ', checkShape := ' +
        ('true' if checked else 'false') + ', plain := ' + plain + ',\n  opcodes := [' +
        ', '.join(str(bindings[name]) for name in names) + '], selected := ' + selected +
        ', fallback := ' + fallback + ' }\n\nend Compiler.Extraction.Interner.Queries\n').encode()


def current():
    return extract(*(p.read_bytes() for p in (cache.SOURCE, cache.SEMANTICS, cache.ITEMS, cache.OPCODES)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generated = current()
    if args.check:
        if OUTPUT.read_bytes() != generated:
            parser.error('interner query extraction is stale')
    else:
        OUTPUT.write_bytes(generated)
