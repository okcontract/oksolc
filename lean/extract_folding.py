#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Source-bound constant folding. The dispatch's guards, indices, operations and
opcodes are executable data. Helper bodies have closed admission templates;
their generated integer semantics include the native safety preconditions.
"""
import argparse
import hashlib
from pathlib import Path
from extract_compiler import Unsupported
from extract_storage import function
from extract_cache import opcode_values

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src/libevmasm/rule_list.zig'
OPCODES = ROOT / 'src/libevmasm/instruction.zig'
OUTPUT = ROOT / 'lean/Compiler/Extraction/FoldingProgram.lean'

# Each template consumes the entire function, including overflow guards and
# loop updates. Unsupported changes reject instead of reusing a proof by hash.
HELPERS = [
    ('fn asSigned(value: u256) i256', '{ return @bitCast(value); }', ''),
    ('fn signedDivision(left: u256, right: u256) u256', '''{
        if (right == 0) return 0;
        const lhs = asSigned(left); const rhs = asSigned(right);
        if (lhs == std.math.minInt(i256) and rhs == -1) return left;
        return @bitCast(@divTrunc(lhs, rhs)); }''', '''
def signedDivision (left right : Word) : Result :=
  if right = 0 then .ok 0
  else if left.toInt = -(2 ^ 255) ∧ right.toInt = -1 then .ok left
  else Zig.divTrunc left right
'''),
    ('fn signedModulo(left: u256, right: u256) u256', '''{
        if (right == 0) return 0;
        const lhs = asSigned(left); const rhs = asSigned(right);
        if (rhs == 1 or rhs == -1) return 0;
        return @bitCast(@rem(lhs, rhs)); }''', '''
def signedModulo (left right : Word) : Result :=
  if right = 0 then .ok 0
  else if right.toInt = 1 ∨ right.toInt = -1 then .ok 0
  else Zig.rem left right
'''),
    ('fn wrappingPower(base_value: u256, exponent_value: u256) u256', '''{
        var base = base_value; var exponent = exponent_value; var result: u256 = 1;
        while (exponent != 0) : (exponent >>= 1) {
            if ((exponent & 1) != 0) result *%= base;
            base *%= base;
        } return result; }''', '''
def powerLoop : Nat → Word → Word → Word → Result
  | 0, _, exponent, result => if exponent = 0 then .ok result else .error .recursionLimit
  | fuel + 1, base, exponent, result =>
    if exponent = 0 then .ok result else
      powerLoop fuel (base * base) (exponent >>> 1)
        (if (exponent &&& 1) ≠ 0 then result * base else result)

def wrappingPower (base exponent : Word) : Result := powerLoop 256 base exponent 1
'''),
    ('fn byteValue(index: u256, value: u256) u256', '''{
        if (index >= 32) return 0;
        const shift: u8 = @intCast(8 * (31 - index));
        return (value >> shift) & 0xff; }''', '''
def byteValue (index value : Word) : Result := do
  if index.toNat ≥ 32 then return 0
  let distance ← Zig.checkedSub 31 index.toNat
  let wide ← Zig.checkedMul 256 8 distance
  let shift ← Zig.narrow 8 wide
  return (value >>> shift) &&& 255
'''),
    ('fn addMod(left: u256, right: u256, modulus: u256) u256', '''{
        if (modulus == 0) return 0;
        return @intCast((@as(u257, left) + @as(u257, right)) % @as(u257, modulus)); }''', '''
def addMod (left right modulus : Word) : Result := do
  if modulus = 0 then return 0
  let sum ← Zig.checkedAdd 257 (left.setWidth 257).toNat (right.setWidth 257).toNat
  let result ← Zig.narrow 256 (sum % (modulus.setWidth 257).toNat)
  return BitVec.ofNat 256 result
'''),
    ('fn mulMod(left: u256, right: u256, modulus: u256) u256', '''{
        if (modulus == 0) return 0;
        return @intCast((@as(u512, left) * @as(u512, right)) % @as(u512, modulus)); }''', '''
def mulMod (left right modulus : Word) : Result := do
  if modulus = 0 then return 0
  let product ← Zig.checkedMul 512 (left.setWidth 512).toNat (right.setWidth 512).toNat
  let result ← Zig.narrow 256 (product % (modulus.setWidth 512).toNat)
  return BitVec.ofNat 256 result
'''),
    ('fn signExtend(byte_index: u256, value: u256) u256', '''{
        if (byte_index >= 31) return value;
        const test_bit: u8 = @intCast(byte_index * 8 + 7);
        const mask = (@as(u256, 1) << test_bit) - 1;
        return if ((value & (@as(u256, 1) << test_bit)) != 0) value | ~mask else value & mask; }''', '''
def signExtend (index value : Word) : Result := do
  if index.toNat ≥ 31 then return value
  let times ← Zig.checkedMul 256 index.toNat 8
  let wide ← Zig.checkedAdd 256 times 7
  let testBit ← Zig.narrow 8 wide
  let high : Word := (1 : Word) <<< testBit
  let low ← Zig.checkedSub high.toNat 1
  let mask := BitVec.ofNat 256 low
  return if (value &&& high) ≠ 0 then value ||| ~~~mask else value &&& mask
'''),
    ('fn shiftLeft(amount: u256, value: u256) u256', '''{
        return if (amount >= 256) 0 else value << @intCast(amount); }''', '''
def shiftLeft (amount value : Word) : Result := do
  if amount.toNat ≥ 256 then return 0
  let shift ← Zig.narrow 8 amount.toNat
  return value <<< shift
'''),
    ('fn shiftRight(amount: u256, value: u256) u256', '''{
        return if (amount >= 256) 0 else value >> @intCast(amount); }''', '''
def shiftRight (amount value : Word) : Result := do
  if amount.toNat ≥ 256 then return 0
  let shift ← Zig.narrow 8 amount.toNat
  return value >>> shift
'''),
]

CALLS = {'signedDivision':'sdiv', 'signedModulo':'smod', 'wrappingPower':'exp',
         'byteValue':'byte', 'addMod':'addmod', 'mulMod':'mulmod', 'signExtend':'signextend',
         'shiftLeft':'shl', 'shiftRight':'shr'}
OPERATORS = {'+%':'add', '*%':'mul', '-%':'sub', '/':'div', '%':'mod', '&':'and', '|':'or', '^':'xor',
             '<':'lt', '>':'gt', '==':'eq'}


def number(p):
    value = p.pop()
    if not value.isascii() or not value.isdecimal():
        raise Unsupported('unsupported folder index or arity')
    return int(value)


def argument(p):
    p.expect('arguments[')
    result = number(p)
    p.expect(']')
    return result


def body(p):
    guard = 'none'
    if p.take('if'):
        p.expect('(')
        index = argument(p)
        p.expect('== 0)')
        value = number(p)
        if value >= 2**256:
            raise Unsupported('folder return exceeds word width')
        p.expect('else')
        guard = 'some (' + str(index) + ', ' + str(value) + ')'
    if p.peek() in CALLS:
        operation = CALLS[p.pop()]
        p.expect('(')
        indices = [argument(p)]
        while p.take(','):
            indices.append(argument(p))
        p.expect(')')
    elif p.take('~'):
        operation, indices = 'not', [argument(p)]
    else:
        boolean = p.take('@intFromBool')
        if boolean:
            p.expect('(')
        signed = p.take('asSigned')
        if signed:
            p.expect('(')
        first = argument(p)
        if signed:
            p.expect(')')
        token = p.pop()
        if token in ('+', '*', '-') and p.take('%'):
            token += '%'
        if token not in OPERATORS:
            raise Unsupported('unsupported folder operator')
        operation = OPERATORS[token]
        if signed:
            if not boolean or token not in ('<', '>'):
                raise Unsupported('unsupported signed comparison')
            operation = 's' + operation
            p.expect('asSigned(')
        if boolean and not signed and token == '==' and p.take('0'):
            operation, indices = 'iszero', [first]
        else:
            indices = [first, argument(p)]
        if signed:
            p.expect(')')
        if boolean:
            p.expect(')')
        if boolean != (operation in ('lt', 'gt', 'slt', 'sgt', 'eq', 'iszero')):
            raise Unsupported('folder boolean/word mismatch')
    return '{ op := .' + operation + ', indices := ' + str(indices) + ', zeroGuard := ' + guard + ' }'


def extract(data, opcodes):
    function(data, 'const std =').expect('@import("std");')
    function(data, 'const Instruction =').expect('@import("instruction.zig").Instruction;')
    bindings = opcode_values(opcodes)
    definitions = []
    for header, native, lean in HELPERS:
        function(data, header).expect(native)
        definitions.append(lean)
    p = function(data, 'fn foldConstants(instruction: Instruction, arguments: []const u256) ?u256')
    p.expect('{ return switch (instruction) {')
    clauses = []
    while p.take('.'):
        opcode = p.ident()
        if opcode not in bindings:
            raise Unsupported('unknown fold opcode')
        p.expect('=> if (arguments.len ==')
        arity = number(p)
        p.expect(')')
        expression = body(p)
        p.expect('else null,')
        clauses.append('  { opcode := ' + str(bindings[opcode]) + ', arity := ' + str(arity) + ', body := ' + expression + ' }')
    p.expect('else => null, }; }')
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.Folding\n\nnamespace Compiler.Extraction.Folding\nopen Contract.Yul\n\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n' + ''.join(definitions) +
        '\ndef helpers : Helpers := ⟨signedDivision, signedModulo, wrappingPower, byteValue, addMod, mulMod, signExtend, shiftLeft, shiftRight⟩\n\n'
        'def clauses : List Clause := [\n' + ',\n'.join(clauses) + ']\n\n'
        'end Compiler.Extraction.Folding\n').encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    output = extract(SOURCE.read_bytes(), OPCODES.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != output:
            p.error('constant-folder extraction is stale; review source and proofs')
    else:
        OUTPUT.write_bytes(output)


if __name__ == '__main__':
    main()
