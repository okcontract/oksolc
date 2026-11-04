#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admit binaryLogarithm, preserving short-circuiting, checked subtraction and
the target-dependent usize cast. The CTZ primitive uses Lean's bitvector model.
"""
import argparse
import hashlib
from extract_storage import function
from extract_folding import ROOT, SOURCE

OUTPUT = ROOT / 'lean/Compiler/Extraction/BinaryLogarithmProgram.lean'


def extract(data):
    function(data, 'pub fn binaryLogarithm(value: u256) ?usize').expect('''{
        if (value == 0 or (value & (value - 1)) != 0) return null;
        return @intCast(@ctz(value));
    }''')
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.BinaryLogarithm\n\nnamespace Compiler.Extraction.BinaryLogarithm\n'
        'open Contract.Yul\n\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n' + '''
def binaryLogarithm (usizeBits : Nat) (value : Word) : Except Folding.Fault (Option Nat) := do
  if value == 0 then return none
  let predecessor ← Folding.Zig.checkedSub value.toNat 1
  if value &&& BitVec.ofNat 256 predecessor != 0 then return none
  let count ← Folding.Zig.narrow usizeBits value.ctz.toNat
  return some count

end Compiler.Extraction.BinaryLogarithm
''').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(SOURCE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale binary-logarithm extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
