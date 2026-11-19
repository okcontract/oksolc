#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Bind the owned-key interpreter to the closed publishOwned profile shared with
storage/interner admission. Hash-map and allocator primitive refinement remains
explicit; any change to this profile requires a new reviewed extraction.
"""
import argparse
import hashlib
from extract_storage import SOURCE, ROOT, check_publication

OUTPUT = ROOT / 'lean/Compiler/Extraction/OwnedKeysProgram.lean'


def extract(data):
    check_publication(data)
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.OwnedKeys\n\nnamespace Compiler.Extraction.OwnedKeys\n\n'
        '-- Exact publishOwned profile admitted by storage and interner extraction.\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        'def publicationCode : Code := { releaseExisting := true, replaceKey := true, value := .input }\n\n'
        'end Compiler.Extraction.OwnedKeys\n').encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    result = extract(SOURCE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != result:
            p.error('owned-key extraction is stale; review source and proofs')
    else:
        OUTPUT.write_bytes(result)


if __name__ == '__main__':
    main()
