#!/usr/bin/env python3
"""Reject malformed or rebound private-header debug metadata.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Synthetic parser fixtures are not source admission or native acceptance.
"""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean/zig_air'))
import generate_map_bucket_storage as admission


def fixture(lib):
    return ('''target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-apple-macosx27.0.1-unknown"
!1 = !DIFile(filename: "std/hash_map.zig", directory: "''' + str(lib) + '''")
!2 = !DICompositeType(tag: DW_TAG_structure_type, name: "''' + admission.buckets.MAP + '''", file: !1)
!3 = !DICompositeType(tag: DW_TAG_structure_type, name: "''' + admission.HEADER + '''", scope: !2, file: !1, line: 1, size: 192, align: 64, elements: !4)
!4 = !{!5, !6, !7}
!5 = !DIDerivedType(tag: DW_TAG_member, name: "values", scope: !3, baseType: !8, size: 64, align: 64)
!6 = !DIDerivedType(tag: DW_TAG_member, name: "keys", scope: !3, baseType: !9, size: 64, align: 64, offset: 64)
!7 = !DIDerivedType(tag: DW_TAG_member, name: "capacity", scope: !3, baseType: !10, size: 32, align: 32, offset: 128)
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "[*]u32", scope: !2, baseType: !10, size: 64, align: 64)
!9 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "[*]''' + admission.buckets.KEY + '''", scope: !2, baseType: !11, size: 64, align: 64)
!10 = !DIBasicType(name: "u32", size: 32, encoding: DW_ATE_unsigned)
!11 = !DICompositeType(tag: DW_TAG_structure_type, name: "''' + admission.buckets.KEY + '''", size: 512, align: 128)
''').encode()


class HeaderTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.lib = Path(self.directory.name)
        (self.lib / 'std').mkdir()
        (self.lib / 'std/hash_map.zig').write_text('const Header = struct {\n};\n')
        self.raw = fixture(self.lib)

    def rejected(self, before, after):
        self.assertIn(before, self.raw)
        with self.assertRaises(ValueError): admission.header(self.raw.replace(before, after), self.lib)

    def test_complete_header(self):
        result = admission.header(self.raw, self.lib)
        self.assertEqual((result['bytes'], result['alignment']), (24, 8))
        self.assertEqual([f['offset'] for f in result['fields']], [0, 8, 16])

    def test_member_inventory(self):
        for values in (b'!{!5, !6}', b'!{!6, !5, !7}', b'!{!5, !5, !7}', b'!{!5, !6, !7, !7}'):
            self.rejected(b'!{!5, !6, !7}', values)

    def test_field_geometry_and_scope(self):
        for before, after in ((b'offset: 128', b'offset: 96'), (b'offset: 64)', b'offset: 65)'),
                              (b'size: 192', b'size: 160'), (b'scope: !3,', b'scope: !2,')):
            self.rejected(before, after)

    def test_pointer_permissions_and_children(self):
        for before, after in ((b'[*]u32', b'[*]const u32'), (b'baseType: !11', b'baseType: !10'),
                              (b'baseType: !8', b'baseType: !9'), (b'size: 512', b'size: 256')):
            self.rejected(before, after)

    def test_unknown_and_duplicate_attributes(self):
        for before, after in ((b'offset: 128)', b'offset: 128, flags: DIFlagBitField)'),
                              (b'offset: 128)', b'offset: 128, offset: 128)'),
                              (b'!4 = !{', b'!4 = !{}\n!4 = !{')):
            self.rejected(before, after)

    def test_missing_or_ambiguous_header(self):
        self.rejected(admission.HEADER.encode(), b'unknown.Header')
        line = next(line for line in self.raw.splitlines() if line.startswith(b'!3 ='))
        with self.assertRaises(ValueError): admission.header(self.raw + line.replace(b'!3 =', b'!12 =') + b'\n', self.lib)

    def test_source_binding(self):
        for before, after in ((b'std/hash_map.zig', b'../hash_map.zig'), (b'line: 1', b'line: 0'),
                              (b'line: 1', b'line: 500000')):
            self.rejected(before, after)

    def test_scalar_and_target(self):
        for before, after in ((b'DW_ATE_unsigned', b'DW_ATE_signed'), (b'aarch64-apple', b'x86_64-apple'),
                              (b'e-m:o-', b'E-m:o-')):
            self.rejected(before, after)

    def test_unparsed_or_missing_references(self):
        self.rejected(b'baseType: !10', b'baseType: !999')
        self.rejected(b'offset: 128)', b'offset: add(64, 64))')


class PackedMetadataTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.lib = Path(self.directory.name)
        (self.lib / 'std').mkdir()
        (self.lib / 'std/hash_map.zig').write_text('const Header = struct {\n};\nconst Metadata = ' + admission.METADATA_SOURCE + '\n};\n')
        self.raw = fixture(self.lib) + ('''!20 = !DICompositeType(tag: DW_TAG_structure_type, name: "''' + admission.METADATA + '''", scope: !2, file: !1, line: 3, size: 8, align: 8, elements: !21)
!21 = !{!22}
!22 = !DIDerivedType(tag: DW_TAG_member, name: "bits", scope: !20, baseType: !23, size: 8, align: 8)
!23 = !DIBasicType(name: "u8", size: 8, encoding: DW_ATE_unsigned)
''').encode()

    def test_complete_backing(self):
        result = admission.packed_metadata(self.raw, self.lib)
        self.assertEqual((result['bytes'], result['alignment'], result['backing'], result['usedBit']), (1, 1, 'u8', 7))

    def test_reject_geometry_and_inventory(self):
        for before, after in ((b'!21 = !{!22}', b'!21 = !{}'), (b'!21 = !{!22}', b'!21 = !{!22, !22}'),
                              (b'line: 3, size: 8', b'line: 3, size: 16'), (b'name: "bits"', b'name: "fingerprint"'),
                              (b'scope: !20,', b'scope: !2,'), (b'baseType: !23', b'baseType: !10'),
                              (b'name: "u8"', b'name: "i8"'), (b'line: 3,', b'line: 1,')):
            with self.subTest(before=before, after=after), self.assertRaises(ValueError):
                admission.packed_metadata(self.raw.replace(before, after), self.lib)

    def test_reject_source_bit_semantics(self):
        path = self.lib / 'std/hash_map.zig'; original = path.read_text()
        for before, after in (('const FingerPrint = u7;', 'const FingerPrint = u6;'),
                              ('used: u1 = 0,', 'used: u1 = 1,'), ('return self.used == 1;', 'return self.used == 0;'),
                              ('const free: FingerPrint = 0;', 'const free: FingerPrint = 2;')):
            path.write_text(original.replace(before, after))
            with self.assertRaises(ValueError): admission.packed_metadata(self.raw, self.lib)
        path.write_text(original)


if __name__ == '__main__':
    unittest.main()
