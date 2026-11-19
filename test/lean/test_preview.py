"""The preview mutation must reach semantics, not a broken deployment binding.
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import copy
import unittest

import check_preview as preview


class PreviewTests(unittest.TestCase):
    def test_corruption_preserves_installed_image_and_changes_only_return(self):
        pair = preview.fixture()
        changed = preview.corrupted(pair)
        parsed, before, _ = preview.functions.artifact(*pair)
        _, after, _ = preview.functions.artifact(*changed)
        differences = [(a, b) for a, b in zip(before, after) if a != b]
        self.assertEqual(differences, [(0xf3, 0xfd)])
        self.assertTrue(preview.functions.creation_code(parsed, changed[1]).endswith(after))
        self.assertEqual(pair[0], changed[0])
        self.assertEqual(len(preview.negative_pairs([pair])), 1)

    def test_changed_native_artifact_cannot_reuse_retained_control(self):
        changed = copy.deepcopy(preview.fixture())
        changed[1]["contracts"]["Function.sol"]["Identity"]["evm"]["methodIdentifiers"]["identity(uint256)"] = "00000000"
        with self.assertRaisesRegex(ValueError, "artifacts changed"):
            preview.negative_pairs([changed])
