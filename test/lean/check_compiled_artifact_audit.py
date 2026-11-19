#!/usr/bin/env python3
"""Exercise compiled declaration audits with the actual pinned Lean compiler.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import copy
import json
import os
from pathlib import Path
import unittest

import compiler_artifacts as artifacts

MODULE = "CompiledAuditFixture"
SCHEMA = "oksolc.compiled-audit-regression.v1"
CLAIMS = [MODULE + ".identity"]


class CompiledAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.env, _, cls.tools = artifacts.gate.source.toolchain(cls.lean_bin, 1)
        cls.env["LEAN_PATH"] = str(cls.output) + os.pathsep + cls.env["LEAN_PATH"]
        cls.lean = [cls.tools["lean"]["path"], "-M4096", "-DwarningAsError=true"]
        code = ("import Lean.Elab.Command\nimport Contract.Check.Declarations\nnamespace " + MODULE + "\n"
                "theorem identity (n : Nat) : n = n := rfl\n"
                "def notTheorem : Nat := 3\n"
                "axiom untrusted : False\n"
                "theorem invalid : False := untrusted\n" +
                "\n".join(artifacts.audit_source(MODULE, CLAIMS, SCHEMA))).encode()
        (cls.output / (MODULE + ".lean")).write_bytes(code)
        cls.preflight = artifacts.gate.require_success(cls.output, "build", cls.lean +
            ["-o", str(cls.output / (MODULE + ".olean")), "--stdin"], cls.env, 60,
            data=code, cwd=artifacts.ROOT / "lean")
        code = artifacts.compiled_audit_source(MODULE, CLAIMS, SCHEMA)
        cls.compiled = artifacts.gate.require_success(cls.output, "audit", cls.lean + ["--stdin"],
            cls.env, 60, data=code, cwd=artifacts.ROOT / "lean")

    def test_exact_statement_dependency_axiom_parity(self):
        artifacts.matching_audit(self.preflight, self.compiled, CLAIMS, SCHEMA)
        self.assertEqual(self.preflight, self.compiled)

    def test_missing_declaration_rejects(self):
        self.reject("missing", "missing", b"Unknown constant")

    def test_definition_is_not_a_certificate(self):
        self.reject("definition", "notTheorem", b"not a theorem")

    def test_transitive_untrusted_axiom_rejects(self):
        self.reject("axiom", "invalid", b"disallowed axiom")

    def reject(self, name, claim, diagnostic):
        code = artifacts.compiled_audit_source(MODULE, [MODULE + "." + claim], SCHEMA)
        status = artifacts.gate.run(self.output, name, self.lean + ["--stdin"], self.env, 60,
                                   data=code, cwd=artifacts.ROOT / "lean")
        self.assertEqual(status, 1)
        self.assertIn(diagnostic, artifacts.gate.read(self.output, name + ".stdout"))

    def test_statement_dependency_and_permitted_axiom_changes_reject(self):
        original = json.loads(self.compiled)
        variants = []
        changed = copy.deepcopy(original)
        changed["claims"][0]["statement"] = {"different": True}
        variants.append(changed)
        changed = copy.deepcopy(original)
        changed["dependencies"].append("Nat.add")
        variants.append(changed)
        changed = copy.deepcopy(original)
        changed["axioms"] = ["Classical.choice"]
        variants.append(changed)
        for value in variants:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "differ"):
                artifacts.matching_audit(self.preflight, json.dumps(value).encode(), CLAIMS, SCHEMA)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    CompiledAuditTests.lean_bin, CompiledAuditTests.output = args.lean_bin, args.output.resolve()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(CompiledAuditTests))
    raise SystemExit(not result.wasSuccessful())
