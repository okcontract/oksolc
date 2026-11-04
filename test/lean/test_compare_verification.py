"""Synthetic retained-evidence fixtures; these are not proof certificates.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
from pathlib import Path
import tempfile
import unittest

import compare_verification as compare


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(compare.canonical(value))


def raw(path, data=b"synthetic fixture"):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return compare.sha(data)


def fixture(root, native=False):
    root.mkdir()
    receipt = {"status": "passed", "exitCode": 0, "resourceLimit": None, "seconds": 10,
               "peakSampledTreeRssBytes": 100, "rssLimitBytes": 200, "command": ["harness", "--output", str(root)]}
    write(root / "receipt.json", receipt)
    claim = {"theorem": "Fixture.claim", "statement": {"root": 0, "nodes": [{"value": "original"}]}}
    audit = {"schema": "oksolc.compiler-word-audit.v1", "claims": [claim], "axioms": ["propext"], "dependencies": ["Fixture.body"]}
    report = {"schema": "oksolc.compiler-word-verification.v1", "status": "passed", "accepted": True,
              "freshPackage": True, "freshKernelReplay": True, "requestedCases": 1,
              "corpusRequested": True, "corpusComplete": True, "claims": ["Fixture.claim"], "axioms": ["propext"],
              "sourceSha256": {"source": "old"}, "tools": {}, "wholeCompilerVerified": False}
    batch = {"directory": ".", "cases": [0], "claims": ["Fixture.claim"], "axioms": ["propext"],
             "freshPackage": True, "freshKernelReplay": True,
             "proofSourceSha256": raw(root / "Artifact.lean"), "proofObjectSha256": raw(root / "Artifact.olean")}
    report["cases"] = [{"case": 0, "theorem": "Fixture.claim", "accepted": True,
                        "requestPath": str(root / "case-0.request.json"),
                        "requestSha256": raw(root / "case-0.request.json", b"{}"),
                        "responseSha256": raw(root / "case-0.response.json", b"{}") }]
    report["proofBatches"] = [batch]
    for phase in ("preflight", "fresh-build", "audit", "replay"):
        write(root / (phase + ".process.json"), {"status": "completed", "exitCode": 0, "seconds": 1,
                                                 "command": ["tool", "--fresh", "Fixture"]})
        raw(root / (phase + ".stderr"), b"")
    for name in ("preflight.stdout", "audit.stdout"):
        write(root / name, audit)
    report["negativeControls"] = []
    for name in ("wrong-value", "wrong-input"):
        report["negativeControls"].append({"case": name, "rejected": True, "exitCode": 1})
        prefix = root / ("negative-" + name)
        for suffix in (".stdin", ".stdout", ".stderr", ".pairs.json"):
            raw(Path(str(prefix) + suffix), name.encode())
        write(Path(str(prefix) + ".process.json"), {"status": "completed", "exitCode": 1, "seconds": 1})
    if native:
        report = {"schema": compare.NATIVE, "status": "passed", "memoryIdentityBoundaryVerified": True,
                  "auditedDeclarations": 1, "captures": [], "controls": [], "inputs": {"source": "old"}}
        claim.update(axioms=audit["axioms"], dependencies=audit["dependencies"])
        write(root / "audit.json", {"claims": [claim]})
        report["audit"] = {"claims": 1, "sha256": compare.sha((root / "audit.json").read_bytes())}
        proof = {"status": "passed", "freshKernelReplay": True, "replayIncludesImports": True,
                 "auditedDeclarations": ["Fixture.claim"], "phases": {name: {"status": "passed", "seconds": 1,
                 "command": ["tool", "--fresh", "Fixture"]} for name in ("build", "audit", "replay")}}
        write(root / "proof/report.json", proof)
        report["proofReportSha256"] = compare.sha((root / "proof/report.json").read_bytes())
        for name in proof["phases"]:
            raw(root / ("proof/" + name + ".stderr.txt"), b"")
        plan = []
        for name, expected in (("unchanged", True), ("mutation", False)):
            record = {"name": name, "expectedAcceptance": expected, "status": "passed", "seconds": 1,
                      "exitCode": 0 if expected else 1,
                      "sourceSha256": raw(root / (name + ".lean")),
                      "stdoutSha256": raw(root / (name + ".stdout"), b"" if expected else b"expected rejection"),
                      "stderrSha256": raw(root / (name + ".stderr"), b"")}
            write(root / (name + ".process.json"), record)
            report["controls"].append(record)
            plan.append({k: record[k] for k in ("name", "expectedAcceptance", "sourceSha256")})
        write(root / "control-plan.json", plan)
        matrix = {"status": "passed", "seconds": 2, "childUserSeconds": 1, "childSystemSeconds": 1,
                  "controls": [{"name": c["name"], "status": "passed"} for c in report["controls"]]}
        write(root / "control-matrix.json", matrix)
        report["controlMatrix"] = matrix
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            observation = {"mode": mode, "value": 123}
            write(root / ("observation-" + mode + ".json"), observation)
            report["captures"].append({"mode": mode, "observed": observation,
                "observationSha256": compare.sha((root / ("observation-" + mode + ".json")).read_bytes())})
        write(root / "fixture-interfaces/interfaces.json", [{"name": "Fixture.body", "value": "original"}])
        report["fixtureInterfaces"] = {"sha256": compare.sha((root / "fixture-interfaces/interfaces.json").read_bytes())}
    write(root / "report.json", report)
    return report


class ComparisonTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.before, self.after = self.root / "before", self.root / "after"
        self.left, self.right = fixture(self.before), fixture(self.after)

    def result(self):
        write(self.after / "report.json", self.right)
        return compare.compare(self.before / "report.json", self.after / "report.json",
                               self.before / "receipt.json", self.after / "receipt.json")

    def native(self):
        self.before, self.after = self.root / "native-before", self.root / "native-after"
        self.left, self.right = fixture(self.before, True), fixture(self.after, True)

    def change_audit(self, field, value):
        audit = json.loads((self.after / "audit.stdout").read_bytes())
        audit[field] = value
        for name in ("preflight.stdout", "audit.stdout"):
            write(self.after / name, audit)

    def test_relocated_run_is_equal_without_new_acceptance(self):
        result = self.result()
        self.assertEqual(result["status"], "equal")
        self.assertFalse(result["newAcceptance"])
        self.assertFalse(result["premiseDischarge"])

    def test_statement_change(self):
        self.change_audit("claims", [{"theorem": "Fixture.claim", "statement": {"newPremise": "assumeSuccess"}}])
        self.assertIn("statements", self.result()["changedCategories"])

    def test_permitted_axiom_change(self):
        self.change_audit("axioms", ["Classical.choice"])
        self.right["proofBatches"][0]["axioms"] = ["Classical.choice"]
        self.right["axioms"] = ["Classical.choice"]
        self.assertIn("axioms", self.result()["changedCategories"])

    def test_dependency_change(self):
        self.change_audit("dependencies", ["Fixture.otherBody"])
        self.assertIn("dependencies", self.result()["changedCategories"])

    def test_forbidden_axiom_is_incomplete(self):
        self.change_audit("axioms", ["sorryAx"])
        self.assertEqual(self.result()["status"], "incomplete")

    def test_control_reordering_remains_visible(self):
        self.right["negativeControls"].reverse()
        self.assertIn("controls", self.result()["changedCategories"])

    def test_removed_control_is_incomplete(self):
        self.right["negativeControls"].pop()
        self.assertEqual(self.result()["status"], "incomplete")

    def test_changed_control_source_is_visible(self):
        raw(self.after / "negative-wrong-value.stdin", b"different mutation")
        self.assertIn("controls", self.result()["changedCategories"])

    def test_wrong_source_hash_is_incomplete(self):
        raw(self.after / "Artifact.lean", b"tampered proof")
        self.assertEqual(self.result()["status"], "incomplete")

    def test_source_identity_change(self):
        self.right["sourceSha256"]["source"] = "new"
        self.assertIn("identities", self.result()["changedCategories"])

    def test_unknown_fields_and_json_types_remain_visible(self):
        self.right["futureScope"] = "a new assumption"
        self.assertIn("metadata", self.result()["changedCategories"])
        del self.right["futureScope"]
        self.right["wholeCompilerVerified"] = 0
        self.assertIn("metadata", self.result()["changedCategories"])

    def test_unknown_audit_fields_remain_visible(self):
        self.change_audit("newAssuranceFlag", True)
        self.assertIn("auditMetadata", self.result()["changedCategories"])

    def test_reported_strings_are_not_relocated(self):
        self.left["observedString"] = str(self.before / "data")
        self.right["observedString"] = str(self.after / "data")
        write(self.before / "report.json", self.left)
        self.assertIn("metadata", self.result()["changedCategories"])

    def test_timing_only_change(self):
        receipt = json.loads((self.after / "receipt.json").read_bytes())
        receipt["seconds"] = 20
        write(self.after / "receipt.json", receipt)
        result = self.result()
        self.assertEqual(result["status"], "equal")
        self.assertTrue(result["timingOnlyChange"])

    def test_missing_or_failed_receipt(self):
        (self.after / "receipt.json").unlink()
        self.assertEqual(self.result()["status"], "incomplete")
        write(self.after / "receipt.json", {"status": "failed", "exitCode": 1})
        self.assertEqual(self.result()["status"], "incomplete")

    def test_receipt_cannot_be_borrowed_from_another_run(self):
        raw(self.after / "receipt.json", (self.before / "receipt.json").read_bytes())
        self.assertEqual(self.result()["status"], "incomplete")

    def test_missing_replay_receipt(self):
        (self.after / "replay.process.json").unlink()
        self.assertEqual(self.result()["status"], "incomplete")

    def test_unknown_schema_and_incomplete_batch(self):
        self.right["schema"] = "future-schema"
        self.assertEqual(self.result()["status"], "incomplete")
        self.right["schema"] = self.left["schema"]
        self.right["proofBatches"][0]["freshKernelReplay"] = False
        self.assertEqual(self.result()["status"], "incomplete")

    def test_escaping_path_is_incomplete(self):
        self.right["proofBatches"][0]["directory"] = "../outside"
        self.assertEqual(self.result()["status"], "incomplete")

    def test_duplicate_fields_and_nonfinite_json_reject(self):
        for data in (b'{"x":1,"x":2}', b'{"x":NaN}', b'not json'):
            raw(self.before / "report.json", data)
            self.assertEqual(self.result()["status"], "incomplete")

    def test_changed_input_during_inspection_rejects(self):
        evidence = compare.Evidence(self.before / "report.json", self.before / "receipt.json")
        raw(self.before / "report.json", b"changed after read")
        with self.assertRaisesRegex(ValueError, "changed while reading"):
            evidence.finish()

    def test_native_self_comparison(self):
        self.native()
        self.assertEqual(self.result()["status"], "equal")

    def test_native_definition_change(self):
        self.native()
        path = self.after / "fixture-interfaces/interfaces.json"
        write(path, [{"name": "Fixture.body", "value": "changed"}])
        self.right["fixtureInterfaces"]["sha256"] = compare.sha(path.read_bytes())
        self.assertIn("definitions", self.result()["changedCategories"])

    def test_native_missing_observation(self):
        self.native()
        (self.after / "observation-Debug.json").unlink()
        self.assertEqual(self.result()["status"], "incomplete")

    def test_native_incomplete_replay(self):
        self.native()
        path = self.after / "proof/report.json"
        proof = json.loads(path.read_bytes()); proof["replayIncludesImports"] = False
        write(path, proof)
        self.right["proofReportSha256"] = compare.sha(path.read_bytes())
        self.assertEqual(self.result()["status"], "incomplete")

    def test_native_control_plan_and_receipts_are_required(self):
        self.native()
        self.right["controls"][1]["sourceSha256"] = "wrong"
        self.assertEqual(self.result()["status"], "incomplete")


if __name__ == "__main__":
    unittest.main()
