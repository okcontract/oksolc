#!/usr/bin/env python3
"""Regression controls for coverage claims and production inventory drift.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
import unittest

import check_verification_map as coverage


class CoverageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.document = json.loads(coverage.MAP.read_bytes())
        cls.sources = {}

    def read(self, path):
        if path not in self.sources:
            self.sources[path] = (coverage.ROOT / path).read_bytes()
        return self.sources[path]

    def check(self, document=None):
        return coverage.check(document or self.document, self.read)

    def reject(self, mutate, reason):
        document = copy.deepcopy(self.document)
        mutate(document)
        with self.assertRaisesRegex(ValueError, reason):
            self.check(document)

    def test_current_map_is_consistent_and_not_acceptance(self):
        report = self.check()
        self.assertEqual(report["registeredYulSteps"], 32)
        self.assertEqual(report["declaredClosedByKind"], {"artifact-route": 6, "contract": 4, "model": 2, "production-operation": 1})
        self.assertEqual(report["declaredClosedProductionOperations"], ["normalization.production"])
        self.assertFalse(report["wholeCompilerVerified"])
        self.assertFalse(report["proofReplayPerformed"])
        self.assertFalse(report["inventoryComplete"])
        self.assertEqual(report["next"], "normalization.recursiveBridge")

    def test_boundary_is_versioned(self):
        self.reject(lambda d: d["trustBoundary"]["assumptions"][0].update(contract="Assume every compiler is correct"), "trust boundary changed")
        self.reject(lambda d: d.update(boundaryVersion=1), "trust boundary changed")

    def test_migration_changes_only_the_host_toolchain_pin(self):
        assumptions = copy.deepcopy(self.document["trustBoundary"]["assumptions"])
        for assumption in assumptions:
            assumption["contract"] = assumption["contract"].replace("Zig 0.17", "Zig 0.16")
        encoded = json.dumps(assumptions, sort_keys=True, separators=(",", ":")).encode()
        self.assertEqual(coverage.digest(encoded), coverage.BOUNDARIES[1])

    def test_production_scopes_are_not_whole_entry_point_claims(self):
        report = self.check()
        entries = report["productionEntryPoints"]
        self.assertEqual(len(entries), len({(e["path"], e["symbol"]) for e in entries}))
        closed = [e for e in entries if e["scopes"]["closed"]]
        self.assertEqual({e["symbol"] for e in closed},
                         {"NormalizedArguments." + n for n in ("init", "takeOwned", "deinit")})
        find = next(e for e in entries if e["symbol"] == "ExpressionClasses.find")
        self.assertEqual(find["scopes"]["closed"], [])
        self.assertIn("normalization.recursiveBridge", find["scopes"]["partial"])
        self.assertIn("optimizer.graphMemory", find["scopes"]["partial"])
        def duplicate(document):
            record = next(r for r in document["obligations"] if r["id"] == "normalization.production")
            record["entryPoints"].append(dict(record["entryPoints"][0]))
        self.reject(duplicate, "duplicate entry point")

    def test_qualified_theorem_owner_is_checked(self):
        def wrong_owner(document):
            record = next(r for r in document["obligations"] if r["id"] == "optimizer.graphMemory")
            record["evidence"][0]["declaration"] = record["evidence"][0]["declaration"].replace("Valid.cleanup", "Invalid.cleanup")
        self.reject(wrong_owner, "missing declaration")

    def test_priorities_show_transitive_blockers_and_skip_closed_scopes(self):
        document = copy.deepcopy(self.document)
        document["priority"].insert(0, "normalization.production")
        report = self.check(document)
        self.assertEqual(report["next"], "normalization.recursiveBridge")
        self.assertEqual(report["priorityMilestones"][0]["remaining"], [])
        pending = report["priorityMilestones"][1]["remaining"]
        self.assertIn("normalization.recursiveBridge", pending)
        self.assertIn("optimizer.recursiveConstructors", pending)
        self.assertIn("optimizer.graphMemory", pending)
        self.assertIn("optimizer.itemClone", pending)
        self.assertNotIn("normalization.production", pending)
        document["priority"] = ["normalization.production"]
        self.assertIsNone(self.check(document)["next"])

    def test_completion_routes_keep_artifact_acceptance_scoped(self):
        routes = self.check()["completionRoutes"]
        self.assertIn("frontend.parsing", routes["implementation"]["remaining"])
        self.assertIn("optimizer.recursiveConstructors", routes["implementation"]["remaining"])
        self.assertFalse(routes["artifact-validator"]["currentArtifactValidated"])
        self.assertEqual({r["id"] for r in routes["artifact-validator"]["scopedRoutes"]},
                         set(self.document["finalClaim"]["scopedArtifactRoutes"]))
        self.assertTrue(all(r["status"] == "closed" and r["remaining"] == []
                            for r in routes["artifact-validator"]["scopedRoutes"]))

    def test_progress_is_independent_of_record_order(self):
        document = copy.deepcopy(self.document)
        document["obligations"].reverse()
        before, after = self.check(), self.check(document)
        for key in ("declaredObligationsByKind", "productionEntryPoints", "priorityMilestones", "completionRoutes"):
            self.assertEqual(before[key], after[key])

    def test_whole_compiler_and_inventory_cannot_be_promoted(self):
        self.reject(lambda d: d["finalClaim"].update(status="closed"), "no whole-compiler acceptance")
        self.reject(lambda d: d["inventory"].update(complete=True), "explicitly partial")

    def test_dependencies_and_connections_are_closed_and_acyclic(self):
        self.reject(lambda d: d["obligations"][0]["requires"].append("missing"), "unknown dependency")
        self.reject(lambda d: d["obligations"][0]["requires"].append("normalization.recursiveBridge"), "open dependency")
        self.reject(lambda d: d["obligations"][0]["requires"].append(d["obligations"][0]["id"]), "cyclic proof dependency")
        self.reject(lambda d: d["obligations"][0].update(finalConnection=d["obligations"][0]["id"]), "cyclic final connection")
        self.reject(lambda d: d["obligations"][0].update(finalConnection="missing"), "unknown final connection")

    def test_production_closure_requires_a_composed_theorem(self):
        def promote(d):
            record = next(r for r in d["obligations"] if r["id"] == "normalization.production")
            record.update(status="closed", supportedSemantics=["claimed complete normalization"],
                          evidence=copy.deepcopy(d["obligations"][0]["evidence"]))
        self.reject(promote, "needs a composed theorem")

    def test_references_assumptions_and_limits_remain_explicit(self):
        self.reject(lambda d: d["obligations"][0]["evidence"][0].update(declaration="Missing.theorem"), "missing declaration")
        self.reject(lambda d: d["obligations"][0]["evidence"][0].update(path="../outside.lean"), "escapes repository")
        self.reject(lambda d: d["obligations"][0]["assumptions"].append("assume.compilerCorrect"), "unknown assumption")
        self.reject(lambda d: d["obligations"][0].update(supportedSemantics=[]), "without scoped evidence")
        self.reject(lambda d: d["obligations"][0].update(unsupported=[]), "missing limitations")

    def test_artifact_route_is_independent_of_open_implementation(self):
        report = self.check()
        self.assertIn("frontend.lowering", report["openObligations"])
        self.assertIn("backend.lowering", report["openObligations"])
        self.assertEqual(report["declaredClosedByKind"]["artifact-route"], 6)
        self.assertEqual(self.document["finalClaim"]["scopedArtifactRoutes"],
                         ["artifact.solidityFunction", "artifact.solidityContract", "artifact.solidityStorage"])
        self.reject(lambda d: d["finalClaim"].update(scopedArtifactRoutes=["frontend.lowering"]), "unknown final artifact route")
        self.reject(lambda d: d["obligations"][-1].update(route="implementation"), "artifact route mislabeled")

    def test_registry_cannot_drop_or_promote_a_pass(self):
        self.reject(lambda d: d["registeredYulSteps"]["entries"].pop(), "inventory changed")
        self.reject(lambda d: d["registeredYulSteps"].update(status="closed"), "no preservation evidence")
        self.reject(lambda d: d["registeredYulSteps"]["entries"][0].update(abbreviation="!"), "inventory changed")

    def test_changed_production_registry_is_detected(self):
        path = self.document["registeredYulSteps"]["source"]
        original = self.read(path)
        variants = [
            (b"stepDescriptor(BlockFlattener, 'f'),", b"stepDescriptor(BlockFlattener, 'z'),", "inventory changed"),
            (b"stepDescriptor(BlockFlattener, 'f'),", b"unknownDescriptor(BlockFlattener, 'f'),", "unadmitted Yul registry row"),
            (b"stepDescriptor(BlockFlattener, 'f'),", b"stepDescriptor(BlockFlattener, 'l'),", "duplicate name"),
        ]
        for before, after, reason in variants:
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError, reason):
                changed = original.replace(before, after)
                coverage.check(self.document, lambda p: changed if p == path else self.read(p))


if __name__ == "__main__":
    unittest.main()
