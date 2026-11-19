#!/usr/bin/env python3
"""Compare retained compiler verification evidence without granting acceptance.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Exit 0: equal compared evidence (timings may differ); 1: changes; 2: incomplete.
This checks retained receipts and bindings, not the truth of new proof premises.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re

from triage_evidence import comparison_digest, difference_message, first_difference

ARTIFACTS = {
    "oksolc.compiler-graph-verification.v2",
    "oksolc.compiler-graph-failure-verification.v1",
    "oksolc.compiler-word-verification.v1",
    "oksolc.compiler-contract-verification.v1",
    "oksolc.compiler-function-verification.v4",
    "oksolc.compiler-storage-verification.v4",
}
NATIVE = "oksolc.native-map-memory-acceptance.v1"
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
LIMIT = 64 * 1024**2


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON field: " + key)
        result[key] = value
    return result


class Evidence:
    def __init__(self, report, receipt):
        self.root = Path(report).resolve().parent
        self.inputs = {}
        self.report_path, self.receipt_path = Path(report).resolve(), Path(receipt).resolve()
        self.report, self.receipt = self.json(self.report_path), self.json(self.receipt_path)
        self.timing = {}

    def path(self, relative):
        path = (self.root / relative).resolve()
        require(path.is_relative_to(self.root), "evidence path escapes its run: " + str(relative))
        return path

    def raw(self, path):
        path = Path(path)
        with path.open("rb") as stream:
            raw = stream.read(LIMIT + 1)
        require(len(raw) <= LIMIT, "evidence exceeds read limit: " + str(path))
        digest = sha(raw)
        require(path not in self.inputs or self.inputs[path] == digest, "evidence changed while reading: " + str(path))
        self.inputs[path] = digest
        return raw

    def json(self, path):
        return json.loads(self.raw(path), object_pairs_hook=unique_object,
                          parse_constant=lambda value: (_ for _ in ()).throw(ValueError("non-finite JSON: " + value)))

    def bound(self, relative, digest):
        path = self.path(relative)
        require(sha(self.raw(path)) == digest, "changed retained bytes: " + str(relative))
        return path

    def process(self, relative, expected=0, status="completed"):
        value = self.json(self.path(relative + ".process.json"))
        require(value.get("status") == status and type(value.get("exitCode")) is int and
                value["exitCode"] == expected and not value.get("error"), "incomplete process: " + relative)
        seconds = value["seconds"]
        require(type(seconds) in (int, float) and math.isfinite(seconds) and seconds >= 0,
                "invalid phase time: " + relative)
        self.timing[relative] = seconds
        return value

    def normalize(self, value, field=None):
        # Relocate only paths rooted in this run; preserve tool/source identities
        # and all other values, including ordering and unknown report fields.
        if isinstance(value, dict):
            return {k: self.normalize(v, k) for k, v in value.items()}
        if isinstance(value, list):
            return [self.normalize(v, field) for v in value]
        if (field in {"requestPath", "directory", "path", "cwd", "command", "sourceFile"} and
                isinstance(value, str) and Path(value).is_absolute()):
            path = Path(value).resolve()
            if path.is_relative_to(self.root):
                return "<run>/" + str(path.relative_to(self.root))
        return value

    def finish(self):
        for path, digest in list(self.inputs.items()):
            require(sha(self.raw(path)) == digest, "evidence changed during comparison: " + str(path))
        return {"reportSha256": self.inputs[self.report_path], "receiptSha256": self.inputs[self.receipt_path],
                "inspectedFiles": len(self.inputs), "inspectionSha256": sha(canonical({
                    self.normalize(str(path), "path"): digest for path, digest in self.inputs.items()}))}


def audit_claims(audit, names, *, per_claim):
    claims = audit["claims"]
    require(names and len(set(names)) == len(names) and [r["theorem"] for r in claims] == names,
            "incomplete or duplicated declaration inventory")
    axioms = [r["axioms"] for r in claims] if per_claim else [audit["axioms"]]
    dependencies = [r["dependencies"] for r in claims] if per_claim else [audit["dependencies"]]
    require(all(isinstance(a, list) and set(a) <= AXIOMS for a in axioms) and all(dependencies),
            "invalid axiom or dependency audit")
    require(all("statement" in r for r in claims), "missing theorem statement")
    return ([{k: v for k, v in r.items() if k not in {"axioms", "dependencies"}} for r in claims], axioms, dependencies)


def artifact_view(e, view):
    r = e.report
    require(r.get("accepted") is True and r.get("freshPackage") is True and r.get("freshKernelReplay") is True,
            "artifact acceptance or fresh replay is incomplete")
    require(not r.get("corpusRequested") or r.get("corpusComplete") is True, "incomplete requested corpus")
    require(not r.get("unvalidatedCases"), "unvalidated cases remain")
    cases, batches = r["cases"], r["proofBatches"]
    require(cases and len(cases) == r["requestedCases"] and
            [c["case"] for c in cases] == list(range(len(cases))) and all(c.get("accepted") is True for c in cases),
            "incomplete case inventory")
    for i, case in enumerate(cases):
        for side in ("request", "response"):
            e.bound(f"case-{i}.{side}.json", case[side + "Sha256"])
    covered, names = [], []
    view["statements"], view["axioms"], view["dependencies"] = [], [], []
    view["auditMetadata"] = []
    for b in batches:
        prefix = b["directory"].rstrip("/") + "/"
        e.path(prefix)
        require(b.get("freshPackage") is True and b.get("freshKernelReplay") is True, "incomplete proof batch")
        e.bound(prefix + "Artifact.lean", b["proofSourceSha256"])
        e.bound(prefix + "Artifact.olean", b["proofObjectSha256"])
        audit = e.json(e.path(prefix + "audit.stdout"))
        require(audit.get("schema") == r["schema"].replace("-verification", "-audit"), "wrong artifact audit schema")
        require(canonical(audit) == canonical(e.json(e.path(prefix + "preflight.stdout"))), "compiled/preflight audits differ")
        parts = audit_claims(audit, b["claims"], per_claim=False)
        view["auditMetadata"].append({k: v for k, v in audit.items() if k not in {"claims", "axioms", "dependencies"}})
        require(audit["axioms"] == b["axioms"], "batch axioms differ from audit")
        for key, part in zip(("statements", "axioms", "dependencies"), parts):
            view[key].append(part)
        if "auditSourceSha256" in b:
            e.bound(prefix + "Audit.lean", b["auditSourceSha256"])
        for phase in ("preflight", "fresh-build", "audit", "replay"):
            process = e.process(prefix + phase)
            require(not e.raw(e.path(prefix + phase + ".stderr")).strip(), "unexpected proof stderr")
            if phase == "replay":
                require("--fresh" in process["command"], "replay is not fresh")
        covered += b["cases"]
        names += b["claims"]
    require(covered == list(range(len(cases))) and names == r["claims"] and len(set(names)) == len(names),
            "proof batches do not cover the exact case inventory")
    require(names == [c["theorem"] for c in cases], "case theorem mapping changed")
    require(r["axioms"] == sorted({a for batch in batches for a in batch["axioms"]}), "aggregate axiom inventory differs")
    controls = []
    for control in r["negativeControls"]:
        name = "negative-" + control["case"]
        require(re.fullmatch(r"[\w.-]+", name) and control.get("rejected") is True and control.get("exitCode") == 1,
                "invalid negative control")
        e.process(name, 1)
        controls.append({**control, **{suffix + "Sha256": sha(e.raw(e.path(name + "." + suffix)))
                                      for suffix in ("stdin", "stdout", "stderr", "pairs.json")}})
    expected = {"negative-" + c["case"] + ".pairs.json" for c in r["negativeControls"]}
    require(expected == {p.name for p in e.root.glob("negative-*.pairs.json")} and
            len(expected) == len(controls) and (not r.get("corpusRequested") or controls),
            "incomplete negative-control inventory")
    view["controls"] = controls
    # Keep package/source/object hashes and newly introduced batch fields visible.
    view["artifactBindings"] = {k: r[k] for k in ("cases", "proofBatches", "claims", "axioms")}
    return {"cases", "proofBatches", "claims", "axioms", "negativeControls"}


def native_view(e, view):
    r = e.report
    require(r.get("memoryIdentityBoundaryVerified") is True, "native report is preflight or incomplete")
    require(len(r["captures"]) == 3 and {c["mode"] for c in r["captures"]} ==
            {"Debug", "ReleaseSafe", "ReleaseFast"}, "native capture modes are incomplete")
    proof = e.json(e.bound("proof/report.json", r["proofReportSha256"]))
    require(proof.get("status") == "passed" and proof.get("freshKernelReplay") is True and
            proof.get("replayIncludesImports") is True, "fresh imported kernel replay is incomplete")
    audit = e.json(e.bound("audit.json", r["audit"]["sha256"]))
    names = proof["auditedDeclarations"]
    require(len(names) == r["auditedDeclarations"] == r["audit"]["claims"], "native claim count differs")
    view["statements"], view["axioms"], view["dependencies"] = audit_claims(audit, names, per_claim=True)
    view["auditMetadata"] = {k: v for k, v in audit.items() if k != "claims"}
    phases = proof["phases"]
    require({"build", "audit", "replay"} <= phases.keys() and all(p["status"] == "passed" for p in phases.values())
            and "--fresh" in phases["replay"]["command"], "native proof phases are incomplete")
    e.timing.update({"proof/" + name: p["seconds"] for name, p in phases.items()})
    for phase in phases:
        require(not e.raw(e.path("proof/" + phase + ".stderr.txt")).strip(), "native proof wrote stderr")
    plan, matrix = e.json(e.path("control-plan.json")), e.json(e.path("control-matrix.json"))
    require(matrix == r["controlMatrix"] and matrix["status"] == "passed" and
            all(c["status"] == "passed" for c in matrix["controls"]), "control matrix is incomplete")
    controls = r["controls"]
    require(controls and [c["name"] for c in controls] == [c["name"] for c in plan] ==
            [c["name"] for c in matrix["controls"]] and len({c["name"] for c in controls}) == len(controls),
            "control plan differs from results")
    retained_controls = set()
    for path in sorted(e.root.glob("*.process.json")):
        record = e.json(path)
        if "expectedAcceptance" in record:
            retained_controls.add(record["name"])
    require(retained_controls == {c["name"] for c in controls}, "retained control inventory differs")
    for record, planned in zip(controls, plan):
        name = record["name"]
        require(re.fullmatch(r"[\w.-]+", name) and record["status"] == "passed" and
                type(record["expectedAcceptance"]) is bool and
                record["expectedAcceptance"] == planned["expectedAcceptance"] and
                record["sourceSha256"] == planned["sourceSha256"], "changed control source or outcome")
        require(e.process(name, 0 if record["expectedAcceptance"] else 1, "passed") == record,
                "control receipt differs from report")
        for suffix, field in (("lean", "sourceSha256"), ("stdout", "stdoutSha256"), ("stderr", "stderrSha256")):
            e.bound(name + "." + suffix, record[field])
    view["controls"] = {"plan": plan, "results": [{k: v for k, v in c.items() if k != "seconds"} for c in controls],
                        "matrix": {k: v for k, v in matrix.items() if k not in {"seconds", "childUserSeconds", "childSystemSeconds"}},
                        "additional": {k: v for k, v in r.items() if k.endswith("Controls")}}
    exports, export_hashes = {}, set()
    for path in [e.root / "interfaces.json", *sorted(e.root.glob("*-interfaces/interfaces.json"))]:
        if path.exists():
            export_hashes.add(sha(e.raw(path)))
            exports[str(path.relative_to(e.root))] = e.json(path)
    for key, record in r.items():
        if key.endswith("Interfaces"):
            require(record["sha256"] in export_hashes, "missing or changed interface export: " + key)
    view["definitions"] = exports
    # Native observations are retained both in reports and hashed raw streams.
    streams = {}
    for path in sorted(e.root.glob("*.stdout")) + sorted(e.root.glob("*observation*.json")):
        streams[sha(e.raw(path))] = path

    def observations(value):
        if isinstance(value, dict):
            if "observationSha256" in value:
                require(value["observationSha256"] in streams, "missing or changed native observation")
                if "observed" in value:
                    require(canonical(e.json(streams[value["observationSha256"]])) == canonical(value["observed"]),
                            "native observation differs from report")
            for child in value.values():
                observations(child)
        elif isinstance(value, list):
            for child in value:
                observations(child)
    observations(r)
    view["proofInputs"] = {k: v for k, v in proof.items() if k != "phases"}
    view["proofExecution"] = {name: {k: v for k, v in phase.items() if k != "seconds"} for name, phase in phases.items()}
    e.timing["controlMatrix"] = {k: matrix[k] for k in ("seconds", "childUserSeconds", "childSystemSeconds")}
    return {"controls", "controlMatrix", "proofReportSha256", "audit", "auditedDeclarations", *view["controls"]["additional"]}


def inspect(report, receipt):
    e = Evidence(report, receipt)
    r, terminal = e.report, e.receipt
    require(r.get("schema") in ARTIFACTS | {NATIVE}, "unsupported report schema")
    require(r.get("status") == "passed" and terminal.get("status") == "passed" and
            type(terminal.get("exitCode")) is int and terminal["exitCode"] == 0 and
            terminal.get("resourceLimit") is None and not terminal.get("error") and not terminal.get("cleanupError"),
            "missing successful terminal receipt or acceptance report")
    require(terminal["peakSampledTreeRssBytes"] <= terminal["rssLimitBytes"], "memory bound exceeded")
    argv = terminal["command"]
    require(argv.count("--output") == 1 and Path(argv[argv.index("--output") + 1]).resolve() == e.root,
            "terminal receipt belongs to a different run")
    view = {}
    used = artifact_view(e, view) if r["schema"] in ARTIFACTS else native_view(e, view)
    identity_keys = {"sourceSha256", "inputs", "leanInputs", "stdInputs", "tools", "zigSha256"}
    view["identities"] = {k: v for k, v in r.items() if k in identity_keys}
    # Unknown fields and scope/assurance flags are never silently discarded.
    view["metadata"] = {k: v for k, v in r.items() if k not in used | identity_keys}
    view["timings"] = {"phases": e.timing, "totalSeconds": terminal["seconds"],
                       "peakSampledRssBytes": terminal["peakSampledTreeRssBytes"]}
    return e.normalize(view), e.finish()


def compare(before, after, before_receipt, after_receipt):
    result = {"schema": "oksolc.verification-comparison.v1", "status": "incomplete",
              "newAcceptance": False, "premiseDischarge": False, "categories": {}}
    try:
        left, result["before"] = inspect(before, before_receipt)
        right, result["after"] = inspect(after, after_receipt)
        for category in sorted(left.keys() | right.keys()):
            a, b = left.get(category), right.get(category)
            equal = canonical(a) == canonical(b)
            entry = {"equal": equal, "comparisonSha256": comparison_digest(a, b)}
            if not equal:
                difference = first_difference(a, b)
                entry["firstDifference"] = difference_message(difference) if difference else "JSON value types differ"
                entry["pointer"] = difference[0] if difference else ""
            result["categories"][category] = entry
        changed = [k for k, v in result["categories"].items() if k != "timings" and not v["equal"]]
        result.update(status="changed" if changed else "equal", changedCategories=changed,
                      timingOnlyChange=not changed and not result["categories"]["timings"]["equal"],
                      phaseTimes={"before": left["timings"], "after": right["timings"]})
    except (OSError, ValueError, KeyError, IndexError, AttributeError, TypeError, RecursionError) as error:
        result["failure"] = {"kind": type(error).__name__, "message": str(error)[:1200]}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("--before-receipt", type=Path, required=True)
    parser.add_argument("--after-receipt", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = compare(args.before, args.after, args.before_receipt, args.after_receipt)
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, allow_nan=False)
        stream.write("\n")
    print(json.dumps({k: result[k] for k in ("status", "changedCategories", "failure") if k in result}))
    return {"equal": 0, "changed": 1, "incomplete": 2}[result["status"]]


if __name__ == "__main__":
    raise SystemExit(main())
