#!/usr/bin/env python3
"""Check declared compiler coverage, not proof acceptance.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
MAP = ROOT / "docs/compiler-verification-map.json"
# Version 2 changes only the reviewed host toolchain pin; no trust contract is added.
BOUNDARIES = {
    1: "845b720582d1bb578f06c0ee000224102f81a70bd7db3b68b3db762917f5e59f",
    2: "15e10eb7aeb4f52921167e064115b08042a69e491294cc399f68c444056e7f7d",
}
KINDS = {"contract", "model", "production-operation", "pipeline-pass", "artifact-route"}
ROUTES = {"implementation", "artifact-validator", "undecided"}


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique(values, label):
    require(isinstance(values, list) and all(isinstance(v, str) and v for v in values), label + ": expected names")
    require(len(values) == len(set(values)), label + ": duplicate name")
    return set(values)


def registry(source, path):
    """Admit only the current explicit step registry, failing on unknown rows.

    This is an inventory parser, not a Zig parser or a preservation proof.
    """
    blocks = re.findall(r"const step_descriptors = \[_\]StepDescriptor\{(.*?)\n\};", source, re.S)
    require(len(blocks) == 1, "ambiguous or missing Yul registry")
    entries = []
    for line in blocks[0].splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"\s*stepDescriptor\(([\w.]+), '(.)'\),\s*", line)
        require(match is not None, "unadmitted Yul registry row")
        symbol, abbreviation = match.groups()
        alias, *nested = symbol.split(".")
        imports = re.findall(r"const " + re.escape(alias) + r' = @import\("([^"\n]+)"\)(?:\.(\w+))?;', source)
        require(len(imports) == 1, "ambiguous Yul step import: " + alias)
        imported, selected = imports[0]
        require(bool(selected) != bool(nested) and len(nested) <= 1, "unadmitted Yul step type: " + symbol)
        resolved = (ROOT / path).parent.joinpath(imported).resolve()
        require(resolved.is_relative_to(ROOT), "Yul step import escapes repository")
        entries.append({"path": resolved.relative_to(ROOT).as_posix(),
                        "symbol": (selected or nested[0]) + ".run", "abbreviation": abbreviation})
    require(entries, "empty Yul registry")
    unique([e["abbreviation"] for e in entries], "Yul abbreviations")
    unique([e["symbol"] for e in entries], "Yul symbols")
    return entries


def progress(by_id, final, priority):
    """Summarize declared scopes; neither count proofs nor infer acceptance."""
    closures = {}

    def closure(name):
        if name not in closures:
            closures[name] = {name}.union(*(closure(d) for d in by_id[name]["requires"]))
        return closures[name]

    def remaining(roots):
        names = set().union(*(closure(name) for name in roots))
        return sorted(name for name in names if by_id[name]["status"] != "closed")

    entries = {}
    for name, record in sorted(by_id.items()):
        if record["kind"] not in {"production-operation", "pipeline-pass"}:
            continue
        for entry in record["entryPoints"]:
            scopes = entries.setdefault((entry["path"], entry["symbol"]),
                                        {status: [] for status in ("closed", "partial", "open")})
            scopes[record["status"]].append(name)
    milestones = [{"id": name, "status": by_id[name]["status"],
                   "remaining": remaining([name])} for name in priority]
    return {
        "declaredObligationsByKind": {
            kind: dict(sorted(Counter(r["status"] for r in by_id.values() if r["kind"] == kind).items()))
            for kind in sorted({r["kind"] for r in by_id.values()})},
        # A closed scope does not establish every use of a shared entry point.
        "productionEntryPoints": [{"path": path, "symbol": symbol, "scopes": scopes}
                                  for (path, symbol), scopes in sorted(entries.items())],
        "priorityMilestones": milestones,
        "next": next((m["id"] for m in milestones if m["status"] != "closed"), None),
        "completionRoutes": {
            "implementation": {"remaining": remaining(final["implementationRequires"])},
            "artifact-validator": {"scopedRoutes": [
                {"id": name, "status": by_id[name]["status"], "remaining": remaining([name])}
                for name in sorted(final["scopedArtifactRoutes"])], "currentArtifactValidated": False}},
    }


def check(document, read=None):
    inspected = {}

    def source(path):
        require(isinstance(path, str) and path, "missing source path")
        candidate = ROOT / path
        require(not Path(path).is_absolute() and candidate.resolve().is_relative_to(ROOT), "source path escapes repository")
        if path not in inspected:
            data = read(path) if read else candidate.read_bytes()
            inspected[path] = data
        return inspected[path].decode("utf-8")

    def reference(ref, proof=False):
        text = source(ref["path"])
        name = ref["declaration"] if proof else ref["symbol"]
        require(isinstance(name, str) and re.fullmatch(r"[\w.]+", name), "invalid declaration reference")
        if proof:
            declared = re.findall(r"\btheorem\s+([\w.]+)\b", text)
            require(any(name == local or name.endswith("." + local) for local in declared), "missing declaration: " + name)
            source(ref["gate"])
        else:
            leaf = name.rsplit(".", 1)[-1]
            require(re.search(r"\bfn\s+" + re.escape(leaf) + r"\s*\(", text) is not None, "missing declaration: " + name)

    require(document["schema"] == "oksolc.compiler-verification-map.v1", "unknown map schema")
    boundary = document["trustBoundary"]
    assumptions = unique([a["id"] for a in boundary["assumptions"]], "assumptions")
    require(all(isinstance(a["contract"], str) and a["contract"] for a in boundary["assumptions"]), "empty trust contract")
    encoded = json.dumps(boundary["assumptions"], sort_keys=True, separators=(",", ":")).encode()
    require(type(document["boundaryVersion"]) is int and
            BOUNDARIES.get(document["boundaryVersion"]) == digest(encoded), "trust boundary changed without a reviewed version")
    source(boundary["document"])
    final = document["finalClaim"]
    require(final["id"] == "compiler.sourceToBytecode" and final["status"] == "open", "v1 has no whole-compiler acceptance checker")
    require(set(final["routes"]) == {"implementation", "artifact-validator"}, "missing completion route")
    require(final["scope"] and final["remaining"], "missing final claim limitations")
    inventory = document["inventory"]
    require(inventory["complete"] is False and inventory["remaining"] and inventory["scope"], "v1 inventory is explicitly partial")

    records = document["obligations"]
    ids = unique([r["id"] for r in records], "obligations")
    require(final["id"] not in ids, "final claim duplicates an obligation")
    by_id = {r["id"]: r for r in records}
    for record in records:
        name = record["id"]
        require(record["kind"] in KINDS and record["route"] in ROUTES, "unknown kind or route: " + name)
        require(record["status"] in {"open", "partial", "closed"}, "unknown status: " + name)
        require(unique(record["requires"], name + " dependencies") <= ids, "unknown dependency: " + name)
        require(unique(record["assumptions"], name + " assumptions") <= assumptions, "unknown assumption: " + name)
        require(record["finalConnection"] in ids | {final["id"]}, "unknown final connection: " + name)
        require(record["unsupported"] and record["acceptance"], "missing limitations or acceptance: " + name)
        unique(record["supportedSemantics"], name + " semantics")
        entries = [(entry["path"], entry["symbol"]) for entry in record["entryPoints"]]
        require(len(entries) == len(set(entries)), "duplicate entry point: " + name)
        for entry in record["entryPoints"]:
            reference(entry)
        for evidence in record["evidence"]:
            reference(evidence, proof=True)
        if record["status"] == "closed":
            require(record["supportedSemantics"] and record["evidence"] and record["route"] != "undecided", "closed obligation without scoped evidence: " + name)
            require(all(by_id[d]["status"] == "closed" for d in record["requires"]), "closed obligation has an open dependency: " + name)
            if record["kind"] in {"production-operation", "pipeline-pass"}:
                require(record["entryPoints"] and record.get("composedTheorem") in
                        [e["declaration"] for e in record["evidence"]], "production completion needs a composed theorem: " + name)
        if record["kind"] == "artifact-route":
            require(record["route"] == "artifact-validator", "artifact route mislabeled: " + name)
        if record["kind"] == "pipeline-pass":
            require(record["entryPoints"], "pipeline pass missing entry point: " + name)

    # Check both graphs. Connection edges describe the route to the final claim;
    # requires edges are proof dependencies, not a prescribed pass execution order.
    def visit(name, active, finished):
        require(name not in active, "cyclic proof dependency: " + name)
        if name not in finished:
            for dependency in by_id[name]["requires"]:
                visit(dependency, active | {name}, finished)
            finished.add(name)

    finished = set()
    for name in ids:
        visit(name, set(), finished)
        visited, current = set(), name
        while current != final["id"]:
            require(current not in visited, "cyclic final connection: " + name)
            visited.add(current)
            current = by_id[current]["finalConnection"]
    require(unique(document["priority"], "priority") <= ids, "unknown priority")
    require(unique(final["implementationRequires"], "final dependencies") <= ids, "unknown final dependency")
    routes = unique(final["scopedArtifactRoutes"], "artifact routes")
    require(routes <= ids and all(by_id[r]["kind"] == "artifact-route" for r in routes), "unknown final artifact route")

    steps = document["registeredYulSteps"]
    require(steps["status"] == "open" and steps["route"] == "undecided" and steps["supportedSemantics"] == [], "registered steps have no preservation evidence in v1")
    require(steps["unsupported"] and steps["semantics"], "missing registry limitations")
    require(unique(steps["requires"], "registry dependencies") <= ids, "unknown registry dependency")
    require(unique(steps["assumptions"], "registry assumptions") <= assumptions, "unknown registry assumption")
    require(steps["finalConnection"] == "yul.optimization" and steps["finalConnection"] in ids, "missing registry composition")
    actual = registry(source(steps["source"]), steps["source"])
    require(steps["entries"] == actual, "registered Yul step inventory changed")
    for entry in actual:
        reference(entry)

    closed = [r for r in records if r["status"] == "closed"]
    return {"schema": "oksolc.compiler-verification-map-check.v1", "status": "consistent",
            "boundaryVersion": document["boundaryVersion"], "boundarySha256": digest(encoded),
            "inventoryComplete": False, "registeredYulSteps": len(actual), "registeredYulStepsClosed": 0,
            "declaredClosedByKind": dict(sorted(Counter(r["kind"] for r in closed).items())),
            "declaredClosedProductionOperations": [r["id"] for r in closed if r["kind"] == "production-operation"],
            "openObligations": sorted(r["id"] for r in records if r["status"] != "closed"),
            **progress(by_id, final, document["priority"]),
            "wholeCompilerVerified": False, "proofReplayPerformed": False,
            "scope": "Inventory/reference consistency only; closure declarations require the referenced acceptance gates. No current artifact was validated.",
            "inputs": {path: digest(data) for path, data in sorted(inspected.items())}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--map", type=Path, default=MAP)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = args.map.read_bytes()
    try:
        report = check(json.loads(data))
    except (ValueError, KeyError, TypeError, IndexError, OSError) as error:
        report = {"status": "rejected", "error": str(error), "wholeCompilerVerified": False, "proofReplayPerformed": False}
    report["mapSha256"] = digest(data)
    encoded = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")
    return 0 if report["status"] == "consistent" else 1


if __name__ == "__main__":
    raise SystemExit(main())
