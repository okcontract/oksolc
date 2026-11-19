#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check sequential byte exchange over initialized typed u32 storage.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This gate does not admit std.mem.swap's generic AIR or certify native noalias.
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import prove
from build_toolchain import digest, run, write_json
from check_word_bytes import inputs
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.ZigAir.MemoryByteExchangeTests"
NS = "Compiler.ZigAir.Memory.ByteExchange."
CLAIMS = ["Compiler.ZigAir.WordBytes." + n for n in ("exchangeLane_read", "exchange_four")]
CLAIMS += [NS + n for n in ("updated_self", "updated_updated", "updated_left", "updated_right", "step_refines",
                           "run_refines", "exchange_refines", "byte_addresses_apart")]
CLAIMS += [NS + "Tests." + n for n in ("writable", "represented", "total_witness", "little_exact", "big_exact",
                                      "readonly_reject", "uninitialized_reject", "logical_bounds_reject", "dead_reject",
                                      "empty_no_effect", "repeated_lane")]


def audit(output, env, lean):
    source = "import " + MODULE + '''
import Contract.Check.Declarations
import Lean.Elab.Command
open Lean Elab Command Contract.Check in
run_cmd do
  let mut claims := #[]
  for root in #[
''' + ",\n".join("    ``" + name for name in CLAIMS) + '''] do
    let .ok dependencies := Declarations.closure (← getEnv) #[root] | throwError "invalid closure: {root}"
    let .ok axioms := Declarations.axioms dependencies | throwError "disallowed axiom: {root}"
    let some info := (← getEnv).find? root | throwError "missing theorem: {root}"
    unless info matches .thmInfo _ do throwError "not a theorem: {root}"
    claims := claims.push <| Json.mkObj [
      ("theorem", .str root.toString), ("statement", Declarations.expression info.type),
      ("axioms", toJson axioms), ("dependencies", toJson (dependencies.map (·.name.toString)))]
  liftIO <| IO.println (Json.mkObj [("claims", .arr claims)]).compress
'''
    (output / "audit.lean").write_text(source)
    run(output, "audit", [lean, "-DwarningAsError=true", output / "audit.lean"], cwd=ROOT / "lean", env=env)
    raw = (output / "audit.stdout").read_bytes()
    (output / "audit.json").write_bytes(raw)
    claims = json.loads(raw)["claims"]
    if [c["theorem"] for c in claims] != CLAIMS:
        raise ValueError("unexpected byte-exchange claims")
    for claim in claims:
        if not set(claim["axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError("unexpected byte-exchange axiom")
        if claim["theorem"] in (NS + "exchange_refines", NS + "Tests.total_witness"):
            required = {NS + n for n in ("step", "run", "step_refines", "run_refines")}
            required |= {"Compiler.ZigAir.WordBytes.exchange_four"}
            required |= {"Compiler.ZigAir.Memory." + n for n in
                         ("State.valid", "WordArray.Writable", "WordArray.Represents", "WordArray.Frame",
                          "WordByteView.read_word", "WordByteView.write_refines", "load", "store")}
            if not required <= set(claim["dependencies"]):
                raise ValueError("byte-exchange proof lost its effect or premise dependencies")
    return {"claims": len(CLAIMS), "sha256": digest(output / "audit.json")}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/ZigAir"
    original = "import Compiler.ZigAir.MemoryWordBytes\n"
    original += "".join(without_imports((directory / name).read_text()) for name in
                        ("WordByteExchange.lean", "MemoryByteExchange.lean"))
    result = [mutation_check(output, "exchange-unchanged", original, True, env, lean)]
    for name, before, after in (
            ("omitted-last-lane", "exchangeLanes order (a, b) [0, 1, 2, 3]", "exchangeLanes order (a, b) [0, 1, 2]"),
            ("repeated-first-lane", "exchangeLanes order (a, b) [0, 1, 2, 3]", "exchangeLanes order (a, b) [0, 1, 2, 0]"),
            ("wrong-second-write", "match WordByteView.write order middle (view.pointer right) index.val a with",
             "match WordByteView.write order middle (view.pointer right) index.val b with"),
            ("skipped-loop-tail", "| (.ok (), after) => run order view left right rest after", "| (.ok (), after) => (.ok (), after)"),
    ):
        if original.count(before) != 1:
            raise ValueError("ambiguous byte-exchange mutation: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    for record in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("byte-exchange control hit a resource or syntax failure")
    return result


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.byte-exchange-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "typedHeapInitializedU32ByteExchange", "capturedSwapLoopVerified": False,
              "genericSpecializationVerified": False, "nativeNoaliasVerified": False,
              "sourceSafetyVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False,
              "assumptions": ["valid heap", "initialized writable contained u32 view", "distinct in-view word indices",
                              "explicit byte order", "sequential nonvolatile storage"]}
    try:
        report["inputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "preflight", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
        report["controls"] = controls(output, env, tools["lean"]["path"])
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("byte-exchange fresh kernel replay failed")
        if inputs() != report["inputs"] or lean_check.source_inputs() != report["leanInputs"]:
            raise ValueError("byte-exchange acceptance inputs changed")
        report.update(status="passed", auditedDeclarations=len(CLAIMS), typedHeapByteExchangeVerified=True)
    finally:
        write_json(output / "report.json", report)
    print("Typed-heap byte exchange passed; captured generic loop and native preservation remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
