#!/usr/bin/env python3
"""Check reached-state cleanup/publication and their recursive-step consumers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path

import check_recursive_nonempty as gate
import caller_native_insertion_checks as caller
import physical_dispatch_preservation_checks as projection
import native_cache_checks as cache
import native_entry_checks as entry
import native_lookup_checks as lookup
import native_take_checks as take
import native_spare_checks as spare
import native_growth_checks as growth
import native_first_checks as first
import native_backing_failure_checks as backing
import native_publication_rollback_checks as rollback
import native_parent_return_checks as parent_return
import native_parent_release_checks as parent_release
import native_parent_publication_checks as parent_publication
import native_parent_entry_checks as parent_entry
import native_parent_leaf_checks as parent_leaf
import native_parent_insertion_checks as parent_insertion
import caller_custody_checks as caller_custody
import caller_growing_rollback_checks as caller_rollback
import caller_growth_allocation_failure_checks as caller_backing
import caller_first_success_checks as caller_first
import caller_spare_success_checks as caller_spare
import caller_growing_success_checks as caller_growing
import caller_origin_checks as origin
import native_preparation_failure_checks as preparation_failure
import caller_transferred_preparation_failure_checks as transferred_preparation
import caller_transferred_allocation_failure_checks as transferred_backing
import caller_transferred_growth_checks as transferred_growth
import native_unrelocated_transferred_checks as transferred_unrelocated
import caller_capacity_checks as capacity
import caller_capacity_completion_checks as capacity_completion
from assembly_item_creation_checks import checked_controls
from build_toolchain import digest, write_json
from check_zig_air_proofs import mutation_check

SUITES = (("step", "Compiler.Extraction.InternerNativeStep", gate.native_step),
          ("growth", "Compiler.Extraction.InternerRecursiveGrowthTests", gate.recursive_growth))
CALLER_SUITE = ("caller", "Compiler.Extraction.InternerCallerInsertionInputTests", caller)
PREPARATION_SUITES = (
    ("insertion-model", gate.MODULE, gate.insertion_model),
    ("completion", gate.MODULE, gate.preparation_completion),
    ("capacity", gate.MODULE, capacity),
    ("capacity-return", "Compiler.Extraction.InternerCallerInsertionCapacityCompletionTests", capacity_completion),
    CALLER_SUITE,
    ("failure", "Compiler.Extraction.InternerInsertionPreparationFailureTests", preparation_failure),
    ("transferred-preparation", transferred_preparation.MODULE, transferred_preparation),
    ("composition", gate.MODULE, gate.composition))
CACHE_SUITES = (
    ("cache", "Compiler.Extraction.InternerNativeCacheHitTests", cache),
    ("local", "Compiler.Extraction.InternerNativeLocalTests", gate.native_local),
    ("origin", "Compiler.Extraction.InternerCallerOriginTests", origin))
ENTRY_SUITES = (("entry", entry.MODULE, entry), CACHE_SUITES[0], CACHE_SUITES[2])
LOOKUP_SUITE = ("lookup", lookup.MODULE, lookup)
LOOKUP_SUITES = (SUITES[0], LOOKUP_SUITE, *CACHE_SUITES, SUITES[1])
TAKE_SUITES = (("take", take.MODULE, take), LOOKUP_SUITE, ENTRY_SUITES[0], *CACHE_SUITES)
SPARE_SUITES = (SUITES[0], PREPARATION_SUITES[0], ("spare", spare.MODULE, spare),
    ("caller-spare", "Compiler.Extraction.InternerCallerInsertionSpareSuccessTests", caller_spare),
    ("caller-growing", "Compiler.Extraction.InternerCallerInsertionGrowingSuccessTests", caller_growing),
    ("native-constant", gate.MODULE, gate.native_constant))
GROWING_SUITES = tuple((name, growth.MODULE if module == gate.MODULE else module, checks)
    for name, module, checks in SPARE_SUITES) + (("relocation", growth.MODULE, growth), ("transferred-growth", transferred_growth.MODULE, transferred_growth),
    ("transferred-unrelocated", transferred_unrelocated.MODULE, transferred_unrelocated))
FIRST_SUITES = tuple((name, first.MODULE if module == growth.MODULE else module, checks)
    for name, module, checks in GROWING_SUITES) + (
    ("first", first.MODULE, first),
    ("caller-first", "Compiler.Extraction.InternerCallerInsertionFirstSuccessTests", caller_first))
BACKING_SUITES = (SUITES[0],
    ("backing", backing.MODULE, backing),
    ("insertion-model", backing.MODULE, gate.insertion_model),
    ("completion", backing.MODULE, gate.preparation_completion),
    ("caller-backing", "Compiler.Extraction.InternerCallerInsertionGrowthAllocationFailureTests", caller_backing),
    ("transferred-backing", transferred_backing.MODULE, transferred_backing),
    ("capacity-return", "Compiler.Extraction.InternerCallerInsertionCapacityCompletionTests", capacity_completion))
ROLLBACK_SUITES = (SUITES[0],
    ("rollback", rollback.MODULE, rollback),
    ("insertion-model", rollback.MODULE, gate.insertion_model),
    ("caller-rollback", "Compiler.Extraction.InternerCallerInsertionGrowingRollbackTests", caller_rollback),
    ("relocation", rollback.MODULE, growth),
    ("first", rollback.MODULE, first),
    ("spare", rollback.MODULE, spare))
PARENT_RETURN_SUITES = (*SUITES, ("parent-return", parent_return.MODULE, parent_return))
PARENT_RELEASE_SUITES = (SUITES[0],
    ("parent-release", parent_release.MODULE, parent_release),
    ("child", parent_release.MODULE, gate.recursive), SUITES[1],
    ("fold-growth", parent_release.MODULE, gate.constant_fold_growth))
PARENT_PUBLICATION_SUITES = (SUITES[0],
    ("parent-publication", parent_publication.MODULE, parent_publication),
    ("custody", parent_publication.MODULE, caller_custody), SUITES[1],
    ("parent-release", parent_publication.MODULE, parent_release))
PARENT_ENTRY_SUITES = (*SUITES, ("parent-entry", parent_entry.MODULE, parent_entry),
    ("parent-return", parent_entry.MODULE, parent_return))
PARENT_LEAF_SUITES = (*TAKE_SUITES, ("parent-leaf", parent_leaf.MODULE, parent_leaf))
PARENT_INSERTION_SUITES = (*SUITES,
    ("parent-insertion", parent_insertion.MODULE, parent_insertion),
    ("first", first.MODULE, first), ("spare", spare.MODULE, spare),
    ("relocation", growth.MODULE, growth),
    ("caller-first", "Compiler.Extraction.InternerCallerInsertionFirstSuccessTests", caller_first))
CURSOR_PROJECTION_SUITES = (SUITES[0],
    ("projection", projection.MODULE, projection),
    ("dispatcher", gate.MODULE, gate.native_recursion))
GROWTH_CONTROLS = {"publication-cleanup", "failed-parent", "postconditions", "release"}
COMPOSITION_CONTROLS = {"allocation", "complete-growth"}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    frozen, library = gate.inputs(), args.zig_lib_dir.resolve()
    write_json(output / "inputs.json", frozen)
    report = {"status": "failed", "jobs": 4, "preflightOnly": args.preflight, "preparation": args.preparation, "cache": args.cache, "entry": args.entry, "lookup": args.lookup, "take": args.take, "spare": args.spare, "growth": args.growth, "first": args.first, "backing": args.backing, "rollback": args.rollback, "parentReturn": args.parent_return, "parentRelease": args.parent_release, "parentPublication": args.parent_publication, "parentEntry": args.parent_entry, "parentLeaf": args.parent_leaf, "parentInsertion": args.parent_insertion, "cursorProjection": args.cursor_projection,
        "scope": "native reached-state cleanup and publication completion with matched probe decisions; taken proper-child step and existing recursive publication success/failure clients",
        "allEntryPrefixesVerified": False, "composedProductionTheoremVerified": False,
        "suites": [], "controls": []}
    suites = (SUITES[0], *PREPARATION_SUITES, SUITES[1]) if args.preparation else SUITES
    if args.cache or args.lookup:
        suites = (SUITES[0], *CACHE_SUITES, SUITES[1])
        report["scope"] = "general cache-hit entry through actual item/scratch/normalizer cleanup, including an owned temporary; scoped native graph, exact key table, all old allocations and proper-child cache leaf with word preservation; existing named-local and taken-miss return consumers"
    if args.lookup:
        suites = LOOKUP_SUITES
        report["scope"] = "initialized key existence and shared cache/miss routing; common ordinary initialized native return and proper-child leaf specialized by cache hits and classification errors; exact rejected state retention; existing named-local and taken-miss return consumers"
    if args.preparation:
        report["scope"] = "general taken-step reduction with actual-callback outcome/graph projection and successful candidate derived from actual preparation in both ownership modes and explicit local policy/preparation bindings; reached capacity and duplicate/create/clone OOM; successful preparation, entry-caller and constant-growth specializations; existing recursive growth/publication/cleanup clients"
    if args.entry:
        suites = ENTRY_SUITES
        report["scope"] = "capacity and ordinary initializer failure before lookup ownership, derived scratch allocation after typed item preparation, exact rejected initialization retention, native frame and proper-child error leaf; existing normalization/cache corpus"
    if args.take:
        suites = TAKE_SUITES
        report["scope"] = "actual failed take derives OOM and exact reached-world cleanup; common constructor/native return with derived local postconditions, specialized by take, lookup/cache/classification and entry failure; existing named-local and normalization clients"
    if args.spare:
        suites = SPARE_SUITES
        report["scope"] = "reached deterministic spare publication derives native graph preservation from actual preparation/probe observations; old caller proof and growth data preservation specialize general proofs; proper-child taken step excludes successful spare publication from its remaining native-frame premise, retaining the explicit enclosing parent law"
    if args.growth:
        suites = GROWING_SUITES
        report["scope"] = "reached successful nonempty no-remap relocation derives native graph preservation and exact old-backing retirement; spare and growing proofs share publication payload preservation and native graph construction; existing six-insertion corpus and caller specialize the reached proof; proper-child taken step excludes both publication cases from the remaining native-frame premise with one explicit enclosing parent law"
    if args.first:
        suites = FIRST_SUITES
        report["scope"] = "reached first publication derives its native frame with arbitrary empty sentinel, live unique old keys and optional growth callbacks; existing first caller specializes the reached proof; first, spare and relocation executions use one source-observed publication completion in the proper-child step, retaining the separate enclosing parent law"
    if args.growth or args.first:
        report["scope"] += "; transferred first/spare/no-remap success uses the same general enclosing reducer, with existing callers and arbitrary optional growth for first/spare"
    if args.backing:
        suites = BACKING_SUITES
        report["scope"] = "reached deterministic first and nonempty no-remap backing OOM share preparation, cleanup and unpublished native completion; existing caller growth-OOM proof specializes the reached result; the proper-child step excludes these source-observed failures using its existing private-cleanup parent law; existing capacity/preparation return consumers remain checked"
    if args.parent_publication:
        suites = PARENT_PUBLICATION_SUITES
        report["scope"] = "actual child publication and replacement derive the live-parent source, normalized custody and typed item frame; original child provenance protects new keys while reached custody protects old keys; existing growth/privacy proofs specialize shared origin helpers; publication completion composes this law with private release after refusal; actual child entry and next outer laws remain open"
    if args.parent_insertion:
        suites = PARENT_INSERTION_SUITES
        report["scope"] = "first/spare/no-remap successful insertion retains physical frames in one completion; original child provenance, reached custody and input storage geometry derive the concrete enclosing call; existing growth return consumes it; next outer laws, other insertion outcomes and all-entry induction remain open"
    if args.parent_leaf:
        suites = PARENT_LEAF_SUITES
        report["scope"] = "cache/classification, ordinary entry failure and take-OOM step leaves retain exact keys and original allocations through one return interface; shared adapter derives the enclosing live call; existing named-local cache return and parent publication consume the concrete frame; next outer laws, all-entry induction and production correspondence remain open"
    if args.parent_entry:
        suites = PARENT_ENTRY_SUITES
        report["scope"] = "actual child item/scratch/normalization/take observations derive the child and enclosing call frames; literals, items and normalization reuse one allocation frame; original child provenance remains anchored at the constructed world; existing recursive growth consumes the shared entry; next outer laws, other entry paths and all-entry induction remain open"
    if args.parent_release:
        suites = PARENT_RELEASE_SUITES
        report["scope"] = "original child normalization origin and reached private graph custody derive live-parent private cleanup and release; failed-child completion consumes that law; publication refusal derives its private release guard; general step requires that guard rather than an arbitrary-world release law; existing simplifier OOM and growth/publication clients share the foundations; outer laws and all-entry induction remain open"
    if args.parent_return:
        suites = PARENT_RETURN_SUITES
        report["scope"] = "general input/item cleanup from original entry lifetimes and reached frames; concrete localParent instance and graph-return composition; existing recursive relocation with parent publication success/OOM and item retention; arbitrary outer laws and all-entry induction remain open"
    if args.rollback:
        suites = ROLLBACK_SUITES
        report["scope"] = "reached first/spare/no-remap publication OOM derives the restored native graph and consumes normalized input; all paths share preparation composition and rollback; first/spare append owners come from existing native proofs with arbitrary optional growth; existing successful fixtures supply the observations and reached frames; the general step consumes one refusal completion with a separate enclosing-parent law; other insertion frames and full production correspondence remain open"
    if args.cursor_projection:
        suites = CURSOR_PROJECTION_SUITES
        report["scope"] = "exact reached-state simulation with an explicit observation; cursor-only projection preserves native read values, cache and representative observations; existing dispatcher and word clients specialize the generalized proofs; complete native allocation-stream coupling and all-entry induction remain open"
    try:
        std, profiles = gate.std_inputs(library), gate.profiles(library)
        write_json(output / "std-inputs.json", std)
        write_json(output / "source-profiles.json", profiles)
        env, _, tools = gate.harness.lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        for name, module, checks in suites:
            folder = output / name
            folder.mkdir()
            audit = gate.harness.audit(folder, env, tools["lean"]["path"], module, checks.CLAIMS)
            rows = json.loads((folder / "audit.json").read_bytes())["claims"]
            dependencies = {row["theorem"]: set(row["dependencies"]) for row in rows}
            record = {"name": name, "module": module, "roots": checks.CLAIMS,
                "audit": audit, "dependencies": getattr(checks, "audit_claims", checks.audit)(dependencies)}
            if hasattr(checks, "audit_statements"):
                record["interface"] = checks.audit_statements(rows)
            report["suites"].append(record)
        print("Cached composition and consumer audits passed; checking controls.", flush=True)
        controls = [] if (args.entry or args.take or args.parent_leaf) else gate.native_step.controls(output, env, tools["lean"]["path"])
        write_json(output / "controls.json", controls)
        if args.cursor_projection:
            for checks in (projection, gate.native_recursion):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.parent_insertion:
            for checks in (parent_insertion, first, spare, growth, caller_first):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.parent_leaf:
            controls += parent_leaf.controls(output, env, tools["lean"]["path"])
            write_json(output / "controls.json", controls)
        if args.parent_entry:
            for checks in (parent_entry, parent_return):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.parent_publication:
            for checks in (parent_publication, caller_custody, parent_release):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.parent_release:
            for checks in (parent_release, gate.recursive, gate.constant_fold_growth):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.parent_return:
            controls += parent_return.controls(output, env, tools["lean"]["path"])
            write_json(output / "controls.json", controls)
        if args.rollback:
            for checks in (rollback, caller_rollback, growth, first, spare):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.backing:
            for checks in (backing, caller_backing, transferred_backing, gate.preparation_completion, capacity_completion):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.first:
            for checks in (first, caller_first):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.growth or args.first:
            controls += transferred_growth.controls(output, env, tools["lean"]["path"])
            controls += transferred_unrelocated.controls(output, env, tools["lean"]["path"])
            write_json(output / "controls.json", controls)
            for checks in (growth, caller_growing):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.spare or args.growth or args.first:
            for checks in (spare, caller_spare):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.spare or args.growth or args.first or args.backing or args.rollback:
            model_groups = set()
            for group, text, changes in gate.insertion_model.mutation_cases():
                if group != "completion":
                    continue
                model_groups.add(group)
                for name, before, _, count in changes:
                    if text.count(before) != count:
                        raise ValueError("ambiguous spare model control: " + name)
                controls += checked_controls(output, [mutation_check(output,
                    "spare-model-unchanged", text, True, env, tools["lean"]["path"])])
                for name, before, after, _ in changes:
                    controls += checked_controls(output, [mutation_check(output,
                        "spare-model-" + name, text.replace(before, after), False, env, tools["lean"]["path"])])
                write_json(output / "controls.json", controls)
            if model_groups != {"completion"}:
                raise ValueError("missing spare model controls")
        if args.take or args.parent_leaf:
            for checks in (take, lookup, entry, cache, gate.native_local, origin):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.entry:
            for checks in (entry, cache, origin):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.lookup:
            controls += lookup.controls(output, env, tools["lean"]["path"])
            write_json(output / "controls.json", controls)
        if args.cache or args.lookup:
            for checks in (cache, gate.native_local, origin):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.preparation:
            for checks in (gate.insertion_model, gate.preparation_completion, capacity, capacity_completion, preparation_failure, transferred_preparation, caller):
                controls += checks.controls(output, env, tools["lean"]["path"])
                write_json(output / "controls.json", controls)
        if args.preparation or args.cache or args.lookup:
            wanted = {"return"} if (args.cache or args.lookup) else COMPOSITION_CONTROLS
            prefix = "cache" if (args.cache or args.lookup) else "preparation"
            composition_groups = set()
            for group, text, changes in gate.composition.mutation_cases():
                if group not in wanted:
                    continue
                composition_groups.add(group)
                for name, before, _, count in changes:
                    if text.count(before) != count:
                        raise ValueError("ambiguous preparation consumer mutation: " + group + "-" + name)
                controls += checked_controls(output, [mutation_check(output,
                    prefix + "-consumer-" + group + "-unchanged", text, True, env, tools["lean"]["path"])])
                for name, before, after, _ in changes:
                    controls += checked_controls(output, [mutation_check(output,
                        prefix + "-consumer-" + group + "-" + name, text.replace(before, after), False, env, tools["lean"]["path"])])
                write_json(output / "controls.json", controls)
            if composition_groups != wanted:
                raise ValueError("missing preparation consumer controls")
        growth_controls = set() if (args.cursor_projection or args.entry or args.take or args.parent_leaf or args.spare or args.growth or args.first or args.backing or args.rollback) else GROWTH_CONTROLS
        if args.parent_publication:
            growth_controls = growth_controls | {"graph-custody"}
        selected = set()
        for group, text, changes in gate.recursive_growth.mutation_cases():
            if group not in growth_controls:
                continue
            selected.add(group)
            for name, before, _, count in changes:
                if text.count(before) != count:
                    raise ValueError("ambiguous cleanup consumer mutation: " + group + "-" + name)
            controls += checked_controls(output, [mutation_check(output,
                "cleanup-" + group + "-unchanged", text, True, env, tools["lean"]["path"])])
            write_json(output / "controls.json", controls)
            for name, before, after, _ in changes:
                controls += checked_controls(output, [mutation_check(output,
                    "cleanup-" + group + "-" + name, text.replace(before, after), False, env, tools["lean"]["path"])])
                write_json(output / "controls.json", controls)
        if selected != growth_controls:
            raise ValueError("missing cleanup consumer controls")
        report["controls"] = controls
        print("Composition and consumer controls passed.", flush=True)
        if not args.preflight:
            # The selected suites share a large import closure. Replay their
            # audited root union once, with imports, instead of rebuilding and
            # rechecking the same clients separately for every selected suite.
            replays = report["suites"]
            if args.cursor_projection or args.preparation or args.cache or args.entry or args.lookup or args.take or args.spare or args.growth or args.first or args.backing or args.rollback or args.parent_return or args.parent_release or args.parent_publication or args.parent_entry or args.parent_leaf or args.parent_insertion:
                replay_name = "cursor-projection-replay" if args.cursor_projection else "parent-insertion-replay" if args.parent_insertion else "parent-leaf-replay" if args.parent_leaf else "parent-entry-replay" if args.parent_entry else "parent-publication-replay" if args.parent_publication else "parent-release-replay" if args.parent_release else "parent-return-replay" if args.parent_return else "rollback-replay" if args.rollback else "backing-replay" if args.backing else "first-replay" if args.first else "growth-replay" if args.growth else "spare-replay" if args.spare else "take-replay" if args.take else "lookup-replay" if args.lookup else "entry-replay" if args.entry else "cache-replay" if args.cache else "preparation-replay"
                replay_module = gate.MODULE if args.cursor_projection else parent_insertion.MODULE if args.parent_insertion else parent_leaf.MODULE if args.parent_leaf else parent_entry.MODULE if args.parent_entry else parent_publication.MODULE if args.parent_publication else parent_release.MODULE if args.parent_release else parent_return.MODULE if args.parent_return else rollback.MODULE if args.rollback else backing.MODULE if args.backing else first.MODULE if args.first else growth.MODULE if args.growth else take.MODULE if args.take else entry.MODULE if args.entry else gate.MODULE
                replays = [{"name": replay_name, "module": replay_module,
                    "roots": list(dict.fromkeys(root for record in replays for root in record["roots"]))}]
                (output / replays[0]["name"]).mkdir()
            report["replays"] = replays
            for record in replays:
                print("Starting fresh imported replay: " + record["name"], flush=True)
                proof, artifacts = gate.harness.prove.check_module(record["module"], record["roots"],
                    lean_bin=args.lean_bin, jobs=4, fresh=True, timeout=1800)
                folder = output / record["name"]
                for name, data in artifacts.items():
                    (folder / ("proof-" + name)).write_bytes(data)
                if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                        proof.get("replayIncludesImports") is not True):
                    raise ValueError("fresh cleanup replay failed: " + str(proof.get("failure")))
                record["proof"] = {"sha256": digest(folder / "proof-report.json"),
                    "freshKernelReplay": True, "replayIncludesImports": True}
        gate.check_compiler.require_stable(frozen, gate.inputs())
        if profiles != gate.profiles(library) or std != gate.std_inputs(library):
            raise ValueError("source admission changed during cleanup verification")
        report.update(status="passed", frozenInputs=len(frozen),
            zigLibrary={"path": str(library), "inputs": len(std), "sha256": digest(output / "std-inputs.json")})
    finally:
        write_json(output / "report.json", report)
    print(json.dumps({"status": report["status"], "suites": len(report["suites"]),
        "controls": len(report["controls"]), "preflightOnly": args.preflight}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--zig-lib-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--preflight", action="store_true")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--cursor-projection", action="store_true", help="Check reached cursor observations, existing native dispatcher and proper-child step with one fresh imported replay.")
    selection.add_argument("--parent-insertion", action="store_true", help="Check shared successful-insertion parent framing with first/spare/relocation branches and existing recursive growth in one fresh replay.")
    selection.add_argument("--parent-leaf", action="store_true", help="Check shared parent framing for ordinary unchanged-graph leaves and existing named-local publication in one fresh replay.")
    selection.add_argument("--parent-entry", action="store_true", help="Check derived child/live-parent preparation with the general step and existing recursive growth/return clients in one fresh replay.")
    selection.add_argument("--parent-publication", action="store_true", help="Check derived live-parent publication/replacement and refusal cleanup with existing custody and recursive clients in one fresh replay.")
    selection.add_argument("--parent-release", action="store_true", help="Check shared child-private parent framing, guarded release and actual recursive failure/publication clients in one fresh replay.")
    selection.add_argument("--parent-return", action="store_true", help="Check derived live-parent local return, general-step interface and existing recursive growth/publication clients in one fresh replay.")
    selection.add_argument("--rollback", action="store_true", help="Check shared preparation and first/spare/no-remap publication rollback, native frames and general-step consumers with one scoped fresh replay.")
    selection.add_argument("--backing", action="store_true", help="Check reached first/no-remap backing OOM, shared cleanup/completion and existing failure consumers with one scoped fresh replay.")
    selection.add_argument("--growth", action="store_true", help="Check reached nonempty relocation, shared native graph/payload proofs and proper-child general-step consumers with one scoped fresh replay.")
    selection.add_argument("--first", action="store_true", help="Check reached first publication, arbitrary empty sentinels/callbacks and the shared first/spare/relocation completion with one scoped fresh replay.")
    selection.add_argument("--spare", action="store_true", help="Check reached spare native preservation and general-step, existing spare caller, growth-chain and native constant consumers.")
    selection.add_argument("--take", action="store_true", help="Check take OOM and shared return composition with lookup, entry, cache, named-local and normalization consumers.")
    selection.add_argument("--lookup", action="store_true", help="Check shared initialized routing/return and classification errors with cache/taken consumers.")
    selection.add_argument("--entry", action="store_true", help="Check pre-lookup entry failures, derived scratch allocation and existing normalization/cache consumers.")
    selection.add_argument("--cache", action="store_true", help="Include general cache-hit entry and existing named-local consumers.")
    selection.add_argument("--preparation", action="store_true", help="Include reached preparation/capacity model coupling and entry-caller specialization checks.")
    check(parser.parse_args())
