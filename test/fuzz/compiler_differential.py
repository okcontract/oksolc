#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.
"""Stateful oksolc-versus-solc differential campaign and reducer."""

from __future__ import annotations

import argparse
from copy import deepcopy
from dataclasses import asdict, dataclass
import hashlib
import json
import os
from pathlib import Path
import posixpath
import queue
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from typing import Any, Callable, Sequence


REFERENCE_VERSION = "0.8.36"
PREAMBLE = f"// SPDX-License-Identifier: UNLICENSED\npragma solidity {REFERENCE_VERSION};\n"
ARTIFACTS = (
    (
        "storageLayout",
        "evm.bytecode.object",
        "evm.deployedBytecode.object",
        "evm.methodIdentifiers",
    ),
    ("evm.deployedBytecode.object",),
    ("abi", "evm.bytecode.object"),
)
OPTIMIZER_RUNS = (0, 1, 200, 1_000, 10_000)
RECURSIVE_SHAPES = (
    "contract Recursive { struct A { B[] children; } struct B { A parent; } }",
    "contract Recursive { struct A { mapping(uint256 => B) children; } struct B { A parent; } }",
    "contract Recursive { struct A { A[] children; } }",
    "contract Recursive { struct A { B[1] child; } struct B { A parent; } }",
    "contract Recursive { struct A { B[] children; } struct B { B parent; } }",
)
ACTIONS = (
    "first_body",
    "second_body",
    "signature_failure",
    "selective_reexport",
    "import_cycle",
    "imported_alias_swap",
    "recursive_shape",
    "alternate_source_names",
    "reverse_source_order",
    "extra_source",
    "optimizer_runs",
    "projection",
    "inherited_body",
    "library_body",
    "modifier_limit",
    "wide_base_storage",
    "inherited_signature_failure",
    "super_signature_failure",
    "error_signature_failure",
)
IMPORT_PATTERN = re.compile(r"\bimport\b[^;]*?[\"']([^\"']+)[\"'][^;]*;", re.DOTALL)
REFERENCE_CORPUS_EXCLUSIONS = {
    "legacy-smoke.json": "legacy code generation is outside the via-IR compatibility target",
    "solidity-named-events-errors-bytecode.json": "intentional HACK-28 named-argument correction",
    "solidity-require-named-errors-bytecode.json": "intentional HACK-28 named-argument correction",
}
BOUNDARY_NUMBERS = (
    "0",
    "1",
    "2",
    "7",
    "31",
    "32",
    "255",
    "256",
    "2147483647",
    "2147483648",
    "4294967295",
    "18446744073709551616",
    "57896044618658097711785492504343953926634992332820282019728792003956564819968",
    "115792089237316195423570985008687907853269984665640564039457584007913129639935",
    "115792089237316195423570985008687907853269984665640564039457584007913129639936",
)
EVM_VERSIONS = (
    "homestead",
    "byzantium",
    "constantinople",
    "istanbul",
    "berlin",
    "london",
    "paris",
    "shanghai",
    "cancun",
    "prague",
    "osaka",
)
SOURCE_MUTATIONS = (
    (re.compile(r"(?<=\[)[0-9](?:_?[0-9])*(?=\])"), BOUNDARY_NUMBERS),
    (re.compile(r"(?<![A-Za-z0-9_.$])(?:0x[0-9A-Fa-f]+|[0-9](?:_?[0-9])*)(?![A-Za-z0-9_.$])"), BOUNDARY_NUMBERS),
    (
        re.compile(r'hex"(?:[0-9A-Fa-f]{2})*"'),
        ('hex""', 'hex"00"', 'hex"ff"', 'hex"c080"', 'hex"0102030405"'),
    ),
    (re.compile(r"\b(?:true|false)\b"), ("true", "false")),
    (
        re.compile(r"\buint(?:8|16|32|64|128|160|192|224|256)?\b"),
        ("uint8", "uint32", "uint64", "uint128", "uint160", "uint256"),
    ),
    (
        re.compile(r"\bint(?:8|16|32|64|128|160|192|224|256)?\b"),
        ("int8", "int32", "int64", "int128", "int160", "int256"),
    ),
    (
        re.compile(r"\bbytes(?:1|2|4|8|16|20|24|32)?\b"),
        ("bytes", "bytes1", "bytes4", "bytes20", "bytes32"),
    ),
    (re.compile(r"\baddress(?:\s+payable)?\b"), ("address", "address payable")),
    (re.compile(r"\b(?:external|public|internal|private)\b"), ("external", "public", "internal", "private")),
    (re.compile(r"\b(?:pure|view|payable)\b"), ("pure", "view", "payable")),
    (re.compile(r"\b(?:memory|calldata|storage)\b"), ("memory", "calldata", "storage")),
    (re.compile(r"\[\]|\[[123]\]"), ("[]", "[1]", "[2]", "[3]")),
    (re.compile(r"(?<=\s)(?:<=|>=|==|!=|<|>)(?=\s)"), ("<", "<=", ">", ">=", "==", "!=")),
    (re.compile(r"(?<=\s)(?:&&|\|\|)(?=\s)"), ("&&", "||")),
    (re.compile(r"(?<=\s)(?:\+|-|\*|/|%)(?=\s)"), ("+", "-", "*", "/", "%")),
)
MUTATIONS_PER_REVISION = (1, 1, 2, 3)
STORAGE_ELEMENT_TYPES = ("uint8", "uint128", "uint256", "bytes31", "Word")
FIXED_BYTES_TYPES = ("bytes1", "bytes2", "bytes4", "bytes20", "bytes32")
STRING_LITERALS = ('""', '"a"', '"root"', 'hex"00"', 'hex"ff"', 'hex"c080"')
FIXED_POINT_BITS = (8, 32, 64, 128, 256)
FIXED_POINT_DECIMALS = (0, 1, 10, 18, 79, 80)


@dataclass
class ProjectState:
    first_body: int = 1
    second_body: int = 2
    signature_failure: bool = False
    selective_reexport: bool = False
    import_cycle: bool = False
    imported_alias_swap: bool = False
    recursive_shape: int = 0
    alternate_source_names: bool = False
    reverse_source_order: bool = False
    extra_source: bool = False
    optimizer_runs: int = 200
    projection: int = 0
    inherited_body: int = 3
    library_body: int = 4
    modifier_limit: int = 64
    wide_base_storage: bool = False
    inherited_signature_failure: bool = False
    super_signature_failure: bool = False
    error_signature_failure: bool = False

    def mutate(self, rng: random.Random) -> None:
        action = rng.choice(ACTIONS)
        if action in ("first_body", "second_body", "inherited_body", "library_body"):
            setattr(self, action, rng.randint(1, 63))
        elif action == "modifier_limit":
            self.modifier_limit = rng.randint(2, 63)
        elif action == "recursive_shape":
            self.recursive_shape = rng.randrange(len(RECURSIVE_SHAPES))
        elif action == "optimizer_runs":
            self.optimizer_runs = rng.choice(OPTIMIZER_RUNS)
        elif action == "projection":
            self.projection = rng.randrange(len(ARTIFACTS))
        else:
            setattr(self, action, not getattr(self, action))


@dataclass
class Failure:
    kind: str
    revision: int
    path: tuple[str, ...]
    detail: str
    reference: Any = None
    candidate: Any = None
    candidate_fresh: Any = None
    session_mode: str = "memory"
    oracle: str = "reference"

    def diagnostic_signature(self) -> tuple[tuple[str, ...], tuple[str, ...]]:
        def error_codes(output: Any) -> tuple[str, ...]:
            if not isinstance(output, dict) or not isinstance(output.get("errors"), list):
                return ()
            signature = []
            for diagnostic in output["errors"]:
                if not isinstance(diagnostic, dict) or diagnostic.get("severity") != "error":
                    continue
                code = diagnostic.get("errorCode")
                signature.append(
                    str(code)
                    if code is not None
                    else f"{diagnostic.get('type', '<uncoded>')}:{diagnostic.get('message', '')}"
                )
            return tuple(signature)

        return error_codes(self.reference), error_codes(self.candidate)

    def campaign_diagnostic_signature(self) -> tuple[Any, ...]:
        def diagnostics(output: Any) -> list[Any]:
            if not isinstance(output, dict) or not isinstance(output.get("errors"), list):
                return []
            return output["errors"]

        def identity(diagnostic: Any) -> str:
            if not isinstance(diagnostic, dict):
                return f"<invalid>:{diagnostic!r}"
            code = diagnostic.get("errorCode")
            if code is not None:
                return str(code)
            return f"{diagnostic.get('type', '<uncoded>')}:{diagnostic.get('message', '')}"

        reference = diagnostics(self.reference)
        candidate = diagnostics(self.candidate)
        if len(self.path) > 1 and self.path[1].isdigit():
            index = int(self.path[1])
            reference_item = identity(reference[index]) if index < len(reference) else "<missing>"
            candidate_item = identity(candidate[index]) if index < len(candidate) else "<missing>"
            return self.path[-1], reference_item, candidate_item

        def error_identities(values: list[Any]) -> list[str]:
            return [
                identity(value)
                for value in values
                if isinstance(value, dict) and value.get("severity") == "error"
            ]

        reference_errors = error_identities(reference)
        candidate_errors = error_identities(candidate)
        for index in range(max(len(reference_errors), len(candidate_errors))):
            reference_item = (
                reference_errors[index] if index < len(reference_errors) else "<missing>"
            )
            candidate_item = (
                candidate_errors[index] if index < len(candidate_errors) else "<missing>"
            )
            if reference_item != candidate_item:
                return reference_item, candidate_item
        return ()

    def campaign_signature(self) -> tuple[Any, ...]:
        path = (
            ("errors", self.path[-1])
            if self.path[:1] == ("errors",)
            else self.path[:5]
        )
        return (
            self.kind,
            path,
            self.session_mode,
            self.oracle,
            self.campaign_diagnostic_signature()
            if self.path[:1] == ("errors",)
            else self.diagnostic_signature(),
        )

    def compatible(self, other: Failure) -> bool:
        return (
            self.kind == other.kind
            and self.path[:2] == other.path[:2]
            and self.session_mode == other.session_mode
            and self.oracle == other.oracle
            and (
                self.path[:1] != ("errors",)
                or self.diagnostic_signature() == other.diagnostic_signature()
            )
        )


def request_for_state(state: ProjectState) -> dict[str, Any]:
    first_name = "RenamedA.sol" if state.alternate_source_names else "A.sol"
    reexport_name = "RenamedB.sol" if state.alternate_source_names else "B.sol"
    first_type = "bytes32" if state.signature_failure else "uint256"
    first_expression = "uint256(x)" if state.signature_failure else "x"
    first_source = (
        PREAMBLE
        + f"function f({first_type} x) pure returns (uint256) {{\n"
        + f"    return {first_expression} + {state.first_body};\n"
        + "}\n"
        + "function f(address) pure returns (uint256) {\n"
        + f"    return {state.second_body};\n"
        + "}\n"
    )
    if state.selective_reexport:
        reexport_import = f'import {{f as exportF}} from "{first_name}";\n'
        called_symbol = "exportF"
    else:
        reexport_import = f'import "{first_name}";\n'
        called_symbol = "f"
    reexport_source = (
        PREAMBLE
        + reexport_import
        + ('import "Cycle.sol";\n' if state.import_cycle else "")
        + "library ReexportMarker {\n"
        + "    function marker() internal pure returns (uint256) { return 1; }\n"
        + "}\n"
    )
    cycle_source = PREAMBLE
    if state.import_cycle:
        cycle_source += f'import "{reexport_name}";\n'
    cycle_source += "library CycleMarker {}\n"
    auth_source = (
        PREAMBLE
        + "function authorized(uint256 value) pure returns (bool) {\n"
        + "    return value == 7;\n"
        + "}\n"
        + "function rejected(uint256 value) pure returns (bool) {\n"
        + "    return value != 7;\n"
        + "}\n"
    )
    alias_import = (
        "import {authorized as rejected, rejected as authorized} from \"Auth.sol\";\n"
        if state.imported_alias_swap
        else "import {authorized, rejected} from \"Auth.sol\";\n"
    )
    main_source = (
        PREAMBLE
        + f'import * as R from "{reexport_name}";\n'
        + 'import * as M from "Aliases.sol";\n'
        + "using {M.authorized, M.rejected} for uint256;\n"
        + "contract Main {\n"
        + "    function symbol(uint256 x) external pure returns (uint256) {\n"
        + f"        return R.{called_symbol}(x);\n"
        + "    }\n"
        + "    function isAuthorized(uint256 x) external pure returns (bool) {\n"
        + "        return x.authorized();\n"
        + "    }\n"
        + "    function isRejected(uint256 x) external pure returns (bool) {\n"
        + "        return x.rejected();\n"
        + "    }\n"
        + "}\n"
    )
    storage_members = (
        "uint256 internal left; uint256 internal right;"
        if state.wide_base_storage
        else "uint128 internal left; uint128 internal right;"
    )
    inherited_type = "bytes32" if state.inherited_signature_failure else "uint256"
    inherited_value = "uint256(value)" if state.inherited_signature_failure else "value"
    super_type = "uint64" if state.super_signature_failure else "uint256"
    error_type = "bytes32" if state.error_signature_failure else "uint256"
    dependency_source = (
        PREAMBLE
        + "struct Payload { uint256 value; uint256 salt; }\n"
        + "library PayloadLib {\n"
        + "    function score(Payload memory self) internal pure returns (uint256) {\n"
        + f"        return self.value * 3 + self.salt + {state.library_body};\n"
        + "    }\n"
        + "}\n"
        + f"error SharedError({error_type} value);\n"
        + "contract Base {\n"
        + f"    {storage_members}\n"
        + "    modifier adjusted(uint256 value) {\n"
        + f"        require(value < {state.modifier_limit});\n"
        + "        _;\n"
        + "    }\n"
        + f"    function inherited({inherited_type} value) public pure returns (uint256) {{\n"
        + f"        return {inherited_value} + {state.inherited_body};\n"
        + "    }\n"
        + "}\n"
    )
    consumer_source = (
        PREAMBLE
        + 'import {Base, Payload, PayloadLib, SharedError} from "Dependency.sol";\n'
        + "using PayloadLib for Payload;\n"
        + "contract Consumer is Base {\n"
        + "    function run(uint256 value) external pure adjusted(value) returns (uint256) {\n"
        + "        if (value == 0) revert SharedError(value);\n"
        + "        return inherited(value) + Payload(value, 5).score();\n"
        + "    }\n"
        + "}\n"
    )
    hierarchy_source = (
        PREAMBLE
        + "contract ConcreteBase {\n"
        + "    function dispatch(bool value) public pure virtual returns (uint256) {\n"
        + "        return value ? 1 : 2147483648;\n"
        + "    }\n"
        + f"    function dispatch({super_type} value) public pure virtual returns (uint256) {{\n"
        + "        return value + 17;\n"
        + "    }\n"
        + "}\n"
        + "abstract contract AbstractBase {\n"
        + "    function dispatch(uint256 value) public pure virtual returns (uint256);\n"
        + "}\n"
        + "contract SuperConsumer is ConcreteBase, AbstractBase {\n"
        + "    function dispatch(uint256 value) public pure override(ConcreteBase, AbstractBase) returns (uint256) {\n"
        + "        return super.dispatch(value);\n"
        + "    }\n"
        + "}\n"
    )
    source_entries = [
        (first_name, first_source),
        (reexport_name, reexport_source),
        ("Cycle.sol", cycle_source),
        ("Auth.sol", auth_source),
        ("Aliases.sol", PREAMBLE + alias_import),
        ("Recursive.sol", PREAMBLE + RECURSIVE_SHAPES[state.recursive_shape] + "\n"),
        ("Main.sol", main_source),
        ("Dependency.sol", dependency_source),
        ("Consumer.sol", consumer_source),
        ("Hierarchy.sol", hierarchy_source),
    ]
    if state.reverse_source_order:
        source_entries.reverse()
    if state.extra_source:
        source_entries.append(
            (
                "Extra.sol",
                PREAMBLE
                + "contract Extra {\n"
                + "    function value() external pure returns (uint256) { return 99; }\n"
                + "}\n",
            )
        )
    return {
        "language": "Solidity",
        "sources": {name: {"content": source} for name, source in source_entries},
        "settings": {
            "viaIR": True,
            "optimizer": {"enabled": True, "runs": state.optimizer_runs},
            "metadata": {"appendCBOR": False},
            "outputSelection": {"*": {"*": list(ARTIFACTS[state.projection])}},
        },
    }


def generate_history(rng: random.Random, max_revisions: int) -> list[dict[str, Any]]:
    state = ProjectState()
    history = [request_for_state(state)]
    for _ in range(rng.randint(1, max_revisions - 1)):
        state.mutate(rng)
        history.append(request_for_state(state))
    return history


def storage_boundary_request(
    array_length: str,
    base_slot: str,
    element_type: str,
) -> dict[str, Any]:
    return {
        "language": "Solidity",
        "sources": {
            "StorageBoundary.sol": {
                "content": (
                    PREAMBLE
                    + "type Word is uint32;\n"
                    + "contract Base { uint128 base; }\n"
                    + f"contract Layout is Base layout at {base_slot} {{\n"
                    + f"    struct Data {{ {element_type}[{array_length}] values; }}\n"
                    + "    Data data;\n"
                    + "    uint256 transient scratch;\n"
                    + "}\n"
                )
            }
        },
        "settings": {
            "viaIR": False,
            "outputSelection": {
                "*": {"Layout": ["storageLayout", "transientStorageLayout"]}
            },
        },
    }


def conversion_boundary_request(
    fixed_type: str,
    fixed_literal: str,
    string_literal: str,
) -> dict[str, Any]:
    return {
        "language": "Solidity",
        "sources": {
            "ConversionBoundary.sol": {
                "content": (
                    PREAMBLE
                    + "contract ConversionBoundary {\n"
                    + "    function f() external pure {\n"
                    + f"        {fixed_type}({fixed_literal});\n"
                    + f"        string({string_literal});\n"
                    + "    }\n"
                    + "}\n"
                )
            }
        },
        "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
    }


def fixed_point_boundary_request(
    source_bits: int,
    source_decimals: int,
    target_bits: int,
    target_decimals: int,
    source_unsigned: bool,
    target_unsigned: bool,
) -> dict[str, Any]:
    source_prefix = "u" if source_unsigned else ""
    target_prefix = "u" if target_unsigned else ""
    source_type = f"{source_prefix}fixed{source_bits}x{source_decimals}"
    target_type = f"{target_prefix}fixed{target_bits}x{target_decimals}"
    return {
        "language": "Solidity",
        "sources": {
            "FixedPointBoundary.sol": {
                "content": (
                    PREAMBLE
                    + "contract FixedPointBoundary {\n"
                    + f"    {source_type} value;\n"
                    + f"    {target_type} converted = value;\n"
                    + "}\n"
                )
            }
        },
        "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
    }


def generate_targeted_history(
    rng: random.Random,
    max_revisions: int,
) -> list[dict[str, Any]]:
    revision_count = rng.randint(2, max_revisions)
    history_kind = rng.randrange(3)
    if history_kind == 0:
        array_length = "2"
        base_slot = "42"
        element_type = "uint256"
        history = [storage_boundary_request(array_length, base_slot, element_type)]
        for _ in range(revision_count - 1):
            field = rng.randrange(3)
            if field == 0:
                array_length = rng.choice(BOUNDARY_NUMBERS)
            elif field == 1:
                base_slot = rng.choice(BOUNDARY_NUMBERS)
            else:
                element_type = rng.choice(STORAGE_ELEMENT_TYPES)
            history.append(storage_boundary_request(array_length, base_slot, element_type))
        return history

    if history_kind == 1:
        fixed_type = "bytes4"
        fixed_literal = '"root"'
        string_literal = 'hex"726f6f74"'
        history = [conversion_boundary_request(fixed_type, fixed_literal, string_literal)]
        for _ in range(revision_count - 1):
            field = rng.randrange(3)
            if field == 0:
                fixed_type = rng.choice(FIXED_BYTES_TYPES)
            elif field == 1:
                fixed_literal = rng.choice(STRING_LITERALS)
            else:
                string_literal = rng.choice(STRING_LITERALS)
            history.append(
                conversion_boundary_request(fixed_type, fixed_literal, string_literal)
            )
        return history

    source_bits = 128
    source_decimals = 18
    target_bits = 128
    target_decimals = 18
    source_unsigned = False
    target_unsigned = False
    history = [
        fixed_point_boundary_request(
            source_bits,
            source_decimals,
            target_bits,
            target_decimals,
            source_unsigned,
            target_unsigned,
        )
    ]
    for _ in range(revision_count - 1):
        field = rng.randrange(6)
        if field == 0:
            source_bits = rng.choice(FIXED_POINT_BITS)
        elif field == 1:
            source_decimals = rng.choice(FIXED_POINT_DECIMALS)
        elif field == 2:
            target_bits = rng.choice(FIXED_POINT_BITS)
        elif field == 3:
            target_decimals = rng.choice(FIXED_POINT_DECIMALS)
        elif field == 4:
            source_unsigned = not source_unsigned
        else:
            target_unsigned = not target_unsigned
        history.append(
            fixed_point_boundary_request(
                source_bits,
                source_decimals,
                target_bits,
                target_decimals,
                source_unsigned,
                target_unsigned,
            )
        )
    return history


def load_corpus_requests(directory: Path) -> list[tuple[str, dict[str, Any]]]:
    requests: list[tuple[str, dict[str, Any]]] = []
    for path in sorted(directory.glob("*.json")):
        try:
            request = json.loads(path.read_text())
        except json.JSONDecodeError as error:
            raise RuntimeError(f"invalid transition corpus JSON {path}: {error}") from error
        if not isinstance(request, dict):
            continue
        sources = request.get("sources")
        if request.get("language") not in ("Solidity", "Yul") or not isinstance(sources, dict):
            continue
        if not all(
            isinstance(source, dict) and isinstance(source.get("content"), str)
            for source in sources.values()
        ):
            continue
        normalized_names = {posixpath.normpath(name) for name in sources}
        self_contained = True
        for source_name, source in sources.items():
            for match in IMPORT_PATTERN.finditer(source["content"]):
                imported = match.group(1)
                resolved = posixpath.normpath(
                    posixpath.join(posixpath.dirname(source_name), imported)
                )
                if posixpath.normpath(imported) not in normalized_names and resolved not in normalized_names:
                    self_contained = False
                    break
            if not self_contained:
                break
        if not self_contained:
            continue
        requests.append((path.name, request))
    if not requests:
        raise RuntimeError(f"transition corpus contains no inline compiler requests: {directory}")
    return requests


def requests_ir_text(request: dict[str, Any]) -> bool:
    output_selection = request.get("settings", {}).get("outputSelection", {})

    def contains_ir(value: Any) -> bool:
        if isinstance(value, list):
            return "ir" in value or "irOptimized" in value
        if isinstance(value, dict):
            return any(contains_ir(child) for child in value.values())
        return False

    return contains_ir(output_selection)


def without_ir_text(value: Any) -> Any:
    if isinstance(value, list):
        return [without_ir_text(item) for item in value]
    if isinstance(value, dict):
        return {
            key: without_ir_text(child)
            for key, child in value.items()
            if key not in ("ir", "irOptimized")
        }
    return value


IR_TEXT_VALUE = re.compile(
    rb'("(?:ir|irOptimized)"[ \t\r\n]*:[ \t\r\n]*)"(?:[^"\\]|\\.)*"'
)


def without_raw_ir_text(value: bytes) -> bytes:
    return IR_TEXT_VALUE.sub(lambda match: match.group(1) + b'""', value)


def audit_reference_corpus(
    candidate: Path,
    reference: Path,
    entries: Sequence[tuple[str, dict[str, Any]]],
    timeout: float,
) -> tuple[int, int, tuple[str, dict[str, Any], Failure] | None]:
    checked = 0
    skipped = 0
    for name, request in entries:
        if name in REFERENCE_CORPUS_EXCLUSIONS:
            skipped += 1
            continue
        reference_raw, reference_output = run_compiler_response(
            reference,
            request,
            timeout,
        )
        candidate_raw, candidate_output = run_compiler_response(
            candidate,
            request,
            timeout,
            candidate=True,
        )
        checked += 1
        if has_internal_compiler_error(reference_output):
            skipped += 1
            continue
        path = response_mismatch_path(
            request,
            "reference",
            reference_raw,
            reference_output,
            candidate_raw,
            candidate_output,
        )
        if path is None:
            continue
        return checked, skipped, (
            name,
            request,
            Failure(
                "output-mismatch",
                0,
                path,
                f"clean oksolc differs from solc 0.8.36 for corpus case {name}",
                reference_output,
                candidate_output,
                candidate_output,
                oracle="reference",
            ),
        )
    return checked, skipped, None


def corpus_transition_histories(
    directory: Path,
    rng: random.Random,
    max_revisions: int,
) -> list[list[dict[str, Any]]]:
    requests = [request for _, request in load_corpus_requests(directory)]

    rng.shuffle(requests)
    histories: list[list[dict[str, Any]]] = []
    batch_size = max_revisions - 1
    for start in range(0, len(requests), batch_size):
        batch = requests[start : start + batch_size]
        history = deepcopy(batch)
        restored = deepcopy(batch[0])
        restored = {key: restored[key] for key in reversed(restored)}
        history.append(restored)
        histories.append(history)
    return histories


def mutate_corpus_request(
    request: dict[str, Any],
    rng: random.Random,
) -> dict[str, Any]:
    result = deepcopy(request)
    sources = result["sources"]
    first_action = rng.randrange(len(SOURCE_MUTATIONS) + 2)
    if first_action >= len(SOURCE_MUTATIONS):
        settings = result.setdefault("settings", {})
        if first_action == len(SOURCE_MUTATIONS):
            optimizer = settings.setdefault("optimizer", {})
            optimizer["enabled"] = not bool(optimizer.get("enabled", False))
            optimizer["runs"] = rng.choice(OPTIMIZER_RUNS)
        else:
            settings["evmVersion"] = rng.choice(EVM_VERSIONS)
        return result

    for offset in range(len(SOURCE_MUTATIONS)):
        action = (first_action + offset) % len(SOURCE_MUTATIONS)
        pattern, replacements = SOURCE_MUTATIONS[action]
        matches = [
            (source, match)
            for source in sources.values()
            for match in pattern.finditer(source["content"])
        ]
        if not matches:
            continue
        source, match = rng.choice(matches)
        choices = [value for value in replacements if value != match.group(0)]
        if not choices:
            continue
        replacement = rng.choice(choices)
        content = source["content"]
        source["content"] = content[: match.start()] + replacement + content[match.end() :]
        return result
    return result


def generate_corpus_mutation_history(
    entries: Sequence[tuple[str, dict[str, Any]]],
    rng: random.Random,
    max_revisions: int,
) -> list[dict[str, Any]]:
    eligible = [
        request
        for name, request in entries
        if name not in REFERENCE_CORPUS_EXCLUSIONS and not requests_ir_text(request)
    ]
    if not eligible:
        raise RuntimeError("transition corpus contains no reference-compatible requests")
    current = deepcopy(rng.choice(eligible))
    history = [current]
    for _ in range(rng.randint(1, max_revisions - 1)):
        for _ in range(rng.choice(MUTATIONS_PER_REVISION)):
            current = mutate_corpus_request(current, rng)
        history.append(current)
    return history


def seed_histories() -> tuple[list[dict[str, Any]], ...]:
    reexport = ProjectState()
    reexport_history = [request_for_state(reexport)]
    reexport.selective_reexport = True
    reexport_history.append(request_for_state(reexport))
    reexport.first_body = 20
    reexport_history.append(request_for_state(reexport))
    reexport.signature_failure = True
    reexport_history.append(request_for_state(reexport))
    reexport.signature_failure = False
    reexport_history.append(request_for_state(reexport))

    aliases = ProjectState()
    alias_history = [request_for_state(aliases)]
    aliases.imported_alias_swap = True
    alias_history.append(request_for_state(aliases))
    aliases.reverse_source_order = True
    alias_history.append(request_for_state(aliases))

    recursive = ProjectState()
    recursive_history = [request_for_state(recursive)]
    recursive.recursive_shape = 3
    recursive_history.append(request_for_state(recursive))
    recursive.recursive_shape = 4
    recursive_history.append(request_for_state(recursive))
    recursive.recursive_shape = 1
    recursive_history.append(request_for_state(recursive))

    dependencies = ProjectState()
    dependency_history = [request_for_state(dependencies)]
    dependencies.inherited_body = 9
    dependency_history.append(request_for_state(dependencies))
    dependencies.library_body = 11
    dependency_history.append(request_for_state(dependencies))
    dependencies.modifier_limit = 32
    dependency_history.append(request_for_state(dependencies))
    dependencies.wide_base_storage = True
    dependency_history.append(request_for_state(dependencies))
    dependencies.inherited_signature_failure = True
    dependency_history.append(request_for_state(dependencies))
    dependencies.inherited_signature_failure = False
    dependency_history.append(request_for_state(dependencies))
    dependencies.error_signature_failure = True
    dependency_history.append(request_for_state(dependencies))
    dependencies.error_signature_failure = False
    dependency_history.append(request_for_state(dependencies))

    hierarchy = ProjectState()
    hierarchy_history = [request_for_state(hierarchy)]
    hierarchy.super_signature_failure = True
    hierarchy_history.append(request_for_state(hierarchy))
    hierarchy.super_signature_failure = False
    hierarchy_history.append(request_for_state(hierarchy))

    def backend_request(evm_version: str, optimizer: bool, offset: int) -> dict[str, Any]:
        return {
            "language": "Solidity",
            "sources": {
                "Backend.sol": {
                    "content": PREAMBLE
                    + "contract Backend { function f(uint256 value) external pure returns "
                    + f"(uint256) {{ return value + {offset}; }} }}\n"
                }
            },
            "settings": {
                "evmVersion": evm_version,
                "viaIR": True,
                "optimizer": {"enabled": optimizer, "runs": 200},
                "outputSelection": {"*": {"*": ["evm.bytecode.object"]}},
            },
        }

    backend_history = [
        backend_request("osaka", True, 0),
        backend_request("homestead", False, 0),
        backend_request("osaka", True, 1),
    ]

    def diagnostic_request(initializer: str, index: int) -> dict[str, Any]:
        return {
            "language": "Solidity",
            "sources": {
                "Diagnostics.sol": {
                    "content": PREAMBLE
                    + "contract Diagnostics { function f() external pure returns (uint256) { "
                    + f"uint256[1] memory values = {initializer}; return values[{index}]; }} }}\n"
                }
            },
            "settings": {
                "viaIR": True,
                "outputSelection": {"*": {"*": ["evm.bytecode.object"]}},
            },
        }

    diagnostic_history = [
        diagnostic_request("[uint256(1)]", 0),
        diagnostic_request("new uint256[](2)", 2),
        diagnostic_request("[uint256(9)]", 0),
    ]

    def resolution_request(first_missing: bool, second_missing: bool) -> dict[str, Any]:
        first_body = "missingFirst();" if first_missing else ""
        second_body = "missingSecond();" if second_missing else ""
        return {
            "language": "Solidity",
            "sources": {
                "Resolution.sol": {
                    "content": PREAMBLE
                    + f"contract First {{ function f() external {{ {first_body} }} }}\n"
                    + f"contract Second {{ function f() external {{ {second_body} }} }}\n"
                }
            },
            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
        }

    resolution_history = [
        resolution_request(False, False),
        resolution_request(True, True),
        resolution_request(False, True),
        resolution_request(False, False),
    ]

    def push_request(base_type: str, value: int) -> dict[str, Any]:
        return {
            "language": "Solidity",
            "sources": {
                "Push.sol": {
                    "content": PREAMBLE
                    + f"contract Push {{ {base_type}[] values; "
                    + f"function f() external {{ values.push({value}); }} }}\n"
                }
            },
            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
        }

    push_history = [
        push_request("uint8", 1),
        push_request("uint8", 256),
        push_request("uint256", 256),
    ]

    def yul_ast_request(literal: str) -> dict[str, Any]:
        return {
            "language": "Solidity",
            "sources": {
                "Assembly.sol": {
                    "content": "contract C { function f() public { assembly { "
                    + f"mstore({literal}, 1)"
                    + " } } }"
                }
            },
            "settings": {
                "stopAfter": "parsing",
                "outputSelection": {"Assembly.sol": {"": ["ast"]}},
            },
        }

    yul_ast_history = [
        yul_ast_request("32"),
        yul_ast_request(
            "115792089237316195423570985008687907853269984665640564039457584007913129639936"
        ),
        yul_ast_request("64"),
    ]

    def static_library_request(parameter_type: str) -> dict[str, Any]:
        return {
            "language": "Solidity",
            "sources": {
                "Library.sol": {
                    "content": PREAMBLE
                    + f"library L {{ function f({parameter_type} value) external pure "
                    + f"returns ({parameter_type}) {{ return value; }} }}\n"
                },
                "Consumer.sol": {
                    "content": PREAMBLE
                    + 'import {L} from "Library.sol";\n'
                    + "contract C { function f(uint256 value) external returns (uint256) { "
                    + "return L.f(value); } }\n"
                },
            },
            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
        }

    static_library_history = [
        static_library_request("uint256"),
        static_library_request("uint32"),
        static_library_request("uint8"),
        static_library_request("uint256"),
    ]

    def inner_cycle_request(array_length: str, self_cycle: bool) -> dict[str, Any]:
        parent_type = "B" if self_cycle else "uint256"
        return {
            "language": "Solidity",
            "sources": {
                "Cycle.sol": {
                    "content": PREAMBLE
                    + f"contract C {{ struct A {{ B[{array_length}] children; }} "
                    + f"struct B {{ {parent_type} parent; }} }}\n"
                }
            },
            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
        }

    inner_cycle_history = [
        inner_cycle_request("1", False),
        inner_cycle_request("0", True),
        inner_cycle_request(
            "115792089237316195423570985008687907853269984665640564039457584007913129639936",
            True,
        ),
        inner_cycle_request("1", False),
    ]
    storage_boundary_history = [
        storage_boundary_request("2", "42", "uint256"),
        storage_boundary_request(
            "57896044618658097711785492504343953926634992332820282019728792003956564819968",
            "42",
            "uint256",
        ),
        storage_boundary_request(
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            "42",
            "Word",
        ),
        storage_boundary_request("2", "42", "uint256"),
    ]
    conversion_boundary_history = [
        conversion_boundary_request("bytes4", '"root"', 'hex"726f6f74"'),
        conversion_boundary_request("bytes1", '"root"', 'hex"726f6f74"'),
        conversion_boundary_request("bytes4", '"root"', 'hex"ff"'),
        conversion_boundary_request("bytes4", '"root"', 'hex"726f6f74"'),
    ]
    fixed_point_boundary_history = [
        fixed_point_boundary_request(128, 18, 128, 18, False, False),
        fixed_point_boundary_request(128, 18, 128, 10, False, False),
        fixed_point_boundary_request(128, 18, 128, 10, True, True),
        fixed_point_boundary_request(128, 18, 128, 10, False, True),
        fixed_point_boundary_request(128, 18, 128, 18, False, False),
    ]
    return (
        reexport_history,
        alias_history,
        recursive_history,
        dependency_history,
        hierarchy_history,
        backend_history,
        diagnostic_history,
        resolution_history,
        push_history,
        yul_ast_history,
        static_library_history,
        inner_cycle_history,
        storage_boundary_history,
        conversion_boundary_history,
        fixed_point_boundary_history,
    )


def encode_request(request: dict[str, Any]) -> bytes:
    return json.dumps(request, ensure_ascii=False, separators=(",", ":")).encode()


def resolve_executable(value: str) -> Path:
    if os.sep in value or (os.altsep and os.altsep in value):
        result = Path(value).expanduser().resolve()
        if not result.is_file():
            raise RuntimeError(f"executable does not exist: {result}")
        return result
    found = shutil.which(value)
    if found is None:
        raise RuntimeError(f"executable not found on PATH: {value}")
    return Path(found).resolve()


def compiler_version(executable: Path, *args: str) -> str:
    result = subprocess.run(
        [str(executable), *args, "--version"],
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )
    if result.returncode != 0:
        raise RuntimeError(f"{executable} --version failed: {result.stdout}{result.stderr}")
    return result.stdout.strip()


def evm_environment(executable: Path) -> dict[str, str]:
    environment = dict(os.environ)
    library_directory = executable.parent.parent / "lib"
    if library_directory.is_dir():
        for name in ("LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"):
            existing = environment.get(name)
            environment[name] = (
                f"{library_directory}{os.pathsep}{existing}"
                if existing
                else str(library_directory)
            )
    return environment


def evm_version(executable: Path) -> str:
    result = subprocess.run(
        [str(executable), "--version"],
        check=False,
        capture_output=True,
        env=evm_environment(executable),
        text=True,
        timeout=20,
    )
    if result.returncode != 0:
        raise RuntimeError(f"{executable} --version failed: {result.stdout}{result.stderr}")
    return (result.stdout + result.stderr).strip()


def read_exact(stream: Any, length: int) -> bytes:
    chunks: list[bytes] = []
    remaining = length
    while remaining:
        chunk = stream.read(remaining)
        if not chunk:
            raise EOFError("compiler service closed an incomplete response")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


class CandidateService:
    def __init__(
        self,
        executable: Path,
        timeout: float,
        directory: Path,
        session_mode: str,
    ):
        self.timeout = timeout
        self.responses: queue.Queue[bytes | Exception] = queue.Queue()
        self.errors: list[bytes] = []
        environment = dict(os.environ)
        environment["XDG_CACHE_HOME"] = str(directory / "cache")
        environment["XDG_CONFIG_HOME"] = str(directory / "config")
        command = [str(executable), "serve", "--stdio", "--solc-version", REFERENCE_VERSION]
        if session_mode == "memory":
            command.append("--no-cache")
        else:
            config = directory / "config" / "oksolc"
            config.mkdir(parents=True, exist_ok=True)
            (config / "config.toml").write_text("cache = true\n")
        self.process = subprocess.Popen(
            command,
            cwd=directory,
            env=environment,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.reader = threading.Thread(target=self._read_responses, daemon=True)
        self.error_reader = threading.Thread(target=self._read_errors, daemon=True)
        self.writer: threading.Thread | None = None
        self.closed = False
        self.reader.start()
        self.error_reader.start()

    def _read_responses(self) -> None:
        try:
            assert self.process.stdout is not None
            while True:
                content_length: int | None = None
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        if content_length is None:
                            raise EOFError("compiler service closed before response")
                        raise EOFError("compiler service closed an incomplete header")
                    if line in (b"\n", b"\r\n"):
                        break
                    name, separator, value = line.partition(b":")
                    if separator and name.strip().lower() == b"content-length":
                        content_length = int(value.strip())
                if content_length is None:
                    raise ValueError("compiler service omitted Content-Length")
                self.responses.put(read_exact(self.process.stdout, content_length))
        except Exception as error:
            self.responses.put(error)

    def _read_errors(self) -> None:
        assert self.process.stderr is not None
        for line in self.process.stderr:
            self.errors.append(line)

    def _write_request(
        self, body: bytes, completed: queue.Queue[Exception | None]
    ) -> None:
        try:
            assert self.process.stdin is not None
            self.process.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode())
            self.process.stdin.write(body)
            self.process.stdin.flush()
        except Exception as error:
            completed.put(error)
        else:
            completed.put(None)

    def compile(self, request: dict[str, Any]) -> bytes:
        deadline = time.monotonic() + self.timeout
        body = encode_request(request)
        if self.process.poll() is not None:
            raise RuntimeError(self.diagnostic("compiler service exited"))
        completed: queue.Queue[Exception | None] = queue.Queue(maxsize=1)
        self.writer = threading.Thread(
            target=self._write_request, args=(body, completed), daemon=True
        )
        self.writer.start()
        try:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise queue.Empty
            sent = completed.get(timeout=remaining)
            self.writer.join()
            self.writer = None
            if sent is not None:
                raise RuntimeError(
                    self.diagnostic("compiler service broke its input pipe")
                ) from sent
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise queue.Empty
            response = self.responses.get(timeout=remaining)
        except queue.Empty as error:
            # Closing buffered stdin while its writer is blocked can itself
            # hang. Kill first, then reap the worker and drain the I/O threads.
            if self.process.poll() is None:
                self.process.kill()
            self.close()
            raise TimeoutError(self.diagnostic("compiler service timed out")) from error
        if isinstance(response, Exception):
            raise RuntimeError(self.diagnostic(str(response))) from response
        return response

    def diagnostic(self, message: str) -> str:
        errors = b"".join(self.errors).decode(errors="replace")
        return f"{message}; exit={self.process.poll()}; stderr={errors}"

    def close(self) -> None:
        if self.closed:
            return
        self.closed = True
        if self.writer is not None:
            if self.writer.is_alive():
                if self.process.poll() is None:
                    self.process.kill()
                self.process.wait(timeout=2)
            self.writer.join(timeout=2)
            self.writer = None
        if self.process.stdin is not None:
            try:
                self.process.stdin.close()
            except BrokenPipeError:
                pass
        try:
            self.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.process.terminate()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=5)
        self.reader.join(timeout=2)
        self.error_reader.join(timeout=2)
        for stream in (self.process.stdout, self.process.stderr):
            if stream is not None:
                stream.close()


def parse_output(label: str, raw: bytes) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"{label} emitted invalid Standard JSON: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"{label} emitted a non-object Standard JSON response")
    return value


def has_internal_compiler_error(output: dict[str, Any]) -> bool:
    errors = output.get("errors")
    return isinstance(errors, list) and any(
        isinstance(diagnostic, dict)
        and diagnostic.get("severity") == "error"
        and diagnostic.get("type") == "InternalCompilerError"
        for diagnostic in errors
    )


def run_compiler_response(
    executable: Path,
    request: dict[str, Any],
    timeout: float,
    candidate: bool = False,
) -> tuple[bytes, dict[str, Any]]:
    command = [str(executable), "--standard-json"]
    if candidate:
        command.extend(("--no-cache", "--solc-version", REFERENCE_VERSION))
    result = subprocess.run(
        command,
        input=encode_request(request),
        check=False,
        capture_output=True,
        timeout=timeout,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"{' '.join(command)} exited {result.returncode}: "
            + result.stderr.decode(errors="replace")
        )
    return result.stdout, parse_output(str(executable), result.stdout)


def first_difference(left: Any, right: Any, path: tuple[str, ...] = ()) -> tuple[str, ...]:
    if type(left) is not type(right):
        return path + ("<type>",)
    if isinstance(left, dict):
        for key in sorted(set(left) | set(right)):
            if key not in left or key not in right:
                return path + (str(key),)
            difference = first_difference(left[key], right[key], path + (str(key),))
            if difference:
                return difference
        return ()
    if isinstance(left, list):
        if len(left) != len(right):
            return path + ("<length>",)
        for index, (left_item, right_item) in enumerate(zip(left, right)):
            difference = first_difference(left_item, right_item, path + (str(index),))
            if difference:
                return difference
        return ()
    return () if left == right else path


def response_mismatch_path(
    request: dict[str, Any],
    oracle: str,
    expected_raw: bytes,
    expected_output: dict[str, Any],
    candidate_raw: bytes,
    candidate_output: dict[str, Any],
) -> tuple[str, ...] | None:
    if candidate_raw == expected_raw:
        return None
    comparable_expected = expected_output
    comparable_candidate = candidate_output
    if oracle == "reference" and requests_ir_text(request):
        if without_raw_ir_text(candidate_raw) == without_raw_ir_text(expected_raw):
            return None
        comparable_expected = without_ir_text(expected_output)
        comparable_candidate = without_ir_text(candidate_output)
    return first_difference(comparable_expected, comparable_candidate) or ("<serialization>",)


def semantic_case(
    request: dict[str, Any],
    revision: int,
) -> tuple[str, int, int] | None:
    sources = request.get("sources")
    if not isinstance(sources, dict):
        return None
    first_source = next(
        (
            source.get("content")
            for name, source in sources.items()
            if name in ("A.sol", "RenamedA.sol") and isinstance(source, dict)
        ),
        None,
    )
    aliases = sources.get("Aliases.sol")
    if not isinstance(first_source, str) or not isinstance(aliases, dict):
        return None
    body_match = re.search(r"return x \+ ([0-9]+);", first_source)
    alias_source = aliases.get("content")
    if body_match is None or not isinstance(alias_source, str):
        return None
    first_body = int(body_match.group(1))
    swapped = "authorized as rejected" in alias_source
    digest = hashlib.sha256(encode_request(request) + revision.to_bytes(4, "little")).digest()
    value = (0, 7, 42)[digest[1] % 3]
    signature = (
        "symbol(uint256)",
        "isAuthorized(uint256)",
        "isRejected(uint256)",
    )[digest[0] % 3]
    if signature == "symbol(uint256)":
        expected = value + first_body
    elif signature == "isAuthorized(uint256)":
        expected = int(value != 7 if swapped else value == 7)
    else:
        expected = int(value == 7 if swapped else value != 7)
    return signature, value, expected


def main_artifact(output: dict[str, Any]) -> tuple[str, dict[str, str]] | None:
    try:
        evm = output["contracts"]["Main.sol"]["Main"]["evm"]
        code = evm["deployedBytecode"]["object"]
        methods = evm["methodIdentifiers"]
    except (KeyError, TypeError):
        return None
    if not isinstance(code, str) or not isinstance(methods, dict):
        return None
    if not all(isinstance(key, str) and isinstance(value, str) for key, value in methods.items()):
        return None
    return code, methods


def run_evm(
    executable: Path,
    code: str,
    calldata: str,
    timeout: float,
) -> tuple[str, str]:
    result = subprocess.run(
        [
            str(executable),
            "run",
            "--gas",
            "10000000",
            "--input",
            calldata,
            code,
        ],
        check=False,
        capture_output=True,
        env=evm_environment(executable),
        text=True,
        timeout=timeout,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"evm execution failed with {result.returncode}: {result.stdout}{result.stderr}"
        )
    status = re.search(r"^Result:\s*(\S+)\s*$", result.stdout, re.MULTILINE)
    output = re.search(r"^Output:\s*([0-9a-fA-F]*)\s*$", result.stdout, re.MULTILINE)
    if status is None or output is None:
        raise RuntimeError(f"unrecognized evm output: {result.stdout}{result.stderr}")
    return status.group(1), output.group(1).lower()


def semantic_mismatch(
    executable: Path,
    output: dict[str, Any],
    request: dict[str, Any],
    revision: int,
    timeout: float,
) -> tuple[str, str] | None:
    case = semantic_case(request, revision)
    artifact = main_artifact(output)
    if case is None or artifact is None:
        return None
    signature, value, expected = case
    code, methods = artifact
    selector = methods.get(signature)
    if selector is None:
        return signature, "compiled output omitted its method selector"
    calldata = selector + value.to_bytes(32, "big").hex()
    status, actual = run_evm(executable, code, calldata, timeout)
    expected_output = expected.to_bytes(32, "big").hex()
    if status != "success" or actual != expected_output:
        return (
            signature,
            f"input={value}, expected success/{expected_output}, got {status}/{actual}",
        )
    return None


def evaluate_history(
    candidate: Path,
    reference: Path,
    history: Sequence[dict[str, Any]],
    timeout: float,
    classify: bool = False,
    evm: Path | None = None,
    session_mode: str = "memory",
    oracle: str = "reference",
) -> Failure | None:
    if oracle not in ("reference", "clean"):
        raise ValueError(f"unknown comparison oracle: {oracle}")
    with tempfile.TemporaryDirectory(prefix="oksolc-differential-") as temporary:
        directory = Path(temporary).resolve()
        (directory / ".git").mkdir()
        service = CandidateService(candidate, timeout, directory, session_mode)
        try:
            for revision, request in enumerate(history):
                revision_oracle = oracle
                expected_raw, expected_output = run_compiler_response(
                    reference if oracle == "reference" else candidate,
                    request,
                    timeout,
                    candidate=oracle == "clean",
                )
                if (
                    oracle == "reference"
                    and has_internal_compiler_error(expected_output)
                ):
                    expected_raw, expected_output = run_compiler_response(
                        candidate,
                        request,
                        timeout,
                        candidate=True,
                    )
                    revision_oracle = "clean"
                try:
                    candidate_raw = service.compile(request)
                    candidate_output = parse_output("stateful oksolc", candidate_raw)
                except TimeoutError as error:
                    return Failure(
                        "candidate-timeout",
                        revision,
                        (),
                        str(error),
                        expected_output,
                        session_mode=session_mode,
                        oracle=revision_oracle,
                    )
                except (RuntimeError, ValueError) as error:
                    return Failure(
                        "candidate-service-failure",
                        revision,
                        (),
                        str(error),
                        expected_output,
                        session_mode=session_mode,
                        oracle=revision_oracle,
                    )
                path = response_mismatch_path(
                    request,
                    revision_oracle,
                    expected_raw,
                    expected_output,
                    candidate_raw,
                    candidate_output,
                )
                if path is not None:
                    failure = Failure(
                        "output-mismatch",
                        revision,
                        path,
                        "stateful output differs from "
                        + (
                            "solc 0.8.36"
                            if revision_oracle == "reference"
                            else "clean oksolc"
                        ),
                        expected_output,
                        candidate_output,
                        session_mode=session_mode,
                        oracle=revision_oracle,
                    )
                    if revision_oracle == "clean":
                        failure.candidate_fresh = expected_output
                    elif classify:
                        try:
                            fresh_raw, failure.candidate_fresh = run_compiler_response(
                                candidate,
                                request,
                                timeout,
                                candidate=True,
                            )
                            failure.detail = (
                                "incremental output differs; clean oksolc matches solc"
                                if response_mismatch_path(
                                    request,
                                    "reference",
                                    expected_raw,
                                    expected_output,
                                    fresh_raw,
                                    failure.candidate_fresh,
                                ) is None
                                else "clean and incremental oksolc differ from solc"
                            )
                        except (RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
                            failure.detail += f"; clean classification failed: {error}"
                    return failure
                if evm is not None:
                    mismatch = semantic_mismatch(
                        evm,
                        candidate_output,
                        request,
                        revision,
                        timeout,
                    )
                    if mismatch is not None:
                        signature, detail = mismatch
                        return Failure(
                            "semantic-mismatch",
                            revision,
                            ("execution", signature),
                            detail,
                            expected_output,
                            candidate_output,
                            session_mode=session_mode,
                            oracle=revision_oracle,
                        )
                if session_mode == "restart" and revision + 1 != len(history):
                    service.close()
                    service = CandidateService(candidate, timeout, directory, session_mode)
        finally:
            service.close()
    return None


def ddmin_history(
    history: list[dict[str, Any]],
    preserves: Callable[[list[dict[str, Any]]], bool],
) -> list[dict[str, Any]]:
    if len(history) <= 1:
        return history
    prefix = history[:-1]
    final = history[-1]
    granularity = 2
    while prefix:
        chunk_size = max(1, (len(prefix) + granularity - 1) // granularity)
        reduced = False
        for start in range(0, len(prefix), chunk_size):
            candidate = prefix[:start] + prefix[start + chunk_size :] + [final]
            if preserves(candidate):
                prefix = candidate[:-1]
                granularity = max(2, granularity - 1)
                reduced = True
                break
        if reduced:
            continue
        if granularity >= len(prefix):
            break
        granularity = min(len(prefix), granularity * 2)
    return prefix + [final]


def remove_source(
    history: list[dict[str, Any]],
    source_name: str,
) -> list[dict[str, Any]]:
    candidate = deepcopy(history)
    for request in candidate:
        request.get("sources", {}).pop(source_name, None)
    return candidate


def remove_source_line(
    history: list[dict[str, Any]],
    source_name: str,
    line_index: int,
) -> list[dict[str, Any]]:
    candidate = deepcopy(history)
    for request in candidate:
        source = request.get("sources", {}).get(source_name)
        if not isinstance(source, dict) or not isinstance(source.get("content"), str):
            continue
        lines = source["content"].splitlines(keepends=True)
        if line_index < len(lines):
            del lines[line_index]
            source["content"] = "".join(lines)
    return candidate


def reduce_history(
    candidate: Path,
    reference: Path,
    history: list[dict[str, Any]],
    original: Failure,
    timeout: float,
    evm: Path | None = None,
    session_mode: str = "memory",
    oracle: str = "reference",
) -> tuple[list[dict[str, Any]], int]:
    evaluations = 0

    def preserves(value: list[dict[str, Any]]) -> bool:
        nonlocal evaluations
        evaluations += 1
        failure = evaluate_history(
            candidate,
            reference,
            value,
            timeout,
            evm=evm,
            session_mode=session_mode,
            oracle=oracle,
        )
        return failure is not None and original.compatible(failure)

    result = ddmin_history(history[: original.revision + 1], preserves)
    source_names = sorted(
        {name for request in result for name in request.get("sources", {})}
    )
    for source_name in source_names:
        reduced = remove_source(result, source_name)
        if preserves(reduced):
            result = reduced

    for source_name in source_names:
        line_index = 0
        while True:
            line_counts = [
                len(source["content"].splitlines(keepends=True))
                for request in result
                if isinstance((source := request.get("sources", {}).get(source_name)), dict)
                and isinstance(source.get("content"), str)
            ]
            if not line_counts or line_index >= max(line_counts):
                break
            reduced = remove_source_line(result, source_name, line_index)
            if preserves(reduced):
                result = reduced
            else:
                line_index += 1
    return result, evaluations


def failure_json(failure: Failure | None) -> Any:
    if failure is None:
        return None
    result = asdict(failure)
    result["path"] = list(failure.path)
    return result


def write_bundle(
    path: Path,
    history: Sequence[dict[str, Any]],
    failure: Failure,
    candidate_version: str,
    reference_version: str,
    seed: int,
    iteration: int,
    reducer_evaluations: int = 0,
    execution_oracle_version: str | None = None,
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    # Preserve request key order for byte-exact replay and cache identity.
    path.write_text(
        json.dumps(
            {
                "schema": "oksolc-differential-reproducer-v1",
                "seed": seed,
                "iteration": iteration,
                "candidate_version": candidate_version,
                "reference_version": reference_version,
                "execution_oracle_version": execution_oracle_version,
                "reducer_evaluations": reducer_evaluations,
                "failure": failure_json(failure),
                "history": history,
            },
            indent=2,
        )
        + "\n"
    )


def parse_seed(value: str) -> int:
    return int(value, 0)


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", required=True, help="oksolc executable")
    parser.add_argument("--reference", required=True, help="solc 0.8.36 executable")
    parser.add_argument("--evm", help="optional evmone executable for semantic execution")
    parser.add_argument(
        "--session-mode",
        choices=("memory", "persistent", "restart", "all"),
        default="memory",
        help="candidate cache/restart mode",
    )
    parser.add_argument("--iterations", type=int, default=100)
    parser.add_argument(
        "--max-failures",
        type=int,
        default=1,
        help="reduce this many distinct failures before stopping",
    )
    parser.add_argument("--max-revisions", type=int, default=6)
    parser.add_argument("--seed", type=parse_seed, default=0x6A09E667F3BCC909)
    parser.add_argument("--timeout", type=float, default=40.0)
    parser.add_argument("--artifacts", type=Path, default=Path("build/fuzz-differential"))
    parser.add_argument(
        "--corpus",
        type=Path,
        help="directory of Standard JSON requests used for cross-project transitions",
    )
    parser.add_argument("--replay", type=Path)
    parser.add_argument("--no-reduce", action="store_true")
    return parser.parse_args()


def main() -> int:
    options = parse_arguments()
    if options.iterations <= 0:
        raise RuntimeError("--iterations must be positive")
    if options.max_failures <= 0:
        raise RuntimeError("--max-failures must be positive")
    if options.max_revisions < 2:
        raise RuntimeError("--max-revisions must be at least two")
    if options.timeout <= 0:
        raise RuntimeError("--timeout must be positive")
    candidate = resolve_executable(options.candidate)
    reference = resolve_executable(options.reference)
    evm = resolve_executable(options.evm) if options.evm else None
    candidate_version = compiler_version(candidate, "--solc-version", REFERENCE_VERSION)
    reference_version = compiler_version(reference)
    if f"Version: {REFERENCE_VERSION}" not in reference_version:
        raise RuntimeError(f"reference compiler is not solc {REFERENCE_VERSION}: {reference_version}")
    execution_oracle_version = evm_version(evm) if evm is not None else None

    if options.replay is not None:
        bundle = json.loads(options.replay.read_text())
        history = bundle["history"]
        bundled_failure = bundle.get("failure") or {}
        replay_mode = bundled_failure.get("session_mode", options.session_mode)
        replay_oracle = bundled_failure.get("oracle", "reference")
        if replay_mode == "all":
            replay_mode = "memory"
        failure = evaluate_history(
            candidate,
            reference,
            history,
            options.timeout,
            classify=True,
            evm=evm,
            session_mode=replay_mode,
            oracle=replay_oracle,
        )
        if failure is None:
            print(f"reproducer no longer fails: {options.replay}")
            return 0
        print(
            f"reproduced {failure.kind} at revision {failure.revision}: "
            f"{failure.detail}; path={'/'.join(failure.path)}"
        )
        return 1

    rng = random.Random(options.seed)
    campaign_histories = [(history, "reference") for history in seed_histories()]
    corpus_history_count = 0
    corpus_audit_checked = 0
    corpus_audit_skipped = 0
    corpus_entries: list[tuple[str, dict[str, Any]]] = []
    if options.corpus is not None:
        corpus_entries = load_corpus_requests(options.corpus)
        corpus_audit_checked, corpus_audit_skipped, audit_failure = audit_reference_corpus(
            candidate,
            reference,
            corpus_entries,
            options.timeout,
        )
        if audit_failure is not None:
            name, request, failure = audit_failure
            path = options.artifacts / f"corpus-audit-{Path(name).stem}.json"
            write_bundle(
                path,
                [request],
                failure,
                candidate_version,
                reference_version,
                options.seed,
                -1,
                execution_oracle_version=execution_oracle_version,
            )
            print(
                f"found {failure.kind} in corpus case {name}; saved {path}",
                file=sys.stderr,
            )
            return 1
        corpus_histories = corpus_transition_histories(
            options.corpus,
            rng,
            options.max_revisions,
        )
        corpus_history_count = len(corpus_histories)
        campaign_histories.extend((history, "clean") for history in corpus_histories)
    session_modes = (
        ("memory", "persistent", "restart")
        if options.session_mode == "all"
        else (options.session_mode,)
    )
    failure_signatures: set[tuple[Any, ...]] = set()
    duplicate_failures = 0
    for iteration in range(options.iterations):
        if iteration < len(campaign_histories):
            history, oracle = campaign_histories[iteration]
        else:
            history_kind = rng.randrange(3) if corpus_entries else rng.randrange(2) + 1
            if history_kind == 0:
                history = generate_corpus_mutation_history(
                    corpus_entries,
                    rng,
                    options.max_revisions,
                )
            elif history_kind == 1:
                history = generate_targeted_history(rng, options.max_revisions)
            else:
                history = generate_history(rng, options.max_revisions)
            oracle = "reference"
        failure = None
        for session_mode in session_modes:
            failure = evaluate_history(
                candidate,
                reference,
                history,
                options.timeout,
                classify=True,
                evm=evm,
                session_mode=session_mode,
                oracle=oracle,
            )
            if failure is not None:
                break
        if failure is None:
            continue
        signature = failure.campaign_signature()
        if signature in failure_signatures:
            duplicate_failures += 1
            continue
        failure_signatures.add(signature)
        stem = f"failure-{options.seed:016x}-{iteration:06d}"
        original_path = options.artifacts / f"{stem}-original.json"
        write_bundle(
            original_path,
            history[: failure.revision + 1],
            failure,
            candidate_version,
            reference_version,
            options.seed,
            iteration,
            execution_oracle_version=execution_oracle_version,
        )
        minimized = history[: failure.revision + 1]
        evaluations = 0
        if not options.no_reduce:
            minimized, evaluations = reduce_history(
                candidate,
                reference,
                minimized,
                failure,
                options.timeout,
                evm,
                failure.session_mode,
                failure.oracle,
            )
        minimized_failure = evaluate_history(
            candidate,
            reference,
            minimized,
            options.timeout,
            classify=True,
            evm=evm,
            session_mode=failure.session_mode,
            oracle=failure.oracle,
        )
        if minimized_failure is None:
            raise RuntimeError("reducer lost the original failure")
        minimized_path = options.artifacts / f"{stem}-minimized.json"
        write_bundle(
            minimized_path,
            minimized,
            minimized_failure,
            candidate_version,
            reference_version,
            options.seed,
            iteration,
            evaluations,
            execution_oracle_version,
        )
        print(
            f"found {failure.kind} at iteration {iteration}, revision {failure.revision}; "
            f"saved {original_path} and {minimized_path}",
            file=sys.stderr,
        )
        if len(failure_signatures) >= options.max_failures:
            return 1
        print(
            f"continuing after {len(failure_signatures)} distinct failure(s); "
            f"limit {options.max_failures}",
            file=sys.stderr,
        )
    if failure_signatures:
        print(
            f"stateful differential fuzzing completed with "
            f"{len(failure_signatures)} distinct failure(s) and "
            f"{duplicate_failures} duplicate reproduction(s)",
            file=sys.stderr,
        )
        return 1
    print(
        f"stateful differential fuzzing passed: {options.iterations} histories, "
        f"seed {options.seed:#x}, up to {options.max_revisions} revisions, "
        f"{corpus_history_count} transition-corpus histories, "
        f"{corpus_audit_checked} corpus reference checks, "
        f"{corpus_audit_skipped} reviewed exclusions"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"compiler differential fuzzer: {error}", file=sys.stderr)
        raise SystemExit(2) from error
