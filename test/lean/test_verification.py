# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""End-to-end integration tests for oksolc's Zig verification exporters and oksolc-verify."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

REPO_ROOT = Path(__file__).resolve().parents[2]
ZIG_OUT_BIN = REPO_ROOT / "zig-out" / "bin"
OKSOLC_BIN = ZIG_OUT_BIN / "oksolc"
RULES_EXPORT_BIN = ZIG_OUT_BIN / "compiler-rules-export"
GRAPH_EXPORT_BIN = ZIG_OUT_BIN / "compiler-graph-export"
WORD_EXPORT_BIN = ZIG_OUT_BIN / "compiler-word-export"
OKSOLC_VERIFY_BIN = REPO_ROOT / "lean" / ".lake" / "build" / "bin" / "oksolc-verify"


def make_standard_json_request(filename: str, content: str) -> dict:
    return {
        "language": "Solidity",
        "sources": {filename: {"content": content}},
        "settings": {
            "viaIR": True,
            "optimizer": {"enabled": True, "runs": 200},
            "evmVersion": "cancun",
            "metadata": {"appendCBOR": False, "bytecodeHash": "none"},
            "outputSelection": {
                "*": {
                    "*": [
                        "evm.bytecode.object",
                        "evm.deployedBytecode.object",
                        "evm.methodIdentifiers",
                    ]
                }
            },
        },
    }


def run_verify(mode: str, req_bytes: bytes, resp_bytes: bytes) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        req_path = tmp_dir / "request.json"
        resp_path = tmp_dir / "response.json"
        req_path.write_bytes(req_bytes)
        resp_path.write_bytes(resp_bytes)
        return subprocess.run(
            [str(OKSOLC_VERIFY_BIN), mode, str(req_path), str(resp_path)],
            capture_output=True,
            text=True,
            check=False,
        )


def compile_standard_json(req: dict) -> tuple[bytes, bytes, dict]:
    req_bytes = (json.dumps(req, indent=2) + "\n").encode("utf-8")
    proc = subprocess.run(
        [str(OKSOLC_BIN), "--standard-json"],
        input=req_bytes,
        capture_output=True,
        check=True,
    )
    resp_bytes = proc.stdout
    return req_bytes, resp_bytes, json.loads(resp_bytes.decode("utf-8"))


class VerificationSuiteTest(unittest.TestCase):
    def test_binaries_exist(self) -> None:
        for binary in (
            OKSOLC_BIN,
            RULES_EXPORT_BIN,
            GRAPH_EXPORT_BIN,
            WORD_EXPORT_BIN,
            OKSOLC_VERIFY_BIN,
        ):
            self.assertTrue(binary.is_file(), f"missing required binary: {binary}")

    def test_exported_rules_match_checked_in_lean_rules(self) -> None:
        proc = subprocess.run(
            [str(RULES_EXPORT_BIN)],
            capture_output=True,
            text=True,
            check=True,
        )
        rules_lean = (REPO_ROOT / "lean" / "Compiler" / "Algebraic" / "Rules.lean").read_text(
            encoding="utf-8"
        )
        self.assertEqual(proc.stdout, rules_lean)

    @staticmethod
    def _strip_lean_comments(text: str) -> str:
        out: list[str] = []
        i = 0
        depth = 0
        n = len(text)
        while i < n:
            if depth == 0 and text[i : i + 2] == "--":
                nl = text.find("\n", i + 2)
                if nl == -1:
                    break
                i = nl + 1
                out.append("\n")
            elif text[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif depth > 0 and text[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                if depth == 0:
                    out.append(text[i])
                i += 1
        return "".join(out)

    def test_lean_codebase_has_zero_sorry_and_zero_unsafe_tactics(self) -> None:
        lean_files = sorted((REPO_ROOT / "lean").rglob("*.lean"))
        self.assertGreaterEqual(len(lean_files), 15)
        for path in lean_files:
            if ".lake" in path.parts:
                continue
            code = self._strip_lean_comments(path.read_text(encoding="utf-8"))
            self.assertNotRegex(code, r"\bsorry\b", f"disallowed sorry in {path}")
            self.assertNotRegex(code, r"\bnative_decide\b", f"disallowed native_decide in {path}")
            self.assertNotRegex(code, r"\bbv_decide\b", f"disallowed bv_decide in {path}")

    def test_graph_mode_positive_0ary_and_extended_ops_and_negative_controls(self) -> None:
        cases = [
            # 0-ary leaf literal + identity fold (#44 regression check)
            {
                "schema": "oksolc.compiler-graph-request.v1",
                "nodes": [
                    {"input": "x"},
                    {"literal": "0"},
                    {"binary": {"op": "add", "left": 0, "right": 1}},
                ],
                "root": 2,
            },
            # Pure 0-ary constant root
            {
                "schema": "oksolc.compiler-graph-request.v1",
                "nodes": [{"literal": "42"}],
                "root": 0,
            },
            # Environmental 0-ary opcode + 160-bit mask + signextend(0, shr(248, x)) -> sar + addmod
            {
                "schema": "oksolc.compiler-graph-request.v1",
                "nodes": [
                    {"nullary": "caller"},
                    {"literal": str((1 << 160) - 1)},
                    {"binary": {"op": "and", "left": 0, "right": 1}},
                    {"literal": "248"},
                    {"input": "x"},
                    {"binary": {"op": "shr", "left": 3, "right": 4}},
                    {"literal": "0"},
                    {"binary": {"op": "signextend", "left": 6, "right": 5}},
                    {"ternary": {"op": "addmod", "first": 2, "second": 7, "third": 1}},
                ],
                "root": 8,
            },
        ]
        for req in cases:
            req_bytes = json.dumps(req).encode("utf-8")
            exp = subprocess.run(
                [str(GRAPH_EXPORT_BIN)],
                input=req_bytes,
                capture_output=True,
                check=True,
            )
            res = run_verify("graph", req_bytes, exp.stdout)
            self.assertEqual(res.returncode, 0, msg=res.stderr)
            report = json.loads(res.stdout)
            self.assertTrue(report["accepted"])
            self.assertEqual(report["requestSha256"], hashlib.sha256(req_bytes).hexdigest())

        # Negative control 1: corrupt optimized literal
        req_bytes = json.dumps(cases[1]).encode("utf-8")
        exp = subprocess.run([str(GRAPH_EXPORT_BIN)], input=req_bytes, capture_output=True, check=True)
        tampered = json.loads(exp.stdout.decode("utf-8"))
        tampered["nodes"] = [{"literal": "43"}]
        bad = run_verify("graph", req_bytes, json.dumps(tampered).encode("utf-8"))
        self.assertNotEqual(bad.returncode, 0)

        # Negative control 2: corrupt CSE cache entry even when root is untouched
        req_bytes = json.dumps(cases[0]).encode("utf-8")
        exp = subprocess.run([str(GRAPH_EXPORT_BIN)], input=req_bytes, capture_output=True, check=True)
        tampered_cache = json.loads(exp.stdout.decode("utf-8"))
        tampered_cache["cache"][0]["id"] = 1
        bad_cache = run_verify("graph", req_bytes, json.dumps(tampered_cache).encode("utf-8"))
        self.assertNotEqual(bad_cache.returncode, 0)

        # Negative control 3: requestSha256 mismatch
        tampered_sha = json.loads(exp.stdout.decode("utf-8"))
        tampered_sha["requestSha256"] = "0" * 64
        bad_sha = run_verify("graph", req_bytes, json.dumps(tampered_sha).encode("utf-8"))
        self.assertNotEqual(bad_sha.returncode, 0)

    def test_graph_failure_sweep_positive_and_negative_controls(self) -> None:
        req = {
            "schema": "oksolc.compiler-graph-failure-request.v1",
            "nodes": [
                {"input": "x"},
                {"literal": "3"},
                {"binary": {"op": "add", "left": 0, "right": 1}},
                {"literal": "5"},
                {"binary": {"op": "add", "left": 2, "right": 3}},
            ],
            "root": 4,
        }
        req_bytes = json.dumps(req).encode("utf-8")
        exp = subprocess.run([str(GRAPH_EXPORT_BIN)], input=req_bytes, capture_output=True, check=True)
        res = run_verify("graph-failure", req_bytes, exp.stdout)
        self.assertEqual(res.returncode, 0, msg=res.stderr)
        report = json.loads(res.stdout)
        self.assertTrue(report["accepted"])
        self.assertGreater(report["observations"], 2)

        # Negative control: drop an intermediate OOM cut so cut indices are non-contiguous
        tampered = json.loads(exp.stdout.decode("utf-8"))
        del tampered["observations"][1]
        bad = run_verify("graph-failure", req_bytes, json.dumps(tampered).encode("utf-8"))
        self.assertNotEqual(bad.returncode, 0)

        # Negative control: corrupt partial state inside an OOM cut
        tampered_cut = json.loads(exp.stdout.decode("utf-8"))
        for obs in tampered_cut["observations"]:
            if obs["attempt"]["outcome"] == "outOfMemory" and len(obs["attempt"]["resultIds"]) >= 1:
                obs["attempt"]["nodes"][0] = {"literal": "999"}
                break
        bad_cut = run_verify("graph-failure", req_bytes, json.dumps(tampered_cut).encode("utf-8"))
        self.assertNotEqual(bad_cut.returncode, 0)

    def test_word_mode_positive_and_negative_controls(self) -> None:
        cases = [
            {
                "schema": "oksolc.compiler-word-request.v1",
                "arithmetic": "unchecked",
                "evmVersion": "cancun",
                "parameters": ["x", "y", "frame"],
                "nodes": [
                    {"input": "x"},
                    {"input": "y"},
                    {"binary": {"op": "shl", "left": 0, "right": 1}},
                ],
                "root": 2,
            },
            {
                "schema": "oksolc.compiler-word-request.v1",
                "arithmetic": "unchecked",
                "evmVersion": "cancun",
                "parameters": ["a", "b"],
                "nodes": [
                    {"input": "a"},
                    {"literal": "0"},
                    {"binary": {"op": "add", "left": 0, "right": 1}},
                    {"input": "b"},
                    {"binary": {"op": "xor", "left": 2, "right": 3}},
                    {"binary": {"op": "xor", "left": 4, "right": 3}},
                ],
                "root": 5,
            },
        ]
        for req in cases:
            req_bytes = json.dumps(req).encode("utf-8")
            exp = subprocess.run([str(WORD_EXPORT_BIN)], input=req_bytes, capture_output=True, check=True)
            res = run_verify("word", req_bytes, exp.stdout)
            self.assertEqual(res.returncode, 0, msg=res.stderr)
            self.assertTrue(json.loads(res.stdout)["accepted"])

        # Negative control: swap operand order on non-commutative shift (`80821b` -> `81811b`)
        req_bytes = json.dumps(cases[0]).encode("utf-8")
        exp = subprocess.run([str(WORD_EXPORT_BIN)], input=req_bytes, capture_output=True, check=True)
        tampered = json.loads(exp.stdout.decode("utf-8"))
        tampered["bytecode"] = "81811b"
        bad = run_verify("word", req_bytes, json.dumps(tampered).encode("utf-8"))
        self.assertNotEqual(bad.returncode, 0)

        # Negative control: unreachable invalid/undeclared input node in word request must be rejected
        bad_dead_req = json.loads(req_bytes.decode("utf-8"))
        bad_dead_req["nodes"].append({"input": "undeclared_dead_var"})
        bad_dead_bytes = json.dumps(bad_dead_req).encode("utf-8")
        tampered_dead = json.loads(exp.stdout.decode("utf-8"))
        import hashlib

        tampered_dead["requestSha256"] = hashlib.sha256(bad_dead_bytes).hexdigest()
        bad_dead = run_verify("word", bad_dead_bytes, json.dumps(tampered_dead).encode("utf-8"))
        self.assertNotEqual(bad_dead.returncode, 0)

    def test_public_preview_retained_fresh_and_corrupted(self) -> None:
        ver_dir = REPO_ROOT / "examples" / "verification"
        req_bytes = (ver_dir / "request.json").read_bytes()
        resp_bytes = (ver_dir / "response.json").read_bytes()
        corrupted_bytes = (ver_dir / "corrupted-response.json").read_bytes()

        # 1. Retained positive pair certifies and triggers universalPreviewTheorem = true
        pos = run_verify("standard-json", req_bytes, resp_bytes)
        self.assertEqual(pos.returncode, 0, msg=pos.stderr)
        pos_report = json.loads(pos.stdout)
        self.assertTrue(pos_report["accepted"])
        self.assertTrue(pos_report["universalPreviewTheorem"])

        # 2. Fresh oksolc compilation matches retained artifacts byte-for-byte
        fresh_proc = subprocess.run(
            [str(OKSOLC_BIN), "--standard-json"],
            input=req_bytes,
            capture_output=True,
            check=True,
        )
        fresh_json = json.loads(fresh_proc.stdout.decode("utf-8"))
        retained_json = json.loads(resp_bytes.decode("utf-8"))
        self.assertEqual(
            fresh_json["contracts"]["Function.sol"]["Identity"]["evm"],
            retained_json["contracts"]["Function.sol"]["Identity"]["evm"],
        )
        fresh_ver = run_verify("standard-json", req_bytes, fresh_proc.stdout)
        self.assertEqual(fresh_ver.returncode, 0, msg=fresh_ver.stderr)

        # 3. Corrupted response is rejected
        neg = run_verify("standard-json", req_bytes, corrupted_bytes)
        self.assertNotEqual(neg.returncode, 0)
        self.assertFalse(json.loads(neg.stderr)["accepted"])

    def test_standard_json_contract_corpus_and_mutations(self) -> None:
        corpus = [
            (
                "Empty.sol",
                "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0;\ncontract Empty {}\n",
            ),
            (
                "CheckedOps.sol",
                "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0;\n"
                "contract CheckedOps {\n"
                "    function addChecked(uint256 a, uint256 b) external pure returns (uint256) { return a + b; }\n"
                "    function divChecked(uint256 a, uint256 b) external pure returns (uint256) { return a / b; }\n"
                "}\n",
            ),
            (
                "AddrCheck.sol",
                "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0;\n"
                "contract AddrCheck {\n"
                "    function isSender(address who) external view returns (bool) {\n"
                "        return who == msg.sender;\n"
                "    }\n"
                "}\n",
            ),
            (
                "Vault.sol",
                "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0;\n"
                "contract Vault {\n"
                "    uint256 total = 10;\n"
                "    constructor() payable {\n"
                "        total = total + msg.value;\n"
                "    }\n"
                "    function deposit(uint256 bonus) external payable returns (uint256) {\n"
                "        total = total + msg.value + bonus;\n"
                "        return total;\n"
                "    }\n"
                "    function peek() external view returns (uint256) {\n"
                "        return total;\n"
                "    }\n"
                "}\n",
            ),
            (
                "PackedStorageAndPrecedence.sol",
                "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0;\n"
                "contract PackedStorageAndPrecedence {\n"
                "    bool flagA = true;\n"
                "    address owner;\n"
                "    bool flagB = false;\n"
                "    uint256 count = 7;\n"
                "    constructor() {\n"
                "        owner = msg.sender;\n"
                "    }\n"
                "    function flipAndSet(address nextOwner, bool b) external returns (bool) {\n"
                "        flagA = !flagA;\n"
                "        owner = nextOwner;\n"
                "        flagB = b;\n"
                "        return flagA;\n"
                "    }\n"
                "    function getOwner() external view returns (address) {\n"
                "        return owner;\n"
                "    }\n"
                "    function getFlagB() external view returns (bool) {\n"
                "        return flagB;\n"
                "    }\n"
                "    function checkPrec(uint256 a, uint256 b, uint256 c) external pure returns (bool) {\n"
                "        return a == b & c;\n"
                "    }\n"
                "}\n",
            ),
        ]
        for filename, source in corpus:
            req = make_standard_json_request(filename, source)
            req_bytes, resp_bytes, resp_obj = compile_standard_json(req)
            res = run_verify("standard-json", req_bytes, resp_bytes)
            self.assertEqual(res.returncode, 0, msg=f"{filename} failed: {res.stderr}")
            self.assertTrue(json.loads(res.stdout)["accepted"])

            # Mutate selector map on contracts with functions -> must reject
            contract_name = next(iter(resp_obj["contracts"][filename].keys()))
            method_ids = resp_obj["contracts"][filename][contract_name]["evm"]["methodIdentifiers"]
            if method_ids:
                bad_sel = json.loads(resp_bytes.decode("utf-8"))
                first_sig = next(iter(method_ids.keys()))
                bad_sel["contracts"][filename][contract_name]["evm"]["methodIdentifiers"][first_sig] = "deadbeef"
                bad_res = run_verify("standard-json", req_bytes, json.dumps(bad_sel).encode("utf-8"))
                self.assertNotEqual(bad_res.returncode, 0, f"{filename} accepted corrupted selector")

    def test_solidity_mutability_and_json_surrogate_controls(self) -> None:
        import hashlib

        # 1. Valid UTF-16 surrogate pair in Solidity comment inside request JSON is accepted
        req_dict = make_standard_json_request("SurrogateOk.sol", "placeholder")
        raw_req_str = json.dumps(req_dict).replace(
            '"placeholder"',
            '"// SPDX-License-Identifier: GPL-3.0\\n// Emoji: \\uD83D\\uDE00\\npragma solidity ^0.8.0;\\ncontract SurrogateOk { function ping() external pure returns (uint256) { return 1; } }\\n"',
        )
        req_bytes = raw_req_str.encode("utf-8")
        comp = subprocess.run(
            [str(OKSOLC_BIN), "--standard-json"],
            input=req_bytes,
            capture_output=True,
            check=True,
        )
        ver = run_verify("standard-json", req_bytes, comp.stdout)
        self.assertEqual(ver.returncode, 0, msg=ver.stderr)
        self.assertTrue(json.loads(ver.stdout)["accepted"])

        # 2. Lone high surrogate in JSON must be rejected by oksolc-verify
        lone_req_bytes = raw_req_str.replace("\\uD83D\\uDE00", "\\uD83D").encode("utf-8")
        lone_ver = run_verify("standard-json", lone_req_bytes, comp.stdout)
        self.assertNotEqual(lone_ver.returncode, 0)

        # 3. Spoofed source claiming `pure` while bytecode reads storage (`s`) is rejected by wellFormed
        bad_pure_src = (
            "// SPDX-License-Identifier: GPL-3.0\n"
            "pragma solidity ^0.8.0;\n"
            "contract BadPure {\n"
            "    uint256 s;\n"
            "    function readS() external pure returns (uint256) { return s; }\n"
            "}\n"
        )
        bad_req = json.dumps(make_standard_json_request("BadPure.sol", bad_pure_src)).encode("utf-8")
        fake_resp = json.loads(comp.stdout.decode("utf-8"))
        fake_resp["requestSha256"] = hashlib.sha256(bad_req).hexdigest()
        bad_pure_ver = run_verify("standard-json", bad_req, json.dumps(fake_resp).encode("utf-8"))
        self.assertNotEqual(bad_pure_ver.returncode, 0)


if __name__ == "__main__":
    unittest.main()
