#!/usr/bin/env python3
"""Complete retained corpus units for the expression-contract certificate gate.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import hashlib
import json
import subprocess

from check_word_swap import ROOT
from common import decode_json

ARCHIVE = "test/benchmarks/external-requests/openzeppelin-5.6.1.json.zst"
PROVENANCE = "test/benchmarks/external-requests/openzeppelin-5.6.1/provenance.json"
ARCHIVE_SHA256 = "68fab61cf9514752fef804d459ae1939654bf1f9fa71c47145bc5d6cdd9589ae"
PROVENANCE_SHA256 = "93b3c423d1c4b6e4dbb9275af35e3ea284bc44423fe2940876b62e0b02bb125a"
REQUEST_SHA256 = "9529800e8ba5dbacacb94fe07f501aa86e0fc2fe916d709428e3ccdf46748010"
SOURCE_PATH = "contracts/mocks/token/ERC20ExcessDecimalsMock.sol"
SOURCE_SHA256 = "f529e1171a2a93c8718f4d6731713889950238ebe69e344f21f72bf4af1f5446"
CASE = "openzeppelin-excess-decimals"
BEACON_PATH = "contracts/mocks/proxy/BadBeacon.sol"
BEACON_SHA256 = "dbb600bc91b91a4ad052b0ea71ea9c216401786348afdd5ad4f9e78e9dc4e2d0"
BEACON_CASE = "openzeppelin-bad-beacon"
BEACON_TARGET = "BadBeaconNotContract"
EMPTY_BEACON_CASE = "openzeppelin-empty-beacon"
EMPTY_BEACON_TARGET = "BadBeaconNoImpl"

CLASHING_ARCHIVE = "test/benchmarks/external-requests/openzeppelin-4.7.0.json.zst"
CLASHING_ARCHIVE_SHA256 = "d19bf4eef1b593ed5ad2229833dd51672d4e198d4ca674b526a12be1ec936c7d"
CLASHING_REQUEST_SHA256 = "fddf84aa0182f6ef015666d8a4c2dfc31ee1953782b5d471130ab464f910735d"
CLASHING_PATH = "contracts/mocks/ClashingImplementation.sol"
CLASHING_SHA256 = "ddf71a32153b06df754b85593077e3b3871799f47aab407f6f6a86d9e204b737"
CLASHING_CASE = "openzeppelin-clashing-implementation"
CLASHING_TARGET = "ClashingImplementation"

PAYABLE_ARCHIVE = "test/benchmarks/external-requests/openzeppelin-4.9.0.json.zst"
PAYABLE_ARCHIVE_SHA256 = "9ef95ee7634ef716f2b23efee3d9c4a437ea7994fd896531d17afc45fddeda62"
PAYABLE_REQUEST_SHA256 = "592f32ad442ad5fd5d9dbb2d3432c2d9c54d9f02400c4e3c7df945fbaa03994a"
PAYABLE_PATH = "contracts/mocks/proxy/ClashingImplementation.sol"
PAYABLE_SHA256 = "c1060582801a54099373bf47dd2e1ba55de1f391223695108264b5f1f64aeafd"
PAYABLE_CASE = "openzeppelin-payable-clashing-implementation"

NO_RETURN_ARCHIVE = "test/benchmarks/external-requests/openzeppelin-5.0.2.json.zst"
NO_RETURN_ARCHIVE_SHA256 = "6908620f0e972889f2f0f3aa83ab148031121faaf71fdca4f62c61bf1e308967"
NO_RETURN_REQUEST_SHA256 = "f8aad237c5ef7559007fdfcfefb428984cdce67b47c625ccda7ae8f6c7082ed5"
NO_RETURN_PATH = "contracts/mocks/ERC165/ERC165MissingData.sol"
NO_RETURN_SHA256 = "134040e5061063097ee712a3ba9ee0ab9448ed6ed0bfd60563d081267b3a5b65"
NO_RETURN_TARGET = "ERC165MissingData"
NO_RETURN_CASE = "openzeppelin-erc165-missing-data"
RAW_RETURN_PATH = "contracts/mocks/ERC165/ERC165MaliciousData.sol"
RAW_RETURN_SHA256 = "7dfaa639211c8f49c9138fb26e9696cd7e629ad094f39b3e12cf7c9b645e7c37"
RAW_RETURN_TARGET = "ERC165MaliciousData"
RAW_RETURN_CASE = "openzeppelin-erc165-malicious-data"

RECEIVER_PATH = "contracts/mocks/EtherReceiverMock.sol"
RECEIVER_SHA256 = "85cf94451f1136154d4c1be24a38890281ce0f7c29c337c94a9246e2b4f62a99"
RECEIVER_TARGET = "EtherReceiverMock"
RECEIVER_CASE = "openzeppelin-ether-receiver"

BYTES32_ARCHIVE = "test/benchmarks/external-requests/sablier-v2-1.2.0.json.zst"
BYTES32_ARCHIVE_SHA256 = "1323909196dc38cc8a72e019d89d4470b173d2e8c5f5f8149550494d25f385b7"
BYTES32_REQUEST_SHA256 = "6a320079c52eb6d5772b53c3e9c860886db87d6eed9916874c334957a5c3294c"
BYTES32_PATH = "test/mocks/erc20/ERC20Bytes32.sol"
BYTES32_SHA256 = "9e987b5d9d787cf4882be0e5a85c9d651b261068ef3f48f8078c64e793dbef93"
BYTES32_TARGET = "ERC20Bytes32"
BYTES32_CASE = "sablier-erc20-bytes32"

INTEGER_ARCHIVE = "test/benchmarks/external-requests/eigenlayer-0.3.0.json.zst"
INTEGER_ARCHIVE_SHA256 = "3eda0881b918ba7616f18a7113b3c4c929f83a71b6aa78921739008bd75ed85c"
INTEGER_REQUEST_SHA256 = "89e2c7a3db1406101cf1d85419f31d99a28784794d726ae9609e53e58aa9b0ef"
INTEGER_PATH = "src/test/mocks/EmptyContract.sol"
INTEGER_SHA256 = "94def924f1cf19655142de111c7cbee2aaf358d1ca515b300845aed73dc40387"
INTEGER_TARGET = "EmptyContract"
INTEGER_CASE = "eigenlayer-empty-contract-word-return"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(source_path=SOURCE_PATH, selected=None):
    admitted = {SOURCE_PATH: (SOURCE_SHA256, "ERC20ExcessDecimalsMock", []),
        BEACON_PATH: (BEACON_SHA256, BEACON_TARGET, ["BadBeaconNoImpl"]),
        CLASHING_PATH: (CLASHING_SHA256, CLASHING_TARGET, []),
        PAYABLE_PATH: (PAYABLE_SHA256, CLASHING_TARGET, []),
        NO_RETURN_PATH: (NO_RETURN_SHA256, NO_RETURN_TARGET, []),
        RAW_RETURN_PATH: (RAW_RETURN_SHA256, RAW_RETURN_TARGET, []),
        RECEIVER_PATH: (RECEIVER_SHA256, RECEIVER_TARGET, []),
        BYTES32_PATH: (BYTES32_SHA256, BYTES32_TARGET, []),
        INTEGER_PATH: (INTEGER_SHA256, INTEGER_TARGET, [])}
    if source_path not in admitted:
        raise ValueError("unknown retained contract source")
    source_digest, target, siblings = admitted[source_path]
    if selected is not None:
        inventory = [target, *siblings]
        if selected not in inventory:
            raise ValueError("unknown retained contract target")
        target, siblings = selected, [name for name in inventory if name != selected]
    retained = {
        CLASHING_PATH: (CLASHING_ARCHIVE, CLASHING_ARCHIVE_SHA256, CLASHING_REQUEST_SHA256, "OpenZeppelin 4.7.0"),
        PAYABLE_PATH: (PAYABLE_ARCHIVE, PAYABLE_ARCHIVE_SHA256, PAYABLE_REQUEST_SHA256, "OpenZeppelin 4.9.0"),
        NO_RETURN_PATH: (NO_RETURN_ARCHIVE, NO_RETURN_ARCHIVE_SHA256, NO_RETURN_REQUEST_SHA256, "OpenZeppelin 5.0.2"),
        RAW_RETURN_PATH: (NO_RETURN_ARCHIVE, NO_RETURN_ARCHIVE_SHA256, NO_RETURN_REQUEST_SHA256, "OpenZeppelin 5.0.2"),
        BYTES32_PATH: (BYTES32_ARCHIVE, BYTES32_ARCHIVE_SHA256, BYTES32_REQUEST_SHA256, "Sablier v2 1.2.0"),
        INTEGER_PATH: (INTEGER_ARCHIVE, INTEGER_ARCHIVE_SHA256, INTEGER_REQUEST_SHA256, "EigenLayer 0.3.0"),
    }.get(source_path)
    legacy = retained is not None
    archive, archive_sha, request_sha = retained[:3] if legacy else (ARCHIVE, ARCHIVE_SHA256, REQUEST_SHA256)
    packed = (ROOT / archive).read_bytes()
    provenance_bytes = None if legacy else (ROOT / PROVENANCE).read_bytes()
    if sha(packed) != archive_sha or (provenance_bytes is not None and sha(provenance_bytes) != PROVENANCE_SHA256):
        raise ValueError("retained contract corpus identity changed")
    raw = subprocess.run(["zstd", "-qdc"], input=packed, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=True, timeout=30).stdout
    if sha(raw) != request_sha:
        raise ValueError("retained contract request identity changed")
    request = decode_json(raw.decode())
    # Legacy retained requests have no neighboring provenance record. Bind their
    # exact bytes without inventing an upstream commit or transformation history.
    provenance = decode_json(provenance_bytes.decode()) if provenance_bytes is not None else {
        "project": retained[3] + " retained request", "commit": None, "transforms": None}
    entry = request["sources"][source_path]
    if set(entry) != {"content"} or sha(entry["content"].encode()) != source_digest:
        raise ValueError("retained complete source unit changed")
    settings = (json.dumps(request["settings"], sort_keys=True, separators=(",", ":")) + "\n").encode()
    return entry["content"], {
        "project": provenance["project"], "upstreamCommit": provenance["commit"],
        "archive": archive, "archiveSha256": archive_sha,
        "originalRequestSha256": request_sha, "originalSettingsSha256": sha(settings),
        "originalFork": request["settings"]["evmVersion"],
        "originalSourcePath": source_path, "certificateSourcePath": "Function.sol",
        "sourceSha256": source_digest, "sourceBytes": len(entry["content"].encode()),
        "certificateContract": target, "uncertifiedSiblingContracts": siblings,
        "sourceContentUnchanged": True, "completeSourceUnit": True,
        "originalSourceCount": len(request["sources"]), "omittedSourceCount": len(request["sources"]) - 1,
        "wholeOriginalRequestVerified": False, "originalSettingsPreserved": False,
        "retainedCorpusTransforms": provenance["transforms"],
    }


def matching_origin(content, selected=None):
    path = {SOURCE_SHA256: SOURCE_PATH, BEACON_SHA256: BEACON_PATH, CLASHING_SHA256: CLASHING_PATH,
            PAYABLE_SHA256: PAYABLE_PATH, NO_RETURN_SHA256: NO_RETURN_PATH,
            RAW_RETURN_SHA256: RAW_RETURN_PATH, RECEIVER_SHA256: RECEIVER_PATH,
            BYTES32_SHA256: BYTES32_PATH, INTEGER_SHA256: INTEGER_PATH}.get(sha(content.encode()))
    if path is None:
        return None
    original, origin = load(path, selected)
    if content != original:
        raise ValueError("source digest matched different retained bytes")
    return origin
