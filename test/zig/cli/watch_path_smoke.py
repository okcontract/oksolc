#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.

"""Exercise watch path validation through real atomic publication."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    binary = str(Path(sys.argv[1]).resolve())
    request = json.dumps({
        "language": "Solidity",
        "sources": {"C.sol": {"content": "contract C {}"}},
        "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
    }).encode()
    with tempfile.TemporaryDirectory(prefix="oksolc-watch-paths-") as directory:
        root = Path(directory).resolve()
        source = root / "request.json"
        source.write_bytes(request)
        (root / "child").mkdir()
        (root / "linked").symlink_to(root, target_is_directory=True)
        (root / "input-link.json").symlink_to(source)
        (root / "output-link.json").symlink_to(source)
        env = dict(os.environ, XDG_CONFIG_HOME=str(root / "config"), XDG_CACHE_HOME=str(root / "cache"))

        def run(output, input_path="request.json", reject=True):
            result = subprocess.run(
                [binary, "watch", "--no-cache", "--once", "-o", str(output), str(input_path)],
                cwd=root, env=env, capture_output=True, timeout=30,
            )
            assert source.read_bytes() == request, (input_path, output, "request overwritten")
            if reject:
                assert result.returncode != 0 and b"DuplicateOutputPath" in result.stderr, result
            else:
                assert result.returncode == 0, result.stderr.decode()
                data = result.stdout if output == "-" else (root / output).read_bytes()
                assert "C" in json.loads(data)["contracts"]["C.sol"]

        for output in (
            "request.json", "./request.json", source, "child/../request.json",
            "linked/request.json", "missing/../request.json", "output-link.json",
        ):
            run(output)
        run("request.json", "input-link.json")
        run("./input-link.json", "input-link.json")
        if (root / "REQUEST.JSON").exists():
            run("REQUEST.JSON")
        assert (root / "output-link.json").is_symlink()
        assert not (root / "missing").exists()

        run("-", reject=False)
        run("new/deep/output.json", reject=False)
        os.link(source, root / "hard-link.json")
        run("hard-link.json", reject=False)
        assert source.stat().st_ino != (root / "hard-link.json").stat().st_ino
    print("watch path aliases rejected; stdout, new outputs and distinct hard links preserved")


if __name__ == "__main__":
    main()
