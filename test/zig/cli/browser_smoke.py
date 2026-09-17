#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
Real CLI/HTTP/SQL boundaries; no browser or third-party Python dependency.
"""
import concurrent.futures
import contextlib
import hashlib
import http.client
import json
import pathlib
import socket
import sqlite3
import subprocess
import sys
import tempfile
import time


@contextlib.contextmanager
def browser(cli, directory, arguments, command="browse", wait_for_compilation=True, env=None):
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        port = sock.getsockname()[1]
    with tempfile.TemporaryFile() as log:
        process = subprocess.Popen([cli, command, "--port", str(port), *arguments], cwd=directory, stdout=log, stderr=log, env=env)
        try:
            deadline = time.monotonic() + 45
            while True:
                try:
                    status, _, body = request(port, "/api/compilations")
                    ready = status == 200 and (not wait_for_compilation or json.loads(body))
                    if ready and wait_for_compilation and command == 'serve':
                        ready = data(port, 'status')['phase'] == 'watching'
                    if ready:
                        break
                except OSError:
                    pass
                if process.poll() is not None or time.monotonic() > deadline:
                    log.seek(0)
                    raise AssertionError(f"browser failed to start: {log.read().decode()}")
                time.sleep(.05)
            yield port
        finally:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=5)


def request(port, path, headers=None, method="GET"):
    connection = http.client.HTTPConnection("127.0.0.1", port, timeout=15)
    try:
        connection.request(method, path, headers=headers or {})
        response = connection.getresponse()
        return response.status, dict(response.getheaders()), response.read()
    finally:
        connection.close()


def data(port, route):
    status, _, body = request(port, f"/api/{route}")
    assert status == 200, (route, status, body)
    return json.loads(body)


def main():
    cli = str(pathlib.Path(sys.argv[1]).resolve())
    with tempfile.TemporaryDirectory(prefix="oksolc-browser-") as temporary:
        directory = pathlib.Path(temporary)
        (directory / "lib").mkdir()
        library = '// SPDX-License-Identifier: MIT\npragma solidity >=0.0.0;\nlibrary Math { function twice(uint x) internal pure returns (uint) { return x * 2; } }\n'
        source = '// SPDX-License-Identifier: MIT\npragma solidity >=0.0.0;\n// λ </script><script>window.sourceExecuted=true</script>\nimport "./lib/Math.sol";\ncontract Vault { function check(uint x) external pure returns (uint) { assert(x == x); assert(x > 1); return Math.twice(x); } }\n'
        (directory / "Vault.sol").write_text(source)
        (directory / "lib/Math.sol").write_text(library)
        database = str(directory / "workspace.sqlite")
        with browser(cli, directory, ["--no-cache", "--database", database, "Vault.sol"]) as port:
            status, headers, body = request(port, "/")
            assert status == 200 and b'oksolc' in body
            assert "frame-ancestors 'none'" in headers["Content-Security-Policy"]
            for resource in ["/app.js", "/style.css"]:
                assert request(port, resource)[0] == 200
            assert request(port, "/", {"Host": "remote.example"})[0] == 403
            assert request(port, "/api/output", {"Origin": "https://remote.example"})[0] == 403
            assert request(port, "/api/output", {"Sec-Fetch-Site": "cross-site"})[0] == 403
            assert request(port, "/api/source?compilation=-1")[0] == 400
            assert request(port, "/api/execute?sql=DROP%20TABLE%20source")[0] == 404
            assert request(port, "/api/output", method="POST")[0] == 404
            assert request(port, "/../../etc/passwd")[0] == 404
            for route in ["targets", "annotations", "analysis-results", "analysis-overview", "analysis-settings", "tests", "test", "test-results", "test-suites", "functions"]:
                assert request(port, f"/api/{route}")[0] == 404
            project = data(port, "project")
            assert {row["name"] for row in project} == {"Vault.sol", "lib/Math.sol"}, project
            assert all(row["available"] and row["has_ast"] for row in project)
            captured = data(port, "source?source=lib%2FMath.sol")
            assert captured["content"] == library
            file = data(port, "source?source=Vault.sol")
            assert file["content"] == source
            assert file["tokens"][-1]["end"] == len(source.encode())
            assert any(token["kind"] == "keyword" for token in file["tokens"])
            symbols = data(port, "symbols?source=lib%2FMath.sol&q=twice")
            assert len(symbols) == 1
            references = data(port, f'references?symbol={symbols[0]["id"]}')
            assert any(row["source"] == "Vault.sol" for row in references)
            links = data(port, "links?source=Vault.sol")
            assert any(row["target_source"] == "lib/Math.sol" for row in links)
            assert data(port, "search?q=twice")
            output = request(port, "/api/output")[2]
            input_bytes = request(port, "/api/request")[2]
            snapshot = data(port, "compilations")[0]
            assert snapshot["output_sha256"] == hashlib.sha256(output).hexdigest()
            assert snapshot["origin"] == "compiled"
            with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
                assert all(pool.map(lambda _: request(port, "/api/output")[2] == output, range(12)))
        with sqlite3.connect(database) as sql:
            stored = sql.execute("SELECT request,output FROM compilation").fetchone()
            assert stored == (input_bytes.decode(), output.decode())
            assert sql.execute("PRAGMA user_version").fetchone()[0] == 4
            assert sql.execute("SELECT count(*) FROM sqlite_schema WHERE name='target' OR name LIKE 'analysis_%' OR name LIKE 'inspection_%'").fetchone()[0] == 0
        with browser(cli, directory, ["--database", database]) as port:
            assert request(port, "/api/output")[2] == output
            assert data(port, "source?source=lib%2FMath.sol")["content"] == library
        assert not (directory / ".oksolc").exists(), "explicit database must not create the default directory"
        source_run = subprocess.run([cli, "compile", "--no-cache", "Vault.sol"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=directory)
        assert source_run.returncode == 0, source_run.stderr.decode()
        expected = json.loads(output)
        for entry in expected.get("sources", {}).values():
            entry.pop("ast", None)
        for contracts in expected.get("contracts", {}).values():
            for contract in contracts.values():
                del contract["userdoc"], contract["devdoc"]
                del contract["evm"]["methodIdentifiers"]
                del contract["evm"]["bytecode"]["linkReferences"]
                del contract["evm"]["deployedBytecode"]["linkReferences"]
                del contract["evm"]["deployedBytecode"]["immutableReferences"]
        assert expected == json.loads(source_run.stdout)
        compiled = subprocess.run([cli, "standard-json", "--no-cache", "--base-path", "."], input=input_bytes, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=directory)
        assert compiled.returncode == 0, compiled.stderr.decode()
        (directory / "request.json").write_bytes(input_bytes)
        (directory / "output.json").write_bytes(output)
        with browser(cli, directory, ["--no-cache", "--request", "request.json"]) as port:
            assert request(port, "/api/output")[2] == compiled.stdout
        default_database = directory / ".oksolc/browser.sqlite"
        assert default_database.is_file(), "without a marker, use the working directory"
        with browser(cli, directory, []) as port:
            assert request(port, "/api/output")[2] == compiled.stdout
        (directory / "linked.sqlite").symlink_to(database)
        rejected = subprocess.run([cli, "browse", "--database", "linked.sqlite"], cwd=directory, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
        assert rejected.returncode != 0 and b"DatabaseUnavailable" in rejected.stderr
        with browser(cli, directory, ["--request", "request.json", "--import-output", "output.json", "--database", database]) as port:
            assert data(port, "compilations")[0]["origin"] == "imported"
            assert request(port, "/api/output")[2] == output
            assert data(port, "source?source=lib%2FMath.sol")["content"] is None
        check_project_defaults(cli, directory, output)
        check_library_diagnostics(cli)
        print("browser smoke: compile, SQL, source capture, navigation, isolation, restart, import, canonical bytes, and project database defaults passed")


def check_library_diagnostics(cli):
    with tempfile.TemporaryDirectory(prefix="oksolc-diagnostics-") as temporary:
        directory = pathlib.Path(temporary)
        libraries = ["lib/L.sol", "node_modules/pkg/L.sol", "vendor/L.sol", "@scope/pkg/L.sol", "./lib/L.sol", "lib\\L.sol"]
        project = ["src/App.sol", "contracts/App.sol", "src/lib/Owned.sol", "library/App.sol", "unknown/App.sol", None]
        # More than a full page of libraries precedes the project diagnostics.
        paths = [libraries[i % len(libraries)] for i in range(205)] + [project[i % len(project)] for i in range(207)]
        records = [{"severity": "warning", "message": str(i), **({"sourceLocation": {"file": path, "start": 0, "end": 1}} if path else {})} for i, path in enumerate(paths)]
        output = json.dumps({"errors": records})
        (directory / "request.json").write_text(json.dumps({"language": "Solidity", "sources": {}}))
        (directory / "output.json").write_text(output)
        with browser(cli, directory, ["--request", "request.json", "--import-output", "output.json", "--database", ":memory:"]) as port:
            assert len(data(port, "diagnostics")) == 201
            rows = data(port, "diagnostics?hide_libraries=1")
            assert [json.loads(row["data"])["message"] for row in rows] == [str(i) for i in range(205, 406)]
            tail = data(port, "diagnostics?hide_libraries=1&offset=200")
            assert [json.loads(row["data"])["message"] for row in tail] == [str(i) for i in range(405, 412)]
            assert any(row["source"] is None for row in rows)
            assert data(port, "diagnostics?hide_libraries=1&source=lib%2FL.sol") == []
            assert data(port, "diagnostics?hide_libraries=0&source=lib%2FL.sol")
            assert data(port, "summary?hide_libraries=1") == [{"kind": "diagnostic", "status": "warning", "total": 207, "hidden": 205}]
            assert data(port, "summary") == [{"kind": "diagnostic", "status": "warning", "total": 412, "hidden": 0}]
            assert request(port, "/api/diagnostics?hide_libraries=2")[0] == 400
            assert request(port, "/api/summary?hide_libraries=-1")[0] == 400
            assert request(port, "/api/output")[2] == output.encode()


def check_project_defaults(cli, directory, output):
    (directory / ".git").mkdir()
    nested = directory / "contracts/nested"
    nested.mkdir(parents=True)
    imported = ["--request", str(directory / "request.json"), "--import-output", str(directory / "output.json")]
    with browser(cli, nested, imported) as port:
        assert len(data(port, "compilations")) == 2
        assert request(port, "/api/output")[2] == output
    assert not (nested / ".oksolc").exists()
    for location in [directory, nested]:
        with browser(cli, location, []) as port:
            assert len(data(port, "compilations")) == 2
            assert request(port, "/api/output")[2] == output

    # An explicit source root overrides discovery for compilation and reopening.
    with browser(cli, nested, ["--base-path", ".", *imported]) as port:
        assert len(data(port, "compilations")) == 1
    assert (nested / ".oksolc/browser.sqlite").is_file()
    with browser(cli, nested, ["--base-path", "."]) as port:
        assert len(data(port, "compilations")) == 1

    # A nearer project configuration wins over the enclosing Git root.
    (nested / "oksolc.toml").write_text("parallel = false\n")
    child = nested / "child"
    child.mkdir()
    with browser(cli, child, []) as port:
        assert len(data(port, "compilations")) == 1
    assert not (child / ".oksolc").exists()

    # Worktrees/submodules use a .git file, not a .git directory.
    worktree = directory / "worktree"
    worktree.mkdir()
    (worktree / ".git").write_text("gitdir: /unused-by-marker-discovery\n")
    with browser(cli, worktree, ["--database", ":memory:", *imported]) as port:
        assert request(port, "/api/output")[2] == output
    assert not (worktree / ".oksolc").exists()
    with browser(cli, worktree, imported) as port:
        assert len(data(port, "compilations")) == 1
    assert (worktree / ".oksolc/browser.sqlite").is_file()
    with sqlite3.connect(directory / ".oksolc/browser.sqlite") as sql:
        assert sql.execute("SELECT count(*) FROM compilation").fetchone()[0] == 2


if __name__ == "__main__":
    main()
