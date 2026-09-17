#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
Exercise the terminal mode through a real pseudo-terminal.
"""
import os
import pathlib
import subprocess
import sys
import time


def main():
    probe = str(pathlib.Path(sys.argv[1]).resolve())
    for data, expected in ((b"", b""), (b"abc", b"a")):
        result = subprocess.run([probe], input=data, capture_output=True, timeout=5)
        assert result.returncode == 0, result.stderr
        assert result.stdout == expected, result.stdout
    if os.name != "posix":
        print("terminal probe: redirected input passed; pseudo-terminal unavailable")
        return

    import termios

    def restored_mode(fd):
        mode = termios.tcgetattr(fd)
        # The kernel may set PENDIN when canonical mode is restored.
        mode[3] &= ~getattr(termios, "PENDIN", 0)
        return mode

    master, slave = os.openpty()
    try:
        original = termios.tcgetattr(slave)
        original[3] |= termios.ICANON | termios.ECHO
        termios.tcsetattr(slave, termios.TCSANOW, original)
        original = restored_mode(slave)
        process = subprocess.Popen([probe], stdin=slave, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            deadline = time.monotonic() + 5
            while termios.tcgetattr(slave)[3] & (termios.ICANON | termios.ECHO):
                assert process.poll() is None, "terminal reader exited before reading"
                assert time.monotonic() < deadline, "terminal mode was not kept active for the read"
                time.sleep(0.01)
            os.write(master, b"x")  # No newline: canonical input would block.
            output, errors = process.communicate(timeout=5)
            assert process.returncode == 0, errors
            assert output == b"x", output
            assert restored_mode(slave) == original, "terminal mode was not restored"
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate(timeout=5)
        canceled = subprocess.run([probe, "cancel"], stdin=slave, capture_output=True, timeout=5)
        assert canceled.returncode == 0, canceled.stderr
        assert restored_mode(slave) == original, "terminal mode was not restored after cancellation"
    finally:
        os.close(slave)
        os.close(master)
    print("terminal probe: single-byte input, mode restoration, cancellation, redirected input and EOF passed")


if __name__ == "__main__":
    main()
