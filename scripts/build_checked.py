#!/usr/bin/env python3
"""Run Lake while removing completed, regenerable module setup JSON files.

Lake 4.34 emits a large import-map JSON for each compiled module. These
are compiler inputs, not proof artifacts. An input is removed only after
the module has written a newer .olean, or after Lake has exited.
Source files, .olean proofs, dependency traces, and package files are kept.
"""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def trim(completed_only: bool) -> None:
    ir = ROOT / ".lake/build/ir"
    lib = ROOT / ".lake/build/lib/lean"
    for setup in ir.rglob("*.setup.json"):
        relative = setup.relative_to(ir)
        proof = lib / str(relative).removesuffix(".setup.json")
        proof = proof.with_suffix(".olean")
        try:
            if not completed_only or (
                proof.is_file() and proof.stat().st_mtime >= setup.stat().st_mtime
            ):
                setup.unlink()
        except FileNotFoundError:
            pass


def main() -> int:
    lake = shutil.which("lake")
    if lake is None:
        candidate = Path.home() / ".elan/bin/lake"
        if candidate.is_file():
            lake = str(candidate)
    if lake is None:
        raise SystemExit("Lake is not installed or not on PATH.")
    process = subprocess.Popen([lake, *sys.argv[1:]], cwd=ROOT)
    try:
        while process.poll() is None:
            trim(completed_only=True)
            time.sleep(1)
        return process.returncode
    finally:
        if process.poll() is not None:
            trim(completed_only=False)


if __name__ == "__main__":
    sys.exit(main())
