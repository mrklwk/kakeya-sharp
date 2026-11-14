#!/usr/bin/env python3
"""Rerun short checks against existing 4.34.1 artifacts; never label this a clean build."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"


def capture(command, **kwargs):
    return subprocess.run(command, check=True, text=True, capture_output=True, **kwargs).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--checkpoint-root", type=Path, default=ROOT.parent / "kakeya_sharp")
    parser.add_argument("--lean", type=Path, default=Path.home() /
                        ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
    args = parser.parse_args()
    old = args.checkpoint_root.resolve()
    compiler = args.lean.resolve()
    if not compiler.is_file():
        raise SystemExit("Lean 4.34.1 is unavailable. No check was run.")
    version = capture([str(compiler), "--version"]).strip()
    assert "version 4.34.1," in version, version
    manifest = json.loads((old / "lake-manifest.json").read_text())
    dependencies = []
    paths = [ROOT / ".lake/build/lib/lean"]
    assert (paths[0] / "Solution.olean").is_file(), "Missing compiled candidate Solution"
    assert (paths[0] / "Challenge.olean").is_file(), "Missing compiled candidate Challenge"
    for package in manifest["packages"]:
        folder = old / ".lake/packages" / package["name"]
        revision = capture(["git", "-C", str(folder), "rev-parse", "HEAD"]).strip()
        assert revision == package["rev"], package["name"]
        if package["name"] == "mathlib":
            assert revision == MATHLIB
            assert not capture(["git", "-C", str(folder), "status", "--porcelain=v1"])
        dependency_lib = folder / ".lake/build/lib/lean"
        # Some Lake-only packages have no compiled modules used by these audits.
        # Lean will reject an actually needed missing import during the checks.
        if dependency_lib.is_dir():
            paths.append(dependency_lib)
        dependencies.append({"name": package["name"], "revision": revision,
                             "compiled_library_present": dependency_lib.is_dir()})
    paths.append(compiler.parent.parent / "lib/lean")
    assert old / ".lake/build/lib/lean" not in paths

    source_manifest = json.loads((ROOT / "SOURCE_SHA256.json").read_text())
    lean_hashes = {}
    for name, expected in source_manifest.items():
        if name.endswith(".lean"):
            actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            assert actual == expected, f"Source changed since manifest: {name}"
            lean_hashes[name] = actual
    source_identity = hashlib.sha256(json.dumps(lean_hashes, sort_keys=True).encode()).hexdigest()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in paths)
    checks = []
    for filename, expected_count in [("SubmissionAudit.lean", 2), ("SemanticAudit.lean", 11)]:
        print(f"Checking {filename} with existing 4.34.1 artifacts", flush=True)
        result = subprocess.run([str(compiler), filename], cwd=ROOT, env=env,
                                text=True, capture_output=True)
        log = result.stdout + result.stderr
        (output / (filename + ".log")).write_text(log)
        assert result.returncode == 0 and not re.search(r"error:|sorryAx", log), filename
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        assert len(reports) == expected_count, filename
        for name, values in reports:
            assert {v.strip() for v in values.split(",") if v.strip()} <= ALLOWED, name
        checks.append({"file": filename, "status": "passed", "axiom_reports": len(reports)})
    print("Comparing statements in separate imported environments", flush=True)
    binding_log = capture([sys.executable, str(ROOT / "scripts/audit_statement_bindings.py"),
                           "--lean", str(compiler), "--output", str(output / "bindings.json")],
                          cwd=ROOT, env=env)
    (output / "bindings.log").write_text(binding_log)
    source_log = capture([sys.executable, str(ROOT / "scripts/check_submission.py"),
                          "--axiom-report", str(output / "SubmissionAudit.lean.log")], cwd=ROOT)
    (output / "source-checks.json").write_text(source_log)
    result = {"status": "passed", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
              "lean": version, "dependencies": dependencies,
              "lean_source_files": len(lean_hashes), "lean_source_identity_sha256": source_identity,
              "checks": checks, "statement_binding_expressions": 10,
              "original_project_build_excluded_from_lean_path": True,
              "scope": "Rechecked short source audits using existing candidate proof artifacts and pinned dependency caches; not a fresh proof rebuild or independent kernel replay",
              "target_435_validation": "not run", "claude_review": "not run by this script"}
    (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
