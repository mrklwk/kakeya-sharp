#!/usr/bin/env python3
"""Local source checks. These do not replace Palomar Comparator or replay."""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = {"KakeyaPalomar.sharpMaximalBound", "KakeyaPalomar.sharpTubeBound"}


def code_only(source):
    result = []
    index = depth = 0
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
        elif source.startswith("/-", index):
            result.append(" ")
            depth = 1
            index += 2
        elif source.startswith("--", index):
            end = source.find("\n", index)
            index = len(source) if end < 0 else end
        elif source[index] == '"':
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            result.append(" ")
        else:
            result.append(source[index])
            index += 1
    return "".join(result)


def imports(text):
    return re.findall(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)",
                      code_only(text), re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--axiom-report", type=Path)
    args = parser.parse_args()
    files = sorted(p for p in ROOT.rglob("*.lean")
                   if not {".lake", ".git"}.intersection(p.relative_to(ROOT).parts))
    for path in files:
        assert not path.is_symlink(), f"Lean source symlink: {path}"
        text = path.read_text(encoding="utf-8")
        code = code_only(text)
        assert code.lstrip().startswith("module"), f"Missing module header: {path}"
        assert len(text.splitlines()) <= 10000, f"Oversized source: {path}"
        if path.name != "Challenge.lean":
            found = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|sorryAx)\b|Lean\.ofReduceBool", code)
            assert found is None, f"Forbidden proof token in {path}: {found}"

    challenge = (ROOT / "Challenge.lean").read_text()
    solution = (ROOT / "Solution.lean").read_text()
    assert imports(challenge) == ["Mathlib"], "Challenge imports must be independent"
    assert len(re.findall(r"\bsorry\b", code_only(challenge))) == 2
    assert len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024
    # A readable source-level equality check, not a substitute for Comparator.
    start = "open MeasureTheory"
    end = "/-- Critical Kakeya maximal upper bound"
    assert challenge.split(start)[1].split(end)[0] == solution.split(start)[1].split(end)[0]
    for name in ("sharpMaximalBound", "sharpTubeBound"):
        pattern = rf"theorem {name}\b[\s\S]*?:= by"
        assert re.search(pattern, challenge)[0] == re.search(pattern, solution)[0]

    reachable = set()
    def visit(name):
        if name in reachable:
            return
        reachable.add(name)
        p = ROOT / (name.replace(".", "/") + ".lean")
        if p.is_file():
            for dependency in imports(p.read_text()):
                visit(dependency)
    visit("Solution")
    assert "Challenge" not in reachable, "Proof imports the statement placeholders"
    local = {str(p.relative_to(ROOT).with_suffix("")).replace("/", ".")
             for p in (ROOT / "KakeyaSharp").rglob("*.lean")}
    assert local <= reachable, "Disconnected local proof module"

    config = json.loads((ROOT / "comparator.json").read_text())
    assert set(config) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    assert config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution"
    assert set(config["theorem_names"]) == TARGETS
    assert set(config["permitted_axioms"]) == ALLOWED

    migration = json.loads((ROOT / "MODULE_MIGRATION.json").read_text())
    for item in migration["files"]:
        data = (ROOT / item["path"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == item["ported_sha256"], item["path"]
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        assert package["type"] == "git", package["name"]
        assert re.fullmatch(r"https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", package["url"])
        assert re.fullmatch(r"[0-9a-f]{40}", package["rev"]), package["name"]

    audit_status = "not supplied"
    if args.axiom_report:
        audit = args.axiom_report.read_text()
        assert not re.search(r"error:|sorryAx", audit)
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
        assert TARGETS <= {name for name, _ in reports}, "Missing result axiom reports"
        for name, axioms in reports:
            found = {a.strip() for a in axioms.split(",") if a.strip()}
            assert found <= ALLOWED, (name, found - ALLOWED)
        audit_status = "supplied report passes axiom allowlist; toolchain recorded separately"
    print(json.dumps({"source_checks": "passed", "lean_files": len(files),
        "challenge_lines": len(challenge.splitlines()), "challenge_bytes": len(challenge.encode()),
        "deliberate_challenge_placeholders": 2, "proof_placeholders": 0,
        "local_modules_reachable": len(local),
        "imported_upstream_modules": sum(n.startswith("OAI.") for n in reachable),
        "axiom_report": audit_status,
        "palomar_full_preflight": "not established by this script"}, indent=2))


if __name__ == "__main__":
    main()
