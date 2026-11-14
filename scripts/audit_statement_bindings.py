#!/usr/bin/env python3
"""Compare elaborated types and definition bodies in separate Lean environments.

Normalize only bound variable names and expression metadata, which carry no
mathematical content. Preserve every constant, argument and typeclass instance.

Run after building Challenge and Solution. By default use `lake env lean`.
For a separately recorded compatible build, --lean accepts an explicit Lean
executable and inherits LEAN_PATH. This is not Palomar Comparator or replay.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DEFINITIONS = ["Space", "sphereMeasure", "tube", "kakeyaMaximal"]
THEOREMS = ["sharpMaximalBound", "sharpTubeBound"]


def export(module, directory, command):
    destination = directory / (module + ".json")
    source = directory / (module + "Bindings.lean")
    names = ", ".join("``KakeyaPalomar." + name for name in DEFINITIONS + THEOREMS)
    source.write_text(f'''module
import {module}
import Lean

private def normalizeBindings : Lean.Expr → Lean.Expr
  | .forallE _ t b i => .forallE .anonymous (normalizeBindings t) (normalizeBindings b) i
  | .lam _ t b i => .lam .anonymous (normalizeBindings t) (normalizeBindings b) i
  | .letE _ t v b n => .letE .anonymous (normalizeBindings t)
      (normalizeBindings v) (normalizeBindings b) n
  | .app f a => .app (normalizeBindings f) (normalizeBindings a)
  | .mdata _ e => normalizeBindings e
  | .proj s i e => .proj s i (normalizeBindings e)
  | e => e

run_cmd do
  let env ← Lean.getEnv
  let mut entries : List (String × Lean.Json) := []
  for name in [{names}] do
    let some ci := env.find? name | throwError "Missing declaration: {{name}}"
    let mut fields := [("type", Lean.Json.str (reprStr (normalizeBindings ci.type)))]
    match ci with
    | .defnInfo value =>
      fields := fields ++ [("value", Lean.Json.str (reprStr (normalizeBindings value.value)))]
    | _ => pure ()
    entries := entries ++ [(name.toString, Lean.Json.mkObj fields)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile {json.dumps(str(destination))}
    (Lean.Json.mkObj entries).compress
''', encoding="utf-8")
    result = subprocess.run(command + [str(source)], cwd=ROOT,
                            text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return json.loads(destination.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", help="Explicit Lean executable; inherit LEAN_PATH")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    command = [args.lean] if args.lean else ["lake", "env", "lean"]
    version = subprocess.run(command + ["--version"], cwd=ROOT, check=True,
                             text=True, capture_output=True).stdout.strip()
    with tempfile.TemporaryDirectory(prefix="kakeya-bindings-") as temp:
        directory = Path(temp)
        challenge = export("Challenge", directory, command)
        solution = export("Solution", directory, command)
    rows = []
    for name in DEFINITIONS + THEOREMS:
        qualified = "KakeyaPalomar." + name
        expected = {"type", "value"} if name in DEFINITIONS else {"type"}
        assert set(challenge[qualified]) == set(solution[qualified]) == expected
        for field in sorted(expected):
            a, b = challenge[qualified][field], solution[qualified][field]
            if a != b:
                difference = "\n".join(list(difflib.unified_diff(
                    a.splitlines(), b.splitlines(), fromfile="Challenge", tofile="Solution"))[:80])
                raise AssertionError(f"Elaborated expression differs: {qualified}.{field}\n{difference}")
            rows.append({"declaration": qualified, "field": field,
                         "expression_sha256": hashlib.sha256(a.encode()).hexdigest(),
                         "equal": True})
    report = {"status": "passed", "lean": version,
              "method": "Equality of Lean Expr representations in separately imported environments, after normalizing bound variable names and metadata only",
              "definitions_compared": DEFINITIONS, "theorem_types_compared": THEOREMS,
              "comparisons": rows,
              "limitations": "Does not replace official Comparator, source rebuild, or independent kernel replay"}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "expressions_compared": len(rows),
                      "lean": version, "report": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
