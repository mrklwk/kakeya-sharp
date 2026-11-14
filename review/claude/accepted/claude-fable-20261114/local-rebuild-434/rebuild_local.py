#!/usr/bin/env python3
"""Recompile every local KakeyaSharp module, plus Solution, Challenge and the
audit files, from current source with Lean 4.34.1, in dependency order, into a
separate output directory. Upstream OAI and mathlib artifacts are taken from the
existing caches. This is a fresh kernel check of the local modules only."""
import json, os, re, subprocess, sys, time, hashlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).resolve()
OLD = ROOT.parent / "kakeya_sharp" / ".lake" / "packages"
LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
WORKERS = int(sys.argv[3]) if len(sys.argv) > 3 else 4

paths = [str(OUT), str(ROOT / ".lake/build/lib/lean")]
for d in ["mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets", "aesop", "Qq", "batteries"]:
    paths.append(str(OLD / d / ".lake/build/lib/lean"))
paths.append(str(LEAN.parent.parent / "lib/lean"))
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(paths)

def module_of(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)

files = sorted((ROOT / "KakeyaSharp").rglob("*.lean")) + [ROOT / "KakeyaSharp.lean",
        ROOT / "Solution.lean", ROOT / "Challenge.lean", ROOT / "SubmissionAudit.lean", ROOT / "SemanticAudit.lean"]
mods = {module_of(f): f for f in files}
imp_re = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)
deps = {}
for m, f in mods.items():
    text = f.read_text()
    deps[m] = {d for d in imp_re.findall(text) if d in mods}

done, failed, running = set(), {}, set()
results = {}
start = time.time()

def compile_one(m):
    f = mods[m]
    out = OUT / (Path(*m.split(".")).with_suffix(".olean"))
    out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    r = subprocess.run([str(LEAN), str(f), "-o", str(out)], cwd=ROOT, env=env, text=True, capture_output=True)
    return m, r.returncode, r.stdout + r.stderr, time.time() - t0, hashlib.sha256(f.read_bytes()).hexdigest()

with ThreadPoolExecutor(max_workers=WORKERS) as ex:
    futures = {}
    while len(done) + len(failed) < len(mods):
        ready = [m for m in mods if m not in done and m not in failed and m not in running and deps[m] <= done]
        blocked = [m for m in mods if m not in done and m not in failed and m not in running and deps[m] & set(failed)]
        for m in blocked:
            failed[m] = "blocked by failed dependency"
        for m in ready:
            running.add(m)
            futures[ex.submit(compile_one, m)] = m
        if not futures:
            break
        fut = next(as_completed(futures))
        m = futures.pop(fut)
        running.discard(m)
        name, rc, log, dt, sha = fut.result()
        results[name] = {"returncode": rc, "seconds": round(dt, 1), "source_sha256": sha,
                         "log": log[-4000:] if log.strip() else ""}
        if rc == 0 and "error" not in log:
            done.add(name)
            print(f"ok   {name} ({dt:.1f}s) [{len(done)}/{len(mods)}]", flush=True)
        else:
            failed[name] = log[-2000:]
            print(f"FAIL {name} ({dt:.1f}s)\n{log[-2000:]}", flush=True)

summary = {"lean": subprocess.run([str(LEAN), "--version"], text=True, capture_output=True).stdout.strip(),
           "modules_total": len(mods), "compiled_ok": len(done), "failed": sorted(failed),
           "elapsed_seconds": round(time.time() - start), "workers": WORKERS,
           "lean_path": paths, "results": results}
(OUT / "rebuild-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps({k: v for k, v in summary.items() if k != "results"}, indent=2))
sys.exit(0 if not failed else 1)
