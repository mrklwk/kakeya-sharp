#!/usr/bin/env python3
"""Refresh the source manifest and create a source-only release archive."""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def included(path):
    relative = path.relative_to(ROOT)
    if {".lake", ".git", "__pycache__"}.intersection(relative.parts):
        return False
    if relative.parts[:3] == ("review", "claude", "runs"):
        return False
    if path.name == ".DS_Store" or path.name == ".env" or path.name.startswith(".env."):
        return False
    if path.suffix in {".pyc", ".olean", ".ilean"}:
        return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    destination = args.output.resolve()
    assert not destination.is_relative_to(ROOT), "Write the archive outside its source tree"
    files = sorted(p for p in ROOT.rglob("*") if p.is_file() and included(p))
    for path in files:
        assert not path.is_symlink(), f"Unexpected source symlink: {path}"
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in files if p.name != "SOURCE_SHA256.json"}
    hash_file = ROOT / "SOURCE_SHA256.json"
    hash_file.write_text(json.dumps(hashes, indent=2) + "\n")
    if hash_file not in files:
        files.append(hash_file)
        files.sort()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(destination, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in files:
            archive.write(path, Path("Kakeya_Palomar") / path.relative_to(ROOT))
    with zipfile.ZipFile(destination) as archive:
        assert archive.testzip() is None
        for name, digest in hashes.items():
            assert hashlib.sha256(archive.read("Kakeya_Palomar/" + name)).hexdigest() == digest
    print(json.dumps({"archive": str(destination), "entries": len(files),
                      "bytes": destination.stat().st_size,
                      "sha256": hashlib.sha256(destination.read_bytes()).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
