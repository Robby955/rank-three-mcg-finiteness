#!/usr/bin/env python3
"""Check that every audited name has exactly one accurate source link."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    declarations = json.loads((ROOT / "receipts/declarations.json").read_text())
    table = (ROOT / "CORRESPONDENCE.md").read_text()
    links = re.findall(r"\[`(\w+)`\]\((Normalizer/\w+\.lean)#L(\d+)\)", table)
    expected = {
        (d["name"].removeprefix("Normalizer."), d["file"], str(d["line"]))
        for d in declarations
    }
    if len(links) != len(expected) or set(links) != expected:
        raise SystemExit("Correspondence must link each audited declaration exactly once.")
    for name, file, line in links:
        source_line = (ROOT / file).read_text().splitlines()[int(line) - 1]
        if not re.match(r"^(?:noncomputable )?(?:theorem|def|abbrev) "
                        + re.escape(name) + r"\b", source_line):
            raise SystemExit(f"Stale declaration link: {file}#L{line}")
    for doc in ROOT.glob("*.md"):
        for target in re.findall(r"\]\(([^)]+)\)", doc.read_text()):
            if "://" in target or target.startswith("#"):
                continue
            file = target.split("#", 1)[0]
            if not (doc.parent / file).is_file():
                raise SystemExit(f"Broken local link in {doc.name}: {target}")
    print(f"PASS: {len(expected)} declaration links and package documentation links.")


if __name__ == "__main__":
    main()
