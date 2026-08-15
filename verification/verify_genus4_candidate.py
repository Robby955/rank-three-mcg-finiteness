#!/usr/bin/env python3
"""Verify the public genus-four candidate package.

This is an artifact and claim-boundary gate. It does not certify the
mathematics.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "manuscript/rank3_genus4_extension.tex"
PDF = ROOT / "output/pdf/rank3_genus4_extension.pdf"
CHECKSUMS = ROOT / "CHECKSUMS.sha256"
EXPECTED_PAGES = 30


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def run(command: list[str], *, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
    )


def require_tool(name: str) -> str:
    path = shutil.which(name)
    require(path is not None, f"required tool not found: {name}")
    return path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def expected_hashes() -> dict[str, str]:
    hashes: dict[str, str] = {}
    for line in CHECKSUMS.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        digest, relative_path = line.split(maxsplit=1)
        hashes[relative_path] = digest
    return hashes


def normalized_pdf_text(pdf: Path, pdftotext: str) -> str:
    # Raw extraction follows PDF content order and is stable across the TeX Live
    # versions used on macOS and Ubuntu. Removing whitespace avoids harmless
    # spacing differences around mathematical glyphs while retaining every
    # extracted character in order.
    return "".join(run([pdftotext, "-raw", str(pdf), "-"]).stdout.split())


def verify_source_boundaries() -> None:
    source = TEX.read_text(encoding="utf-8")
    root_status = (ROOT / "STATUS.md").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    dependencies = (ROOT / "DEPENDENCIES.md").read_text(encoding="utf-8")
    proof_map = (ROOT / "PROOF_MAP.md").read_text(encoding="utf-8")
    pipeline_audit = (ROOT / "PIPELINE_AUDIT.md").read_text(encoding="utf-8")
    load_bearing_audit = (ROOT / "LOAD_BEARING_AUDIT.md").read_text(
        encoding="utf-8"
    )
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")

    require(
        ",qquad" not in source,
        "invalid comma before qquad spacing command",
    )
    require(
        "nonzero, its Serre-dual multiplication map from the one-dimensional\n"
        "space" in source,
        "q=10 Serre-dual source dimension is missing",
    )
    require(
        r"\(Q_2=\operatorname{tr}(m^2)\in H^0(L^2)\)" in source,
        "quadratic-invariant notation is missing",
    )

    require(
        r"\begin{candidate}[Rank-three finite image in genus four]" in source,
        "genus-four candidate statement is missing",
    )
    require(
        r"\date{Version 0.1.1-candidate\\15 August 2026}" in source,
        "genus-four candidate version/date is stale",
    )
    require(
        r"\texttt{CANDIDATE}, not as an established theorem" in source,
        "candidate-status disclaimer is missing",
    )
    require(
        "OpenAI Codex (GPT-5.6)" in source
        and "responsible for all\nstatements, proofs, and errors" in source,
        "concise assistance disclosure is missing",
    )
    require(
        "This paper is\nrestricted to genus four and makes no lower-genus assertion"
        in source,
        "lower-genus disclaimer is missing",
    )
    required_imports = (
        "the passage from an MCG-finite rank-three system",
        "the canonical-Deligne and coparabolic convention",
        "the strict endpoint and first-super endpoint estimates",
        "the normalizer boundary-cocycle obstruction",
        "projective finite-index descent, direct Artin devissage",
    )
    require(
        all(fragment in source for fragment in required_imports),
        "imported interface boundary B1--B5 is incomplete",
    )
    require(
        "Rank-three finite image for `g = 4`, all `n ≥ 0` | `CANDIDATE`"
        in root_status,
        "STATUS no longer marks the genus-four extension candidate",
    )
    require(
        "Rank-three finite image for `g = 3` | `OPEN`" in root_status,
        "STATUS no longer preserves the genus-three open boundary",
    )
    require(
        "[Genus-four candidate PDF](output/pdf/rank3_genus4_extension.pdf)"
        in readme
        and "[Genus-four candidate source](manuscript/rank3_genus4_extension.tex)"
        in readme,
        "README genus-four candidate links are missing",
    )
    require(
        "Genus four | **Candidate**" in readme
        and "Genus three | **Open**" in readme,
        "README lower-genus status summary is incomplete",
    )
    require(
        "Rank-three genus-four extension `g = 4` | `CANDIDATE`"
        in dependencies,
        "dependency ledger no longer marks the genus-four extension candidate",
    )
    require(
        "## Separate genus-four candidate" in proof_map
        and "does not certify the proof" in proof_map,
        "proof map no longer separates the genus-four candidate review",
    )
    require(
        "separate\ngenus-four candidate manuscript" in pipeline_audit
        and "Genus three remains open" in pipeline_audit,
        "pipeline audit has a stale lower-genus boundary",
    )
    require(
        "separate\ngenus-four candidate manuscript" in load_bearing_audit
        and "Genus three remains open" in load_bearing_audit
        and "Genus three and four remain a separate method wall"
        not in load_bearing_audit,
        "load-bearing audit has a stale lower-genus boundary",
    )
    require(
        "verify-genus4-candidate:" in makefile
        and "verification/verify_genus4_candidate.py --compile" in makefile,
        "Makefile genus-four candidate gate is missing",
    )
    require(
        "exact finite calculations recorded in\nthis manuscript" in source
        and "version 0.1.5-candidate, 15 August\n2026" in source,
        "public manuscript provenance or finite-calculation boundary is missing",
    )


def verify_artifacts(pdfinfo: str, pdffonts: str, gs: str) -> None:
    hashes = expected_hashes()
    for path in (TEX, PDF):
        relative = str(path.relative_to(ROOT))
        require(relative in hashes, f"checksum entry is missing: {relative}")
        require(sha256(path) == hashes[relative], f"checksum mismatch: {relative}")

    info = run([pdfinfo, str(PDF)]).stdout
    require(
        "Title:           Rank-Three Mapping-Class-Finite Representations in Genus Four: A Candidate Extension"
        in info,
        "genus-four PDF title metadata is missing",
    )
    require("Author:          Robert Sneiderman" in info, "PDF author is missing")
    require(
        "Subject:         New, unrefereed candidate extension" in info,
        "PDF candidate subject is missing",
    )
    require(f"Pages:           {EXPECTED_PAGES}" in info, "wrong PDF page count")
    require("Encrypted:       no" in info, "PDF is encrypted")

    font_lines = run([pdffonts, str(PDF)]).stdout.splitlines()[2:]
    require(font_lines, "no fonts reported")
    for line in font_lines:
        fields = line.split()
        require(
            len(fields) >= 7 and fields[-5] == "yes",
            f"unembedded font: {line}",
        )
    run([gs, "-q", "-dNOPAUSE", "-dBATCH", "-sDEVICE=nullpage", str(PDF)])


def compile_and_compare(latexmk: str, pdftotext: str) -> None:
    with tempfile.TemporaryDirectory(prefix="rank3-genus4-draft-") as temp_name:
        temp_root = Path(temp_name)
        environment = os.environ.copy()
        environment.update(
            {"SOURCE_DATE_EPOCH": "1786838400", "FORCE_SOURCE_DATE": "1"}
        )
        subprocess.run(
            [
                latexmk,
                "-norc",
                "-pdf",
                "-interaction=nonstopmode",
                "-halt-on-error",
                "-file-line-error",
                f"-outdir={temp_root}",
                str(TEX),
            ],
            cwd=ROOT,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        rebuilt = temp_root / PDF.name
        log = temp_root / f"{TEX.stem}.log"
        require(rebuilt.exists(), "fresh genus-four PDF was not produced")
        require(log.exists(), "fresh genus-four log was not produced")
        log_text = log.read_text(encoding="utf-8", errors="replace")
        forbidden_log_markers = (
            "LaTeX Warning:",
            "Package hyperref Warning:",
            "Overfull \\hbox",
            "Underfull \\hbox",
        )
        require(
            not any(marker in log_text for marker in forbidden_log_markers),
            "fresh genus-four build contains a TeX warning or bad box",
        )
        require(
            normalized_pdf_text(rebuilt, pdftotext)
            == normalized_pdf_text(PDF, pdftotext),
            "fresh genus-four build does not match the committed PDF text",
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--compile", action="store_true")
    args = parser.parse_args()

    require(TEX.is_file(), f"missing source: {TEX}")
    require(PDF.is_file(), f"missing PDF: {PDF}")
    verify_source_boundaries()

    pdfinfo = require_tool("pdfinfo")
    pdffonts = require_tool("pdffonts")
    gs = require_tool("gs")
    pdftotext = require_tool("pdftotext")
    verify_artifacts(pdfinfo, pdffonts, gs)

    if args.compile:
        compile_and_compare(require_tool("latexmk"), pdftotext)

    print("GENUS FOUR CANDIDATE CHECKS: PASS (artifact gate, not theorem verification)")


if __name__ == "__main__":
    main()
