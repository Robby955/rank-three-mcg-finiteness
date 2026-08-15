#!/usr/bin/env python3
"""Verify the standalone general-rank square-endpoint review packet.

This is an artifact and boundary gate.  It does not certify the mathematics.
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
TEX = ROOT / "manuscript/general_rank_square_endpoint.tex"
PDF = ROOT / "output/pdf/general_rank_square_endpoint.pdf"
MAIN_TEX = ROOT / "manuscript/rank3_genus5_reader.tex"
CHECKSUMS = ROOT / "CHECKSUMS.sha256"
EXPECTED_PAGES = 6


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def run(
    command: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        env=env,
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
    return " ".join(run([pdftotext, "-layout", str(pdf), "-"]).stdout.split())


def verify_source_boundaries() -> None:
    source = TEX.read_text(encoding="utf-8")
    main_source = MAIN_TEX.read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    status = (ROOT / "STATUS.md").read_text(encoding="utf-8")
    dependencies = (ROOT / "DEPENDENCIES.md").read_text(encoding="utf-8")
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")

    theorem_statement = (
        r"Let $g\ge3$, $n\ge0$, and $r^2\le g+1$.  Every MCG-finite "
        "representation"
    )
    require(
        theorem_statement in source and theorem_statement in main_source,
        "standalone and full-manuscript theorem statements diverge",
    )
    require(
        r"\label{thm:square-endpoint}" in source
        and r"\label{thm:square-endpoint}" in main_source,
        "square-endpoint theorem label changed",
    )
    require(
        "This is a new, unrefereed\ncandidate proof, not an established theorem."
        in source,
        "candidate disclaimer is missing",
    )
    require(
        "OpenAI Codex (GPT-5.6)" in source
        and "responsible for all\nstatements, proofs, and errors" in source,
        "concise assistance disclosure is missing",
    )
    require(
        r"The statement $g\ge r^2-1$ is"
        in source
        and r"$g\ge r^2-4$" in source,
        "general-rank claim boundary is incomplete",
    )
    require(
        "makes no new genus-three or genus-four rank-three\nclaim" in source,
        "lower-genus disclaimer is missing",
    )
    require(
        r"\cite[Theorem~1.2.13]{LLGeo}" in source
        and "earlier numbering Theorem~1.2.12" in source,
        "isomonodromy theorem numbering note is missing",
    )

    equality_markers = (
        "this forces $c=1$",
        "it follows that $N^t=0$",
        "Thus $S=0$",
        r"\mu(A)=\mu(F)",
        "a contradiction",
    )
    require(
        all(marker in source for marker in equality_markers),
        "strict equality-case proof is incomplete",
    )
    artin_markers = (
        r"U_i\otimes\pi^*W_i",
        r"uw\le g",
        r"uw\ge2u(g-u+1)\ge2g>g",
        r"\rk_A\Vcal\le g",
    )
    require(
        all(marker in source for marker in artin_markers),
        "rank-g Artin endpoint is incomplete",
    )
    endpoint_markers = (
        r"r^2-1=g",
        r"n_i d_i\le ab",
        r"\frac{3g-1}{2}",
        "Dualizing embeds the dual quotient as a stable subrepresentation",
        "Maschke semisimplicity then splits the extension",
        "The proof does not use a Spin lift",
    )
    require(
        all(marker in source for marker in endpoint_markers),
        "downstream endpoint audit is incomplete",
    )

    require(
        "Finite image for MCG-finite rank `r` when `r² ≤ g + 1` | `CANDIDATE`"
        in status
        and "Proposed sharper range `g ≥ r² − 4` | `OPEN`" in status,
        "STATUS no longer marks the square endpoint candidate",
    )
    require(
        "General-rank square endpoint `g ≥ r² − 1` | `CANDIDATE`"
        in dependencies,
        "dependency ledger no longer marks the square endpoint candidate",
    )
    require(
        "[Square-endpoint note PDF](output/pdf/general_rank_square_endpoint.pdf)"
        in readme
        and "[Square-endpoint note source](manuscript/general_rank_square_endpoint.tex)"
        in readme,
        "README standalone packet links are missing",
    )
    require(
        "verify-square-endpoint:" in makefile
        and "verification/verify_square_endpoint_packet.py --compile" in makefile,
        "Makefile square-endpoint gate is missing",
    )


def verify_finite_regression() -> None:
    # Finite shadows of the symbolic inequalities, not theorem verification.
    for g in range(3, 1001):
        for u in range(1, g + 1):
            bound = 2 * g - 2 if u == 1 else 2 * g - 2 * u + 2
            for w in range(1, g // u + 1):
                require(w < bound, f"Artin endpoint shadow failed: g={g}, u={u}, w={w}")

    for r in range(2, 100001):
        g = r * r - 1
        upper = (g + 1) / 4
        lower = (3 * g - 1) / 2
        require(lower > upper, f"extension margin failed: r={r}")


def verify_artifacts(pdfinfo: str, pdffonts: str, gs: str) -> None:
    hashes = expected_hashes()
    for path in (TEX, PDF):
        relative = str(path.relative_to(ROOT))
        require(relative in hashes, f"checksum entry is missing: {relative}")
        require(sha256(path) == hashes[relative], f"checksum mismatch: {relative}")

    info = run([pdfinfo, str(PDF)]).stdout
    require(
        "Title:           The General-Rank Square Endpoint for MCG-Finite Surface-Group Representations"
        in info,
        "square-endpoint PDF title metadata is missing",
    )
    require("Author:          Robert Sneiderman" in info, "PDF author is missing")
    require(
        "Subject:         New, unrefereed candidate note" in info,
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
    with tempfile.TemporaryDirectory(prefix="square-endpoint-packet-") as temp_name:
        temp_root = Path(temp_name)
        environment = os.environ.copy()
        environment.update(
            {"SOURCE_DATE_EPOCH": "1786320000", "FORCE_SOURCE_DATE": "1"}
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
        require(rebuilt.exists(), "fresh square-endpoint PDF was not produced")
        require(log.exists(), "fresh square-endpoint log was not produced")
        log_text = log.read_text(encoding="utf-8", errors="replace")
        forbidden_log_markers = (
            "LaTeX Warning:",
            "Package hyperref Warning:",
            "Overfull \\hbox",
            "Underfull \\hbox",
        )
        require(
            not any(marker in log_text for marker in forbidden_log_markers),
            "fresh square-endpoint build contains a TeX warning or bad box",
        )
        require(
            normalized_pdf_text(rebuilt, pdftotext)
            == normalized_pdf_text(PDF, pdftotext),
            "fresh square-endpoint build does not match the committed PDF text",
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--compile", action="store_true")
    args = parser.parse_args()

    for path in (TEX, PDF, MAIN_TEX, CHECKSUMS):
        require(path.is_file(), f"missing artifact: {path}")

    verify_source_boundaries()
    verify_finite_regression()

    pdfinfo = require_tool("pdfinfo")
    pdffonts = require_tool("pdffonts")
    gs = require_tool("gs")
    pdftotext = require_tool("pdftotext")
    verify_artifacts(pdfinfo, pdffonts, gs)
    if args.compile:
        compile_and_compare(require_tool("latexmk"), pdftotext)

    print("SQUARE-ENDPOINT PACKET CHECKS: PASS (artifact gate, not theorem verification)")


if __name__ == "__main__":
    main()
