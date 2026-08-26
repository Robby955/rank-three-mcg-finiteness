#!/usr/bin/env python3
"""Verify the focused rank-three candidate-manuscript release."""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "manuscript/rank3_genus5_reader.tex"
PDF = ROOT / "output/pdf/rank3_genus5_reader-v0.1.5-candidate.pdf"
LICENSE = ROOT / "LICENSE"
CITATION = ROOT / "CITATION.cff"
REVIEW_REQUEST = ROOT / "REVIEW_REQUEST.md"
EXPECTED_PAGES = 35
EXPECTED_HASHES = {
    TEX: "4a0c3710810bce4f8ac32e91ad7e1f42af55edef8d9eeb3f465d732061a09505",
    PDF: "a51aa0ca10c138f186f24d72c8df1c62b507f7dce30558114c7ca71baf492faf",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


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


def pdf_text(pdf: Path, pdftotext: str) -> str:
    output = run([pdftotext, "-layout", str(pdf), "-"]).stdout
    # TeX and Poppler versions can choose different line wrapping while
    # preserving the same extracted mathematical text. Collapse whitespace so
    # hosted verification checks content rather than platform-specific layout.
    return " ".join(output.split())


def verify_claim_boundaries() -> None:
    source = TEX.read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    status = (ROOT / "STATUS.md").read_text(encoding="utf-8")
    license_text = LICENSE.read_text(encoding="utf-8")
    citation = CITATION.read_text(encoding="utf-8")
    review_request = REVIEW_REQUEST.read_text(encoding="utf-8")
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")
    math_readme = (ROOT / "verification/math/README.md").read_text(encoding="utf-8")
    require(r"\author{Robert Sneiderman}" in source, "manuscript author is missing")
    require(
        r"Version 0.1.5-candidate\\19 August 2026" in source,
        "manuscript candidate version is missing",
    )

    require(
        "unrefereed candidate proof" in source,
        "manuscript candidate status is missing",
    )
    require(
        "OpenAI Codex (GPT-5.6)" in source
        and "responsible for all\nstatements, proofs, and errors" in source,
        "concise assistance disclosure is missing",
    )
    require(
        r"Let $g\ge5$ and $n\ge0$" in source,
        "main theorem boundary is not g >= 5",
    )
    require(
        "No claim is\nmade in genus three or four" in source,
        "genus-three/four disclaimer is missing",
    )
    require(
        "quotient normalizer has dimension one" in source,
        "q=9 orbit classification is missing",
    )
    require(
        "remaining nonzero orbit types are the semisimple type $(2,1)$" in source,
        "q=9 semisimple case is missing",
    )
    require(
        r"\begin{proposition}[Normalizer boundary-cocycle obstruction]" in source
        and r"\label{prop:normalizer-boundary}" in source
        and r"\partial[x,y]" in source
        and r"[x,y]=\lambda(x)y-\lambda(y)x" in source,
        "normalizer boundary-cocycle proposition is missing",
    )
    require(
        "This eliminates the\nzero-weight $q=9$ branch" in source
        and "Hence the final high-HN branch is impossible" in source,
        "normalizer boundary-cocycle applications are missing",
    )
    require(
        r"y\in\{9,10\}" in source
        and r"q+y\ge20" in source
        and r"q+y\ge16" in source
        and r"\text{allowed }q" in source,
        "expanded genus-six/five HN tables are missing",
    )
    require(
        r"s_*\circ e\circ A=0" in source
        and r"\operatorname{rank}A\le1" in source
        and "generically rank-four trivial subbundle" in source
        and "without identifying the divisor of $L$ with $2p$" in source
        and "can be supported only at the sole" not in source,
        "repaired q=10 normalizer-naturality proof is missing",
    )
    require(
        r"\paragraph{Published propagation map.}" in source
        and r"\cite[Lemma 8.5.1]{LLCan}" in source
        and r"\cite[Lemma 8.5.2]{LLCan}" in source
        and r"\cite[Section 8.7]{LLCan}" in source,
        "published propagation dependency map is missing",
    )
    require(
        r"\paragraph{Load-bearing dependency roadmap.}" in source
        and r"\label{rem:general-fibre}" in source
        and r"\label{rem:stability-bookkeeping}" in source
        and r"\degp(P)=(y-8)+(S-\beta)<0" in source,
        "v0.1.4 referee-proofing blocks are missing",
    )
    require(
        r"\cite[Proposition 4.2.2]{LLCan}" in source
        and "real rank-one system" in source
        and "two conjugate\nHodge types" in source,
        "complex fixed-part rank-one route is missing",
    )
    require(
        r"H^1(\Ocal_C)=0" not in source
        and "The morphism-of-extensions identity\nsays that the composite" in source,
        "universal-extension composite is misstated",
    )
    require(
        "status-candidate" in readme
        and "have not received independent mathematical review" in readme
        and "Genus three remains open" in readme
        and "Aaron Landesman and Daniel Litt" in readme
        and "https://annals.math.princeton.edu/2024/199-2/p06" in readme
        and "https://arxiv.org/abs/2205.15352v4" in readme
        and "https://doi.org/10.1090/jams/1038" in readme
        and "https://arxiv.org/abs/2202.00039v3" in readme
        and "current tagged public review release" in readme
        and "current tagged public review release is `v0.1.5-candidate`" in readme
        and "v0.1.5-candidate" in readme
        and "releases/tag/v0.1.5-candidate" in readme
        and "archived and unchanged" in readme
        and "rank3_genus5_reader-v0.1.5-candidate.pdf" in readme
        and "rank3_genus4_extension.pdf" in readme,
        "README claim boundary is missing",
    )
    require(
        "Rank-three finite image for `g = 4`, all `n ≥ 0` | `CANDIDATE`"
        in status
        and "Rank-three finite image for `g = 3` | `OPEN`" in status,
        "STATUS loses the genus-four candidate or genus-three open boundary",
    )
    require(
        "Copyright (c) 2026 Robert Sneiderman" in license_text
        and "Creative Commons Attribution 4.0 International" in license_text
        and "MIT License" in license_text,
        "dual-license terms are incomplete",
    )
    require(
        'version: "0.1.5-candidate"' in citation
        and "family-names: Sneiderman" in citation
        and "given-names: Robert" in citation
        and 'date-released: "2026-08-19"' in citation
        and not any(line.startswith("type:") for line in citation.splitlines()),
        "candidate citation metadata is incomplete",
    )
    require(
        "genus-at-least-five `CANDIDATE` manuscript" in review_request
        and "makes no genus-three or genus-four claim" in review_request
        and "separate conditional genus-four candidate" in review_request,
        "focused review request loses the claim boundary",
    )
    require(
        (ROOT / "verification/math/verify_q10_jet.py").is_file()
        and "verification/math/verify_q10_jet.py" in makefile
        and "`verify_q10_jet.py`" in math_readme,
        "non-load-bearing q=10 diagnostic is not wired into the release",
    )

    forbidden_markdown = ("$", "```math", r"\(", r"\)", r"\[", r"\]")
    for markdown in sorted(ROOT.rglob("*.md")):
        if any(part.startswith(".") or part == "build" for part in markdown.parts):
            continue
        text = markdown.read_text(encoding="utf-8")
        for fragment in forbidden_markdown:
            require(
                fragment not in text,
                f"unsupported GitHub math syntax {fragment!r}: {markdown.relative_to(ROOT)}",
            )
        latex_command = re.search(r"\\[A-Za-z]+", text)
        require(
            latex_command is None,
            (
                "unsupported GitHub LaTeX command "
                f"{latex_command.group(0)!r}: {markdown.relative_to(ROOT)}"
                if latex_command
                else ""
            ),
        )


def verify_pdf(pdfinfo: str, pdffonts: str, gs: str) -> None:
    info = run([pdfinfo, str(PDF)]).stdout
    require(
        "Title:           A Candidate Proof of Finite Image for Rank-Three Surface-Group Representations in Genus at Least Five"
        in info,
        "PDF title metadata is missing",
    )
    require(
        "Author:          Robert Sneiderman" in info, "PDF author metadata is missing"
    )
    require(
        "Subject:         Unrefereed candidate manuscript" in info,
        "PDF candidate-status metadata is missing",
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


def render_pages(pdf: Path, prefix: Path, pdftoppm: str) -> list[Path]:
    run([pdftoppm, "-r", "120", str(pdf), str(prefix)])
    pages = sorted(prefix.parent.glob(f"{prefix.name}-*.ppm"))
    require(
        len(pages) == EXPECTED_PAGES,
        f"rendered {len(pages)} pages, expected {EXPECTED_PAGES}",
    )
    return pages


def compile_and_compare(
    *,
    pdflatex: str,
    pdfinfo: str,
    pdftotext: str,
    pdftoppm: str | None,
    compare_text: bool,
) -> None:
    with tempfile.TemporaryDirectory(prefix="rank3-release-") as temp_name:
        temp_root = Path(temp_name)
        temp_tex = temp_root / TEX.name
        shutil.copy2(TEX, temp_tex)

        environment = os.environ.copy()
        environment.update(
            {"SOURCE_DATE_EPOCH": "1787097600", "FORCE_SOURCE_DATE": "1"}
        )
        command = [
            pdflatex,
            "-interaction=nonstopmode",
            "-halt-on-error",
            "-file-line-error",
            temp_tex.name,
        ]
        for _ in range(3):
            run(command, cwd=temp_root, env=environment)

        log = temp_tex.with_suffix(".log").read_text(encoding="utf-8", errors="replace")
        forbidden = (
            "LaTeX Warning:",
            "Package rerunfilecheck Warning:",
            "Overfull \\hbox",
            "Overfull \\vbox",
            "Undefined control sequence",
        )
        for fragment in forbidden:
            require(fragment not in log, f"fresh build contains {fragment!r}")

        built_pdf = temp_tex.with_suffix(".pdf")
        info = run([pdfinfo, str(built_pdf)]).stdout
        require(
            f"Pages:           {EXPECTED_PAGES}" in info,
            "fresh build has the wrong page count",
        )
        if compare_text:
            require(
                pdf_text(built_pdf, pdftotext) == pdf_text(PDF, pdftotext),
                "fresh build text differs from the committed PDF",
            )

        if pdftoppm is not None:
            committed_pages = render_pages(PDF, temp_root / "committed", pdftoppm)
            built_pages = render_pages(built_pdf, temp_root / "built", pdftoppm)
            for index, (committed, built) in enumerate(
                zip(committed_pages, built_pages, strict=True), start=1
            ):
                require(
                    committed.read_bytes() == built.read_bytes(),
                    f"fresh build differs visually on page {index}",
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--compile", action="store_true", help="run a fresh TeX build")
    parser.add_argument(
        "--pixels",
        action="store_true",
        help="compare fresh and committed pages at 120 DPI; implies --compile",
    )
    parser.add_argument(
        "--portable",
        action="store_true",
        help="skip cross-TeX-version text equality; requires a clean release build",
    )
    args = parser.parse_args()
    require(
        not (args.portable and args.pixels),
        "--portable and --pixels are mutually exclusive",
    )

    for artifact, expected_hash in EXPECTED_HASHES.items():
        require(artifact.is_file(), f"missing artifact: {artifact.relative_to(ROOT)}")
        require(
            sha256(artifact) == expected_hash,
            f"checksum mismatch: {artifact.relative_to(ROOT)}",
        )

    verify_claim_boundaries()
    pdfinfo = require_tool("pdfinfo")
    pdffonts = require_tool("pdffonts")
    pdftotext = require_tool("pdftotext")
    gs = require_tool("gs")
    verify_pdf(pdfinfo, pdffonts, gs)

    if args.compile or args.pixels:
        pdflatex = require_tool("pdflatex")
        pdftoppm = require_tool("pdftoppm") if args.pixels else None
        compile_and_compare(
            pdflatex=pdflatex,
            pdfinfo=pdfinfo,
            pdftotext=pdftotext,
            pdftoppm=pdftoppm,
            compare_text=not args.portable,
        )

    run(["git", "diff", "--check"], cwd=ROOT)
    print("ALL FOCUSED RELEASE CHECKS PASS")


if __name__ == "__main__":
    main()
