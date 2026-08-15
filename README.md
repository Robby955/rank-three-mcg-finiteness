# Rank-three finite-image problem in genus at least five

[![Status: candidate](https://img.shields.io/badge/status-candidate-C27C0E)](STATUS.md)
[![Verify](https://github.com/Robby955/rank-three-mcg-finiteness/actions/workflows/verify.yml/badge.svg)](https://github.com/Robby955/rank-three-mcg-finiteness/actions/workflows/verify.yml)

A focused manuscript and review package for a proposed extension of the
rank-three finite-image range for punctured surface groups.

The manuscript proposes a proof that has not received
independent mathematical review. No claim is made for genus three or four.

## Published foundation

This candidate starts from two papers by Aaron Landesman and Daniel Litt:

- *Canonical representations of surface groups*, **Annals of Mathematics**
  199 (2024), 823–897
  ([published version](https://annals.math.princeton.edu/2024/199-2/p06),
  [arXiv:2205.15352v4](https://arxiv.org/abs/2205.15352v4)). Their Theorem 1.2.1
  proves finite image for mapping-class-finite representations of rank r when
  r < √(g + 1), with arbitrary punctures.
- *Geometric local systems on very general curves and isomonodromy*,
  **Journal of the American Mathematical Society** 37 (2024), 683–729
  ([published version](https://doi.org/10.1090/jams/1038),
  [arXiv:2202.00039v3](https://arxiv.org/abs/2202.00039v3)). The candidate uses
  its isomonodromy and Harder–Narasimhan estimates in the specialized
  rank-three analysis.

The proposed extension to rank three in genus g ≥ 5 is new and unrefereed;
it is not a theorem claimed by Landesman and Litt.

The current public review release is `v0.1.4-candidate`. This branch prepares
`v0.1.5-candidate`, which keeps the theorem, hypotheses, and proof unchanged
while streamlining the public review package. Earlier releases remain
available as fixed historical review copies.

## Additional general-rank candidate

A separate six-page note isolates a proposed extension of the published
general-rank bound to the square endpoint `r² = g + 1`, equivalently
`g ≥ r² − 1`. This endpoint statement remains `CANDIDATE`. The published
strict range is due to Landesman--Litt. The note does not prove the proposed
sharper range `g ≥ r² − 4`, and it does not change the open status of the
rank-three genus-three and genus-four cases.

## Result under review

For g ≥ 5 and n ≥ 0, consider a complex rank-three representation of the
genus-g surface group with n punctures. The manuscript argues that if its
conjugacy class has finite orbit under the mapping class group, then the
representation has finite image.

Landesman and Litt prove finite image when r < √(g + 1). In rank three, their
published theorem starts at g ≥ 9; the candidate argument treats the remaining
genera 8, 7, 6, and 5.

## Read the argument

| Document | Purpose |
|---|---|
| [Manuscript PDF](output/pdf/rank3_genus5_reader-v0.1.5-candidate.pdf) | Prepared version-specific review copy |
| [TeX source](manuscript/rank3_genus5_reader.tex) | Canonical source corresponding to the PDF |
| [Square-endpoint note PDF](output/pdf/general_rank_square_endpoint.pdf) | Standalone general-rank candidate note |
| [Square-endpoint note source](manuscript/general_rank_square_endpoint.tex) | Canonical source for the standalone note |
| [Proof map](PROOF_MAP.md) | Suggested specialist review order |
| [Pipeline audit](PIPELINE_AUDIT.md) | Exact substitutions in Landesman–Litt Sections 8.2–8.7 |
| [Proof-interface notes](LOAD_BEARING_AUDIT.md) | Normalizer cocycle, fixed part, and Artin propagation expanded in order |
| [Focused review request](REVIEW_REQUEST.md) | Four questions for a specialist reader |
| [Dependency ledger](DEPENDENCIES.md) | Published inputs and new interfaces |
| [Status](STATUS.md) | Exact claim boundaries, including genera three and four |
| [Provenance](PROVENANCE.md) | Source checkpoint and artifact hashes |
| [Citation metadata](CITATION.cff) | Versioned citation for the rank-three candidate |

## Main review points

The main new ingredients are:

1. the normalizer boundary-cocycle obstruction, including full boundary-map
   injectivity in its two genus-five applications;
2. the zero-weight genus-five q = 9 closed-family boundary descent;
3. the rank-one fixed-part construction on the full finite cover;
4. the propagation from adjoint vanishing to arbitrary rank-three
   representations.

Each appears in the manuscript itself or is tied to a published input.

The manuscript also includes separate q = 9 Pfaffian/spectral-projector and
canonical-Deligne no-pole reconstructions. Neither is used in the main
elimination.

## Range and status

| Genus | Status | Basis |
|---|---|---|
| `g ≥ 9` | **Published** | Landesman–Litt |
| `5 ≤ g ≤ 8` | **Candidate** | Manuscript in this repository |
| `g = 3, 4` | **Open** | Not claimed; the present endpoint argument loses rank |


## Verification

With TeX Live, Poppler, and Ghostscript installed:

```sh
make verify-release
```

The release check verifies both candidate notes. It enforces source and PDF
hashes, claim-status language, page counts, encryption state, embedded fonts,
Ghostscript preflight, clean fresh builds, extracted-text equality, and a
120-DPI pixel comparison for the rank-three manuscript. GitHub Actions runs
the portable rank-three gate and the standalone square-endpoint gate on every
push and pull request.

To check only the standalone note, run:

```sh
make verify-square-endpoint
```

The separate finite-mathematics checks are:

```sh
make verify-math
```

They enumerate the displayed genus-six and genus-five HN arithmetic,
reconstruct the q = 10 local jet matrices, and check the q = 9 fibre algebra
with exact rational and polynomial arithmetic. Their precise scope is recorded
in [`verification/math`](verification/math).

## Citation and licensing

The current public review release is
[`v0.1.4-candidate`](https://github.com/Robby955/rank-three-mcg-finiteness/releases/tag/v0.1.4-candidate).
This branch prepares `v0.1.5-candidate`; earlier versioned review copies remain
archived and unchanged on the
[Releases page](https://github.com/Robby955/rank-three-mcg-finiteness/releases).
The root [CITATION.cff](CITATION.cff) describes the rank-three candidate.

The standalone note may be cited as:

> Robert Sneiderman, *The General-Rank Square Endpoint for MCG-Finite
> Surface-Group Representations*, version 0.1.0-candidate, 2026.

The manuscript and documentation are licensed under CC BY 4.0. Verification
software and repository infrastructure are licensed under the MIT License.
See [LICENSE](LICENSE) for the exact path mapping and terms.

## Scope

This repository contains the rank-three manuscript, the standalone
general-rank square-endpoint note, and the review materials needed to evaluate
them. Exploratory lower-genus work and internal working material are outside
its scope.
