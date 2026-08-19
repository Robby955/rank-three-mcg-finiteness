# Rank-three finite-image candidates in genus at least four

[![Status: candidate](https://img.shields.io/badge/status-candidate-C27C0E)](STATUS.md)
[![Verify](https://github.com/Robby955/rank-three-mcg-finiteness/actions/workflows/verify.yml/badge.svg)](https://github.com/Robby955/rank-three-mcg-finiteness/actions/workflows/verify.yml)

A public manuscript and review package for proposed extensions of the
rank-three finite-image range for punctured surface groups.

The genus-at-least-five manuscript and the separate conditional genus-four
extension are new and have not received independent mathematical review.
Genus three remains open.

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

The proposed rank-three extensions in genus at least five and genus four are
new and unrefereed; neither is a theorem claimed by Landesman and Litt.

The current tagged public review release is `v0.1.4-candidate`. The repository
contains the repaired `v0.1.5-candidate` genus-at-least-five package together
with the standalone square-endpoint and genus-four candidate notes. Earlier
releases remain available as fixed historical review copies.

## Additional general-rank candidate

A separate six-page note isolates a proposed extension of the published
general-rank bound to the square endpoint `r² = g + 1`, equivalently
`g ≥ r² − 1`. This endpoint statement remains `CANDIDATE`. The published
strict range is due to Landesman--Litt. The note does not prove the proposed
sharper range `g ≥ r² − 4`, and it does not change the open status of the
rank-three genus-three case or the conditional candidate status of the
separate genus-four extension.

## Genus-at-least-five candidate

For g ≥ 5 and n ≥ 0, consider a complex rank-three representation of the
genus-g surface group with n punctures. The manuscript argues that if its
conjugacy class has finite orbit under the mapping class group, then the
representation has finite image.

Landesman and Litt prove finite image when r < √(g + 1). In rank three, their
published theorem starts at g ≥ 9; the candidate argument treats the remaining
genera 8, 7, 6, and 5.

## Genus-four candidate extension

A separate 30-page manuscript proposes the same finite-image conclusion for
rank three in genus four, with arbitrary punctures. Its statement is
explicitly conditional on the five imported interface groups B1--B5 from the
companion genus-at-least-five candidate. The proposed genus-four argument
addresses the dense rank-eight, rank-five orthogonal, and rank-six monomial
coefficient cases and the remaining propagation equality.

This extension is `CANDIDATE`, not an established theorem. The manuscript
lists its imported assumptions and the geometric steps requiring independent
specialist reconstruction. It makes no genus-three claim.

## Read the argument

| Document | Purpose |
|---|---|
| [Genus-at-least-five manuscript PDF](output/pdf/rank3_genus5_reader-v0.1.5-candidate.pdf) | Prepared version-specific review copy |
| [Genus-at-least-five source](manuscript/rank3_genus5_reader.tex) | Canonical source corresponding to the PDF |
| [Genus-four candidate PDF](output/pdf/rank3_genus4_extension.pdf) | Standalone conditional candidate extension |
| [Genus-four candidate source](manuscript/rank3_genus4_extension.tex) | Canonical source for the genus-four PDF |
| [Square-endpoint note PDF](output/pdf/general_rank_square_endpoint.pdf) | Standalone general-rank candidate note |
| [Square-endpoint note source](manuscript/general_rank_square_endpoint.tex) | Canonical source for the standalone note |
| [Proof map](PROOF_MAP.md) | Suggested specialist review order |
| [Pipeline audit](PIPELINE_AUDIT.md) | Exact substitutions in Landesman–Litt Sections 8.2–8.7 |
| [Proof-interface notes](LOAD_BEARING_AUDIT.md) | Normalizer cocycle, fixed part, and Artin propagation expanded in order |
| [Focused review request](REVIEW_REQUEST.md) | Four questions on the genus-at-least-five manuscript |
| [Dependency ledger](DEPENDENCIES.md) | Published inputs and new interfaces |
| [Status](STATUS.md) | Exact claim boundaries, including genera three and four |
| [Provenance](PROVENANCE.md) | Source checkpoint and artifact hashes |
| [Citation metadata](CITATION.cff) | Versioned citation for the rank-three candidate |

## Main review points

### Genus at least five

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

### Genus four

The genus-four review should begin with the B1--B5 dependency boundary and
then check the dense rank-eight elimination, the two proper projective-closure
coefficients, and the scalar propagation equality. Finite enumeration and a
successful TeX build do not certify those geometric arguments.

## Range and status

| Genus | Status | Basis |
|---|---|---|
| `g ≥ 9` | **Published** | Landesman–Litt |
| `5 ≤ g ≤ 8` | **Candidate** | Manuscript in this repository |
| Genus four | **Candidate** | Separate conditional manuscript in this repository |
| Genus three | **Open** | Substantial reductions exist, but explicit residual walls remain |


## Verification

With TeX Live, Poppler, and Ghostscript installed:

```sh
make verify-release
```

The release check verifies all three candidate packages. It enforces source
and PDF hashes, claim-status language, page counts, encryption state, embedded fonts,
Ghostscript preflight, clean fresh builds, extracted-text equality, and a
120-DPI pixel comparison for the rank-three manuscript. GitHub Actions runs
the portable genus-at-least-five gate and the standalone square-endpoint and
genus-four gates on every push and pull request.

To check either standalone note, run:

```sh
make verify-square-endpoint
make verify-genus4-candidate
```

The separate finite-mathematics checks are:

```sh
make verify-math
```

They enumerate the displayed genus-six and genus-five HN arithmetic and check
the q = 9 fibre algebra with exact rational and polynomial arithmetic. They
also retain a non-load-bearing replay of the former q = 10 local jet
calculation. Their precise scope is recorded in
[`verification/math`](verification/math).

## Citation and licensing

The current public review release is
[`v0.1.4-candidate`](https://github.com/Robby955/rank-three-mcg-finiteness/releases/tag/v0.1.4-candidate).
The repository contains the repaired, untagged `v0.1.5-candidate` package;
earlier versioned review copies remain archived and unchanged on the
[Releases page](https://github.com/Robby955/rank-three-mcg-finiteness/releases).
The root [CITATION.cff](CITATION.cff) describes the rank-three candidate.

The standalone note may be cited as:

> Robert Sneiderman, *The General-Rank Square Endpoint for MCG-Finite
> Surface-Group Representations*, version 0.1.0-candidate, 2026.

The genus-four extension may be cited as:

> Robert Sneiderman, *Rank-Three Mapping-Class-Finite Representations in
> Genus Four: A Candidate Extension*, version 0.1.1-candidate, 2026.

The manuscript and documentation are licensed under CC BY 4.0. Verification
software and repository infrastructure are licensed under the MIT License.
See [LICENSE](LICENSE) for the exact path mapping and terms.

## Scope

This repository contains the genus-at-least-five rank-three manuscript, the
standalone genus-four and general-rank square-endpoint candidate notes, and the
review materials needed to evaluate them. Genus-three working material and
exploratory notes are outside its scope.
