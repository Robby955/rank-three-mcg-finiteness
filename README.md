# Mapping-class-finite representations and Lean proofs

This project studies complex representations of surface groups whose conjugacy
classes have finite mapping class group orbits. It contains Lean 4 proofs of
normalizer obstructions and curve cohomology, together with candidate
manuscripts on finite-image bounds.

## Proved in Lean

### A dimension obstruction in sl₃

Let F be a field of characteristic zero and m a nonzero element of sl₃(F).
Write N(m) for the Lie normalizer of the line Fm, and define its character
by [x,m] = λ(x)m. If a subspace U of N(m)/Fm satisfies

```text
[x,y] = λ(x)y − λ(y)x    for all x,y in U,
```

then **dim_F U ≤ 2**. In particular, the boundary law excludes a
three-dimensional subspace of the normalizer quotient.

The proof covers every nonzero traceless 3×3 matrix. It includes the explicit
semisimple representative diag(1,1,−2), the minimal-nilpotent representative
E₁₂, their quotient brackets, and the reduction over arbitrary
characteristic-zero fields.
[Theorem and proof](lean/normalizer-core/Normalizer/ActualNormalizerQuotient.lean#L91).

The preceding cocycle calculation proves
∂[x,y] = λ(x)∂y − λ(y)∂x. When ∂ is injective, this gives the displayed
bracket identity and hence the obstruction.
[Boundary law](lean/normalizer-core/Normalizer/Boundary.lean).

### Affine vanishing and finite-dimensional curve cohomology

The package also formalizes the following results in mathlib's sheaf-cohomology
framework. These are supporting results from algebraic geometry.

| Hypotheses | Proved conclusion | Lean source |
|---|---|---|
| R any commutative ring, M any R-module | H¹(Spec R, M̃) = 0 | [Affine vanishing](lean/normalizer-core/Normalizer/AffineH1Vanishing.lean#L43) |
| A finite morphism X → ℙ¹_k, over any field k | H¹(X,O_X) is finite-dimensional over k | [Finite-map theorem](lean/normalizer-core/Normalizer/FiniteMapH1.lean#L115) |
| X a proper normal integral curve over k | Construction of a finite map X → ℙ¹_k, and finiteness of H¹(X,O_X) | [Normal curves](lean/normalizer-core/Normalizer/CurveMapExistence.lean#L206) |
| X a proper integral curve, normal away from one specified point | The same conclusions, allowing a singularity at that point | [Singular curve case](lean/normalizer-core/Normalizer/CurveMapSingular.lean#L64) |

Further proofs construct top exterior sheaves and their stalk comparisons,
prove nonzeroness of determinant sections from generic independence, and
construct the zero scheme and sheaf exact sequence of a nonzero line-bundle
section. [Proof guide](lean/normalizer-core/README.md) ·
[Theorem correspondence](lean/normalizer-core/CORRESPONDENCE.md).

## Check the proofs

The public package contains **875 named theorems and 84 examples**. Its build
and axiom audit passed [GitHub Actions](https://github.com/Robby955/rank-three-mcg-finiteness/actions/runs/34649596032).
Every one of its 1,230 named declarations is audited; the only axioms used are
`propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `admit`,
or custom axioms.

With [elan](https://github.com/leanprover/elan#installation), Git and Python 3.10+
installed, run:

```sh
cd lean/normalizer-core
lake exe cache get
python3 scripts/verify.py
python3 scripts/check_correspondence.py
```

Lean and mathlib are pinned in the package. The verifier builds the proofs and
examples, runs `#print axioms` for every named declaration, and saves the
output in `receipts/`. [Verification details](lean/normalizer-core/VERIFICATION.md).

## The representation problem

For a genus-g surface with n punctures, what is the smallest rank of an
infinite-image complex representation with finite mapping class group orbit?
This is [Litt's Problem 10](https://www.problemsilike.com/10).

Aaron Landesman and Daniel Litt proved finite image when r < √(g + 1),
for arbitrary punctures. In rank three this gives g ≥ 9. The candidate
manuscripts below propose extending the bound to the square endpoint in
general rank and to genera 5–8 in rank three, with a separate conditional
argument for genus four.

[![Manuscript status: candidate](https://img.shields.io/badge/status-candidate-C27C0E)](STATUS.md)

| Proposed range | Status | Qualification |
|---|---|---|
| General rank, r² ≤ g + 1 | **Candidate** | Equality endpoint beyond the published strict bound |
| Rank three, 5 ≤ g ≤ 8 | **Candidate** | Full geometric and representation arguments remain to be established |
| Genus four | **Candidate** | Rank-three extension conditional on B1–B5 |
| Genus three | **Open** | No finite-image theorem claimed |
| General rank, g ≥ r² − 4 | **Open** | No theorem claimed |

The complete candidate representation theorems are not formalized in Lean.
The remaining steps include the determinant degree argument, the geometric
bound h⁰(E/M) ≤ 4, and the representation-theoretic and finiteness arguments.
[Roadmap](PUBLICATION_ROADMAP.md) · [Detailed status](STATUS.md).

## Manuscripts and references

| Manuscript | PDF | Source |
|---|---|---|
| Rank three, genus at least five | [Genus-five PDF](output/pdf/rank3_genus5_reader-v0.1.6-candidate.pdf) | [Genus-five source](manuscript/rank3_genus5_reader.tex) |
| General-rank square endpoint | [Square-endpoint note PDF](output/pdf/general_rank_square_endpoint.pdf) | [Square-endpoint note source](manuscript/general_rank_square_endpoint.tex) |
| Conditional genus-four extension | [Genus-four candidate PDF](output/pdf/rank3_genus4_extension.pdf) | [Genus-four candidate source](manuscript/rank3_genus4_extension.tex) |

The manuscripts are unrefereed. Their dependency and review notes are in
[LOAD_BEARING_AUDIT.md](LOAD_BEARING_AUDIT.md), [PROOF_MAP.md](PROOF_MAP.md),
and [DEPENDENCIES.md](DEPENDENCIES.md).

The published foundation is:

- Landesman–Litt, *Canonical representations of surface groups*,
  Annals of Mathematics 199 (2024), 823–897.
  [Published paper](https://annals.math.princeton.edu/2024/199-2/p06) ·
  [arXiv](https://arxiv.org/abs/2205.15352v4).
- Landesman–Litt, *Geometric local systems on very general curves and
  isomonodromy*, JAMS 37 (2024), 683–729.
  [Published paper](https://doi.org/10.1090/jams/1038) ·
  [arXiv](https://arxiv.org/abs/2202.00039v3).

The [v0.1.5-candidate release](https://github.com/Robby955/rank-three-mcg-finiteness/releases/tag/v0.1.5-candidate)
is an August 2026 manuscript snapshot and predates the Lean package. The
repository contains the later v0.1.6-candidate genus-five manuscript and the
Lean sources described above. Release tags preserve their original files.

For manuscript reproduction, `make verify-release` checks the PDFs and
sources; `make verify-math` checks the finite arithmetic calculations.
[Verification scope](verification/math/README.md).

## Citation and license

[CITATION.cff](CITATION.cff) describes the candidate manuscript. The Lean
package is [Apache-2.0](lean/normalizer-core/LICENSE); manuscripts and
documentation are CC BY 4.0, and other verification software is MIT.
See [LICENSE](LICENSE) for the path-specific terms.
