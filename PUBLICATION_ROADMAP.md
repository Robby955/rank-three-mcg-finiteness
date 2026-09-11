# Proof and publication roadmap

The public Lean package proves the sl₃ normalizer obstruction, affine H¹
vanishing, and structure-sheaf H¹ finiteness for finite maps to ℙ¹ and several
classes of proper curves. [Results and source links](lean/normalizer-core/README.md).

These proofs support the proposed finite-image bounds for surface-group
representations. Completing the geometric section bound and the
representation argument remains the central objective.

## Published proof sources

[PR #9](https://github.com/Robby955/rank-three-mcg-finiteness/pull/9) is merged.
Public commit `79cba419e3ddfd0a5d5c6c736a176402233e8e3d` contains 875 named
theorems, 1,230 audited declarations and 84 examples. Its
[Lean build and axiom audit](https://github.com/Robby955/rank-three-mcg-finiteness/actions/runs/34649596032)
and [repository checks](https://github.com/Robby955/rank-three-mcg-finiteness/actions/runs/34649596055)
passed. The only axioms used are `propext`, `Classical.choice`, and `Quot.sound`.

| Completed result | Scope |
|---|---|
| Normalizer boundary obstruction | Every characteristic-zero field; all nonzero traceless 3×3 matrices |
| Affine H¹ vanishing | Every commutative ring and module; also quasicoherent sheaves |
| H¹ finiteness for finite X → ℙ¹_k | Any field; source need not be integral or reduced |
| Finite-map construction and H¹ finiteness for proper curves | Normal integral curves, smooth integral curves, and integral curves normal away from one specified point |
| Exterior sheaves and determinant sections | Stalk comparison from bundle charts; nonzero section from generic independence |
| Line-section zero scheme and exact sequence | Constructed maps, finite zero scheme on a proper integral curve, and cokernel cohomology comparisons |

The table describes formalized statements, including classical supporting
mathematics. It is not a count of new mathematical results.

## Remaining proof obligations

### 1. Determinant degree and nonvanishing

The line, its specified nonzero section, its zero scheme, the sheaf exact
sequence and cohomology comparisons have been constructed. What remains is
the passage to Euler characteristic and the established degree of a line
bundle. This includes the unrestricted singular-curve H¹ finiteness argument
and higher-cohomology vanishing.

The intended conclusion is that a nonzero section of a line bundle of
nonpositive degree on a proper integral curve is nowhere vanishing.
[Detailed interfaces](lean/normalizer-core/DEGREE_NONVANISHING_GAP.md).

### 2. The geometric bound h⁰(E/M) ≤ 4

Construct the evaluation subbundle, establish its degree properties, finish
the rank-two estimate, and assemble the boundary argument for the specified
bundle and saturated line. The normalizer dimension obstruction alone does
not supply these geometric inputs.

### 3. The representation theorem

Derive the geometric inputs from the surface-group representations, establish
exhaustive coverage of the genus-five cases, and complete the fixed-part,
Hodge-theoretic, arithmetic and finiteness arguments. The general-rank endpoint
and conditional genus-four argument need their own complete proof chains.

## Status of the proposed bounds

| Statement | Status |
|---|---|
| Landesman–Litt: finite image when r < √(g + 1) | Published |
| General-rank equality endpoint r² = g + 1 | Candidate |
| Rank-three finite image for g ≥ 5 | Candidate |
| Rank-three finite image in genus four | Candidate, conditional on B1–B5 |
| Rank-three finite image in genus three | Open |
| General range g ≥ r² − 4 | Open |

[STATUS.md](STATUS.md) records the manuscript claim boundaries. The available
Lean proofs do not yet establish an improvement of the Landesman–Litt
representation bound.

## Release policy

A Lean release should name its principal theorems, link to the exact source,
and include the pinned dependencies and a successful build and axiom audit.
It should state the remaining mathematical assumptions once, with a link to
the detailed correspondence.

A representation-result announcement requires the complete argument and
independent mathematical review. Until then, the manuscripts remain
candidates and the Lean results are presented individually.

The [August manuscript release](https://github.com/Robby955/rank-three-mcg-finiteness/releases/tag/v0.1.5-candidate)
predates the Lean package. Its original tag and files identify that version;
the public branch contains the subsequent proof sources.
