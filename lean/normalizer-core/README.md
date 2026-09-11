# Normalizer obstructions and curve cohomology in Lean

Lean 4 proofs of a dimension obstruction for line normalizers in sl₃, and
algebraic geometry used in its proposed application to surface-group
representations. The package contains 875 named theorems and 84 examples.

## Normalizer obstruction

Over a characteristic-zero field F, let m ≠ 0 lie in sl₃(F), let N(m)
normalize Fm, and let λ be the character defined by [x,m] = λ(x)m.
Every subspace U of N(m)/Fm satisfying

```text
[x,y] = λ(x)y − λ(y)x    for x,y in U
```

has dimension at most two. The proof classifies all nonzero traceless
3×3 matrices and includes the semisimple and minimal-nilpotent normalizer
calculations. The linear representatives used in the proof are constructed.

Start with
[`slThree_quotient_boundary_finrank`](Normalizer/ActualNormalizerQuotient.lean#L91).
[Boundary.lean](Normalizer/Boundary.lean) proves the cocycle identity that
produces the bracket law when the boundary map is injective.
[Flagship.lean](Normalizer/Flagship.lean) gives the explicit quotient obstructions,
and [Examples.lean](Normalizer/Examples.lean) contains the matrix checks.

## Cohomology and curve maps

Throughout this table k is a field. Cohomology uses mathlib's Ext construction
for abelian sheaves; its k-action comes from the scheme's structure morphism.

| Result | Hypotheses | Declaration |
|---|---|---|
| H¹(Spec R, M̃) = 0 | Any commutative ring R and R-module M | [`tilde_H1_subsingleton`](Normalizer/AffineH1Vanishing.lean#L43) |
| H¹(Spec R, F) = 0 | F a quasicoherent module sheaf | [`quasicoherent_Spec_H1_subsingleton`](Normalizer/AffineH1Vanishing.lean#L59) |
| H¹(X,O_X) finite-dimensional over k | A finite morphism X → ℙ¹_k | [`finiteMap_projectiveLine_unit_H1_finite`](Normalizer/FiniteMapH1.lean#L115) |
| A finite map X → ℙ¹_k exists | X proper, integral, normal, of dimension at most one | [`properNormalCurve_exists_finite_projectiveLine`](Normalizer/CurveMapExistence.lean#L206) |
| A finite map exists, giving finite-dimensional H¹(X,O_X) | X proper and integral of dimension at most one, normal away from one specified point | [`properCurve_exists_finite_projectiveLine_of_normalAwayPoint`](Normalizer/CurveMapSingular.lean#L64) |

The finite-map theorem allows nonreduced and nonintegral sources. The curve
existence theorems construct the map; they do not require a rational function
or a finite map as input. The smooth-curve case follows by deriving normality.
[Proof order and hypotheses](COHOMOLOGY_REVIEW.md).

## Bundles, determinants and zero schemes

The supporting constructions include:

- Local freeness of a finitely presented module sheaf with free stalks:
  [`sheaf_isLocallyFree_of_free_stalks`](Normalizer/LocallyFreeAssembly.lean#L60).
- The stalk comparison for a top exterior sheaf, preserving wedges of germs:
  [`schemeExteriorStalkEquivOfChart`](Normalizer/ExteriorStalkComparison.lean#L231).
- A nonzero determinant section from generic independence of the specified
  sections: [`schemeExteriorGlobalSection_ne_zero`](Normalizer/DeterminantGenericNonzero.lean#L33).
- The zero scheme D of a nonzero line-bundle section s, and the short exact
  sequence 0 → O_X → L → i_*(L restricted to D) → 0:
  [`properScheme_exists_sectionLine_shortExact`](Normalizer/SectionLineExact.lean#L282).

The zero scheme is finite on a proper integral curve. The package proves
its section-dimension comparisons, the associated cohomology sequence, and
vanishing of positive-degree cohomology of the section cokernel.
[Construction details](DEGREE_NONVANISHING_GAP.md) ·
[Complete declaration correspondence](CORRESPONDENCE.md).

## Remaining application

The determinant degree/nonvanishing implication and the complete geometric
bound h⁰(E/M) ≤ 4 remain unformalized. The unrestricted singular-curve case
still requires a construction yielding H¹ finiteness. Higher curve vanishing
and the Euler-characteristic comparison with line-bundle degree are also
unfinished.

The proposed rank-three finite-image theorem and general-rank square endpoint
remain candidates. Their representation-derived geometric inputs, branch
coverage and final finiteness arguments are separate obligations.
[Project roadmap](../../PUBLICATION_ROADMAP.md).

## Reproduce the build

Install [elan](https://github.com/leanprover/elan#installation), Git and Python
3.10 or later. From this directory:

```sh
lake exe cache get
python3 scripts/verify.py
python3 scripts/check_correspondence.py
```

The package pins Lean `4.34.0-rc2` and mathlib commit
`7974e751bece493b6ff508039423ca9fa2452fa8`. The verifier builds the library
and examples, generates `AxiomAudit.lean`, and checks every named declaration.
All 1,230 declarations pass; the only axioms used are `propext`,
`Classical.choice`, and `Quot.sound`. There are no proof placeholders or
custom axioms. [Successful public build](https://github.com/Robby955/rank-three-mcg-finiteness/actions/runs/34649596032).

Build logs, axiom output and source hashes are written to `receipts/`.
Check the distribution with `sha256sum -c SHA256SUMS` on Linux or
`shasum -a 256 -c SHA256SUMS` on macOS.
[Verification record](VERIFICATION.md).

## Attribution and license

The candidate application builds on Aaron Landesman and Daniel Litt's work
on surface-group representations. Classical support lemmas and manuscript
claims are identified separately in [CORRESPONDENCE.md](CORRESPONDENCE.md).

Licensed under [Apache-2.0](LICENSE). See [NOTICE](NOTICE) for attribution
and dependency licenses.
