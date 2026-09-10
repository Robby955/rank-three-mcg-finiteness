# Specified zero ideal checkpoint

Verdict: **PARTIAL** for the geometric section bound and representation
campaign. The listed formal propositions are proved with their displayed
hypotheses. This local continuation starts from public PR #7's merged
commit `a7544c5b9136dd88d6741188a7be531d49bbace2`; it has not been pushed
or tested by hosted CI.

## New mathematical content

| Construction or implication | Exact scope |
|---|---|
| Actual dual evaluation at s | Genuine Hom sheaf and restriction-compatible morphism into the structure sheaf. |
| Local equations and transitions | Extracted from actual line charts; transitions are proved units and preserve the specified section. |
| Regularity and monicity | Integral scheme plus nonzero actual generic germ and covering line charts. No injectivity or nowhere-vanishing assumption. |
| Global zero ideal and closed subscheme | Constructed from a finite genuine line-chart cover with quasi-compact inclusions; overlap compatibility is proved. |
| Cover independence | Actual global ideals and schemes agree for the same sheaf map, with the comparison preserving the closed immersion. |
| Actual image ideal module | Canonically isomorphic to the source of a monic map; exact section-image and affine-chart ideal comparisons. |
| Inverse ideal module and specified section | Hom(image(evaluation at s),O) is canonically isomorphic to L; the actual inclusion section maps exactly to s. Rank-one charts, local freeness and finite presentation are constructed. |
| Specified determinant | Its line charts and generic nonzeroness come from genuine rank-n bundle charts and independence of the actual generic section germs. |

The decisive section identities are
`schemeSectionInverseIdealIso_section` in
[SectionIdealBundle.lean](Normalizer/SectionIdealBundle.lean) and
`schemeDeterminantInverseIdealIso_section` in
[DeterminantZeroDivisor.lean](Normalizer/DeterminantZeroDivisor.lean).
These preserve the given section; they do not merely construct an abstract
line-bundle isomorphism.

## Files and checks

Thirteen new modules are imported by [Normalizer.lean](Normalizer.lean):
`SectionLocalEquation`, `SectionDualEvaluation`, `SectionZeroIdeal`,
`IdealSheafGluing`, `SectionZeroScheme`, `ZeroIdealUniqueness`,
`SectionEvaluationMono`, `SectionImageSheaf`, `DualTransport`, `LineBidual`,
`SectionZeroDivisor`, `SectionIdealBundle`, and `DeterminantZeroDivisor`.

[Examples.lean](Normalizer/Examples.lean) adds four checks: zero section,
unit section, a regular but noninvertible polynomial equation, and retention
of multiplicity in a squared principal ideal. Existing matrix and geometric
examples remain in the build.

The full build and complete axiom audit pass: **547 named theorems, 791
audited declarations and 52 examples**, up from 472, 679 and 48 at the base.
Every audited declaration uses only `propext`, `Classical.choice` and
`Quot.sound`. There are no proof placeholders or custom axioms.
[CORRESPONDENCE.md](CORRESPONDENCE.md) links every declaration to its source
and exact role; [VERIFICATION.md](VERIFICATION.md) describes reproduction.

## What this does not establish

There is no general bundled effective-Cartier-divisor/O(D) API here. The
constructed ideal and inverse module are connected by actual chart data;
the full general correspondence of Stacks 31.15.10 is not claimed.

The next exact geometric lemma is finiteness of this actual zero scheme
over the base field on a proper integral curve. Then come the established
curve-degree comparison and positivity needed for the specified-section
nonvanishing argument. See [the remaining gap](DEGREE_NONVANISHING_GAP.md).

The complete bound h0(E/M) <= 4, its residual representation inputs,
exhaustive genus-five branches and upstream finiteness arguments remain
unformalized. Manuscripts and theorem labels are unchanged. No new
rank-three finite-image result or genus-three solution is asserted.
