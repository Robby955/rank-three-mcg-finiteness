# Specified zero scheme finiteness checkpoint

Verdict: **PARTIAL** for the geometric section bound and representation
campaign. The listed formal propositions are proved with their displayed
hypotheses. This checkpoint starts from public PR #7's merged
commit `a7544c5b9136dd88d6741188a7be531d49bbace2`. The present finiteness
step extends the clean local zero-ideal commit
`d5cc96d0dcf8af6a42a047463a7a75c924680926`. Local verification passed;
hosted verification of the source commit is recorded in its pull request
checks and workflow runs.

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
| Global-to-generic injection | Genuine pointwise line charts on an integral scheme prove that a global section is nonzero exactly when its generic germ is nonzero. |
| Finite chart extraction | Proper curve and genuine pointwise line charts construct a finite cover with quasi-compact inclusions. |
| Actual finite zero scheme | Generic-point exclusion gives dimension at most zero, then finiteness of the actual zero-scheme morphism to the field. No reducedness is assumed. |
| Zeros and function dimension | A nonunit actual local equation is equivalent to membership in the actual support. Such a zero gives a positive-dimensional actual global function space on D. |

The decisive section identities are
`schemeSectionInverseIdealIso_section` in
[SectionIdealBundle.lean](Normalizer/SectionIdealBundle.lean) and
`schemeDeterminantInverseIdealIso_section` in
[DeterminantZeroDivisor.lean](Normalizer/DeterminantZeroDivisor.lean).
These preserve the given section; they do not merely construct an abstract
line-bundle isomorphism.

## Files and checks

The zero-ideal step added thirteen modules imported by [Normalizer.lean](Normalizer.lean):
`SectionLocalEquation`, `SectionDualEvaluation`, `SectionZeroIdeal`,
`IdealSheafGluing`, `SectionZeroScheme`, `ZeroIdealUniqueness`,
`SectionEvaluationMono`, `SectionImageSheaf`, `DualTransport`, `LineBidual`,
`SectionZeroDivisor`, `SectionIdealBundle`, and `DeterminantZeroDivisor`.

The finiteness step adds eight modules: `CurveClosedSubscheme`,
`FiniteZeroDimensional`, `SectionZeroSupport`, `FiniteLineCharts`,
`FiniteSchemeSections`, `SectionZeroLocus`, `LineGenericInjection`, and
`SectionZeroFinite`.

[Examples.lean](Normalizer/Examples.lean) adds four checks: zero section,
unit section, a regular but noninvertible polynomial equation, and retention
of multiplicity in a squared principal ideal. Two additional checks retain
a nonzero square-zero element of Q[X]/(X^2) and verify positive function
dimension for its actual finite scheme over Q. Existing matrix and
geometric examples remain in the build.

The full build and complete axiom audit pass: **591 named theorems, 836
audited declarations and 54 examples**, up from 547, 791 and 52 at the
local zero-ideal baseline, and 472, 679 and 48 at public PR #7.
Every audited declaration uses only `propext`, `Classical.choice` and
`Quot.sound`. There are no proof placeholders or custom axioms.
[CORRESPONDENCE.md](CORRESPONDENCE.md) links every declaration to its source
and exact role; [VERIFICATION.md](VERIFICATION.md) describes reproduction.

## What this does not establish

There is no general bundled effective-Cartier-divisor/O(D) API here. The
constructed ideal and inverse module are connected by actual chart data;
the full general correspondence of Stacks 31.15.10 is not claimed.

The next exact construction is the actual short exact sequence
`0 -> O_X --s--> L -> i_*(L|D) -> 0`. Its Euler-characteristic comparison
must identify the established line degree with the proved finite function
dimension of D. That dimension has not been defined to be the line degree.
The full degree/nonvanishing implication remains unformalized. See
[the remaining gap](DEGREE_NONVANISHING_GAP.md).

The complete bound h0(E/M) <= 4, its residual representation inputs,
exhaustive genus-five branches and upstream finiteness arguments remain
unformalized. Manuscripts and theorem labels are unchanged. No new
rank-three finite-image result or genus-three solution is asserted.
