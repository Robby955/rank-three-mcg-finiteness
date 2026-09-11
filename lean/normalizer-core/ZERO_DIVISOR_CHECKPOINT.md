# Specified section exact sequence and cohomology checkpoint

Verdict: **PARTIAL** for the geometric section bound and representation
campaign. This continuation starts from local ambient-cohomology commit
`3a46ebbb94b8d94ee912eb076bdc0422e1166fa3`. Public PR #8 is merged at
`307a99b7ace7a51380c1377fba50504352af0999` and contains the preceding
591-theorem zero-scheme/finiteness checkpoint. The later scalar, line-sequence,
cohomology and restricted-line dimension work has passed local verification and has not been pushed or
checked by hosted CI.

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
| Actual scalar cokernel | Affine ideal/image equality and actual stalk lifts prove the canonical cokernel comparison with i_*O_D; the quotient map is preserved. |
| Actual scalar short exact sequence | Nonzero s on an integral scheme gives `0 -> L-dual -> O_X -> i_*O_D -> 0`, including the specified determinant specialization. |
| Actual line-section map | Nonzero s and genuine charts give Mono(O_X -> L), with its actual coordinate formula. |
| Local pullback target comparison | The full actual adjunction square and original chart equation are proved. |
| Actual line exact sequence | The canonical cokernel comparison gives `0 -> O_X -> L -> i_*i^*L -> 0`, preserving the specified section and actual restriction map. |
| Proper-scheme application | Genuine pointwise charts construct a finite quasi-compact cover and the actual line short exact sequence. The determinant specialization is also proved. |
| Intrinsic finite-scheme cohomology | Higher cohomology of every actual abelian sheaf on the constructed finite D vanishes, including nonreduced D. |
| Closed-pushforward comparison | Actual cohomology agrees with source cohomology in every degree, naturally in the sheaf; degree zero is the actual global-section identification. |
| Actual cokernel acyclicity | The actual section cokernel on a proper integral curve has zero positive-degree cohomology; finite charts and generic nonzeroness are constructed from pointwise line charts and nonzero s. |
| Actual cohomology exact segment | The actual section and restriction maps, together with the extension-class connecting map, give the exact H⁰-to-H¹ segment, with H⁰ injectivity and H¹ surjectivity on the finite-type integral curve. |

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

The scalar-cokernel step adds eight modules: `ClosedSubschemeModules`,
`SectionZeroIdealAffine`, `SheafCokernelComparison`, `SectionZeroCokernel`,
`SectionHomMono`, `SectionZeroExact`, `LineRestrictionComparison`, and
`LineRestrictionUnit`.

[Examples.lean](Normalizer/Examples.lean) adds four checks: zero section,
unit section, a regular but noninvertible polynomial equation, and retention
of multiplicity in a squared principal ideal. Two additional checks retain
a nonzero square-zero element of Q[X]/(X^2) and verify positive function
dimension for its actual finite scheme over Q. Existing matrix and
geometric examples remain in the build.

Two scalar-sequence checks instantiate the actual cokernel comparison for a zero
map without monicity and verify that the actual closed-subscheme structure
quotient retains the doubled point's nonzero square-zero coordinate.

The line-sequence step adds five modules: `PullbackRestrictionUnit`,
`LineRestrictionCompatibility`, `SectionLineExact`, `DiscreteSheafCohomology`,
and `FiniteSchemeCohomology`. A new doubled-point example verifies intrinsic
higher-cohomology vanishing without reducing the scheme.

The ambient-cohomology continuation adds seven modules:
`AbelianSheafPullbackExact`, `ClosedPushforwardExact`, `ConstantSheafPullback`,
`ClosedPushforwardCohomology`, `ModuleAbelianPushforward`,
`SectionCokernelCohomology` and `SectionCohomologyExact`. Its doubled-point
example proves higher-cohomology vanishing after the actual closed
pushforward to the affine line.

The restricted-line dimension continuation adds seven modules:
`DiscreteLineTrivialization`, `FiniteLineSections`, `ModulePushforwardSections`,
`ModuleSheafCohomologyScalars`, `SectionCohomologyLinear`,
`SectionCokernelSections` and `ProperLineSectionsFinite`.
The new examples prove dimension two for arbitrary genuine line sheaves on
the doubled point and on Spec(Q × Q), deriving the actual field action.

The finite-kernel continuation adds `SectionCohomologyDimension` and
`SheafCohomologyTerminal`: 11 theorems and four constructions. It proves the
actual finite H¹ kernel, the H¹ finiteness equivalence, the exact finite-term
dimension balance and a natural terminal-object cohomology comparison.
The new example checks the latter on the actual doubled point.

The slice-site continuation adds `OverAbelianExtension` and
`OverSheafCohomology`: 11 theorems, 10 constructions and two examples.
It constructs both exact functors and their adjunction, identifies the
extended integer sheaf with the represented abelian sheaf, and proves the
all-degree cohomology comparison with naturality and degree-zero evaluation.

The affine continuation adds `AffinePrincipalLocalization`, `AffineCechOne`,
`AffineSheafLifting` and `AffineH1Vanishing`: 13 theorems, two named
constructions and four examples. It proves actual H¹(Spec R, tilde M) = 0
for arbitrary commutative rings and modules, and the quasicoherent-sheaf
corollary. The difference cocycle is constructed and solved in an arbitrary
abelian-sheaf extension; the final step uses the actual injective presentation.

The actual-open continuation adds `OpenSheafCohomology`,
`SchemeOpenCohomology` and `TwoAffineCohomology`. It constructs all-degree
geometric open restriction with structure-field linearity, proves actual
affine-open H1 vanishing, and gives the linear Mayer-Vietoris quotient
presentation for a supplied two-affine cover. Neither the cover nor
finite dimension of the quotient is assumed constructed on the proper curve.

The finite-map continuation adds `LaurentCechFinite` and `CurveFiniteMap`:
11 theorems, one construction and two examples. The bounded Laurent window
proves finite generation of its algebraic quotient. The geometric theorem
proves a given nonconstant proper curve map finite, deriving finite fibres.
That earlier checkpoint did not construct the map or chart comparison.
The normal-map checkpoint added 30 theorems, 17 constructions and three
examples. It constructed normal-curve extension and a specified function's
actual P1 map, plus actual section quotients and finite chart modules.
The coordinate continuation added 27 theorems, 13 constructions and four
examples. It identifies both actual chart section rings with polynomial
rings and their overlap with Laurent polynomials, preserving both actual
restriction maps. It proves actual H1(P1_k,O)=0 for every field k.
The finite-map continuation now adds 28 theorems, 11 constructions and
three examples. It connects actual overlap localization, original scalars,
finite chart generators and both restriction images to the Laurent quotient
argument. Actual H1(X,O_X) is finite for any finite X -> P1_k; no source
normality or integrality is required. The latest two modules add 20 theorems and three examples. They construct
finite maps and actual H1 finiteness for proper normal curves, proper smooth
curves and integral curves normal away from one possibly singular point.
Dimension zero is closed. The general singular integral map-existence
problem remains: construct an affine open containing every nonnormal point,
or complete normalization/defect/cohomology transfer.

The full build and complete axiom audit pass: **875 named theorems, 1230
audited declarations and 84 examples**, up from 855, 1210 and 81 at the
finite-chart checkpoint.
Every audited declaration uses only `propext`, `Classical.choice` and
`Quot.sound`. There are no proof placeholders or custom axioms.
[CORRESPONDENCE.md](CORRESPONDENCE.md) links every declaration to its source
and exact role; [VERIFICATION.md](VERIFICATION.md) describes reproduction.

## What this does not establish

There is no general bundled effective-Cartier-divisor/O(D) API here. The
constructed ideal and inverse module are connected by actual chart data;
the full general correspondence of Stacks 31.15.10 is not claimed.

The actual restricted-line dimension comparison, cokernel section and H⁰
finiteness, induced cohomology field actions and connecting-map linearity
are proved. Actual affine H¹ vanishing is now also proved. Over an
algebraically closed field, actual line-bundle sections
and H⁰ are finite from genuine pointwise charts. The next missing geometric
lemma is the affine neighborhood of the nonnormal locus for the unrestricted
proper integral curve target. Actual H¹(X,O_X) finiteness is now proved for
normal, smooth and one-exceptional-point curves with their stated hypotheses.
The remaining curve higher vanishing and numerical Euler comparison still
have to connect the actual linear sequence to established line degree.
The dimension of Gamma(D,O_D) has not been defined to be line degree.
The full degree/nonvanishing implication remains unformalized. See
[the remaining gap](DEGREE_NONVANISHING_GAP.md).

The complete bound h0(E/M) <= 4, its residual representation inputs,
exhaustive genus-five branches and upstream finiteness arguments remain
unformalized. Manuscripts and theorem labels are unchanged. No new
rank-three finite-image result or genus-three solution is asserted.
