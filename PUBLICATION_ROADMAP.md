# Formalization and publication roadmap

The current package proves actual structure-sheaf H1 finiteness for every
finite map X -> P1_k. It also constructs such a map for proper normal
integral curves, derives the smooth case, and treats integral curves normal
away from one possibly singular point. Proper dimension-zero schemes are
covered without reducedness or integrality. Rational functions and
nonconstancy are constructed where needed.

This update advances the package from public [PR #8](https://github.com/Robby955/rank-three-mcg-finiteness/pull/8),
commit `307a99b7ace7a51380c1377fba50504352af0999`, from 591 to **875 named
theorems**, from 836 to **1230 audited declarations**, and from 54 to
**84 examples**. Counts describe coverage, not completion of the candidate
representation theorem. See the [review guide](lean/normalizer-core/COHOMOLOGY_REVIEW.md)
for the final theorem assumptions and the dependency order.

The complete package passed local build, source-hash, correspondence and
axiom checks. Hosted verification of this update remains pending; results
must be read from the pull request's checks before claiming a hosted pass.

The unrestricted singular integral case still needs an affine neighborhood
of its nonnormal locus or normalization/cohomology transfer. Higher curve
vanishing, Euler/degree comparison, the complete section bound and the
representation theorem remain separate. Claim labels are unchanged.

## Completed formal interfaces

| Interface | Checked scope |
|---|---|
| Normalizer algebra | Exhaustive characteristic-zero traceless 3×3 matrix reduction and the boundary-law obstruction. |
| Actual curve quotient support | Finite presentation, stalk exactness, saturation-to-torsion-freeness, smooth-stalk regularity and local-freeness assembly under actual bundle and curve inputs. |
| Character and generic quotient | Actual constants and scalar-character constructions; actual generic quotient comparisons preserving bracket and character under the stated ambient identification. |
| Generic dimension | Preservation from an actual free inclusion or actual trivialized subsheaf; no inference from base-field independence alone. |
| Exterior line | Genuine rank-n bundle charts construct rank-one charts of the actual top exterior sheaf. |
| Exterior stalk | The canonical actual stalk comparison is an isomorphism on genuine rank-n charts and preserves the specified wedge of section germs. |
| Specified determinant | Function-field independence of the actual generic germs proves the specified exterior section has nonzero generic germ and is globally nonzero. |
| Zero subscheme | Finite genuine line charts with quasi-compact inclusions construct the global ideal and closed subscheme, with exact restrictions and cover independence. |
| Regularity | On an integral scheme, nonzero generic germ proves regular local equations and actual monic dual evaluation. |
| Inverse ideal module | The dual of the actual image ideal module is locally free, finitely presented and canonically isomorphic to the original line, carrying the inclusion section to the specified section. |
| Global-to-generic injection | Genuine pointwise line charts on an integral scheme prove global section nonzeroness equivalent to nonzero generic germ. |
| Finite charts and zero scheme | Proper curve and genuine pointwise line charts construct a finite quasi-compact chart cover. A nonzero specified section has an actual zero scheme finite over the field. |
| Positive zero-scheme function dimension | A zero of the specified section gives nonempty D and positive finite dimension of Gamma(D,O_D), using the actual structure morphism. The determinant specialization is proved. |
| Actual scalar cokernel | Actual affine defining ideals and stalk lifts prove cokernel(dual evaluation at s) is i_*O_D, preserving the quotient map. The general line-map comparison does not require monicity. |
| Scalar short exact sequence | Nonzero s on an integral scheme and genuine finite charts give the actual `0 -> L-dual -> O_X -> i_*O_D -> 0`, including the specified determinant specialization. |
| Specified-map compatibility | The complete actual pullback/restriction square and original line-chart equation commute. |
| Actual line short exact sequence | Nonzero s on an integral scheme gives `0 -> O_X -> L -> i_*i^*L -> 0`, with the specified section and original adjunction unit. A proper-scheme corollary constructs the finite chart cover. |
| Intrinsic higher cohomology on D | Actual finiteness supplies discreteness; every abelian sheaf on the constructed zero scheme has vanishing higher cohomology, with nilpotents retained. |
| Closed-pushforward cohomology | Actual exact abelian-sheaf adjoints give a natural additive equivalence in every degree, equal to the actual global-section comparison in degree zero. |
| Ambient cokernel vanishing | Positive cohomology of the actual specified-section cokernel vanishes on the proper integral curve. Genuine pointwise charts construct the finite cover; the determinant specialization derives its line charts and nonzero section from the original bundle and generic germs. |
| Actual cohomology sequence | The underlying abelian section sequence is short exact; its extension class gives the canonical connecting map and the actual H⁰-to-H¹ segment is exact at its four interior terms. The H⁰ map is injective and, on the finite-type integral curve, the H¹ map is surjective. |
| Restricted-line dimension on D | Genuine line charts construct O_D ≅ i^*L on the finite scheme, including nilpotents. Actual sections have the same base-field dimension as Gamma(D,O_D). |
| Cokernel section and H⁰ dimensions | Actual direct-image and H⁰ comparisons give the same dimension for the actual section cokernel. A zero gives positive dimension; every cohomology group of this cokernel is finite and higher ones vanish. |
| Actual cohomology scalars | Actual scalar endomorphisms induce the field action on Sheaf.H; induced maps, the H⁰ comparison and the original connecting map are linear. |
| Line-bundle H⁰ finiteness | On a proper integral curve over an algebraically closed field, genuine pointwise line charts prove finite-dimensional sections and H⁰. No nonzero section, finite cover or H¹ finiteness is supplied. |
| Finite H¹ kernel | The actual section map H¹(O_X) -> H¹(L) has finite kernel; finiteness of either whole space is equivalent to finiteness of the other. Neither absolute assertion is proved. |
| Exact finite-term balance | Over the algebraically closed base, h⁰(L) + dim ker(H¹(O_X) -> H¹(L)) = 1 + dim Gamma(D,O_D), using only proved finite H⁰ domains. |
| Terminal cohomology comparison | The general-site H'(F,T,n) at terminal T is naturally equivalent to actual H(F,n), with degree-zero evaluation compatibility. |
| Slice cohomology comparison | Actual cohomology-presheaf evaluation equals intrinsic cohomology on the small slice site in every degree. Both exact adjoints and the normalized representing-object comparison are constructed. |
| Actual affine H¹ vanishing | H¹(Spec R, tilde M) = 0 for all commutative rings and modules, computed in all abelian sheaves; also every quasicoherent module sheaf on Spec R. Finite principal-cover lifting and cocycle correction are constructed. |

| Actual geometric open comparison | All-degree ambient-open cohomology equals cohomology of the actual restricted module, linearly for the structure-field actions. |
| Affine-open H1 | Every quasicoherent module sheaf on an arbitrary ambient scheme has vanishing H1 on each actual affine open. |
| Two-affine quotient presentation | For a supplied actual two-affine cover, the original Mayer-Vietoris boundary is linear and surjective onto actual global H1, with kernel exactly the restriction differences. This does not prove finite dimension. |
| Laurent quotient finiteness | Two Laurent-generating families, the first finite, give a finite coefficient-ring quotient by their nonnegative and nonpositive power spans. A finite spanning window is constructed. |
| Nonconstant curve maps | A supplied nonconstant map from a proper integral curve over a field to a separated scheme over that field is proved finite, with finite fibres derived from the curve dimension. |

| Normal-curve extension | Actual integrally closed stalks and curve dimension give valuation stalks; properness constructs local lifts, neighbourhood representatives and a unique global morphism. |
| Actual projective line and map | Proj of k[X0,X1], its proper structure map and standard affine charts; a specified rational function extends to an actual map on a normal curve. The later CurveMapExistence module constructs a suitable section and proves nonconstancy. |
| Actual chart sections | The actual open H0 comparison is linear and restriction-compatible; overlap sections modulo actual restriction differences compute H1. Finite maps supply finite actual inverse-image chart modules. Polynomial/Laurent coordinates and both actual restriction maps are now identified. |

| Actual Proj coordinates | Both actual chart section rings are polynomial rings and their overlap is Laurent; the actual restrictions send the two coordinates to T and T^-1. Valid over every commutative coefficient ring. |
| Actual projective-line H1 | H1(P1_k,O)=0 for every field, using actual sheaf cohomology and the actual chart restriction decomposition; finite for the actual structure-field action. General proper integral curve H1 finiteness remains. |

| Actual overlap localization | The actual inverse-image overlap is the principal open of the pulled-back ratio; actual restriction is the corresponding localization. |
| Original scalar action | Actual chart constants equal structure-map constants; the Laurent action via f.app has the same coefficient action as the actual cohomology boundary. |
| Finite-map H1 | For any finite X -> P1_k, actual chart generators give the two Laurent power spans and actual H1(X,O_X) is finite-dimensional. No source normality, integrality or reducedness is required. |
| Constructed finite maps | Normal and smooth proper integral curves; curves normal away from one point; all proper dimension-zero schemes. No rational function or nonconstancy input. |
| General singular-curve interface | Extension is proved when the nonnormal locus lies in a supplied nontrivial affine open. Constructing that open from the original hypotheses remains. |

## Next mathematical construction

Finish the unrestricted singular integral case by constructing a nontrivial
affine open containing the nonnormal locus. The finite-map and H1 results
are now proved for normal and smooth curves and for curves normal away
from one point. Dimension zero is closed. The new extension theorem
handles the general case as soon as that actual affine open is constructed.

The existing finite-kernel equivalence then transfers structure-sheaf H1
finiteness to H1 of a line bundle with a specified nonzero section; it is
already applicable on the proved branches. Higher curve vanishing and the
Euler/degree comparison remain separate from this finiteness result.

The actual affine-open comparison, with structure-field scalars, is now
proved. For a supplied actual two-affine cover, the actual Mayer-Vietoris
boundary is surjective onto global H1; its kernel is the differences of
restrictions. The quotient now uses actual overlap sections, with actual restriction
compatibility proved. A specified rational function now constructs a unique
actual map to P1 on the normal-curve branch. For finite maps, the actual
inverse-image chart coordinate modules are proved finite over the chart rings.

`ProjectiveCoordinates` now identifies the actual section rings of both
standard Proj charts with polynomial rings and the actual overlap section
ring with Laurent polynomials, over every commutative coefficient ring.
The first actual restriction is polynomial inclusion; the second sends its
variable to the inverse Laurent variable. This is proved from the actual
homogeneous-localization maps and mathlib's actual Proj sheaf restrictions.
The coordinate maps fix the homogeneous-localization constants.

`ProjectiveLineCohomology` then proves actual H1(P1_k,O)=0 over every field.
Every Laurent polynomial splits into the difference of a polynomial in T
and a polynomial in T^-1. The actual section isomorphisms transport this
decomposition to actual chart sections. Consequently the actual
Mayer-Vietoris boundary is zero; affine-open vanishing makes it surjective.
No cohomology vanishing or finite-dimensionality is supplied as a hypothesis.
Finiteness for the actual structure-field action follows from vanishing.
This is the n=1, d=0, q=1 field-base case of
[Stacks Lemma 30.8.1](https://stacks.math.columbia.edu/tag/01XS).

The finite-map comparison is now constructed. `FiniteChartGeometry`
identifies each actual pulled-back overlap as the principal open of the
actual pulled-back chart ratio, and proves the section restriction is the
corresponding localization. `ProjectiveChartScalars` identifies actual
coordinate constants with those of the original structure morphism.

`FiniteMapLaurent` defines the Laurent action through f.app and proves the
coefficient action agrees with `schemeOpenSectionsModule` for the composed
structure map. The actual restriction is semilinear and its localization
clears denominators. `FiniteMapH1` chooses finite chart generators using
finiteness of the original morphism. Their restrictions generate the actual
overlap over the Laurent ring. Each actual chart restriction image equals
the coefficient span of the corresponding nonnegative or nonpositive powers.
The actual Mayer-Vietoris boundary kills these two spans and is onto; the
proved Laurent quotient finiteness theorem gives finite-dimensional actual
H1(X,O_X). No cohomology dimension or quotient presentation is an input to
the final theorem.

`finiteMap_projectiveLine_unit_H1_finite` requires only an actual finite
f:X -> P1_k, with k a field. It requires no source integrality, normality,
smoothness or reducedness. `properCurve_unit_H1_finite_of_projectiveMap`
derives finiteness from a supplied nonconstant k-map to P1 on a proper
integral curve of dimension at most one, preserving the original p-scalars.
Neither theorem constructs the required map for an arbitrary proper curve.

The finite-map existence construction is now complete on three branches.
`properNormalCurve_exists_finite_projectiveLine` constructs the map on a
proper integral curve with integrally closed actual stalks and dimension
at most one. It supplies both the rational function and nonconstancy:
an affine neighborhood with two points has a section whose invertibility
locus is nonempty and proper. Its [1:s] map extends globally by the
valuative criterion and agrees on the whole original open. That preserves
nonconstancy; properness then makes the map finite. The zero-dimensional
branch is also proved, without integrality or reducedness, using [1:0].

`properSmoothCurve_exists_finite_projectiveLine` derives stalk normality
from smoothness and the dimension bound. The corresponding actual H1
finiteness theorem uses the original structure-field action; it assumes
no map, rational function, local normality or cohomology dimension.

`partialMap_extends_of_valuationOutside` requires valuation stalks only
outside the actual domain. Consequently a nontrivial affine open U whose
complement has integrally closed stalks suffices, even if U is singular.
`properCurve_exists_finite_projectiveLine_of_normalAwayPoint` constructs
such an affine open when the curve is normal away from one specified
point; no normality at that point is assumed. It also yields actual H1
finiteness. These are full results for their explicitly stated branches,
not the unrestricted proper integral curve theorem.

For the unchanged general target, the exact next sufficient lemma is:

```text
p:X -> Spec k proper, X integral, Nontrivial X, dim X <= 1
  => exists U : X.Opens,
       IsAffineOpen U and Nontrivial U and
       forall x not in U, IsIntegrallyClosed (O_X,x).
```

Neither the needed affine neighborhood of the entire nonnormal locus nor
the general normalization/finite-support defect/cohomology transfer is
constructed. Dimension zero is now closed. Normality has not been added
to the unrestricted target. Higher curve vanishing and Euler/degree
comparison remain separate. The normal and smooth H1 results can already
be used wherever their actual geometric hypotheses are established.

See the [precise dependency note](lean/normalizer-core/DEGREE_NONVANISHING_GAP.md).

Complete the remaining curve higher-cohomology vanishing and numerical
Euler additivity for the actual linear exact sequence. These must connect
the established line-bundle degree to dim_k Gamma(D,O_D), as used in
[Stacks Lemma 33.44.9](https://stacks.math.columbia.edu/tag/0AYY).
The positive-degree implication for a specified nonzero section with a zero
in [Stacks Lemma 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40)
remains unformalized. No degree definition tailored to this quotient is used.

The current proofs construct the concrete zero ideal and inverse image-ideal
module. They do not expose a general bundled effective-Cartier-divisor/O(D)
API or prove the full equivalence and uniqueness statement of Stacks 31.15.10.
The finite quasi-compact charts are now constructed from genuine pointwise
line charts on the proper curve. The actual representation-derived bundle
and curve still need to be instantiated. See the [exact gap](lean/normalizer-core/DEGREE_NONVANISHING_GAP.md)
and [local checkpoint](lean/normalizer-core/ZERO_DIVISOR_CHECKPOINT.md).

The construction of the actual saturated evaluation subbundle and its
degree zero, the rank-two section estimate, the global boundary application
and assembly of `h⁰(E/M) ≤ 4` remain separate. After that come the residual
representation inputs, exhaustive genus-five branch coverage and upstream
fixed-part, descent, HN, Hodge-theoretic, arithmetic and finiteness arguments.

## Verification and release boundary

The local checks and their reproducible commands are in the
[verification record](lean/normalizer-core/VERIFICATION.md). The CI workflow
regenerates the axiom audit and checks hashes and correspondence. Its hosted
results are recorded in the pull request checks and
[workflow runs](https://github.com/Robby955/rank-three-mcg-finiteness/actions/workflows/lean-normalizer.yml).
Those checks establish replay of the listed formal propositions. The missing
geometric hypotheses and external mathematical review remain separate.

The degree/nonvanishing step is not a completed formal theorem. This update
is a **PARTIAL formalization milestone**. The manuscript labels stay fixed:
Landesman–Litt's strict range is **PUBLISHED**; the equality endpoint and
rank three for genus at least five are **CANDIDATE**; genus four is
**CANDIDATE conditional on B1–B5**; genus three and the general
`g ≥ r²−4` range are **OPEN**. No manuscript, tag or release is changed.
