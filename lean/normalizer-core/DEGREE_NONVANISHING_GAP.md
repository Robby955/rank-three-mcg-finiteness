# Exact remaining degree/nonvanishing interface

The target is the specified-section implication of
[Stacks Lemma 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40): on a
proper curve, a nonzero section of an invertible sheaf that vanishes at a
point forces positive degree. Its degree-zero contrapositive must concern
the specified determinant section.

## The concrete construction now proved

For an actual module sheaf L with genuine line charts, the core constructs
the actual dual evaluation L-dual -> O at a specified global section s.
On an integral scheme, genuine pointwise line charts prove that the global
section map into the generic stalk is injective. Thus a nonzero global
section has nonzero generic germ. That proves dual evaluation monic and its
actual local equations regular. Here regular means a non-zero-divisor;
it does not mean invertible or nonzero in the residue field.

Finite line-chart covers with quasi-compact inclusions construct an actual
global ideal and closed zero subscheme D, with exact chart restrictions and
cover independence. The actual image module I is identified with L-dual.
Its dual Hom(I,O) is locally free and finitely presented, and a constructed
isomorphism Hom(I,O) -> L carries the inclusion I -> O, viewed as a global
dual section, to the specified s. The image module and global ideal are
explicitly linked by their actual affine-chart ideal data.

The determinant application supplies these line charts from the original
rank-n bundle charts and supplies generic nonzeroness from independence of
the actual specified generic germs. See
[DeterminantZeroDivisor.lean](Normalizer/DeterminantZeroDivisor.lean) and
[SectionIdealBundle.lean](Normalizer/SectionIdealBundle.lean).

This supplies concrete ingredients of
[Stacks Lemma 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0).
It is not a general bundled effective-Cartier-divisor/O(D) API, nor a proof
of the full two-way correspondence and uniqueness assertion on arbitrary
schemes. No global IdealSheafData-to-Modules functor is supplied; the ideal
module of this constructed D is linked by the proved chart comparisons.

## Actual finiteness and positive function dimension now proved

For a proper integral curve p : X -> Spec(k), a nonzero global section s
and genuine pointwise line charts, the core constructs a finite
quasi-compact chart cover and proves its actual zero scheme D finite over k.
The proof derives generic-point exclusion, dimension at most zero, and
finiteness of the actual morphism D -> Spec(k). It retains nilpotents and
includes the empty zero scheme. Properness is sufficient; the fixed-cover
finiteness result only needs X of finite type over k and dimension at most one.

Under the scalar action induced by that actual morphism, Gamma(D,O_D) is
finite-dimensional, its dimension is zero exactly when D is empty, and a
zero of the specified section gives strictly positive dimension. The zero
condition is noninvertibility of the actual local equation in the local
ring. Its equivalence with membership in the constructed support is proved.
The determinant specialization constructs its line charts and generic
nonzeroness from the actual rank-n charts and generic independence. See
[SectionZeroFinite.lean](Normalizer/SectionZeroFinite.lean),
[SectionZeroLocus.lean](Normalizer/SectionZeroLocus.lean) and
[LineGenericInjection.lean](Normalizer/LineGenericInjection.lean).

These are finiteness and function-dimension ingredients of
[Stacks Lemma 33.44.9](https://stacks.math.columbia.edu/tag/0AYY).
They do not yet identify a line-bundle degree with this dimension.

## Actual scalar cokernel and scalar short exact sequence now proved

The actual scalar comparison is constructed:

```text
cokernel (schemeSectionDualEvaluation L s) ≅ i_* O_D.
```

The comparison preserves the original quotient map. The proof identifies
the glued ideal with the actual sectionwise image on affine chart subopens,
then constructs actual stalk lifts. Closed-subscheme structure-map stalk
surjectivity is proved, including at points outside D. No stalk exactness
or surjectivity assumption is supplied in this geometric application.
The more general scalar comparison holds for every line-sheaf map, even
the zero map. See [SectionZeroCokernel.lean](Normalizer/SectionZeroCokernel.lean).

For a nonzero section on an integral scheme, the proved monicity of actual
dual evaluation gives the actual short exact sequence

```text
0 -> L-dual --evaluation at s--> O_X -> i_* O_D -> 0.
```

[SectionZeroExact.lean](Normalizer/SectionZeroExact.lean) packages this in
mathlib's `ShortComplex.ShortExact`, including the specified determinant
specialization. Separately, [SectionHomMono.lean](Normalizer/SectionHomMono.lean)
proves the actual section map O_X -> L monic from nonzero s and genuine
pointwise charts.

## Intrinsic cohomology on the finite zero scheme

[DiscreteSheafCohomology.lean](Normalizer/DiscreteSheafCohomology.lean)
proves that epimorphisms of actual abelian sheaves on a discrete space
are surjective on global sections: lifts on singleton opens glue to an
actual global lift. This proves projectivity of the actual constant integer
sheaf and vanishing of actual `Sheaf.H` in every positive degree.

[FiniteSchemeCohomology.lean](Normalizer/FiniteSchemeCohomology.lean)
derives discreteness from actual finiteness over the field and applies this
vanishing result to the constructed zero scheme D. The scheme's nilpotents
are retained; an example treats the doubled point over the rationals.

The closed-pushforward comparison below now transports this vanishing to X
for the actual constructed quotient. This supplies the higher-cohomology
ingredient of [Stacks Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT).
Its full support construction, Euler formula and rank formula are not claimed.

## Actual line-bundle sequence now proved

[SectionLineExact.lean](Normalizer/SectionLineExact.lean) constructs the
actual short exact sequence

```text
0 -> O_X --s--> L -> i_*(L|D) -> 0.
```

The second map is the unit of the actual pullback-pushforward adjunction for
the constructed zero-scheme closed immersion. Its cokernel comparison
preserves that map. The full local equation

```text
e.hom >> restrict(eta_L) >> c.hom = restrict(q)
```

is proved in [LineRestrictionCompatibility.lean](Normalizer/LineRestrictionCompatibility.lean),
using the scheme-level square and its section formula from
[PullbackRestrictionUnit.lean](Normalizer/PullbackRestrictionUnit.lean).
Transport through the genuine charts supplies the actual stalk kernel,
image and surjectivity statements. Nonzero s on an integral scheme proves
the left injection. No diagram or exactness hypothesis is supplied.

The determinant specialization uses the actual exterior line and specified
wedge section. The proper-scheme corollary constructs the finite
quasi-compact chart cover from genuine pointwise line charts; no dimension
hypothesis is needed for this exact sequence.

## Closed-pushforward cohomology comparison now proved

[ClosedPushforwardCohomology.lean](Normalizer/ClosedPushforwardCohomology.lean)
constructs the actual additive equivalence in every degree:

```text
H^n(X, i_*F) ≃+ H^n(D, F).
```

This formalizes [Stacks Lemma 20.20.1](https://stacks.math.columbia.edu/tag/02UV)
for actual abelian sheaves and actual closed embeddings of topological spaces.
The equivalence is natural in F. In degree zero, mathlib's `H.equiv₀` takes it
to the actual equality of global sections of direct image.

[AbelianSheafPullbackExact.lean](Normalizer/AbelianSheafPullbackExact.lean)
uses mathlib's left exact site pullback and the actual adjunction to prove
inverse-image exactness. [ClosedPushforwardExact.lean](Normalizer/ClosedPushforwardExact.lean)
proves direct-image exactness by local lifts, including on the complement
of the closed image. [ConstantSheafPullback.lean](Normalizer/ConstantSheafPullback.lean)
constructs the constant integer sheaf comparison from actual adjunctions.
The argument then applies mathlib's `Adjunction.extEquiv` for exact adjoints.
It does not treat module-sheaf pullback along a closed immersion as exact.

[ModuleAbelianPushforward.lean](Normalizer/ModuleAbelianPushforward.lean)
identifies actual module pushforward with abelian-sheaf pushforward, preserving
sections, maps and the actual section-cokernel projection.
[SectionCokernelCohomology.lean](Normalizer/SectionCokernelCohomology.lean)
then proves ambient positive-degree cohomology of the actual section cokernel
vanishes. On a proper integral curve, only a nonzero specified section and
genuine pointwise line charts are required: the finite chart cover, generic
nonzeroness and finiteness of D are derived. The determinant specialization
constructs its line charts from pointwise rank-n bundle charts and obtains
nonzeroness from independence of the specified generic germs.

[SectionCohomologyExact.lean](Normalizer/SectionCohomologyExact.lean)
proves that forgetting module structure preserves the actual short exact
sequence. It constructs the canonical connecting map from that sequence's
extension class and proves exactness at the four interior terms of

```text
H^0(O_X) -> H^0(L) -> H^0(i_*i^*L) -> H^1(O_X) -> H^1(L) -> H^1(i_*i^*L).
```

The other maps are the actual `Sheaf.H.map` maps of the specified section
and adjunction restriction. No abstract exact sequence is supplied as a
hypothesis. The actual H⁰ section map is also proved injective. On the
finite-type integral curve, vanishing of the actual quotient's H¹ proves
the H¹ section map surjective. Thus both endpoints needed for the terminated
cohomology sequence are established.

## Restricted-line sections and cohomology scalars now proved

[DiscreteLineTrivialization.lean](Normalizer/DiscreteLineTrivialization.lean)
glues genuine pointwise line charts on singleton opens to construct an actual
sheaf isomorphism O_D ≅ i^*L. Finiteness over the field supplies discreteness;
there is no reducedness, connectedness or nonemptiness assumption on D.
[FiniteLineSections.lean](Normalizer/FiniteLineSections.lean) applies actual
section evaluation and proves the base-field-linear equivalence, finiteness,
dimension equality, and zero-dimension/emptiness equivalence. The actual
pullback charts are constructed from the original line charts. This supplies
the rank-one finite-scheme ingredient of
[Stacks Lemma 33.33.3](https://stacks.math.columbia.edu/tag/0AYT), not its entire
coherent-support and Euler assertion.

[ModulePushforwardSections.lean](Normalizer/ModulePushforwardSections.lean)
preserves the actual structure-morphism scalars, restrictions and maps.
[SectionCokernelSections.lean](Normalizer/SectionCokernelSections.lean) then
constructs the actual comparisons

```text
Gamma(X, cokernel(O_X --s--> L)) ≃_k Gamma(D, i^*L) ≃_k Gamma(D, O_D),
H^0(X, cokernel(O_X --s--> L)) ≃_k Gamma(D, O_D).
```

They derive finiteness and positive dimension when the specified section has
a zero. On the proper integral curve, all actual cohomology groups of this
cokernel are finite over the field; positive degrees vanish. The determinant
specialization derives its line charts and nonzero section from genuine
rank-n charts and independence of the actual generic germs.

[ModuleSheafCohomologyScalars.lean](Normalizer/ModuleSheafCohomologyScalars.lean)
constructs base-field scalars on actual Sheaf.H from actual scalar
endomorphisms. Induced maps and the actual H⁰-to-sections comparison are
linear. [SectionCohomologyLinear.lean](Normalizer/SectionCohomologyLinear.lean)
proves that the original connecting map is linear, using naturality of the
actual short exact sequence's extension class. No scalar compatibility is
supplied as an extra hypothesis.

[ProperLineSectionsFinite.lean](Normalizer/ProperLineSectionsFinite.lean)
proves actual line-bundle section and H⁰ finiteness on proper integral curves
over algebraically closed fields from genuine pointwise line charts. If a
nonzero section exists, exactness at Gamma(X,L), finite constants and the
proved finite cokernel sections suffice; otherwise the section space is zero.
The proof does not assume surjectivity onto sections of the sheaf cokernel,
nor any H¹ finiteness. The algebraically closed base assumption belongs to
this finiteness result; the finite-zero-scheme comparisons allow any field.

## Finite-kernel dimension balance now proved

[SectionCohomologyDimension.lean](Normalizer/SectionCohomologyDimension.lean)
identifies the kernels and ranges of the actual base-field-linear cohomology
maps. On a finite-type integral curve with a nonzero specified line section,
the actual map H¹(O_X) -> H¹(L) has a finite-dimensional kernel. It is
surjective, and H¹(O_X) is finite-dimensional if and only if H¹(L) is.
Neither absolute finiteness assertion follows from this equivalence alone.

For a proper integral curve over an algebraically closed field, the proof
also gives the exact finite-term balance

```text
h⁰(L) + dim_k ker(H¹(O_X) -> H¹(L)) = 1 + dim_k Gamma(D,O_D).
```

All four terms have proved finite dimension. Rank-nullity is applied only
to the finite H⁰ domains of restriction and the connecting map. The scalar
action, D, maps and connecting class are the actual constructions. This
identity does not identify a line degree or use a dimension assigned to an
infinite-dimensional H¹ space.

[SheafCohomologyTerminal.lean](Normalizer/SheafCohomologyTerminal.lean)
constructs the natural comparison H'(F,T,n) ≃ H(F,n) at a terminal object
on a general site. Its degree-zero formula preserves evaluation on the
sheafified identity generator. This supplies the terminal-object comparison
needed to connect mathlib's cohomology-presheaf exact sequences to Sheaf.H.

[OverAbelianExtension.lean](Normalizer/OverAbelianExtension.lean) and
[OverSheafCohomology.lean](Normalizer/OverSheafCohomology.lean) now prove the
small-site comparison

```text
F.H' n U ≃+ (F.over U).H n.
```

The direct-sum extension is constructed, its adjunction with actual slice
restriction is proved, and both functors are proved exact. The representing
object is identified using its actual evaluation property. Naturality in F
and evaluation on the sheafified identity generator in degree zero are
proved. These results require no properness, acyclicity or geometric
exactness premise. The compatible geometric restriction and field-linear specialization are
now constructed below for actual opens of schemes. The degree-one affine theorem is now proved below;
all-degree affine acyclicity is not claimed.

## Actual affine first-cohomology vanishing now proved

[AffinePrincipalLocalization.lean](Normalizer/AffinePrincipalLocalization.lean)
proves that restriction from D(a) to D(a) intersect D(b) in the actual
associated module sheaf is localization away from b.
[AffineCechOne.lean](Normalizer/AffineCechOne.lean) uses two denominator
clearings and a partition of unity to solve every degree-one cocycle on a
finite principal affine cover. This is the degree-one standard-cover result
of [Stacks Lemma 30.2.1](https://stacks.math.columbia.edu/tag/01X9), proved
here directly on actual sections and restrictions.

[AffineSheafLifting.lean](Normalizer/AffineSheafLifting.lean) constructs finite
principal local lifts of a section through an epimorphism of arbitrary
abelian sheaves. With a localizing module sheaf as kernel, exactness on
sections supplies the difference cocycle, the proved correction makes the
lifts compatible, and sheaf gluing produces a global lift. The middle and
quotient sheaves are not assumed quasicoherent or module sheaves.

[AffineH1Vanishing.lean](Normalizer/AffineH1Vanishing.lean) applies this to the
actual injective embedding and its cokernel, and uses mathlib's Ext exact
sequence to prove the following without extra geometric inputs:

```text
Subsingleton (Sheaf.H
  ((schemeModulesToAbelianSheaves (Spec R)).obj (tilde M)) 1).
```

Here R is any commutative ring object and M any R-module. The theorem uses
neither noetherianity, finite generation nor a characteristic restriction.
A corollary gives the same actual H¹ vanishing for every quasicoherent module
sheaf on Spec R, using mathlib's proved quasicoherence/localization criterion.
This formalizes the degree-one Spec R instance of
[Stacks Lemma 30.2.2](https://stacks.math.columbia.edu/tag/01XB). The all-degree affine vanishing theorem is not claimed. Actual geometric
restriction and scalar comparison are now supplied below.

## Exact next cohomology and degree interfaces

The unrestricted geometric finiteness target, including over the algebraically
closed base used in the application, is:

```text
p : X -> Spec(k), IsProper p, IsIntegral X, dim X <= 1
  => Module.Finite k (Sheaf.H (underlying abelian sheaf O_X) 1),
```

with the actual scalar action `schemeModuleCohomologyModule p O_X 1`.
This must be derived from the geometry. It is not an added theorem premise
or a new axiom in the core. Once proved, the actual finite-kernel
finiteness equivalence gives H¹(L) finiteness for the specified nonzero section. The proper
coherent finiteness theorem is a possible general route, but has not been
formalized here. The pinned mathlib sheaf-cohomology and scheme-module files
do not supply this interface; its generic Euler definitions alone do not
prove finiteness or prevent zero values for infinite-dimensional inputs.

The actual affine-open transport is now proved in
[SchemeOpenCohomology.lean](Normalizer/SchemeOpenCohomology.lean):

```text
Subsingleton (((schemeModulesToAbelianSheaves X).obj F).H' 1 U)
```

for any actual affine open U and quasicoherent module sheaf F on X.
[OpenSheafCohomology.lean](Normalizer/OpenSheafCohomology.lean) constructs
the all-degree comparison with topological open restriction, naturally in F.
The geometric module restriction comparison is linear over the structure
field. The scalar actions are independently induced by actual sheaf scalar
endomorphisms; no transported vector-space structure is used to force linearity.
An example applies this to the actual cokernel of a map between finitely
presented module sheaves, deriving its quasicoherence from the proved
cokernel finite-presentation theorem.

[TwoAffineCohomology.lean](Normalizer/TwoAffineCohomology.lean) now uses
mathlib's actual Mayer-Vietoris sequence and the proved affine-open
vanishings. For an actual cover U union V = X by two affine opens, its
original boundary from H0 on the intersection onto actual global H1 is
surjective and base-field linear. Its kernel is exactly the differences
of restrictions from U and V, and the resulting linear quotient
presentation of H1 is constructed. This theorem takes the actual cover as
input. The continuation below constructs it from an actual affine map to P1,
but existence of a suitable finite map for the full curve target remains unproved.
No finite dimension of the intersection section space or quotient is assumed.

## Finite-map route: two supporting results now proved

[LaurentCechFinite.lean](Normalizer/LaurentCechFinite.lean) proves an actual
finite-generation result. Let A = k[T,T^-1], let M be an A-module with a
compatible k-module action, and let v and w be two A-generating families
of M, with v finite. Write P for the k-span of T^n v_i with n >= 0 and Q
for the k-span of T^n w_j with n <= 0. Then

```text
Module.Finite k (M / (P + Q)).
```

The proof constructs a bound B such that all T^n v_i with n <= B belong
to Q. The remaining translates with B <= n <= 0 form a finite family
spanning the quotient. This works over any commutative coefficient ring,
without Noetherianity. Over a field it proves finite dimension. Examples
check arbitrary integer shifts over Z and that T^-1 survives the quotient
over Q by powers >= 0 and powers <= -2. The finite quotient can be nonzero.
This lemma does not identify M, P or Q with actual curve sections.

[CurveFiniteMap.lean](Normalizer/CurveFiniteMap.lean) proves that a given
nonconstant map from a proper integral curve over k to a separated k-scheme
is finite. Properness of the map and Noetherianity of the source are derived.
Every fibre is proved finite: a closed fibre is a proper closed subset of
the curve; a fibre over a nonclosed point contains at most the generic point.
Mathlib's proper/quasi-finite criterion then gives the finite morphism.
This is the integral, nonconstant specialization of
[Stacks Lemma 53.2.4](https://stacks.math.columbia.edu/tag/0CCL), not its full
reducible-source version. No H1 finiteness, projectivity or smoothness is used.

The normal-curve route now constructs the actual map from a specified
rational function. `normalCurve_genericMap_existsUnique` derives valuation
stalks from local Noetherianity, integrality, dimension at most one and
integral closedness of every actual stalk. Properness of the target gives
stalk lifts; spreading out and gluing give the unique actual morphism.
The generic-map statement works over a separated base. This formalizes the
normal-curve extension step of
[Stacks Lemma 53.2.2](https://stacks.math.columbia.edu/tag/0BXZ).

`ProjectiveLine` constructs the actual Proj of k[X0,X1], identifies its
actual degree-zero ring with k, proves its structure map proper, and
constructs the two standard affine opens and their cover. Evaluating
homogeneous coordinates [1:t] on actual global sections gives an actual
base-preserving map, with chart pullbacks equal to the whole source and
the invertibility locus of t. `CurveProjectiveLine` applies this on the
generic stalk and extends the specified map on a normal curve. Choosing
a suitable nonconstant function is not part of that earlier theorem; the
new CurveMapExistence module now supplies it on the normal branch. The zero
function is deliberately allowed; its generic map has empty second chart.

`TwoAffineSections` gives a base-field-linear comparison from actual
open H0 to actual sections and proves compatibility with actual restrictions.
The original Mayer-Vietoris boundary therefore presents global H1 as the
quotient of actual overlap sections by differences of actual restrictions.
For an affine morphism to the constructed projective line, the two
inverse-image charts form an actual affine cover and give this quotient.
For a finite morphism their actual coordinate rings are finite modules over
the corresponding projective-line chart rings, with the action given by
the original sheaf map. These chart results do not need source normality.

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

An alternative general route is [Stacks Lemma 30.19.2](https://stacks.math.columbia.edu/tag/02O6),
via [coherent higher direct images](https://stacks.math.columbia.edu/tag/02O5),
projective vanishing, Chow's lemma and Leray comparison. No ready theorem
providing this chain was found in the pinned mathlib. These are known
mathematical dependencies awaiting formalization. Unrestricted proper
integral curve H1 finiteness remains unproved. The
normal, smooth and one-exceptional-point branches are now proved by the
construction above. A finite affine cover alone does not prove finiteness.

The remaining steps also require curve higher-cohomology vanishing, the
numerical Euler additivity for the actual linear exact sequence, and its
comparison with line-bundle degree. These are the written dependencies behind
[coherent Euler additivity](https://stacks.math.columbia.edu/tag/08AA).

Finally identify the established line degree, the Euler-characteristic
difference in [Stacks Definition 33.44.1](https://stacks.math.columbia.edu/tag/0AYR),
with dim_k Gamma(D,O_D). The proved positive function dimension then gives
positive degree. Defining degree to be the length of this chosen section's
quotient would omit the required comparison. Generic Euler expressions in
the library also require proved finiteness and support bounds before their
numerical values can be used here.

These are missing formalizations of written mathematical dependencies.
No degree function tailored to the conclusion, line-degree positivity assumption,
abstract cohomology dimensions or replacement nonvanishing assumption has
been inserted into the proved core. The complete degree/nonvanishing
theorem and section bound h0(E/M) <= 4 remain unformalized.
